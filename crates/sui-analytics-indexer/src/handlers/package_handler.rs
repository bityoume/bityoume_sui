// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use fastcrypto::encoding::{Base64, Encoding};
use std::path::Path;
use std::sync::Arc;

use typed_store::traits::TableSummary;
use typed_store::traits::TypedStoreDebug;

use sui_indexer::framework::Handler;
use sui_rest_api::CheckpointData;
use sui_types::base_types::ObjectID;
use sui_types::full_checkpoint_content::CheckpointTransaction;
use sui_types::object::Object;
use sui_types::transaction::{Command, TransactionDataAPI, TransactionKind};
use typed_store::rocks::{DBMap, MetricConf};
use typed_store::Map;
use typed_store_derive::DBMapUtils;

use crate::handlers::AnalyticsHandler;
use crate::package_store::Error;
use crate::tables::MovePackageEntry;
use crate::FileType;

#[derive(DBMapUtils)]
pub struct PackageLineageMappingDB {
    // maps an upgraded package's object id to its root version object id
    pub(crate) packages: DBMap<ObjectID, ObjectID>,
}

impl PackageLineageMappingDB {
    pub fn new(path: &Path) -> Arc<Self> {
        Arc::new(Self::open_tables_read_write(
            path.to_path_buf(),
            MetricConf::new("package_mapping"),
            None,
            None,
        ))
    }
    pub(crate) fn update(
        &self,
        package_id: ObjectID,
        root_package_id: ObjectID,
    ) -> sui_package_resolver::Result<()> {
        let mut batch = self.packages.batch();
        batch
            .insert_batch(
                &self.packages,
                std::iter::once((package_id, root_package_id)),
            )
            .map_err(Error::TypedStore)?;
        batch.write().map_err(Error::TypedStore)?;
        Ok(())
    }

    pub(crate) fn get(
        &self,
        package_id: &ObjectID,
    ) -> sui_package_resolver::Result<Option<ObjectID>> {
        let root_package_id = self.packages.get(package_id).map_err(Error::TypedStore)?;
        Ok(root_package_id)
    }
}

pub struct PackageHandler {
    packages: Vec<MovePackageEntry>,
    package_lineage_mapping_db: Arc<PackageLineageMappingDB>,
}

#[async_trait::async_trait]
impl Handler for PackageHandler {
    fn name(&self) -> &str {
        "package"
    }
    async fn process_checkpoint(&mut self, checkpoint_data: &CheckpointData) -> Result<()> {
        let CheckpointData {
            checkpoint_summary,
            transactions: checkpoint_transactions,
            ..
        } = checkpoint_data;
        for checkpoint_transaction in checkpoint_transactions {
            self.process_transaction(
                checkpoint_summary.epoch,
                checkpoint_summary.sequence_number,
                checkpoint_summary.timestamp_ms,
                checkpoint_transaction,
            )?;
        }
        Ok(())
    }
}

#[async_trait::async_trait]
impl AnalyticsHandler<MovePackageEntry> for PackageHandler {
    fn read(&mut self) -> Result<Vec<MovePackageEntry>> {
        let cloned = self.packages.clone();
        self.packages.clear();
        Ok(cloned)
    }

    fn file_type(&self) -> Result<FileType> {
        Ok(FileType::MovePackage)
    }
}

impl PackageHandler {
    pub fn new(path: &Path) -> Self {
        PackageHandler {
            packages: vec![],
            package_lineage_mapping_db: PackageLineageMappingDB::new(path),
        }
    }
    fn process_transaction(
        &mut self,
        epoch: u64,
        checkpoint: u64,
        timestamp_ms: u64,
        checkpoint_transaction: &CheckpointTransaction,
    ) -> Result<()> {
        let transaction = &checkpoint_transaction.transaction;
        let packages: Vec<ObjectID> = match transaction.transaction_data().kind() {
            TransactionKind::ProgrammableTransaction(ptb) => ptb
                .commands
                .iter()
                .map(|cmd| match cmd {
                    Command::Upgrade(_, _, prev_object_id, _) => Some(*prev_object_id),
                    Command::Publish(_, _)
                    | Command::MoveCall(_)
                    | Command::TransferObjects(_, _)
                    | Command::SplitCoins(_, _)
                    | Command::MergeCoins(_, _)
                    | Command::MakeMoveVec(_, _) => None,
                })
                .collect(),
            TransactionKind::ChangeEpoch(_)
            | TransactionKind::Genesis(_)
            | TransactionKind::ConsensusCommitPrologue(_)
            | TransactionKind::AuthenticatorStateUpdate(_)
            | TransactionKind::EndOfEpochTransaction(_)
            | TransactionKind::RandomnessStateUpdate(_)
            | TransactionKind::ConsensusCommitPrologueV2(_) => vec![None],
        }
        .iter()
        .flatten()
        .cloned()
        .collect();
        let prev_package_id = if packages.is_empty() || packages.len() > 1 {
            None
        } else {
            packages.first().cloned()
        };
        for object in checkpoint_transaction.output_objects.iter() {
            self.process_package(epoch, checkpoint, timestamp_ms, object, prev_package_id)?;
        }
        Ok(())
    }
    fn process_package(
        &mut self,
        epoch: u64,
        checkpoint: u64,
        timestamp_ms: u64,
        object: &Object,
        prev_package_id: Option<ObjectID>,
    ) -> Result<()> {
        if let sui_types::object::Data::Package(p) = &object.data {
            let package_id = p.id();
            let root_package_id = if let Some(prev_package_id) = prev_package_id {
                // handle upgrade
                if let Some(root_package_id) =
                    self.package_lineage_mapping_db.get(&prev_package_id)?
                {
                    self.package_lineage_mapping_db
                        .update(package_id, root_package_id)?;
                    root_package_id
                } else {
                    self.package_lineage_mapping_db
                        .update(package_id, prev_package_id)?;
                    prev_package_id
                }
            } else {
                // handle publish
                self.package_lineage_mapping_db
                    .update(package_id, package_id)?;
                package_id
            };
            let package = MovePackageEntry {
                package_id: p.id().to_string(),
                checkpoint,
                epoch,
                timestamp_ms,
                bcs: Base64::encode(bcs::to_bytes(p).unwrap()),
                transaction_digest: object.previous_transaction.to_string(),
                root_package_id: Some(root_package_id.to_string()),
            };
            self.packages.push(package)
        }
        Ok(())
    }
}
