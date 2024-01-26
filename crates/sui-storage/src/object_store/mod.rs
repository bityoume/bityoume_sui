// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Result};
use async_trait::async_trait;
use bytes::Bytes;
use futures::stream::BoxStream;
use object_store::path::Path;
use object_store::{DynObjectStore, ObjectMeta};
use std::sync::Arc;

pub mod http;
pub mod util;

// /// Object-store type.
// #[derive(Debug, Copy, Clone, PartialEq, Eq, Deserialize, Serialize, ValueEnum)]
// pub enum ObjectStoreType {
//     /// Local file system
//     File,
//     /// AWS S3
//     S3,
//     /// Google Cloud Store
//     GCS,
//     /// Azure Blob Store
//     Azure,
// }

// #[derive(Default, Debug, Clone, Deserialize, Serialize, Args)]
// #[serde(rename_all = "kebab-case")]
// pub struct ObjectStoreConfig {
//     /// Which object storage to use. If not specified, defaults to local file system.
//     #[serde(skip_serializing_if = "Option::is_none")]
//     #[arg(value_enum)]
//     pub object_store: Option<ObjectStoreType>,
//     /// Path of the local directory. Only relevant is `--object-store` is File
//     #[serde(skip_serializing_if = "Option::is_none")]
//     #[arg(long)]
//     pub directory: Option<PathBuf>,
//     /// Name of the bucket to use for the object store. Must also set
//     /// `--object-store` to a cloud object storage to have any effect.
//     #[serde(skip_serializing_if = "Option::is_none")]
//     #[arg(long)]
//     pub bucket: Option<String>,
//     /// When using Amazon S3 as the object store, set this to an access key that
//     /// has permission to read from and write to the specified S3 bucket.
//     #[serde(skip_serializing_if = "Option::is_none")]
//     #[arg(long)]
//     pub aws_access_key_id: Option<String>,
//     /// When using Amazon S3 as the object store, set this to the secret access
//     /// key that goes with the specified access key ID.
//     #[serde(skip_serializing_if = "Option::is_none")]
//     #[arg(long)]
//     pub aws_secret_access_key: Option<String>,
//     /// When using Amazon S3 as the object store, set this to bucket endpoint
//     #[serde(skip_serializing_if = "Option::is_none")]
//     #[arg(long)]
//     pub aws_endpoint: Option<String>,
//     /// When using Amazon S3 as the object store, set this to the region
//     /// that goes with the specified bucket
//     #[serde(skip_serializing_if = "Option::is_none")]
//     #[arg(long)]
//     pub aws_region: Option<String>,
//     #[serde(skip_serializing_if = "Option::is_none")]
//     #[arg(long)]
//     pub aws_profile: Option<String>,
//     /// Enable virtual hosted style requests
//     #[serde(default)]
//     #[arg(long, default_value_t = true)]
//     pub aws_virtual_hosted_style_request: bool,
//     /// Allow unencrypted HTTP connection to AWS.
//     #[serde(default)]
//     #[arg(long, default_value_t = true)]
//     pub aws_allow_http: bool,
//     /// When using Google Cloud Storage as the object store, set this to the
//     /// path to the JSON file that contains the Google credentials.
//     #[serde(skip_serializing_if = "Option::is_none")]
//     #[arg(long)]
//     pub google_service_account: Option<String>,
//     /// When using Google Cloud Storage as the object store and writing to a
//     /// bucket with Requester Pays enabled, set this to the project_id
//     /// you want to associate the write cost with.
//     #[serde(skip_serializing_if = "Option::is_none")]
//     #[arg(long)]
//     pub google_project_id: Option<String>,
//     /// When using Microsoft Azure as the object store, set this to the
//     /// azure account name
//     #[serde(skip_serializing_if = "Option::is_none")]
//     #[arg(long)]
//     pub azure_storage_account: Option<String>,
//     /// When using Microsoft Azure as the object store, set this to one of the
//     /// keys in storage account settings
//     #[serde(skip_serializing_if = "Option::is_none")]
//     #[arg(long)]
//     pub azure_storage_access_key: Option<String>,
//     #[serde(default = "default_object_store_connection_limit")]
//     #[arg(long, default_value_t = 20)]
//     pub object_store_connection_limit: usize,
//     #[serde(default)]
//     #[arg(long, default_value_t = false)]
//     pub no_sign_request: bool,
// }

// fn default_object_store_connection_limit() -> usize {
//     20
// }

#[async_trait]
pub trait ObjectStoreGetExt: std::fmt::Display + Send + Sync + 'static {
    /// Return the bytes at given path in object store
    async fn get_bytes(&self, src: &Path) -> Result<Bytes>;
}

macro_rules! as_ref_get_ext_impl {
    ($type:ty) => {
        #[async_trait]
        impl ObjectStoreGetExt for $type {
            async fn get_bytes(&self, src: &Path) -> Result<Bytes> {
                self.as_ref().get_bytes(src).await
            }
        }
    };
}

as_ref_get_ext_impl!(Arc<dyn ObjectStoreGetExt>);
as_ref_get_ext_impl!(Box<dyn ObjectStoreGetExt>);

#[async_trait]
impl ObjectStoreGetExt for Arc<DynObjectStore> {
    async fn get_bytes(&self, src: &Path) -> Result<Bytes> {
        self.get(src)
            .await?
            .bytes()
            .await
            .map_err(|e| anyhow!("Failed to get file: {} with error: {}", src, e.to_string()))
    }
}

#[async_trait]
pub trait ObjectStoreListExt: Send + Sync + 'static {
    /// List the objects at the given path in object store
    async fn list_objects(
        &self,
        src: Option<&Path>,
    ) -> object_store::Result<BoxStream<'_, object_store::Result<ObjectMeta>>>;
}

macro_rules! as_ref_list_ext_impl {
    ($type:ty) => {
        #[async_trait]
        impl ObjectStoreListExt for $type {
            async fn list_objects(
                &self,
                src: Option<&Path>,
            ) -> object_store::Result<BoxStream<'_, object_store::Result<ObjectMeta>>> {
                self.as_ref().list_objects(src).await
            }
        }
    };
}

as_ref_list_ext_impl!(Arc<dyn ObjectStoreListExt>);
as_ref_list_ext_impl!(Box<dyn ObjectStoreListExt>);

#[async_trait]
impl ObjectStoreListExt for Arc<DynObjectStore> {
    async fn list_objects(
        &self,
        src: Option<&Path>,
    ) -> object_store::Result<BoxStream<'_, object_store::Result<ObjectMeta>>> {
        self.list(src).await
    }
}

#[async_trait]
pub trait ObjectStorePutExt: Send + Sync + 'static {
    /// Write the bytes at the given location in object store
    async fn put_bytes(&self, src: &Path, bytes: Bytes) -> Result<()>;
}

macro_rules! as_ref_put_ext_impl {
    ($type:ty) => {
        #[async_trait]
        impl ObjectStorePutExt for $type {
            async fn put_bytes(&self, src: &Path, bytes: Bytes) -> Result<()> {
                self.as_ref().put_bytes(src, bytes).await
            }
        }
    };
}

as_ref_put_ext_impl!(Arc<dyn ObjectStorePutExt>);
as_ref_put_ext_impl!(Box<dyn ObjectStorePutExt>);

#[async_trait]
impl ObjectStorePutExt for Arc<DynObjectStore> {
    async fn put_bytes(&self, src: &Path, bytes: Bytes) -> Result<()> {
        self.put(src, bytes).await?;
        Ok(())
    }
}

#[async_trait]
pub trait ObjectStoreDeleteExt: Send + Sync + 'static {
    /// Delete the object at the given location in object store
    async fn delete_object(&self, src: &Path) -> Result<()>;
}

macro_rules! as_ref_delete_ext_impl {
    ($type:ty) => {
        #[async_trait]
        impl ObjectStoreDeleteExt for $type {
            async fn delete_object(&self, src: &Path) -> Result<()> {
                self.as_ref().delete_object(src).await
            }
        }
    };
}

as_ref_delete_ext_impl!(Arc<dyn ObjectStoreDeleteExt>);
as_ref_delete_ext_impl!(Box<dyn ObjectStoreDeleteExt>);

#[async_trait]

impl ObjectStoreDeleteExt for Arc<DynObjectStore> {
    async fn delete_object(&self, src: &Path) -> Result<()> {
        self.delete(src).await?;
        Ok(())
    }
}
