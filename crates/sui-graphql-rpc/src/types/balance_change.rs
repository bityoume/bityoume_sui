// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use async_graphql::*;
use sui_json_rpc_types::BalanceChange as StoredBalanceChange;
use sui_types::object::Owner as NativeOwner;

use super::{big_int::BigInt, move_type::MoveType, owner::Owner, sui_address::SuiAddress};
use crate::error::Error;

pub(crate) struct BalanceChange {
    stored: StoredBalanceChange,
    // BalanceChange is only available when a tx has been indexed, so it will always have a
    // checkpoint_sequence_number
    checkpoint_viewed_at: u64,
}

/// Effects to the balance (sum of coin values per coin type) owned by an address or object.
#[Object]
impl BalanceChange {
    /// The address or object whose balance has changed.
    async fn owner(&self) -> Option<Owner> {
        use NativeOwner as O;

        match self.stored.owner {
            O::AddressOwner(addr) | O::ObjectOwner(addr) => Some(Owner {
                address: SuiAddress::from(addr),
                checkpoint_viewed_at: Some(self.checkpoint_viewed_at),
            }),

            O::Shared { .. } | O::Immutable => None,
        }
    }

    /// The inner type of the coin whose balance has changed (e.g. `0x2::sui::SUI`).
    async fn coin_type(&self) -> Option<MoveType> {
        Some(MoveType::new(self.stored.coin_type.clone()))
    }

    /// The signed balance change.
    async fn amount(&self) -> Option<BigInt> {
        Some(BigInt::from(self.stored.amount))
    }
}

impl BalanceChange {
    pub(crate) fn read(bytes: &[u8], checkpoint_viewed_at: u64) -> Result<Self, Error> {
        let stored = bcs::from_bytes(bytes)
            .map_err(|e| Error::Internal(format!("Error deserializing BalanceChange: {e}")))?;

        Ok(Self {
            stored,
            checkpoint_viewed_at,
        })
    }
}
