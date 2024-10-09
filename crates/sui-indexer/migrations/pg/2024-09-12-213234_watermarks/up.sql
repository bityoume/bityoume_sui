CREATE TABLE watermarks
(
    -- The table governed by this watermark, i.e `epochs`, `checkpoints`, `transactions`.
    entity                      TEXT          NOT NULL,
    -- Inclusive upper epoch bound for this entity's data. Committer updates this field. Pruner uses
    -- this to determine if pruning is necessary based on the retention policy.
    epoch_hi                    BIGINT        NOT NULL,
    -- Inclusive lower epoch bound for this entity's data. Pruner updates this field when the epoch range exceeds the retention policy.
    epoch_lo                    BIGINT        NOT NULL,
    -- Inclusive upper checkpoint bound for this entity's data. Committer updates this field. All
    -- data of this entity in the checkpoint must be persisted before advancing this watermark. The
    -- committer refers to this on disaster recovery to resume writing.
    checkpoint_hi               BIGINT        NOT NULL,
    -- Inclusive upper transaction sequence number bound for this entity's data. Committer updates
    -- this field.
    tx_hi                       BIGINT        NOT NULL,
    -- Inclusive low watermark that the pruner advances. Corresponds to the epoch id, checkpoint
    -- sequence number, or tx sequence number depending on the entity. Data before this watermark is
    -- considered pruned by a reader. The underlying data may still exist in the db instance.
    reader_lo                   BIGINT        NOT NULL,
    -- Updated using the database's current timestamp when the pruner sees that some data needs to
    -- be dropped. The pruner uses this column to determine whether to prune or wait long enough
    -- that all in-flight reads complete or timeout before it acts on an updated watermark.
    timestamp_ms                BIGINT        NOT NULL,
    -- Column used by the pruner to track its true progress. Data at and below this watermark has
    -- been truly pruned from the db, and should no longer exist. When recovering from a crash, the
    -- pruner will consult this column to determine where to continue.
    pruned_lo                   BIGINT,
    PRIMARY KEY (entity)
);
