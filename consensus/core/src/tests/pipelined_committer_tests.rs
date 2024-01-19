// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::sync::Arc;

use consensus_config::AuthorityIndex;
use parking_lot::RwLock;

use crate::{
    block::{BlockAPI, Slot, TestBlock, Transaction, VerifiedBlock},
    commit::{LeaderStatus, DEFAULT_WAVE_LENGTH},
    context::Context,
    dag_state::DagState,
    storage::mem_store::MemStore,
    test_dag::{build_dag, build_dag_layer},
    universal_committer::universal_committer_builder::UniversalCommitterBuilder,
};

/// Commit one leader.
#[test]
fn direct_commit() {
    telemetry_subscribers::init_for_testing();
    // Commitee of 4 with even stake
    let context = Arc::new(Context::new_for_test(4));
    let dag_state = Arc::new(RwLock::new(DagState::new(
        context.clone(),
        Arc::new(MemStore::new()),
    )));

    // Create committer with pipelining and only 1 leader per round
    let committer = UniversalCommitterBuilder::new(context.clone(), dag_state.clone())
        .with_pipeline(true)
        .build();

    // note: with pipelining but no multi-leader enabled there should be 3 committers.
    let decision_round_wave_0_pipeline_1 = committer.committers[1].decision_round(0);
    build_dag(context, dag_state, None, decision_round_wave_0_pipeline_1);

    let last_committed = Slot::new_for_test(0, 0);
    let sequence = committer.try_commit(last_committed);
    // note: pipelines are zero indexed
    tracing::info!("Commit sequence: {sequence:?}");
    assert_eq!(sequence.len(), 1);

    let leader_round_wave_0_pipeline_1 = committer.committers[1].leader_round(0);
    if let LeaderStatus::Commit(ref block) = sequence[0] {
        assert_eq!(
            block.author(),
            committer.get_leaders(leader_round_wave_0_pipeline_1)[0]
        );
    } else {
        panic!("Expected a committed leader")
    };
}

/// Ensure idempotent replies.
#[test]
fn idempotence() {
    telemetry_subscribers::init_for_testing();
    // Commitee of 4 with even stake
    let context = Arc::new(Context::new_for_test(4));
    let dag_state = Arc::new(RwLock::new(DagState::new(
        context.clone(),
        Arc::new(MemStore::new()),
    )));

    // Create committer with pipelining and only 1 leader per round
    let committer = UniversalCommitterBuilder::new(context.clone(), dag_state.clone())
        .with_pipeline(true)
        .build();

    // Add enough blocks to reach decision round of pipeline 1 wave 0.
    let decision_round_pipeline_1_wave_0 = committer.committers[1].decision_round(0);
    build_dag(
        context.clone(),
        dag_state.clone(),
        None,
        decision_round_pipeline_1_wave_0,
    );

    // Commit one block.
    let last_committed = Slot::new_for_test(0, 0);
    let committed = committer.try_commit(last_committed);
    assert_eq!(committed.len(), 1);
    tracing::info!("Commit sequence: {committed:?}");

    // Ensure we don't commit it again.
    let last = committed.into_iter().last().unwrap();
    let last_committed = Slot::new(last.round(), last.authority());
    let sequence = committer.try_commit(last_committed);
    tracing::info!("Commit sequence: {sequence:?}");
    assert!(sequence.is_empty());
}

/// Commit one by one each leader as the dag progresses in ideal conditions.
#[test]
fn multiple_direct_commit() {
    telemetry_subscribers::init_for_testing();
    // Commitee of 4 with even stake
    let context = Arc::new(Context::new_for_test(4));
    let dag_state = Arc::new(RwLock::new(DagState::new(
        context.clone(),
        Arc::new(MemStore::new()),
    )));
    let wave_length = DEFAULT_WAVE_LENGTH;

    // Create committer with pipelining and only 1 leader per round
    let committer = UniversalCommitterBuilder::new(context.clone(), dag_state.clone())
        .with_pipeline(true)
        .build();

    let mut last_committed = Slot::new_for_test(0, 0);
    let mut ancestors = None;
    for n in 1..=10 {
        let pipeline = n % wave_length as usize;
        let wave_number = committer.committers[pipeline].wave_number(n as u32);
        let decision_round = committer.committers[pipeline].decision_round(wave_number);
        let leader_round = committer.committers[pipeline].leader_round(wave_number);

        ancestors = Some(build_dag(
            context.clone(),
            dag_state.clone(),
            ancestors,
            decision_round,
        ));

        let sequence = committer.try_commit(last_committed);
        tracing::info!("Commit sequence: {sequence:?}");

        assert_eq!(sequence.len(), 1);
        if let LeaderStatus::Commit(ref block) = sequence[0] {
            assert_eq!(
                block.author(),
                *committer.get_leaders(leader_round).first().unwrap()
            );
        } else {
            panic!("Expected a committed leader")
        }

        let last = sequence.into_iter().last().unwrap();
        last_committed = Slot::new(last.round(), last.authority());
    }
}

/// Commit 10 leaders in a row (calling the committer after adding them).
#[test]
fn direct_commit_late_call() {
    telemetry_subscribers::init_for_testing();
    // Commitee of 4 with even stake
    let context = Arc::new(Context::new_for_test(4));
    let dag_state = Arc::new(RwLock::new(DagState::new(
        context.clone(),
        Arc::new(MemStore::new()),
    )));
    let wave_length = DEFAULT_WAVE_LENGTH;

    // Create committer with pipelining and only 1 leader per round
    let committer = UniversalCommitterBuilder::new(context.clone(), dag_state.clone())
        .with_pipeline(true)
        .build();

    let n = 10;
    let pipeline = n % wave_length as usize;
    let wave_number = committer.committers[pipeline].wave_number(n as u32);
    let decision_round = committer.committers[pipeline].decision_round(wave_number);

    build_dag(context.clone(), dag_state.clone(), None, decision_round);

    let last_committed = Slot::new_for_test(0, 0);
    let sequence = committer.try_commit(last_committed);
    tracing::info!("Commit sequence: {sequence:#?}");

    assert_eq!(sequence.len(), n);
    for (i, leader_block) in sequence.iter().enumerate() {
        // First sequenced leader should be in round 1.
        let leader_round = i as u32 + 1;
        if let LeaderStatus::Commit(ref block) = leader_block {
            assert_eq!(block.author(), committer.get_leaders(leader_round)[0]);
        } else {
            panic!("Expected a committed leader")
        };
    }
}

/// Do not commit anything if we are still in the first wave.
#[test]
fn no_genesis_commit() {
    telemetry_subscribers::init_for_testing();
    // Commitee of 4 with even stake
    let context = Arc::new(Context::new_for_test(4));
    let dag_state = Arc::new(RwLock::new(DagState::new(
        context.clone(),
        Arc::new(MemStore::new()),
    )));

    // Create committer with pipelining and only 1 leader per round
    let committer = UniversalCommitterBuilder::new(context.clone(), dag_state.clone())
        .with_pipeline(true)
        .build();

    // Pipeline 0 wave 0 will not have a commit because its leader round is the
    // genesis round.
    let decision_round_pipeline_0_wave_0 = committer.committers[0].decision_round(0);

    let mut ancestors = None;
    for r in 0..decision_round_pipeline_0_wave_0 {
        ancestors = Some(build_dag(context.clone(), dag_state.clone(), ancestors, r));

        let last_committed = Slot::new_for_test(0, 0);
        let sequence = committer.try_commit(last_committed);
        tracing::info!("Commit sequence: {sequence:?}");
        assert!(sequence.is_empty());
    }
}

/// We do not commit anything if we miss the first leader.
#[test]
fn no_leader() {
    telemetry_subscribers::init_for_testing();
    // Commitee of 4 with even stake
    let context = Arc::new(Context::new_for_test(4));
    let dag_state = Arc::new(RwLock::new(DagState::new(
        context.clone(),
        Arc::new(MemStore::new()),
    )));

    // Create committer with pipelining and only 1 leader per round
    let committer = UniversalCommitterBuilder::new(context.clone(), dag_state.clone())
        .with_pipeline(true)
        .build();

    // Add enough blocks to reach the decision round of the first leader of pipeline 1
    // (but without the leader).
    let leader_round_pipeline_1_wave_0 = committer.committers[1].leader_round(0);
    let leader_pipeline_1_wave_0 = committer.get_leaders(leader_round_pipeline_1_wave_0)[0];

    let genesis: Vec<_> = context
        .committee
        .authorities()
        .map(|index| {
            let author_idx = index.0.value() as u32;
            let block = TestBlock::new(0, author_idx).build();
            VerifiedBlock::new_for_test(block).reference()
        })
        .collect();
    let connections = context
        .committee
        .authorities()
        .filter(|&authority| authority.0 != leader_pipeline_1_wave_0)
        .map(|authority| (authority.0, genesis.clone()))
        .collect::<Vec<_>>();
    let references = build_dag_layer(connections, dag_state.clone());

    let decision_round_pipeline_1_wave_0 = committer.committers[1].decision_round(0);
    build_dag(
        context.clone(),
        dag_state.clone(),
        Some(references),
        decision_round_pipeline_1_wave_0,
    );

    // Ensure no blocks are committed.
    let last_committed = Slot::new_for_test(0, 0);
    let sequence = committer.try_commit(last_committed);
    tracing::info!("Commit sequence: {sequence:?}");

    assert_eq!(sequence.len(), 1);
    if let LeaderStatus::Skip(leader) = sequence[0] {
        assert_eq!(leader.authority, leader_pipeline_1_wave_0);
        assert_eq!(leader.round, leader_round_pipeline_1_wave_0);
    } else {
        panic!("Expected to directly skip the leader");
    }
}

/// We directly skip the leader if it has enough blame.
#[test]
fn direct_skip() {
    telemetry_subscribers::init_for_testing();
    // Commitee of 4 with even stake
    let context = Arc::new(Context::new_for_test(4));
    let dag_state = Arc::new(RwLock::new(DagState::new(
        context.clone(),
        Arc::new(MemStore::new()),
    )));

    // Create committer with pipelining and only 1 leader per round
    let committer = UniversalCommitterBuilder::new(context.clone(), dag_state.clone())
        .with_pipeline(true)
        .build();

    // Add enough blocks to reach the first leader.
    let leader_round_1 = 1;
    let references_round_1 = build_dag(context.clone(), dag_state.clone(), None, leader_round_1);

    // Filter out that leader.
    let references_without_leader_1: Vec<_> = references_round_1
        .into_iter()
        .filter(|x| x.author != *committer.get_leaders(leader_round_1).first().unwrap())
        .collect();

    // Add enough blocks to reach the decision round of the first leader.
    let decision_round_1 = committer.committers[1].decision_round(0);
    build_dag(
        context.clone(),
        dag_state.clone(),
        Some(references_without_leader_1),
        decision_round_1,
    );

    let last_committed = Slot::new_for_test(0, 0);
    let sequence = committer.try_commit(last_committed);
    tracing::info!("Commit sequence: {sequence:?}");

    assert_eq!(sequence.len(), 1);
    if let LeaderStatus::Skip(leader) = sequence[0] {
        assert_eq!(leader.authority, committer.get_leaders(leader_round_1)[0]);
        assert_eq!(leader.round, leader_round_1);
    } else {
        panic!("Expected to directly skip the leader");
    }
}

/// Indirect-commit the first leader.
#[test]
fn indirect_commit() {
    telemetry_subscribers::init_for_testing();
    // Commitee of 4 with even stake
    let context = Arc::new(Context::new_for_test(4));
    let dag_state = Arc::new(RwLock::new(DagState::new(
        context.clone(),
        Arc::new(MemStore::new()),
    )));
    let wave_length = DEFAULT_WAVE_LENGTH;

    // Create committer with pipelining and only 1 leader per round
    let committer = UniversalCommitterBuilder::new(context.clone(), dag_state.clone())
        .with_pipeline(true)
        .build();

    // Add enough blocks to reach the 1st leader.
    let leader_round_1 = 1;
    let references_round_1 = build_dag(context.clone(), dag_state.clone(), None, leader_round_1);

    // Filter out that leader.
    let references_without_leader_1: Vec<_> = references_round_1
        .iter()
        .cloned()
        .filter(|x| x.author != *committer.get_leaders(leader_round_1).first().unwrap())
        .collect();

    // Only 2f+1 validators vote for the 1st leader.
    let connections_with_leader_1 = context
        .committee
        .authorities()
        .take(context.committee.quorum_threshold() as usize)
        .map(|authority| (authority.0, references_round_1.clone()))
        .collect();
    let references_with_votes_for_leader_1 =
        build_dag_layer(connections_with_leader_1, dag_state.clone());

    let connections_without_leader_1 = context
        .committee
        .authorities()
        .skip(context.committee.quorum_threshold() as usize)
        .map(|authority| (authority.0, references_without_leader_1.clone()))
        .collect();
    let references_without_votes_for_leader_1 =
        build_dag_layer(connections_without_leader_1, dag_state.clone());

    // Only f+1 validators certify the 1st leader.
    let mut references_round_3 = Vec::new();

    let connections_with_votes_for_leader_1 = context
        .committee
        .authorities()
        .take(context.committee.validity_threshold() as usize)
        .map(|authority| (authority.0, references_with_votes_for_leader_1.clone()))
        .collect::<Vec<_>>();
    references_round_3.extend(build_dag_layer(
        connections_with_votes_for_leader_1,
        dag_state.clone(),
    ));

    let references: Vec<_> = references_without_votes_for_leader_1
        .into_iter()
        .chain(references_with_votes_for_leader_1)
        .take(context.committee.quorum_threshold() as usize)
        .collect();
    let connections_without_votes_for_leader_1 = context
        .committee
        .authorities()
        .skip(context.committee.validity_threshold() as usize)
        .map(|authority| (authority.0, references.clone()))
        .collect::<Vec<_>>();
    references_round_3.extend(build_dag_layer(
        connections_without_votes_for_leader_1,
        dag_state.clone(),
    ));

    // Add enough blocks to decide the 5th leader. The second leader will be skipped
    // (it was the vote for the first leader that we removed) so we add enough blocks
    // to indirectly skip it.
    let leader_round_5 = 5;
    let pipeline_leader_5 = leader_round_5 % wave_length as usize;
    let wave_leader_5 = committer.committers[pipeline_leader_5].wave_number(leader_round_5 as u32);
    let decision_round_5 = committer.committers[pipeline_leader_5].decision_round(wave_leader_5);
    build_dag(
        context.clone(),
        dag_state.clone(),
        Some(references_round_3),
        decision_round_5,
    );

    // Ensure we commit the first leaders.
    let last_committed = Slot::new_for_test(0, 0);
    let sequence = committer.try_commit(last_committed);
    tracing::info!("Commit sequence: {sequence:?}");
    assert_eq!(sequence.len(), 5);

    let committed_leader_round = 1;
    let leader = committer.get_leaders(committed_leader_round)[0];
    if let LeaderStatus::Commit(ref block) = sequence[0] {
        assert_eq!(block.author(), leader);
    } else {
        panic!("Expected a committed leader")
    };

    let skipped_leader_round = 2;
    let leader = committer.get_leaders(skipped_leader_round)[0];
    if let LeaderStatus::Skip(ref slot) = sequence[1] {
        assert_eq!(slot.authority, leader);
    } else {
        panic!("Expected a skipped leader")
    };
}

/// Commit the first 3 leaders, skip the 4th, and commit the next 3 leaders.
#[test]
fn indirect_skip() {
    telemetry_subscribers::init_for_testing();
    // Commitee of 4 with even stake
    let context = Arc::new(Context::new_for_test(4));
    let dag_state = Arc::new(RwLock::new(DagState::new(
        context.clone(),
        Arc::new(MemStore::new()),
    )));
    let wave_length = DEFAULT_WAVE_LENGTH;

    // Create committer with pipelining and only 1 leader per round
    let committer = UniversalCommitterBuilder::new(context.clone(), dag_state.clone())
        .with_pipeline(true)
        .build();

    // Add enough blocks to reach the 4th leader.
    let leader_round_4 = 4;
    let references_round_4 = build_dag(context.clone(), dag_state.clone(), None, leader_round_4);

    // Filter out that leader.
    let references_without_leader_4: Vec<_> = references_round_4
        .iter()
        .cloned()
        .filter(|x| x.author != *committer.get_leaders(leader_round_4).first().unwrap())
        .collect();

    // Only f+1 validators connect to the 4th leader.
    let mut references_round_5 = Vec::new();

    let connections_with_leader_4 = context
        .committee
        .authorities()
        .take(context.committee.validity_threshold() as usize)
        .map(|authority| (authority.0, references_round_4.clone()))
        .collect::<Vec<_>>();
    references_round_5.extend(build_dag_layer(
        connections_with_leader_4,
        dag_state.clone(),
    ));

    let connections_without_leader_4 = context
        .committee
        .authorities()
        .skip(context.committee.validity_threshold() as usize)
        .map(|authority| (authority.0, references_without_leader_4.clone()))
        .collect();
    references_round_5.extend(build_dag_layer(
        connections_without_leader_4,
        dag_state.clone(),
    ));

    // Add enough blocks to reach the decision round of the 7th leader.
    let leader_round_7 = 7;
    let pipeline_leader_7 = leader_round_7 % wave_length as usize;
    let wave_leader_7 = committer.committers[pipeline_leader_7].wave_number(leader_round_7 as u32);
    let decision_round_7 = committer.committers[pipeline_leader_7].decision_round(wave_leader_7);
    build_dag(
        context.clone(),
        dag_state.clone(),
        Some(references_round_5),
        decision_round_7,
    );

    // Ensure we commit the first 3 leaders, skip the 4th, and commit the last 2 leaders.
    let last_committed = Slot::new_for_test(0, 0);
    let sequence = committer.try_commit(last_committed);
    tracing::info!("Commit sequence: {sequence:#?}");
    assert_eq!(sequence.len(), 7);

    // Ensure we commit the first 3 leaders.
    for i in 0..=2 {
        // First sequenced leader should be in round 1.
        let leader_round = i + 1;
        let leader = committer.get_leaders(leader_round)[0];
        if let LeaderStatus::Commit(ref block) = sequence[i as usize] {
            assert_eq!(block.author(), leader);
        } else {
            panic!("Expected a committed leader")
        };
    }

    // Ensure we skip the leader of wave 1 (pipeline one) but commit the others.
    if let LeaderStatus::Skip(leader) = sequence[3] {
        assert_eq!(leader.authority, committer.get_leaders(leader_round_4)[0]);
        assert_eq!(leader.round, leader_round_4);
    } else {
        panic!("Expected a skipped leader")
    }

    // Ensure we commit the last 3 leaders.
    for i in 4..=6 {
        let leader_round = i + 1;
        let leader = committer.get_leaders(leader_round)[0];
        if let LeaderStatus::Commit(ref block) = sequence[i as usize] {
            assert_eq!(block.author(), leader);
        } else {
            panic!("Expected a committed leader")
        };
    }
}

/// If there is no leader with enough support nor blame, we commit nothing.
#[test]
fn undecided() {
    telemetry_subscribers::init_for_testing();
    // Commitee of 4 with even stake
    let context = Arc::new(Context::new_for_test(4));
    let dag_state = Arc::new(RwLock::new(DagState::new(
        context.clone(),
        Arc::new(MemStore::new()),
    )));

    // Create committer with pipelining and only 1 leader per round
    let committer = UniversalCommitterBuilder::new(context.clone(), dag_state.clone())
        .with_pipeline(true)
        .build();

    // Add enough blocks to reach the first leader.
    let leader_round_1 = 1;
    let references_round_1 = build_dag(context.clone(), dag_state.clone(), None, leader_round_1);

    // Filter out that leader.
    let references_1_without_leader: Vec<_> = references_round_1
        .iter()
        .cloned()
        .filter(|x| x.author != *committer.get_leaders(leader_round_1).first().unwrap())
        .collect();

    // Create a dag layer where only one authority votes for the first leader.
    let mut authorities = context.committee.authorities();
    let leader_connection = vec![(authorities.next().unwrap().0, references_round_1)];
    let non_leader_connections: Vec<_> = authorities
        .take((context.committee.quorum_threshold() - 1) as usize)
        .map(|authority| (authority.0, references_1_without_leader.clone()))
        .collect();

    let connections = leader_connection
        .into_iter()
        .chain(non_leader_connections)
        .collect::<Vec<_>>();
    let references_voting_round_1 = build_dag_layer(connections, dag_state.clone());

    // Add enough blocks to reach the first decision round
    let decision_round_1 = committer.committers[1].decision_round(0);
    build_dag(
        context.clone(),
        dag_state.clone(),
        Some(references_voting_round_1),
        decision_round_1,
    );

    // Ensure no blocks are committed.
    let last_committed = Slot::new_for_test(0, 0);
    let sequence = committer.try_commit(last_committed);
    tracing::info!("Commit sequence: {sequence:?}");
    assert!(sequence.is_empty());
}

// This test scenario has one authority that is acting in a byzantine manner. It
// will be sending multiple different blocks to different validators for a round.
// The commit rule should handle this and correctly commit the expected blocks.
// However when extra dag layers are added and the byzantine node is meant to be
// a leader, its block is skipped as there is not enough votes to directly
// decide it and not any certified links to indirectly commit it.
#[test]
fn test_byzantine_validator() {
    telemetry_subscribers::init_for_testing();
    // Commitee of 4 with even stake
    let context = Arc::new(Context::new_for_test(4));
    let dag_state = Arc::new(RwLock::new(DagState::new(
        context.clone(),
        Arc::new(MemStore::new()),
    )));

    // Create committer with pipelining and only 1 leader per round
    let committer = UniversalCommitterBuilder::new(context.clone(), dag_state.clone())
        .with_pipeline(true)
        .build();

    // Add enough blocks to reach leader A12
    let leader_round_12 = 12;
    let references_leader_round_12 =
        build_dag(context.clone(), dag_state.clone(), None, leader_round_12);

    // Add blocks to reach voting round for leader A12
    let voting_round_12 = leader_round_12 + 1;
    // This includes a "good vote" from validator B which is acting as a byzantine validator
    let good_references_voting_round_wave_4 = build_dag(
        context.clone(),
        dag_state.clone(),
        Some(references_leader_round_12.clone()),
        voting_round_12,
    );

    // DagState Update:
    // - A12 got a good vote from 'B' above
    // - A12 will then get a bad vote from 'B' indirectly through the ancenstors of
    //   the decision round blocks (B, C, & D) of leader A12

    // Add block layer for decision round of leader A12 with no votes for leader A12
    // from a byzantine validator B that sent different blocks to all validators.

    // Filter out leader A12
    let leader_wave_4 = committer.get_leaders(leader_round_12)[0];
    let references_without_leader_round_wave_4: Vec<_> = references_leader_round_12
        .into_iter()
        .filter(|x| x.author != leader_wave_4)
        .collect();

    // Accept these references/blocks as ancestors from decision round blocks in dag state
    let byzantine_block_b13_1 = VerifiedBlock::new_for_test(
        TestBlock::new(13, 1)
            .set_ancestors(references_without_leader_round_wave_4.clone())
            .set_transactions(vec![Transaction::new(vec![1])])
            .build(),
    );
    dag_state
        .write()
        .accept_block(byzantine_block_b13_1.clone());

    let byzantine_block_b13_2 = VerifiedBlock::new_for_test(
        TestBlock::new(13, 1)
            .set_ancestors(references_without_leader_round_wave_4.clone())
            .set_transactions(vec![Transaction::new(vec![2])])
            .build(),
    );
    dag_state
        .write()
        .accept_block(byzantine_block_b13_2.clone());

    let byzantine_block_b13_3 = VerifiedBlock::new_for_test(
        TestBlock::new(13, 1)
            .set_ancestors(references_without_leader_round_wave_4)
            .set_transactions(vec![Transaction::new(vec![3])])
            .build(),
    );
    dag_state
        .write()
        .accept_block(byzantine_block_b13_3.clone());

    // Ancestors of decision blocks in round 14 should include multiple byzantine non-votes B13
    // but there are enough good votes to prevent a skip. Additionally only one of the non-votes
    // per authority should be counted so we should not skip leader A12.
    let mut references_round_14 = vec![];
    let decison_block_a14 = VerifiedBlock::new_for_test(
        TestBlock::new(14, 0)
            .set_ancestors(good_references_voting_round_wave_4.clone())
            .build(),
    );
    references_round_14.push(decison_block_a14.reference());
    dag_state.write().accept_block(decison_block_a14.clone());

    let good_references_voting_round_wave_4_without_b13 = good_references_voting_round_wave_4
        .into_iter()
        .filter(|r| r.author != AuthorityIndex::new_for_test(1))
        .collect::<Vec<_>>();

    let decison_block_b14 = VerifiedBlock::new_for_test(
        TestBlock::new(14, 1)
            .set_ancestors(
                good_references_voting_round_wave_4_without_b13
                    .iter()
                    .cloned()
                    .chain(std::iter::once(byzantine_block_b13_1.reference()))
                    .collect(),
            )
            .build(),
    );
    references_round_14.push(decison_block_b14.reference());
    dag_state.write().accept_block(decison_block_b14.clone());

    let decison_block_c14 = VerifiedBlock::new_for_test(
        TestBlock::new(14, 2)
            .set_ancestors(
                good_references_voting_round_wave_4_without_b13
                    .iter()
                    .cloned()
                    .chain(std::iter::once(byzantine_block_b13_2.reference()))
                    .collect(),
            )
            .build(),
    );
    references_round_14.push(decison_block_c14.reference());
    dag_state.write().accept_block(decison_block_c14.clone());

    let decison_block_d14 = VerifiedBlock::new_for_test(
        TestBlock::new(14, 3)
            .set_ancestors(
                good_references_voting_round_wave_4_without_b13
                    .iter()
                    .cloned()
                    .chain(std::iter::once(byzantine_block_b13_3.reference()))
                    .collect(),
            )
            .build(),
    );
    references_round_14.push(decison_block_d14.reference());
    dag_state.write().accept_block(decison_block_d14.clone());

    // DagState Update:
    // - We have A13, B13, D13 & C13 as good votes in the voting round of leader A12
    // - We have 3 byzantine B13 nonvotes that we received as ancestors from decision
    //   round blocks from B, C, & D.
    // - We have  B14, C14 & D14 that include this byzantine nonvote and A14 from the
    //   decision round. But all of these blocks also have good votes from A, B, C & D.

    // Expect a successful direct commit of A12 and leaders at rounds 1 ~ 11 as
    // pipelining is enabled.
    let last_decided = Slot::new_for_test(0, 0);
    let sequence = committer.try_commit(last_decided);
    tracing::info!("Commit sequence: {sequence:?}");

    assert_eq!(sequence.len(), 12);
    if let LeaderStatus::Commit(ref block) = sequence[3] {
        assert_eq!(block.author(), committer.get_leaders(leader_round_12)[0])
    } else {
        panic!("Expected a committed leader")
    };

    // Now build an additional dag layer on top of the existing dag so a commit
    // decision can be made about leader B13 which is the byzantine validator.
    let references_round_15 = build_dag(
        context.clone(),
        dag_state.clone(),
        Some(references_round_14),
        15,
    );

    // Ensure B13 is marked as undecided as there is <2f+1 blame and <2f+1 certs
    let last_sequenced = sequence.last().unwrap();
    let last_decided = Slot::new(last_sequenced.round(), last_sequenced.authority());
    let sequence = committer.try_commit(last_decided);
    tracing::info!("Commit sequence: {sequence:?}");
    assert!(sequence.is_empty());

    // Now build an additional 3 dag layers on top of the existing dag so a commit
    // decision can be made about leader A16 and then an indirect decision can be
    // made about B13
    build_dag(
        context.clone(),
        dag_state.clone(),
        Some(references_round_15),
        18,
    );
    let sequence = committer.try_commit(last_decided);
    tracing::info!("Commit sequence: {sequence:?}");
    assert_eq!(sequence.len(), 4);

    // Ensure we skip B13 as there is no way to have a certified link to any one
    // of the multiple blocks at slot B13.
    let skipped_leader_round = 13;
    let leader = *committer.get_leaders(skipped_leader_round).first().unwrap();
    if let LeaderStatus::Skip(ref slot) = sequence[0] {
        assert_eq!(slot.authority, leader);
    } else {
        panic!("Expected a skipped leader")
    };
}
