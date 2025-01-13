use bitcoin::{
    Amount,
    script::Builder,
    consensus::Encodable,
    absolute::LockTime,
    OutPoint,
    relative::LockTime as RelativeLockTime,
    Script,
    ScriptBuf,
    TapNodeHash,
    Transaction,
    Txid,
    transaction::TxIn,
    transaction::TxOut,
    blockdata::transaction::Version,
    taproot::LeafVersion,
    opcodes::OP_TRUE,
    VarInt,
    Witness,
    XOnlyPublicKey,
};

use bitcoin::hashes::{
    Hash,
    sha256::Midstate,
    sha256::Hash as Sha256,
    sha256::HashEngine as Sha256Engine,
};

use bitcoin::opcodes::all::{
    OP_CLTV as OP_CHECKLOCKTIMEVERIFY,
    OP_CSV as OP_CHECKSEQUENCEVERIFY,
    OP_CHECKSIGVERIFY,
    OP_RETURN_204 as OP_CHECKSIGFROMSTACK,
    OP_NOP4 as OP_CHECKTEMPLATEVERIFY,
    OP_DROP,
    OP_ELSE,
    OP_ENDIF,
    OP_EQUALVERIFY,
    OP_NOP,
    OP_IF,
    OP_GREATERTHAN,
    OP_OVER,
    OP_RETURN_205 as OP_PAIRCOMMIT,
    OP_RETURN,
    OP_SHA256,
    OP_SWAP,
    OP_TUCK,
    OP_VERIFY,
};

use bitcoin::secp256k1::{
    Secp256k1,
    Signing,
    Verification,
};

use rayon::{
    iter::ParallelIterator,
    iter::IntoParallelIterator,
};

use std::{
    io::Write,
    ops::Deref,
    collections::BTreeMap
};

use crate::{
    choose_k,
    builder_with_capacity,
    dummy_input,
    ephemeral_anchor,
    ilog2_ceil,
    get_default_template,
    paircommit,
    paircommit_merkle_commit,
    PartyId,
    PartySet,
    StateUpdate,
    taptree_commit,
};

#[derive(Clone,Eq,PartialEq,PartialOrd,Ord)]
enum Unpenalized {
    None,
    OnlyLastUpdater(PartyId),
    Both {
        last_updater: PartyId,
        maybe_penalize: PartyId,
    },
}

#[derive(Clone,Eq,PartialEq,PartialOrd,Ord)]
struct PenaltyState {
    // Could be implicit but I'm pretty sure this will make a few things simpler
    can_update: PartySet,
    cant_update: PartySet,
    unpenalized: Unpenalized,
}

impl PenaltyState {
    #[cfg(test)]
    fn is_valid(&self) -> bool {
        for party in self.can_update.iter() {
            if self.cant_update.contains(*party) {
                return false;
            }
        }
        match self.unpenalized {
            Unpenalized::None => true,
            Unpenalized::OnlyLastUpdater(last_updater) => self.cant_update.contains(last_updater),
            Unpenalized::Both { last_updater, maybe_penalize } => {
                self.cant_update.contains(last_updater)
                    && self.cant_update.contains(maybe_penalize)
            },
        }
    }
}

// FIXME: do we need to account for the "start" state? (has/doesn't have last_updater and/or
// maybe_penalize) I don't think so right now
#[derive(Debug,PartialEq,Eq)]
enum Transition {
    /// A transition implicitly proving the previous state was revoked because it's more than one
    /// state old. Penalizes both the last updater and the maybe penalized parties.
    PenaltyTransition(usize, PartyId),
    /// A transition that does not penalize the last updater because the state was only advanced by
    /// one. However the maybe penalized party is still penalized.
    NonPenaltyTransition(usize, PartyId),
}

impl Transition {
    fn get_index(&self) -> usize {
        match self {
            Transition::PenaltyTransition(i, _) => *i,
            Transition::NonPenaltyTransition(i, _) => *i,
        }
    }
}

/// Compact representation of `Transition`
struct TransitionRepr(u32); 

impl TransitionRepr {
    const DISC_BITS: u32 = 1;
    const DISC_SHIFT: u32 = u32::BITS - Self::DISC_BITS;
    const DISC_MASK: u32 = 0x01;

    const PENALTY_DISC: u32 = 0;
    const NON_PENALTY_DISC: u32 = 1 << (u32::BITS - Self::DISC_BITS);

    const UPDATER_BITS: u32 = 5; // 32 is generous for the performance we can actually achieve
    const UPDATER_SHIFT: u32 = u32::BITS - Self::UPDATER_BITS - Self::DISC_BITS;
    const UPDATER_MASK: u32 = 0x1F;
    const UPDATER_MAX: PartyId = Self::UPDATER_MASK as PartyId;

    const INDEX_SHIFT: u32 = 0;
    const INDEX_MASK: u32 = u32::MAX >> (Self::DISC_BITS + Self::UPDATER_BITS);
    const INDEX_MAX: u32 = u32::MAX >> (Self::DISC_BITS + Self::UPDATER_BITS);

    fn combine(discriminant: u32, updater: PartyId, index: usize) -> u32 {
        assert!(index <= (Self::INDEX_MAX as usize));
        assert!(updater <= Self::UPDATER_MAX);

        discriminant
            | (((updater as u32) & Self::UPDATER_MASK) << Self::UPDATER_SHIFT)
            | index as u32
    }

    fn from_transition(transition: &Transition) -> Self {
        match transition {
            Transition::PenaltyTransition(i, updater) => Self(
                Self::combine(Self::PENALTY_DISC, *updater, *i)
            ),
            Transition::NonPenaltyTransition(i, updater) => Self(
                Self::combine(Self::NON_PENALTY_DISC, *updater, *i)
            ),
        }
    }

    fn into_transition(&self) -> Transition {
        let discriminant = self.0 & (Self::DISC_MASK << Self::DISC_SHIFT);
        let updater = (self.0 >> Self::UPDATER_SHIFT) & Self::UPDATER_MASK;
        let index = (self.0 >> Self::INDEX_SHIFT) & Self::INDEX_MASK;

        match discriminant {
            Self::PENALTY_DISC =>
                Transition::PenaltyTransition(index as usize, updater as PartyId),
            Self::NON_PENALTY_DISC =>
                Transition::NonPenaltyTransition(index as usize, updater as PartyId),
            _ => unreachable!()
        }
    }
}

pub struct GenerationInfo {
    transactions: Vec<TransactionParameters>,
    depth: u32,
}

pub struct TransactionParameters {
    can_update: PartySet,
    penalized: PartySet,
    transitions: Vec<TransitionRepr>,
}

impl TransactionParameters {
    fn build_settlement_tx<C: Verification>(&self, secp: &Secp256k1<C>, builder: &UpdateTransactionSetBuilder, split: &Vec<Amount>) -> Transaction {
        let (mut split, penalty_amounts): (Vec<_>, Vec<_>) = split.iter()
            .zip(builder.keys.iter())
            .zip(self.penalized.iter_dense())
            .map(|((amount, key), party_id)| {
                (party_id, key, *amount)
            })
            .partition(|(party_id, _, _)| party_id.is_some());

        let penalty_amount = penalty_amounts.into_iter().fold(
            Amount::from_sat(0),
            |total, (_, _, amount)| total + amount
        );

        let party_count: u64 = builder.keys.len() as u64;

        let penalty_amount = penalty_amount.to_sat();

        let penalty_per_remaining = Amount::from_sat(penalty_amount / party_count);

        // FIXME: just send remainder to fees?
        let mut remainder = penalty_amount % party_count;

        for i in 0..split.len() {
            if remainder < 1 {
                break;
            }

            split[i].2 += penalty_per_remaining + Amount::ONE_SAT;
            remainder -= 1;
        }
        let output: Vec<_> = split.into_iter()
            .map(|(_, key, value)| {
                TxOut {
                    value,
                    script_pubkey: ScriptBuf::new_p2tr(secp, *key, None),
                }
            })
            .collect();

        // FIXME: do we want/need another ephemeral anchor or should we have one of the parties
        // CPFP?

        Transaction {
            version: Version::non_standard(3),
            lock_time: LockTime::ZERO,
            input: vec![dummy_input(builder.settlement_relative_timelock)],
            output,
        }
    }
}

pub struct UpdateTransactionSetBuilder {
    keys: Vec<XOnlyPublicKey>,
    generations: Vec<GenerationInfo>,
    total_amount: Amount,
    settlement_relative_timelock: RelativeLockTime,
}

impl UpdateTransactionSetBuilder {
    pub fn from_parties(keys: Vec<XOnlyPublicKey>, total_amount: Amount, settlement_relative_timelock: RelativeLockTime) -> Self {
        let mut state_generations = Vec::new();

        let parties = PartySet::first_n(keys.len());

        for generation_index in 0..parties.len() {
            let mut state_generation = Vec::new();

            let can_update_subset_len = parties.len() - generation_index;

            for can_update_subset in choose_k(&parties, can_update_subset_len).into_iter() {
                let mut cant_update_subset = parties.clone();

                // TODO: if it ends up being warranted, we can do something faster like make a
                // version of choose_k() that partitions parties instead of chooses
                for party in can_update_subset.iter() {
                    cant_update_subset.remove(*party);
                }

                state_generation.push(PenaltyState {
                    can_update: can_update_subset.clone(),
                    cant_update: cant_update_subset.clone(),
                    unpenalized: Unpenalized::None,
                });

                if cant_update_subset.len() >= 2 {
                    // last_updated and next_to_be_penalized
                    for non_penalty_subset in choose_k(&cant_update_subset, 2).into_iter() {
                        assert_eq!(non_penalty_subset.len(), 2);

                        let penalty_subset = {
                            let mut penalty_subset = cant_update_subset.clone();

                            for party in non_penalty_subset.iter() {
                                penalty_subset.remove(*party);
                            }

                            penalty_subset
                        };

                        state_generation.push(PenaltyState {
                            can_update: can_update_subset.clone(),
                            cant_update: cant_update_subset.clone(),
                            unpenalized: Unpenalized::Both {
                                last_updater: non_penalty_subset[0],
                                maybe_penalize: non_penalty_subset[1],
                            },
                        });

                        state_generation.push(PenaltyState {
                            can_update: can_update_subset.clone(),
                            cant_update: cant_update_subset.clone(),
                            unpenalized: Unpenalized::Both {
                                last_updater: non_penalty_subset[1],
                                maybe_penalize: non_penalty_subset[0],
                            },
                        });
                    }
                }

                for last_updater in cant_update_subset.iter() {
                    state_generation.push(PenaltyState {
                        can_update: can_update_subset.clone(),
                        cant_update: cant_update_subset.clone(),
                        unpenalized: Unpenalized::OnlyLastUpdater(
                            *last_updater
                        ),
                    })
                }
            }

            let state_generation_index_map: BTreeMap<_, _> = state_generation.iter().enumerate()
                    .map(|(i, state)| (state.clone(), i))
                    .collect();

            state_generations.push((state_generation, state_generation_index_map));
        }

        let mut generations = Vec::new();
        for (i, (state_generation, _generation_index_map)) in state_generations.iter().enumerate() {
            let next_generation_index = i + 1;

            // (next) depth
            let depth = state_generations.get(next_generation_index)
                .map(|generation| ilog2_ceil(generation.0.len()))
                .unwrap_or(0);

            let mut transactions = Vec::new();

            for PenaltyState { can_update, cant_update, unpenalized } in state_generation.iter() {
                let mut transitions = Vec::new();
                if next_generation_index < state_generations.len() {
                    assert!(can_update.len() > 0);

                    let next_generation = &state_generations[i + 1].1;

                    for party in can_update.iter() {
                        let new_can_update = {
                            let mut can_update = can_update.clone();
                            can_update.remove(*party);

                            can_update
                        };

                        let new_cant_update = {
                            let mut cant_update = cant_update.clone();
                            cant_update.add(*party);

                            cant_update
                        };

                        let new_unpenalized_non_penalty = match unpenalized {
                            Unpenalized::None => Unpenalized::OnlyLastUpdater(*party),
                            Unpenalized::OnlyLastUpdater(last_updater) => Unpenalized::Both{
                                last_updater: *party,
                                maybe_penalize: *last_updater,
                            },
                            Unpenalized::Both { last_updater, maybe_penalize: _ } => Unpenalized::Both {
                                last_updater: *party,
                                maybe_penalize: *last_updater,
                            },
                        };

                        let index = next_generation[&PenaltyState {
                            can_update: new_can_update.clone(),
                            cant_update: new_cant_update.clone(),
                            unpenalized: new_unpenalized_non_penalty,
                        }].clone();

                        transitions.push(
                            TransitionRepr::from_transition(&Transition::NonPenaltyTransition(index, *party))
                        );

                        let new_unpenalized_penalty = Unpenalized::OnlyLastUpdater(*party);

                        let index = next_generation[&PenaltyState {
                            can_update: new_can_update,
                            cant_update: new_cant_update,
                            unpenalized: new_unpenalized_penalty,
                        }].clone();

                        transitions.push(
                            TransitionRepr::from_transition(&Transition::PenaltyTransition(index, *party))
                        );
                    }

                } else {
                    // FIXME: is there anything to do?
                    assert_eq!(can_update.len(), 1);
                }

                let mut penalized = cant_update.clone();

                match unpenalized {
                    Unpenalized::None => {}
                    Unpenalized::OnlyLastUpdater(last_updater) => {
                        penalized.remove(*last_updater);
                    }
                    Unpenalized::Both { last_updater, maybe_penalize } => {
                        penalized.remove(*last_updater);
                        penalized.remove(*maybe_penalize);
                    }
                }

                transactions.push(TransactionParameters {
                    can_update: can_update.clone(),
                    penalized,
                    transitions,
                });
            }

            generations.push(GenerationInfo {
                transactions,
                depth,
            });
        }

        Self {
            generations,
            keys,
            total_amount,
            settlement_relative_timelock,
        }
    }

    const BASE_TIME: u32 = 500000000;
    const NUMS_POINT: Sha256 = Sha256::const_hash("nothing-up-my-sleevee".as_bytes());

    pub fn get_update_commitment<C: Verification>(&self, secp: &Secp256k1<C>, update: &StateUpdate) -> Sha256 {
        let mut commitments: Vec<Sha256> = Vec::new();

        // Generation 0 is in the commitment transaction
        for (i, generation) in self.generations.iter().enumerate().skip(1) {
            let depth = generation.depth;

            let new_script_builder = UpdateScriptBuilder::new(self.keys.len() - i, i, depth as usize);

            let tx_templates = (&generation.transactions).into_par_iter()
                .map_with(new_script_builder, |script_builder, transaction_params| {
                    let internal_key = XOnlyPublicKey::from_slice(Self::NUMS_POINT.as_ref())
                            .unwrap();

                    let mut tap_nodes: Vec<TapNodeHash> = Vec::with_capacity(transaction_params.transitions.len() + 1);

                    let settlement_tx_tapleaf_hash = {
                        let settlement_tx = transaction_params.build_settlement_tx(secp, &self, &update.split);
                        let settlement_tx_template = get_default_template(&settlement_tx, 0);

                        let builder = builder_with_capacity(33 + 1)
                            .push_slice(settlement_tx_template.as_byte_array())
                            .push_opcode(OP_CHECKTEMPLATEVERIFY);

                        TapNodeHash::from_script(builder.as_script(), LeafVersion::TapScript)
                    };

                    // FIXME: put this on key path instead? means more musig though
                    tap_nodes.push(settlement_tx_tapleaf_hash);

                    if i + 1 < self.generations.len() {
                        tap_nodes.extend(
                            transaction_params.transitions.iter()
                                .map(|transition| {
                                    let transition = transition.into_transition();

                                    script_builder.build_script(self, update, &transition);

                                    script_builder.as_tap_node()
                                })
                        );
                    }

                    let root_node_hash = taptree_commit(tap_nodes.into_iter(), 8);

                    let output = TxOut {
                        value: self.total_amount,
                        script_pubkey: ScriptBuf::new_p2tr(secp, internal_key, Some(root_node_hash)),
                    };

                    Transaction {
                        version: Version::non_standard(3),
                        lock_time: LockTime::from_time(Self::BASE_TIME + update.state)
                            .expect("Cannot build valid nLockTime"),
                        input: vec![dummy_input(RelativeLockTime::ZERO)],
                        output: vec![output, ephemeral_anchor()],
                    }
                });

            let tx_templates: Vec<Sha256> = tx_templates
                    .map(|tx| get_default_template(&tx, 0))
                    .collect();

            let commitment = paircommit_merkle_commit(
                tx_templates.into_iter(),
                depth as usize
            );

            commitments.push(commitment);
        }

        let mut rhs = commitments.pop().unwrap();

        while let Some(lhs) = commitments.pop() {
            rhs = paircommit(lhs, rhs);
        }

        rhs
    }

    fn iter_keys(&self) -> impl Iterator<Item=(PartyId, &XOnlyPublicKey)> {
        self.keys.iter().enumerate().map(|(index, key)| (index as PartyId, key))
    }
}

#[derive(Clone)]
struct UpdateScriptBuilder {
    buffer: Vec<u8>,
    generation: usize,
    depth: usize,
}

impl UpdateScriptBuilder {
    fn new(party_count: usize, generation: usize, depth: usize) -> Self {
        // honestly we don't even really need to estimate if we reuse the buffer...
        let script_size =
            5 // script num
            + 2 // CSV DROP
            + (32 + 1) // updater pubkey + push opcode
            + 1 // CHECKSIGVERIFY
            + 1 // CTV
            + (2 * generation) // SWAP|NOP PAIRCOMMIT * generation
            + (2 * depth) // SWAP|NOP PAIRCOMMIT * depth
            + (party_count - 1) * (32 + 1) // pubkey bytes plus push opcode
            + (party_count - 1) * 3 // TUCK CSFS VERIFY
            - 1 // Last CSFS doesn't need a VERIFY
            + 0; //

        Self {
            buffer: Vec::with_capacity(script_size),
            generation,
            depth,
        }
    }

    // A little janky but we want the builder to continue owning the buffer. Re-evaluate interface
    // when we have lots of free time.
    fn build_script(&mut self, update_builder: &UpdateTransactionSetBuilder, update: &StateUpdate, transition: &Transition) {
        let (penalty, mut next_state_index, party_id) = match transition {
            Transition::PenaltyTransition(index, party_id) => (true, *index, *party_id),
            Transition::NonPenaltyTransition(index, party_id) => (false, *index, *party_id),
        };

        let key = update_builder.keys[party_id as usize];

        // We could also just build the script once and replace things in it here. Would be
        // *slightly* faster, probably not enough to be worth it.
        // We actually have a large(?) opportunity to avoid copies by swapping the auth sig
        // and the csfs sig in place instead of writing all of the keys 
        // Need to keep track of the last auth key used to know how to build the next script 
        let party_count = update_builder.keys.len();
        let mut buffer = std::mem::replace(&mut self.buffer, Vec::new());
        buffer.truncate(0);
        let mut builder = Builder::from(buffer)
            .push_int((update.state + 1) as i64)
            .push_opcode(OP_CHECKLOCKTIMEVERIFY)
            .push_opcode(OP_DROP)
            .push_x_only_key(&key)
            .push_opcode(OP_CHECKSIGVERIFY)
            .push_opcode(OP_CHECKTEMPLATEVERIFY);

        for _ in 0..self.depth {
            if (next_state_index & 1) == 1 {
                builder = builder
                    .push_opcode(OP_NOP)
                    .push_opcode(OP_PAIRCOMMIT);
            } else {
                builder = builder
                    .push_opcode(OP_SWAP)
                    .push_opcode(OP_PAIRCOMMIT);
            }

            next_state_index = next_state_index >> 1;
        }
        assert_eq!(next_state_index, 0);

        for _ in 1..self.generation {
            builder = builder
                .push_opcode(OP_PAIRCOMMIT);
        }

        if self.generation == party_count {
            // Last generation is the right leaf
            builder = builder
                .push_opcode(OP_PAIRCOMMIT);
        } else {
            builder = builder
                .push_opcode(OP_SWAP)
                .push_opcode(OP_PAIRCOMMIT);
        }

        // FIXME: can a malicious party malleate a penalty tx into non penalty? I think not because the
        // penalty settlement CTV affects the tx...
        // XXX: What the hell did I even mean by this?
        if penalty {
            // Either the state number is > S + 1 (which implies a revocation for S exists)
            // or explicitly provide a revocation signature if we're updating to S + 1

            // or... 2DUP PAIRCOMMIT SWAP <S + 1> LTE IF SHA256 ENDIF? no, doesn't work, needs a
            // OVER SWAP PAIRCOMMIT SWAP <S + 1> LTE IF SHA256 ENDIF
            builder = builder
                .push_opcode(OP_OVER)
                .push_int((update.state + 1) as i64)
                .push_opcode(OP_GREATERTHAN)
                .push_opcode(OP_IF)
                    .push_opcode(OP_PAIRCOMMIT)
                .push_opcode(OP_ELSE)
                    .push_opcode(OP_PAIRCOMMIT)
                    .push_opcode(OP_SHA256)
                .push_opcode(OP_ENDIF);
        } else {
            builder = builder
                .push_opcode(OP_OVER)
                .push_int((update.state + 1) as i64)
                .push_opcode(OP_EQUALVERIFY)
                .push_opcode(OP_PAIRCOMMIT);
        }

        let mut keys_iter = update_builder.iter_keys()
            .filter(|(this_key_party_id, _key)| *this_key_party_id != party_id)
            .peekable();

        while let Some((_this_key_party_id, key)) = keys_iter.next() {
            builder = builder
                .push_opcode(OP_TUCK)
                .push_x_only_key(key)
                .push_opcode(OP_CHECKSIGFROMSTACK);

            // Last key doesn't need a VERIFY
            if keys_iter.peek().is_some() {
                builder = builder
                    .push_opcode(OP_VERIFY);
            }
        }

        let mut buffer = builder.into_bytes();

        std::mem::swap(&mut self.buffer, &mut buffer);
    }

    pub fn as_script(&self) -> &Script {
        Script::from_bytes(&self.buffer)
    }

    pub fn as_tap_node(&self) -> TapNodeHash {
        TapNodeHash::from_script(Script::from_bytes(&self.buffer), LeafVersion::TapScript)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn transition_roundtrip(transition: Transition) {
        let repr = TransitionRepr::from_transition(&transition);

        assert_eq!(transition, repr.into_transition());
    }

    #[test]
    fn test_transition_repr() {
        transition_roundtrip(Transition::PenaltyTransition(42, 3));

        transition_roundtrip(Transition::NonPenaltyTransition(TransitionRepr::INDEX_MAX as usize, 8));

        transition_roundtrip(Transition::PenaltyTransition(TransitionRepr::INDEX_MAX as usize, 8));
    }
}
