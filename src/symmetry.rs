use bitcoin::{
    Amount,
    script::Builder,
    absolute::LockTime,
    relative::LockTime as RelativeLockTime,
    Script,
    ScriptBuf,
    TapNodeHash,
    Transaction,
    transaction::TxOut,
    blockdata::transaction::Version,
    taproot::LeafVersion,
    XOnlyPublicKey,
};

use bitcoin::hashes::{
    Hash,
    sha256::Hash as Sha256,
};

use bitcoin::opcodes::all::{
    OP_CLTV as OP_CHECKLOCKTIMEVERIFY,
    OP_CHECKSIGVERIFY,
    OP_RETURN_204 as OP_CHECKSIGFROMSTACK,
    OP_NOP4 as OP_CHECKTEMPLATEVERIFY,
    OP_DROP,
    OP_NOP,
    OP_RETURN_205 as OP_PAIRCOMMIT,
    OP_SWAP,
    OP_TUCK,
    OP_VERIFY,
};

use bitcoin::secp256k1::{
    Secp256k1,
    Verification,
};

use rayon::{
    iter::IntoParallelRefIterator,
    iter::ParallelIterator,
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

struct Transition {
    next_state_index: usize,
    // FIXME: do we care? we already know next state id
    updating_party: PartyId,
}

struct TransactionParameters {
    can_update: PartySet,
    transitions: Vec<Transition>,
}

struct GenerationInfo {
    transactions: Vec<TransactionParameters>,
    depth: u32,
}

pub struct UpdateTransactionSetBuilder {
    generations: Vec<GenerationInfo>,
    keys: Vec<XOnlyPublicKey>,
    total_amount: Amount,
    settlement_relative_timelock: RelativeLockTime,
}

impl UpdateTransactionSetBuilder {
    pub fn from_parties(keys: Vec<XOnlyPublicKey>, total_amount: Amount, settlement_relative_timelock: RelativeLockTime) -> Self {
        let mut state_generations = Vec::new();

        let parties = PartySet::first_n(keys.len());

        for i in 0..parties.len() {
            let mut state_generation = Vec::new();
            let mut state_generation_index_map = BTreeMap::new();

            for (i, subset) in choose_k(&parties, parties.len() - i).into_iter().enumerate() {
                state_generation_index_map.insert(subset.clone(), i);
                state_generation.push(subset);
            }

            state_generations.push((state_generation, state_generation_index_map));
        }

        let generations = state_generations.iter().enumerate()
            .map(|(generation_index, (state_generation, index_map))| {
                let next_generation_index = generation_index + 1;

                let mut transactions = Vec::new();

                for can_update_parties in state_generation.iter() {
                    let mut transitions = Vec::new();
                    assert!(can_update_parties.len() > 0);

                    if let Some((_, ref next_generation)) = state_generations.get(next_generation_index) {
                        for party in can_update_parties.iter() {
                            let new_can_update_parties = {
                                let mut parties = can_update_parties.clone();
                                parties.remove(*party);

                                parties
                            };

                            let index = next_generation[&new_can_update_parties];

                            transitions.push(Transition {
                                next_state_index: index,
                                updating_party: party.clone(),
                            });
                        }

                        transactions.push(TransactionParameters {
                            can_update: can_update_parties.clone(),
                            transitions,
                        });
                    } else {
                        // The last generation only needs to be able to add the settlement tx
                        // FIXME: inline settlement into this tx
                        transactions.push(TransactionParameters {
                            can_update: can_update_parties.clone(),
                            transitions: Vec::new(),
                        });
                        assert_eq!(can_update_parties.len(), 1);
                    }
                }

                GenerationInfo {
                    transactions,
                    depth: ilog2_ceil(state_generation.len()),
                }
            })
            .collect();

        Self {
            generations,
            keys,
            total_amount,
            settlement_relative_timelock,
        }
    }

    fn depth_for_generation_len(generation_length: usize) -> u32 {
        assert!(generation_length != 0);

        if generation_length == 1 {
            1
        } else {
            ilog2_ceil(generation_length)
        }
    }

    const BASE_TIME: u32 = 500000000;
    const NUMS_POINT: Sha256 = Sha256::const_hash("nothing-up-my-sleevee".as_bytes());

    fn get_pubkey(&self, party: PartyId) -> Option<&XOnlyPublicKey> {
        self.keys.get(party as usize)
    }

    pub fn get_update_commitment<C: Verification>(&self, secp: &Secp256k1<C>, update: &StateUpdate) -> Sha256 {
        let party_count = self.keys.len();

        let mut commitments: Vec<Sha256> = Vec::new();

        // XXX: Non-penalty version
        let settlement_tx_tapleaf_hash = {
            let parties = PartySet(self.keys.iter().enumerate().map(|(index, _)| (index + 1) as PartyId).collect());
            let settlement_tx = self.build_settlement_tx(secp, &parties, update);
            let settlement_tx_template = get_default_template(&settlement_tx, 0);

            let builder = builder_with_capacity(33 + 1)
                .push_slice(settlement_tx_template.as_byte_array())
                .push_opcode(OP_CHECKTEMPLATEVERIFY);

            TapNodeHash::from_script(builder.as_script(), LeafVersion::TapScript)
        };

        // Generation 0 is in the commitment transaction
        for (generation_index, generation) in self.generations.iter().enumerate().skip(1) {
            let can_update_parties_count = self.keys.len() - generation_index;
            let new_script_builder = UpdateScriptBuilder::new(can_update_parties_count, generation_index, generation.depth);

            let tx_templates = generation.transactions.par_iter()
                .map_with(new_script_builder, |script_builder, transaction_params| {
                    let internal_key = XOnlyPublicKey::from_slice(Self::NUMS_POINT.as_ref())
                            .unwrap();

                    let mut tap_nodes: Vec<TapNodeHash> = Vec::with_capacity(transaction_params.transitions.len() + 1);

                    // FIXME: put this on key path instead? means more musig though
                    tap_nodes.push(settlement_tx_tapleaf_hash);

                    if generation_index + 1 < party_count {
                        tap_nodes.extend(
                            transaction_params.transitions.iter()
                                .map(|transition| {
                                    script_builder.build_script(self, update, transition.updating_party, transition.next_state_index);

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
                generation.depth as usize,
            );

            commitments.push(commitment);
        }

        let mut rhs = commitments.pop().unwrap();

        while let Some(lhs) = commitments.pop() {
            rhs = paircommit(lhs, rhs);
        }

        rhs
    }

    fn build_settlement_tx<C: Verification>(&self, secp: &Secp256k1<C>, parties: &PartySet, update: &StateUpdate) -> Transaction {
        assert!(parties.len() > 0);

        let output: Vec<_> = update.split.iter()
            .zip(self.keys.iter())
            .map(|(value, key)| {
                TxOut {
                    value: *value,
                    script_pubkey: ScriptBuf::new_p2tr(secp, *key, None),
                }
            })
            .collect();

        // FIXME: do we want/need another ephemeral anchor or should we have one of the parties
        // CPFP?

        Transaction {
            version: Version::non_standard(3),
            lock_time: LockTime::ZERO,
            input: vec![dummy_input(self.settlement_relative_timelock)],
            output,
        }
    }

    fn iter_keys(&self) -> impl Iterator<Item=(PartyId, &XOnlyPublicKey)> {
        self.keys.iter().enumerate().map(|(index, key)| (index as PartyId, key))
    }
}

#[derive(Clone)]
struct UpdateScriptBuilder {
    buffer: Vec<u8>,
    generation: usize,
    depth: u32,
}

impl UpdateScriptBuilder {
    fn new(party_count: usize, generation: usize, depth: u32) -> Self {
        // honestly we don't even really need to estimate if we reuse the buffer...
        let script_size =
            5 // script num
            + 2 // CSV DROP
            + (32 + 1) // updater pubkey + push opcode
            + 1 // CHECKSIGVERIFY
            + 1 // CTV
            + (2 * generation) // SWAP|NOP PAIRCOMMIT * generation
            + (2 * depth as usize) // SWAP|NOP PAIRCOMMIT * depth
            + (party_count - 1) * (32 + 1) // pubkey bytes plus push opcode
            + (party_count - 1) * 3 // TUCK CSFS VERIFY
            - 1 // Last CSFS doesn't need a VERIFY
            + 64 // FIXME: just to see if it affects performance/saves an allocation
            + 0; //

        Self {
            buffer: Vec::with_capacity(script_size),
            generation,
            depth,
        }
    }

    // A little janky but we want the builder to continue owning the buffer. Re-evaluate interface
    // when we have lots of free time.
    fn build_script(&mut self, update_builder: &UpdateTransactionSetBuilder, update: &StateUpdate, party_id: PartyId, mut next_state_index: usize) {
        let key = update_builder.get_pubkey(party_id).unwrap();

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
            .push_x_only_key(key)
            .push_opcode(OP_CHECKSIGVERIFY)
            .push_opcode(OP_CHECKTEMPLATEVERIFY);

        println!("depth = {depth}", depth = self.depth);
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

        for _ in 1..self.generation {
            println!("PC");
            builder = builder
                .push_opcode(OP_PAIRCOMMIT);
        }

        if self.generation == party_count {
            println!("last generation");
            builder = builder
                .push_opcode(OP_PAIRCOMMIT);
        } else {
            println!("other than last generation");
            builder = builder
                .push_opcode(OP_SWAP)
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
        TapNodeHash::from_script(self.as_script(), LeafVersion::TapScript)
    }
}

#[cfg(test)]
mod test {
    const SETTLEMENT_TIMELOCK: RelativeLockTime = RelativeLockTime::from_height(12);

    use bitcoin::{
        Amount,
        XOnlyPublicKey,
    };

    use bitcoin::bip32::{
        ChildNumber,
        Xpriv,
    };

    use bitcoin::secp256k1::{
        Signing,
    };

    use std::str::FromStr;
    use std::time::Instant;

    use super::*;

    fn test_keys<C: Signing>(secp: &Secp256k1<C>, n: usize) -> Vec<XOnlyPublicKey> {
        let xpriv = Xpriv::from_str("tprv8ZgxMBicQKsPd1EzCPZcQSPhsotX5HvRDCivA7ASNQFmjWuTsW3WWEwUNKFAZrnD9qpz55rtyLdphqkwRZUqNWYXwSEzd6P4pYvXGByRim3").unwrap();

        (0..n).map(|i| {
            // FIXME: not that it matters for a test but maybe use a standard-ish derivation path
            // later
            let xpriv = xpriv.derive_priv(secp, &[ChildNumber::from(i as u32)]).unwrap();

            let keypair = xpriv.to_keypair(secp);

            keypair.x_only_public_key().0
        })
        .collect()
    }

    fn even_split(builder: &UpdateTransactionSetBuilder) -> Vec<Amount> {
        let party_count = builder.keys.len() as u64;

        let amount_per_party = builder.total_amount / party_count;
        let remainder = builder.total_amount % party_count;

        let mut amounts: Vec<_> = builder.keys.iter().map(|_| amount_per_party).collect();

        let mut remainder = remainder.to_sat();
        for amount in amounts.iter_mut() {
            if remainder < 1 {
                break;
            }

            *amount += Amount::ONE_SAT;
            remainder -= 1;
        }

        amounts
    }

    #[test]
    fn test_update_script() {
        let secp = Secp256k1::new();
        let set = UpdateTransactionSetBuilder::from_parties(test_keys(&secp, 4), Amount::from_sat(100000000), SETTLEMENT_TIMELOCK);

        let mut builder = UpdateScriptBuilder::new(
            3, 1,
            set.generations[1].depth,
        );

        let update = StateUpdate { state: 1, split: even_split(&set) };

        let updater: PartyId = 0;
        let next_state_index = 3;

        builder.build_script(&set, &update, updater, next_state_index);

        let generated_script = builder.as_script().to_owned();

        let expected_script = Builder::new()
            .push_int((update.state + 1) as i64)
            .push_opcode(OP_CHECKLOCKTIMEVERIFY)
            .push_opcode(OP_DROP)
            // Verify
            .push_x_only_key(&set.keys[0]) // <A>
            .push_opcode(OP_CHECKSIGVERIFY)
            .push_opcode(OP_CHECKTEMPLATEVERIFY)
            // Index 3 into [ABC, ABD, ACD, BCD]
            .push_opcode(OP_NOP)
            .push_opcode(OP_PAIRCOMMIT)
            .push_opcode(OP_NOP)
            .push_opcode(OP_PAIRCOMMIT)
            // Generation 1
            .push_opcode(OP_SWAP)
            .push_opcode(OP_PAIRCOMMIT)
            // Verify B state update sig
            .push_opcode(OP_TUCK)
            .push_x_only_key(&set.keys[1])
            .push_opcode(OP_CHECKSIGFROMSTACK)
            .push_opcode(OP_VERIFY)
            // Verify C state update sig
            .push_opcode(OP_TUCK)
            .push_x_only_key(&set.keys[2])
            .push_opcode(OP_CHECKSIGFROMSTACK)
            .push_opcode(OP_VERIFY)
            // Verify D state update sig
            .push_opcode(OP_TUCK)
            .push_x_only_key(&set.keys[3])
            .push_opcode(OP_CHECKSIGFROMSTACK)
            .into_script();

        assert_eq!(expected_script.as_script(), generated_script.as_script());
    }

    #[test]
    fn test_depth_for_len() {
        let f = |l| UpdateTransactionSetBuilder::depth_for_generation_len(l);

        assert_eq!(1, f(1));
        assert_eq!(1, f(2));
        assert_eq!(2, f(3));
        assert_eq!(2, f(4));
        assert_eq!(3, f(5));
        assert_eq!(3, f(7));
        assert_eq!(3, f(8));
        assert_eq!(4, f(9));
        assert_eq!(4, f(16));
        assert_eq!(5, f(17));
        assert_eq!(5, f(32));
    }

    #[test]
    fn test_generation() {
        let secp = Secp256k1::new();
        let set = UpdateTransactionSetBuilder::from_parties(test_keys(&secp, 5), Amount::from_sat(100000000), SETTLEMENT_TIMELOCK);

        let start = Instant::now();
        let _ = set.get_update_commitment(&secp, &StateUpdate { state: 1, split: Vec::new()});
        let duration = Instant::now() - start;

        println!("duration = {}s", duration.as_secs_f64());

        assert_eq!(set.generations[0].transactions.len(), 1);
        assert_eq!(set.generations[1].transactions.len(), 5);
        assert_eq!(set.generations[2].transactions.len(), 10);
        assert_eq!(set.generations[3].transactions.len(), 10);
        assert_eq!(set.generations[4].transactions.len(), 5);
    }
}
