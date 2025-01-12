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
    OP_NOP,
    OP_RETURN_205 as OP_PAIRCOMMIT,
    OP_RETURN,
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
    iter::ParallelBridge,
    iter::ParallelIterator,
    iter::IntoParallelIterator,
};

use std::{io::Write, ops::Deref, collections::BTreeMap};

fn builder_with_capacity(size: usize) -> Builder {
    Builder::from(Vec::with_capacity(size))
}

fn get_default_template(transaction: &Transaction, input_index: u32) -> Sha256 {
    // Since Sha256::write() won't fail and consensus_encode() guarantees to never
    // fail unless the underlying Write::write() fails, we don't need to worry about
    // fallibility
    let mut sha256 = Sha256::engine();

    transaction.version.consensus_encode(&mut sha256).unwrap();
    transaction.lock_time.consensus_encode(&mut sha256).unwrap();

    let any_script_sigs = transaction.input.iter()
        .any(|input| !input.script_sig.is_empty());

    if any_script_sigs {
        let mut script_sig_sha256 = Sha256::engine();

        for input in transaction.input.iter() {
            input.script_sig.consensus_encode(&mut script_sig_sha256).unwrap();
        }

        let script_sig_sha256 = Sha256::from_engine(script_sig_sha256);
        script_sig_sha256.consensus_encode(&mut sha256).unwrap();
    }

    let vin_count: u32 = transaction.input.len() as u32;
    sha256.write(&vin_count.to_le_bytes()).unwrap();

    {
        let mut sequences_sha256 = Sha256::engine();
        for input in transaction.input.iter() {
            let sequence: u32 = input.sequence.to_consensus_u32();
            sequences_sha256.write(&sequence.to_le_bytes()).unwrap();
        }
        let sequences_sha256 = Sha256::from_engine(sequences_sha256);
        sequences_sha256.consensus_encode(&mut sha256).unwrap();
    }

    let vout_count: u32 = transaction.output.len() as u32;
    sha256.write(&vout_count.to_le_bytes()).unwrap();

    {
        let mut outputs_sha256 = Sha256::engine();
        for output in transaction.output.iter() {
            output.consensus_encode(&mut outputs_sha256).unwrap();
        }

        let outputs_sha256 = Sha256::from_engine(outputs_sha256);
        outputs_sha256.consensus_encode(&mut sha256).unwrap();
    }

    sha256.write(&input_index.to_le_bytes()).unwrap();

    Sha256::from_engine(sha256)
}

fn ephemeral_anchor() -> TxOut {
    let mut script_pubkey = ScriptBuf::new();
    script_pubkey.push_opcode(OP_TRUE);

    TxOut {
        value: Amount::from_sat(0),
        script_pubkey,
    }
}

fn dummy_input(lock_time: RelativeLockTime) -> TxIn {
    TxIn {
        previous_output: OutPoint {
            txid: Txid::from_byte_array([0u8; 32]),
            vout: 0,
        },
        script_sig: ScriptBuf::new(),
        sequence: lock_time.to_sequence(),
        witness: Witness::new(),
    }
}

const PAIRCOMMIT_TAG: Midstate = Midstate::hash_tag("PairCommit".as_bytes());

// Right corresponds to the top of the stack
pub fn paircommit<A, B>(left: A, right: B) -> Sha256
where
    A: AsRef<[u8]>,
    B: AsRef<[u8]>,
{
    // Sha256Engine::write() never fails
    // Neither does VarInt::consensus_encode

    let mut sha256 = Sha256Engine::from_midstate(PAIRCOMMIT_TAG, 64);

    let left_size = VarInt::from(left.as_ref().len());
    let right_size = VarInt::from(right.as_ref().len());

    let _ = left_size.consensus_encode(&mut sha256);
    let _ = sha256.write(left.as_ref());
    let _ = right_size.consensus_encode(&mut sha256);
    let _ = sha256.write(right.as_ref()).unwrap();

    Sha256::from_engine(sha256)
}

type PartyId = u8;

pub const NULL_PARTY: PartyId = 0;

#[derive(Clone,Debug,PartialEq,Eq,PartialOrd,Ord)]
pub struct PartySet(Vec<PartyId>);

impl PartySet {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn first_n(n: usize) -> Self {
        Self (
            (0..n).map(|i| (i + 1) as PartyId).collect()
        )
    }

    pub fn add(&mut self, party: PartyId) -> bool {
        // FIXME: ugly
        let original_length = self.0.len();
        let mut dest = self.0.len();

        self.0.resize(self.0.len() + 1, NULL_PARTY);

        while dest >= 1 {
            let source = dest - 1;
            self.0[dest] = self.0[source];

            if self.0[source] < party {
                self.0[dest] = party;
                return true;
            } else if self.0[dest] == party {
                // We shouldn't ever create duplicates so this can be slow
                while dest < self.0.len() {
                    let source = dest - 1;
                    self.0[source] = self.0[dest];
                    dest += 1;
                }
                self.0.resize(original_length, NULL_PARTY);
                return false;
            } else {
                dest -= 1;
            }
        }

        self.0[dest] = party;
        return true;
    }

    pub fn remove(&mut self, party: PartyId) -> bool {
        if let Ok(index) = self.0.binary_search(&party) {
            self.0.remove(index);
            true
        } else {
            false
        }
    }

    pub fn contains(&self, party: PartyId) -> bool {
        //println!("{:?}", &self.0[..]);
        self.0.binary_search(&party).is_ok()
    }
}

fn choose_k(parties: &PartySet, k: usize) -> Vec<PartySet> {
    let mut result = Vec::new();
    let mut buffer: Vec<usize> = (0..k).collect();

    choose_k_impl(&mut result, parties, 0, &mut buffer);

    result
}

// FIXME: this can be so much better but we can/will cache the result...
fn choose_k_impl(result: &mut Vec<PartySet>, parties: &PartySet, i: usize, buffer: &mut Vec<usize>) {
    let n = parties.len();
    let k = buffer.len();
    let max_index = n - k + i + 1;

    if buffer[i] > parties.len() {
        unreachable!();
        return;
    }

    for _ in buffer[i]..max_index {
        if (i + 1) < k {
            choose_k_impl(result, parties, i + 1, buffer);
        } else {
            result.push(
                PartySet(
                    buffer.iter().map(|i| parties.0[*i]).collect()
                )
            );
        }

        buffer[i] += 1;
        for j in (i + 1)..k {
            buffer[j] = buffer[j - 1] + 1;
        }
    }
}

fn ilog2_ceil(i: usize) -> usize {
    let mut log = i.ilog2();

    // Should only ever need one at most...
    while (1 << log) < i {
        log += 1;
    }

    log as usize
}

pub struct StateUpdate {
    state: u32,
    split: Vec<Amount>,
    // TODO: HTLCs etc
}

impl StateUpdate {
    pub fn new(state: u32, split: Vec<Amount>) -> Self {
        Self {
            state,
            split,
        }
    }
}

pub struct UpdateTransactionSetBuilder {
    generations: Vec<BTreeMap<PartySet, usize>>,
    depths: Vec<usize>,
    keys: Vec<XOnlyPublicKey>,
    total_amount: Amount,
}

impl UpdateTransactionSetBuilder {
    pub fn from_parties(keys: Vec<XOnlyPublicKey>, total_amount: Amount) -> Self {
        let mut generations = Vec::new();
        let mut depths = Vec::new();

        let parties = PartySet::first_n(keys.len());

        for i in 0..parties.len() {
            let mut generation = BTreeMap::new();

            for (i, subset) in choose_k(&parties, parties.len() - i).into_iter().enumerate() {
                generation.insert(subset, i);
            }

            let depth = Self::depth_for_generation_len(generation.len());

            depths.push(depth);
            generations.push(generation);
        }

        Self {
            generations,
            keys,
            total_amount,
            depths,
        }
    }

    fn depth_for_generation_len(generation_length: usize) -> usize {
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
        // Maybe NULL_PARTY isn't doing anything useful and just creating complications
        if party < 1 {
            return None;
        }

        self.keys.get((party - 1) as usize)
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
        for generation in 1..self.keys.len() {
            let depth = self.depths[generation];

            let new_script_builder = UpdateScriptBuilder::new(self.keys.len() - generation, generation, depth);

            let tx_templates = (&self.generations[generation]).into_par_iter()
                .map_with(new_script_builder, |script_builder, (parties, _index)| {
                    let internal_key = XOnlyPublicKey::from_slice(Self::NUMS_POINT.as_ref())
                            .unwrap();

                    let mut tap_nodes: Vec<TapNodeHash> = Vec::with_capacity(parties.len());

                    // FIXME: put this on key path instead? means more musig though
                    tap_nodes.push(settlement_tx_tapleaf_hash);

                    if generation + 1 < party_count {
                        tap_nodes = parties.iter()
                            .map(|party_id| {
                                let next_parties = PartySet(parties.iter().filter(|party| *party != party_id).cloned().collect());

                                let next_state_index = self.generations[generation + 1][&next_parties];

                                script_builder.build_script(self, update, *party_id, next_state_index);

                                script_builder.as_tap_node()
                            })
                            .collect();
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
                depth
            );

            commitments.push(commitment);
        }

        let mut rhs = commitments.pop().unwrap();

        while let Some(lhs) = commitments.pop() {
            rhs = paircommit(lhs, rhs);
        }

        rhs
    }

    fn key_index_to_party_id(i: usize) -> PartyId {
        (i + 1) as PartyId
    }

    // FIXME: make variable
    const SETTLEMENT_TIMEOUT: RelativeLockTime = RelativeLockTime::from_height(69);

    fn build_settlement_tx<C: Verification>(&self, secp: &Secp256k1<C>, parties: &PartySet, update: &StateUpdate) -> Transaction {
        assert!(parties.len() > 0);

        let (mut split, penalty_amounts): (Vec<_>, Vec<_>) = update.split.iter()
            .zip(self.keys.iter())
            .enumerate()
            .map(|(i, (amount, key))| {
                let party_id = Self::key_index_to_party_id(i);

                // FIXME: we can be faster than this, but contains() is probably fast enough for
                // our purposes (very small number of elements)
                (parties.contains(party_id), amount.clone(), key)
            })
            .partition(|(valid, _, _)| *valid);

        let penalty_amount = penalty_amounts.into_iter().fold(
            Amount::from_sat(0),
            |total, (_, amount, _)| total + amount
        );

        let party_count: u64 = parties.len() as u64;

        let penalty_amount = penalty_amount.to_sat();

        let penalty_per_remaining = Amount::from_sat(penalty_amount / party_count);

        // FIXME: just send remainder to fees?
        let mut remainder = penalty_amount % party_count;

        for i in 0..split.len() {
            if remainder < 1 {
                break;
            }

            split[i].1 += penalty_per_remaining + Amount::ONE_SAT;
            remainder -= 1;
        }

        let output: Vec<_> = split.into_iter()
            .map(|(_, value, key)| {
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
            input: vec![dummy_input(Self::SETTLEMENT_TIMEOUT)],
            output,
        }
    }

    fn iter_keys(&self) -> impl Iterator<Item=(PartyId, &XOnlyPublicKey)> {
        self.keys.iter().enumerate().map(|(index, key)| ((index + 1) as PartyId, key))
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
            builder = builder
                .push_opcode(OP_PAIRCOMMIT);
        }

        if self.generation == party_count {
            builder = builder
                .push_opcode(OP_PAIRCOMMIT);
        } else {
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
        TapNodeHash::from_script(Script::from_bytes(&self.buffer), LeafVersion::TapScript)
    }
}

impl std::ops::Deref for UpdateTransactionSetBuilder {
    type Target = Vec<BTreeMap<PartySet, usize>>;

    fn deref(&self) -> &Self::Target {
        &self.generations
    }
}

impl AsRef<[PartyId]> for PartySet {
    fn as_ref(&self) -> &[PartyId] {
        self.0.as_ref()
    }
}

impl Deref for PartySet {
    type Target = [PartyId];

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

fn compress_commitment_stack<PC, T>(commit: PC, stack: &mut Vec<(T, u32)>)
where
    PC: Fn(T, T) -> T,
    T: Copy,
{
    loop {
        if stack.len() < 2 {
            break;
        }

        let right_index = stack.len() - 1;
        let left_index = stack.len() - 2;

        let (right_item, right_depth) = stack[right_index];
        let (left_item, left_depth) = stack[left_index];

        assert!(left_depth >= right_depth);

        if left_depth != right_depth {
            break;
        }

        let new_item = commit(left_item, right_item);

        stack[left_index] = (new_item, left_depth + 1);
        stack.pop();
    }
}

pub(crate) fn merkle_commit<PC, T, I>(commit: PC, items: I, stack_size_hint: usize) -> T
where
    I: Iterator<Item=T>,
    PC: Fn(T, T) -> T,
    T: Copy,
{
    let mut max_stack = 0 as usize;
    let mut stack: Vec<(T, u32)> = Vec::new();

    if stack_size_hint > 0 {
        stack.reserve(stack_size_hint);
    } else {
        let (items_size_hint, _) = items.size_hint();
        // FIXME: barely thought about this but it's just a hint anyway
        if let Some(stack_size_hint) = ((items_size_hint << 1) - 1).checked_ilog2() {
            stack.reserve(stack_size_hint as usize);
        }
    }

    for item in items {
        stack.push((item, 0));

        max_stack = usize::max(max_stack, stack.len());

        compress_commitment_stack(&commit, &mut stack);
    }

    while stack.len() > 1 {
        let top_index = stack.len() - 1;
        let (top_item, depth) = stack[top_index];

        stack.push((top_item.clone(), depth));

        compress_commitment_stack(&commit, &mut stack);
    }

    assert!(stack.len() == 1);
    stack[0].0
}

pub(crate) fn paircommit_merkle_commit<I>(transaction_templates: I, stack_size_hint: usize) -> Sha256
where
    I: Iterator<Item=Sha256>
{
    merkle_commit(|a, b| paircommit(a, b), transaction_templates, stack_size_hint)
}

fn taptree_commit<I>(tap_leaves: I, stack_size_hint: usize) -> TapNodeHash
where
    I: Iterator<Item=TapNodeHash>,
{
    merkle_commit(|a, b| TapNodeHash::from_node_hashes(a, b), tap_leaves, stack_size_hint)
}

#[cfg(test)]
mod test {
    use bitcoin::{
        Amount,
        XOnlyPublicKey,
    };

    use bitcoin::bip32::{
        ChildNumber,
        Xpriv,
    };

    use std::str::FromStr;
    use std::time::Instant;

    use super::*;

    #[test]
    fn test_set() {
        let mut parties = PartySet::new();

        parties.add(5);
        assert!(parties.contains(5));
        assert!(!parties.contains(4));
        parties.add(4);
        assert!(parties.contains(4));
        parties.add(6);
        assert!(parties.contains(6));
        assert!(!parties.contains(1));
        parties.add(1);
        parties.add(42);
        assert!(parties.contains(42));

        assert_eq!([1,4,5,6,42], *parties);

        assert!(parties.contains(5));
        parties.remove(5);
        assert!(!parties.contains(5));

        parties.remove(1);
        assert!(!parties.contains(5));

        assert_eq!([4,6,42], *parties);

        parties.remove(42);
        assert!(!parties.contains(42));
        assert_eq!([4,6], *parties);

        parties.remove(6);
        assert!(!parties.contains(6));
        assert_eq!([4], *parties);

        parties.remove(4);
        assert!(!parties.contains(4));
        assert!(parties.len() == 0);

        parties.add(4);
        parties.add(5);
        assert!(parties.contains(4));
        assert!(parties.contains(5));

        parties.remove(4);
        assert!(!parties.contains(4));

        parties.add(6);
        parties.add(6);

        parties.remove(6);
        assert_eq!([5], *parties);
    }

    #[test]
    fn test_hash_txes() {
        let mut hashes: Vec<Sha256> = Vec::new();

        for i in 0..20 {
            hashes.push(Sha256::hash((i as u32).to_le_bytes().as_ref()));
        }

        // I guess just make sure it doesn't panic?
        for _i in (6..=20).rev() {
            let _ = paircommit_merkle_commit(hashes.iter().cloned(), 5);
        }

        hashes.truncate(6);
        let a_b = paircommit(hashes[0], hashes[1]);
        let c_d = paircommit(hashes[2], hashes[3]);
        let e_f = paircommit(hashes[4], hashes[5]);

        let a_b_c_d = paircommit(a_b, c_d);
        let e_f_e_f = paircommit(e_f, e_f);
        let a_b_c_d_e_f_e_f = paircommit(a_b_c_d, e_f_e_f);

        let commitment = paircommit_merkle_commit(hashes.iter().cloned(), 5);
        assert_eq!(commitment, a_b_c_d_e_f_e_f);

        hashes.truncate(5);
        let e_e = paircommit(hashes[4], hashes[4]);
        let e_e_e_e = paircommit(e_e, e_e);
        let a_b_c_d_e_e_e_e = paircommit(a_b_c_d, e_e_e_e);

        let commitment = paircommit_merkle_commit(hashes.iter().cloned(), 5);
        assert_eq!(commitment, a_b_c_d_e_e_e_e);

        hashes.truncate(3);

        let c_c = paircommit(hashes[2], hashes[2]);
        let a_b_c_c = paircommit(a_b, c_c);

        let commitment = paircommit_merkle_commit(hashes.iter().cloned(), 5);
        assert_eq!(a_b_c_c, commitment);

        hashes.truncate(2);

        let commitment = paircommit_merkle_commit(hashes.iter().cloned(), 5);
        assert_eq!(a_b, commitment);

        hashes.truncate(1);

        let commitment = paircommit_merkle_commit(hashes.iter().cloned(), 5);
        assert_eq!(hashes[0], commitment);
    }

    #[test]
    fn test_choose() {
        let parties = PartySet::first_n(5);

        let gen_0_parties = choose_k(&parties, 5);
        assert_eq!(gen_0_parties[0].0, [1, 2, 3, 4, 5]);

        let gen_1_parties = choose_k(&parties, 4);
        assert_eq!(gen_1_parties[0].0, [1, 2, 3, 4]);
        assert_eq!(gen_1_parties[1].0, [1, 2, 3, 5]);
        assert_eq!(gen_1_parties[2].0, [1, 2, 4, 5]);
        assert_eq!(gen_1_parties[3].0, [1, 3, 4, 5]);
        assert_eq!(gen_1_parties[4].0, [2, 3, 4, 5]);

        let gen_2_parties = choose_k(&parties, 3);
        assert_eq!(gen_2_parties[0].0, [1, 2, 3]);
        assert_eq!(gen_2_parties[1].0, [1, 2, 4]);
        assert_eq!(gen_2_parties[2].0, [1, 2, 5]);
        assert_eq!(gen_2_parties[3].0, [1, 3, 4]);
        assert_eq!(gen_2_parties[4].0, [1, 3, 5]);
        assert_eq!(gen_2_parties[5].0, [1, 4, 5]);
        assert_eq!(gen_2_parties[6].0, [2, 3, 4]);
        assert_eq!(gen_2_parties[7].0, [2, 3, 5]);
        assert_eq!(gen_2_parties[8].0, [2, 4, 5]);
        assert_eq!(gen_2_parties[9].0, [3, 4, 5]);

        let gen_3_parties = choose_k(&parties, 2);
        assert_eq!(gen_3_parties[0].0, [1, 2]);
        assert_eq!(gen_3_parties[1].0, [1, 3]);
        assert_eq!(gen_3_parties[2].0, [1, 4]);
        assert_eq!(gen_3_parties[3].0, [1, 5]);
        assert_eq!(gen_3_parties[4].0, [2, 3]);
        assert_eq!(gen_3_parties[5].0, [2, 4]);
        assert_eq!(gen_3_parties[6].0, [2, 5]);
        assert_eq!(gen_3_parties[7].0, [3, 4]);
        assert_eq!(gen_3_parties[8].0, [3, 5]);
        assert_eq!(gen_3_parties[9].0, [4, 5]);

        let gen_4_parties = choose_k(&parties, 1);
        assert_eq!(gen_4_parties[0].0, [1]);
        assert_eq!(gen_4_parties[1].0, [2]);
        assert_eq!(gen_4_parties[2].0, [3]);
        assert_eq!(gen_4_parties[3].0, [4]);
        assert_eq!(gen_4_parties[4].0, [5]);
    }

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
        let set = UpdateTransactionSetBuilder::from_parties(test_keys(&secp, 4), Amount::from_sat(100000000));

        let depth = UpdateTransactionSetBuilder::depth_for_generation_len(set.generations[1].len());

        let mut builder = UpdateScriptBuilder::new(3, 1, depth);
        let update = StateUpdate { state: 1, split: even_split(&set) };

        let parties = PartySet(
            set.keys.iter().enumerate().map(|(index, _)| (index + 1) as PartyId).collect()
        );

        let mut next_parties = parties.clone();
        next_parties.remove(1 as PartyId);

        let next_state_index = set.generations[1][&next_parties];

        assert_eq!(next_state_index, 3);

        builder.build_script(&set, &update, 1 as PartyId, next_state_index);

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
        let set = UpdateTransactionSetBuilder::from_parties(test_keys(&secp, 5), Amount::from_sat(100000000));

        let start = Instant::now();
        let _ = set.get_update_commitment(&secp, &StateUpdate { state: 1, split: Vec::new()});
        let duration = Instant::now() - start;

        println!("duration = {}s", duration.as_secs_f64());

        assert_eq!(set[0].len(), 1);
        assert_eq!(set[1].len(), 5);
        assert_eq!(set[2].len(), 10);
        assert_eq!(set[3].len(), 10);
        assert_eq!(set[4].len(), 5);

        let set = UpdateTransactionSetBuilder::from_parties(test_keys(&secp, 16), Amount::from_sat(100000000));

        let start = Instant::now();
        let _ = set.get_update_commitment(&secp, &StateUpdate { state: 1, split: Vec::new()});
        let duration = Instant::now() - start;

        println!("duration = {}s", duration.as_secs_f64());
    }
}
