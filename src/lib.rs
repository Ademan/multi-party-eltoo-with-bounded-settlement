pub mod penalty;
pub mod symmetry;

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
    iter::ParallelIterator,
    iter::IntoParallelIterator,
    slice::ParallelSlice,
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

pub const NULL_PARTY: PartyId = 255;

#[derive(Clone,Debug,PartialEq,Eq,PartialOrd,Ord)]
pub struct PartySet(Vec<PartyId>);

impl PartySet {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn first_n(n: usize) -> Self {
        Self (
            (0..n).map(|i| i as PartyId).collect()
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
                self.0.truncate(original_length);
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

    pub fn iter_dense<'a>(&'a self) -> DensePartyIterator<'a> {
        DensePartyIterator {
            parties: self,
            current_party: 0,
            i: 0,
        }
    }
}

struct DensePartyIterator<'a> {
    parties: &'a PartySet,
    current_party: u32,
    i: usize,
}

impl<'a> Iterator for DensePartyIterator<'a> {
    type Item = Option<PartyId>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.i >= self.parties.len() {
            return Some(None);
        }

        if self.current_party == self.parties[self.i] as u32 {
            let result = Some(self.current_party as PartyId);
            self.i += 1;
            self.current_party += 1;

            Some(result)
        } else if self.current_party < self.parties[self.i] as u32 {
            self.current_party += 1;

            Some(None)
        } else {
            unreachable!()
        }
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

fn ilog2_ceil(i: usize) -> u32 {
    ((i << 1) - 1).ilog2()
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

pub(crate) fn merkle_commit<PC, T, I>(commit: PC, items: I, stack: &mut Vec<(T, u32)>) -> T
where
    I: Iterator<Item=T>,
    PC: Fn(T, T) -> T,
    T: Copy,
{
    let mut max_stack = 0 as usize;

    for item in items {
        stack.push((item, 0));

        max_stack = usize::max(max_stack, stack.len());

        compress_commitment_stack(&commit, stack);
    }

    while stack.len() > 1 {
        let top_index = stack.len() - 1;
        let (top_item, depth) = stack[top_index];

        stack.push((top_item.clone(), depth));

        compress_commitment_stack(&commit, stack);
    }

    assert!(stack.len() == 1);
    stack[0].0
}

pub(crate) fn par_paircommit_merkle_commit(items: &[Sha256], items_per_thread: usize, stack_size_hint: usize) -> Sha256
{
    let stack: Vec<(Sha256, u32)> = Vec::with_capacity(stack_size_hint);
    let subtree_merkle_roots: Vec<_> = items.par_chunks(items_per_thread)
        .map_with(stack, |stack, chunk| {
            stack.clear();
            // XXX: man that cloned burns...
            merkle_commit(|a, b| paircommit(a, b), chunk.into_iter().map(|hash| *hash), stack)
        })
        .collect();

    paircommit_merkle_commit(subtree_merkle_roots.into_iter(), stack_size_hint)
}

pub(crate) fn paircommit_merkle_commit<I>(transaction_templates: I, stack_size_hint: usize) -> Sha256
where
    I: Iterator<Item=Sha256>
{
    let mut stack = Vec::with_capacity(stack_size_hint);
    merkle_commit(|a, b| paircommit(a, b), transaction_templates, &mut stack)
}

fn taptree_commit<I>(tap_leaves: I, stack_size_hint: usize) -> TapNodeHash
where
    I: Iterator<Item=TapNodeHash>,
{
    let mut stack = Vec::with_capacity(stack_size_hint);
    merkle_commit(|a, b| TapNodeHash::from_node_hashes(a, b), tap_leaves, &mut stack)
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

    fn assert_iter_dense(parties: &PartySet, expected: &[Option<PartyId>]) {
        for (expected, party) in expected.into_iter().zip(parties.iter_dense()) {
            assert_eq!(party, *expected);
        }
    }

    #[test]
    fn test_set() {
        let mut parties = PartySet::new();

        parties.add(5);
        assert!(parties.contains(5));
        assert!(!parties.contains(4));
        assert_iter_dense(&parties, &[None, None, None, None, None, Some(5)]);
        parties.add(4);
        assert!(parties.contains(4));
        parties.add(6);
        assert!(parties.contains(6));
        assert_iter_dense(&parties, &[None, None, None, None, Some(4), Some(5), Some(6)]);
        assert!(!parties.contains(1));
        parties.add(1);
        assert_iter_dense(&parties, &[None, Some(1), None, None, Some(4), Some(5), Some(6)]);
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
        assert_iter_dense(&parties, &[None, None, None, None, Some(4), None, Some(6)]);

        parties.remove(6);
        assert!(!parties.contains(6));
        assert_eq!([4], *parties);
        assert_iter_dense(&parties, &[None, None, None, None, Some(4)]);

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
        assert_eq!(gen_0_parties[0].0, [0, 1, 2, 3, 4]);

        let gen_1_parties = choose_k(&parties, 4);
        assert_eq!(gen_1_parties[0].0, [0, 1, 2, 3]);
        assert_eq!(gen_1_parties[1].0, [0, 1, 2, 4]);
        assert_eq!(gen_1_parties[2].0, [0, 1, 3, 4]);
        assert_eq!(gen_1_parties[3].0, [0, 2, 3, 4]);
        assert_eq!(gen_1_parties[4].0, [1, 2, 3, 4]);

        let gen_2_parties = choose_k(&parties, 3);
        assert_eq!(gen_2_parties[0].0, [0, 1, 2]);
        assert_eq!(gen_2_parties[1].0, [0, 1, 3]);
        assert_eq!(gen_2_parties[2].0, [0, 1, 4]);
        assert_eq!(gen_2_parties[3].0, [0, 2, 3]);
        assert_eq!(gen_2_parties[4].0, [0, 2, 4]);
        assert_eq!(gen_2_parties[5].0, [0, 3, 4]);
        assert_eq!(gen_2_parties[6].0, [1, 2, 3]);
        assert_eq!(gen_2_parties[7].0, [1, 2, 4]);
        assert_eq!(gen_2_parties[8].0, [1, 3, 4]);
        assert_eq!(gen_2_parties[9].0, [2, 3, 4]);

        let gen_3_parties = choose_k(&parties, 2);
        assert_eq!(gen_3_parties[0].0, [0, 1]);
        assert_eq!(gen_3_parties[1].0, [0, 2]);
        assert_eq!(gen_3_parties[2].0, [0, 3]);
        assert_eq!(gen_3_parties[3].0, [0, 4]);
        assert_eq!(gen_3_parties[4].0, [1, 2]);
        assert_eq!(gen_3_parties[5].0, [1, 3]);
        assert_eq!(gen_3_parties[6].0, [1, 4]);
        assert_eq!(gen_3_parties[7].0, [2, 3]);
        assert_eq!(gen_3_parties[8].0, [2, 4]);
        assert_eq!(gen_3_parties[9].0, [3, 4]);

        let gen_4_parties = choose_k(&parties, 1);
        assert_eq!(gen_4_parties[0].0, [0]);
        assert_eq!(gen_4_parties[1].0, [1]);
        assert_eq!(gen_4_parties[2].0, [2]);
        assert_eq!(gen_4_parties[3].0, [3]);
        assert_eq!(gen_4_parties[4].0, [4]);
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
}
