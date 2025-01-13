use bitcoin::bip32::{
    ChildNumber,
    Xpriv,
};

use bitcoin::secp256k1::{
    Secp256k1,
    Signing,
    XOnlyPublicKey,
};

use bitcoin::{
    Amount,
    relative::LockTime as RelativeLockTime,
};

use mpewbs::{
    StateUpdate,
    UpdateTransactionSetBuilder,
};

use std::str::FromStr;
use std::time::{
    Duration,
    Instant,
};

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

fn main() {
    let secp = Secp256k1::new();

    let mut participant_count = 3;

    // XXX: This doesn't do any of the standard things like warming up, etc
    loop {
        let keys = test_keys(&secp, participant_count);

        let builder = UpdateTransactionSetBuilder::from_parties(
            keys,
            Amount::ONE_BTC,
            RelativeLockTime::from_height(12),
        );

        let sats_per_party = Amount::ONE_BTC.to_sat() / (participant_count as u64);
        let mut remainder = Amount::ONE_BTC.to_sat() % (participant_count as u64);

        let mut split: Vec<_> = (0..participant_count)
            .map(|_| Amount::from_sat(sats_per_party))
            .collect();

        for amount in split.iter_mut() {
            if remainder < 1 {
                break;
            }

            *amount += Amount::ONE_SAT;
            remainder -= 1;
        }

        let mut durations: Vec<Duration> = Vec::new();
        const ITERATIONS: u32 = 10;
        for i in 1..=ITERATIONS {
            let update = StateUpdate::new(i, split.clone());

            let start = Instant::now();
            let _commitment = builder.get_update_commitment(&secp, &update);
            durations.push(Instant::now() - start);
        }

        durations.sort();

        // Yes we could just time the whole thing but we could do stats if we record individually
        let total_duration = durations.iter().fold(Duration::ZERO, |a, b| a + *b);
        let duration = total_duration / ITERATIONS;

        let ms = duration.as_secs_f64() * 1000.0;
        let best_ms = durations.first().unwrap().as_secs_f64() * 1000.0;
        let worst_ms = durations.last().unwrap().as_secs_f64() * 1000.0;
        println!("Parties: {participant_count:3} Duration: best: {best_ms:8.3}ms mean: {ms:8.3}ms worst: {worst_ms:8.3}ms");

        if duration > Duration::from_secs(1) {
            break;
        }

        participant_count += 1;
    }
}
