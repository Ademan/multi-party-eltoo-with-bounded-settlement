# Multi-Party Eltoo With Bounded Settlement

This is a fairly naive, probably broken implementation of the scheme described [here](https://gist.github.com/Ademan/4a14614fa850511d63a5b2a9b5104cb7), churned out in a few free hours late at night.

At the time of writing, it isn't even a full proof of concept, but more of a way to measure the ballpark performance of this scheme.
There are multiple improvements that can and should be made, but I'm not sure how far they can take us.
The asymptotic performance of the scheme is exponential so either way we'll hit a hard limit pretty quickly, on my computer that seems to be between 10 and 16 channel parties, closer to 10.

Run the `bench` binary (make sure to build with release mode!) to see how long each state update takes to calculate.
The maximum latency ought to be under 20ms for recalculating an update.
On top of this, network latency, and storage latency will also affect performance.

The code is also downright embarassing in places.
There are places where I wrote something that I know I didn't think through all the way, it's likely buggy, but for the purposes of estimating performance it's close enough to correct to be ok.
If there's any interest I intend to expand this into a working proof of concept complete with P2P.

# Penalty Problems

As I was implementing this, an obvious issue became apparent with the penalty scheme.
If a malicious party collects all other parties' signatures but witholds their own, then they are the only one that can publish the latest state.
In the penalty scheme, the other parties cannot publish the second-to-latest state either because they could be penalized for it by the malicious party.

## Penalty Solutions

### Brute Force

By adding more states to every update, we can enable honest parties to safely publish state S even when S+1 has been fully signed (but the malicious party has witheld signatures).
I'm not positive yet how much extra complexity that adds, but I expect it to be significant.

Every update we partition the set of all parties into two subsets: `can_update` and `cant_update`.
In the penalty version we partition `cant_update` into three subsets: `penalized`, `maybe_penalize`, `last_updater`.
`maybe_penalize` and `last_updater` are both sizes 0 or 1.
The `maybe_penalize` set empties into the `penalized` set every update.
Every update, the `maybe_penalize` set is emptied into the `penalized` set.
If the update only advances the state by one, and does not have a revocation signature for the new state, the `last_updater` moves into the `maybe_penalize` set and the updater enters the `last_updater` set.
If the update only advances the state by one, and does have a revocation signature for the new state, the `last_updater` and `maybe_penalize` move directly into the `penalized` set and the current updater becomes the new `last_updater`.
If the update advances the state by more than one then the `maybe_penalize` and `last_updater` move into the `penalized` set.

This should add `P choose 2 + P choose 1 + 1` states for P in `[0, max_generation]`
