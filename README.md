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
