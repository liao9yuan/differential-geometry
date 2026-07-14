# ParametricPairing

## Producers

- `iterL_pair_unif` combines a compact-slab operator-field jet window with the
  generic balanced pairing estimate.
- `iterL_smul_unif` combines `smul_jet_unif` with `iterL_window_pair`; its
  output is the adjacent `H^(n+1) * H^n` window needed for Young absorption.

Both constants are chosen before the parameter, input tensor, and support.

## Frontier

Both source proofs are complete, but focused verification is pending the
shared dependency chain becoming stable. The exact A1 square estimate is
deliberately not a new frontier: the adjacent-window estimate is the honest
smooth-level input for the closure step.

Endpoint theorem: 0%. Dedicated compact-parameter pairing machinery: about
85% until focused verification is green. Uniform slot transport is now
source-complete in `SlotTransportPairing.lean`, but remains unverified.
