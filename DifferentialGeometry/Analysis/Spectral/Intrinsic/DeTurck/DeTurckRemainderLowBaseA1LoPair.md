# DeTurckRemainderLowBaseA1LoPair

## Role

This sibling turns the fourth-jet-free direct estimate
`a1Lo_pair_lip` into the radial estimate consumed by the ShortTime
low-regularity lift.  It deliberately leaves the foreign-claimed
`DeTurckRemainderLowBaseTimeA1.lean` unchanged.

## Public result

`radialA1Lo_pair` chooses one positive admissible cutoff radius.  For
every smaller realized `H2` cutoff and every bounded spectral `H3`
piece of the smooth core, it proves that the completed `H2 -> H1`
first-order action is Lipschitz in the spectral `H3` distance.

The proof uses the canonical radial cutoff and the existing spectral
inclusion estimates.  It imports no fourth state jet and assumes no
`H3` or `H4` smallness.  The local Lipschitz constant may depend on the
bounded `H3` radius, which is the honest replacement for the false
global `a1Hi` Lipschitz statement.

## Consumer

The theorem has exactly the mathematical content needed to construct
`LowA1CorePair` in the ShortTime layer.  The remaining work is a thin
radius-aligned adapter and then the time-level `hfLo` identity; neither
requires another geometric decomposition.

## Verification

Focused verification and the exact module refresh are GREEN.  The
source contains no `sorry`, `admit`, `axiom`, or `whnf`.

## Project accounting

`ricci_flow_unif_existence` itself remains 0% with its existing
endpoint placeholder.  Dedicated uniform-existence machinery is
approximately 77%; the whole HCG compactness project remains in the
low single digits.
