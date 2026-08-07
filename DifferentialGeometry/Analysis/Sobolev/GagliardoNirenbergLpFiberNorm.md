# GagliardoNirenbergLpFiberNorm

## Explicit mixed-valence coefficient (2026-08-05)

The general-valence interpolation proof now exposes the constants
`gnStepConst`, `gnLogConst`, and `gnRsConst`.  The theorem `gn_rs_bound` proves
the existing mixed-`L^p` estimate with exactly `gnRsConst n k sqrt(vol)`;
the former existential theorem remains as a compatibility wrapper.

This is a producer refactor, not a new analytic assumption.  The proof still
runs through the established finite/sup second-order interpolation and discrete
log-convexity chain.  Focused verification passed.  The exported theorem was
also refreshed as an `.olean`; three pre-existing unused-section-variable
warnings earlier in the general-valence section are unrelated to this endpoint.

The class-facing use belongs above the volume-comparison layer.  It is
implemented in `HCGCompactness/UnifGagliardoNirenberg.lean`, rather than adding
metric-class hypotheses to this reusable single-metric module.
