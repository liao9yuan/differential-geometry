# LowRegBgC0Core

## Role

Public endpoint of the C0Core split — the 494-line entry that replaced the
12.3k-line monolith (backup: `.codex-scratch/c0core-split/
LowRegBgC0Core.before-split.lean`; keep the scratch until the whole chain is
long-term stable).  Public API preserved exactly: `c0CoreData`, `c0Core_self`,
`c0CorePair`, `c0Coeff_aff`, `refold_low_split`.

Chain: `Alg → Joint → Zero → One → {PairBase→PairCurv→PairDA→PairRic |
PairEst | Amix} → CoeffPair → Integrate → Assemble → this`.

## Import repair (2026-08-02)

The split dropped the monolith's `LowRegBgC1Time` import.  This endpoint
consumes the `lowRadial`/`lowRadial_symm`/`lowRadial_norm` layer, which lives
in `DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.
DeTurckRemainderLowBaseTime`; that module is now imported directly (narrow
import instead of C1Time, same rationale as in `LowRegBgC0Assemble.md`).

## Verification

Focused check + targeted `.olean` build GREEN, 2026-08-02 (focused 62.7 s,
build 27 s).  Zero sorry/admit/axiom/whnf/trace.  All 14 chunks of the split
are focused + exact GREEN as of 2026-08-02; the OOM that motivated the split
is resolved (largest single-chunk peak: PairEst ~4.93 GB, Amix ~4.23 GB —
each fits a ~16 GB machine when run singly with LEAN_NUM_THREADS=1).
