# LowRegBgC0Assemble

## Role

Assembly chunk of the C0Core split: `refoldData` and the refold H² lemmas
(`refoldC0_h2`, `refoldC1_h2`, `refoldCoeff_h2`, `refoldA1_hl`), the
`c0Data`/`c0Data_self`/`c0DataPairH2` package, and the small glue lemmas
(`zero_fb_c0`, `incl32_c0`, `sqrt_scale_c0`).

Chain position: `LowRegBgC0Integrate → this → LowRegBgC0Core`.

## Import repair (2026-08-02)

The mechanical split dropped the monolith's `LowRegBgC1Time` import, whose
only role for this content was carrying `LowRegBaseForce` transitively
(`gFibreOpBound_ccTensorBilinSymm_zero`, first consumed here).  Fixed with
the narrow import `DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.
LowRegBaseForce` instead of re-adding C1Time — importing C1Time here would
also have pulled the (then-broken) `LowRegBgA1Pair` closure into every chunk
build.  No chunk uses C1Time's own exports (verified by grep).

## Verification

Focused check + targeted `.olean` build GREEN, 2026-08-02 (focused 62 s with
the fresh import closure, build 50 s).  Zero sorry/admit/axiom/whnf/trace.
