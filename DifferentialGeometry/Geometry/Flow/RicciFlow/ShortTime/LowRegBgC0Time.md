# `LowRegBgC0Time`

## Role

This module completes the refolded order-zero first-order action on the
adjacent Sobolev scales and packages it along time-`L² H³` states.

## 2026-08-02 API preservation

The proof of `c0_time` already constructed affine pointwise bounds for both
completed coefficient maps.  Its public result previously discarded those
bounds and retained only the derived time-`L²` norm estimates.  The result now
also returns the two existing bounds

`‖FHi x‖ ≤ Z + L * ‖x‖` and `‖FLo x‖ ≤ Z + L * ‖x‖`.

This is not new analytic content.  It preserves data already produced by
`c0_ext_pair` so the downstream low affine M-witness can use the refolded A1
without returning to the raw pair route.

## Import repair + verification (2026-08-02)

After the C0Core split the closure of `LowRegBgC0Core` no longer carries the
monolith's `LowRegBgC1Time` import, so two Analysis-layer names this file
uses stopped resolving.  Fixed with narrow imports at this consumer:
`DifferentialGeometry.Analysis.DenseExtension` (for
`DifferentialGeometry.Analysis.exists_extend_le`) and
`DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.
NonautonomousL2Cross` (for `memLp_clm_affine`).  No proof was changed.

Focused check + targeted `.olean` build GREEN, 2026-08-02.  The API-extended
`c0_time` (FHi/FLo affine bounds) is therefore now elaborated and settled.

## 2026-08-02 (fifth pass) — quantifier hoist: `c0_time` → `c0_pack`, GREEN

The public export of this lane is now the **trajectory-free** packet.

- `c0_ext_pair` (private) was promoted verbatim to the public `c0_pack`.  Its
  statement was already exactly the u-free packet: `∃ ρ₀ > 0, ∀ ρ δ …,
  ∃ Z L FHi FLo, Continuous + smooth-core formulas + affine bounds + the
  Sobolev-inclusion square`.  Nothing in the F-construction mentions a
  trajectory, so no extraction work was needed — only the `private` keyword and
  a docstring.
- `c0_time` was **deleted** (was ~155 lines).  It quantified `∃ Z L` *after* the
  state argument `u : timeL2 H³ T`, which is precisely the ordering that blocked
  the endpoint from capping a radius against `L`.  Its only consumer,
  `refold_time`, is gone too (see `LowRegBgA1Refold.md`); the time-`L²`
  certificates it produced are rebuilt downstream from the packet alone by
  `refoldAffA1_memLp` / `refoldAffA1Hi_memLp`, which were already doing exactly
  that and discarding `c0_time`'s versions.

Module docstring updated accordingly.  Focused check + targeted `.olean` build
GREEN; `c0_pack` axiom-clean.
