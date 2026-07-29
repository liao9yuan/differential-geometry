# RiemannCoefficientPalatiniRefold additions

## Low-regularity exports

Two small public aliases were added without changing their underlying proofs:

- `endo_eq_dlb` exposes the equality between the geometric endomorphism arm
  and the concrete `DLb` coefficient field.
- `dlbDiff_grid` exposes the existing pointwise product-grid estimate for the
  change `DLb(g_bg) - DLb(g0)`.

The second estimate has grid window `i + 2`; for `i < 2` it is integrable from
the metric jet through order three in dimension three.

## Verification

Focused verification is pending the shared sequential artifact refresh.  The
underlying producer proofs pre-existed; only their public aliases are new.

## 2026-07-25 — dedup: private `iteratedCovGrad_smul_real` removed

The file-local private copy was deleted; all 32 call sites now use the public
`iteratedCovGrad_smul` from
`Analysis/Spectral/Tensor/CovGrad/IteratedCovGradLinear.lean` (in scope via
`open DifferentialGeometry.PDE.RicciFlow`).  Focused check green.

## 2026-07-29 - fixed-order residual entry

`lrPointwise_bfgw` is now public in its canonical module. Its statement has
no supercritical Sobolev index or high-Sobolev ball: it exposes the pointwise
grid-window estimate for the base-background DeTurck covariant derivative
residual after the exact pair-contraction refold.

Focused and exact verification pass. Radius-free integration of this bound
still leaves an explicit `nabla^(i+2) T` top leak; the theorem is a producer,
not the final low-base `A1` estimate.
