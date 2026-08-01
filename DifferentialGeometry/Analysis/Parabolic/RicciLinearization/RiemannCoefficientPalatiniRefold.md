# RiemannCoefficientPalatiniRefold additions

## Low-regularity exports

Two small public aliases were added without changing their underlying proofs:

- `endo_eq_dlb` exposes the equality between the geometric endomorphism arm
  and the concrete `DLb` coefficient field.
- `dlbDiff_grid` exposes the existing pointwise product-grid estimate for the
  change `DLb(g_bg) - DLb(g0)`.
- `dlaBg_grid` exposes the matching fixed-order product-grid estimate for
  `DLa(g_bg) - DLa(g0)`, without the all-order Sobolev ball parameters.

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

## 2026-07-30 - two-state lifted connection arm

`lieCovArm2_sub_l2` is the linear two-metric companion of the existing
`lieCovArm2_l2` estimate. It controls every covariant jet of the lifted arm
difference by the same jet of
`connDiffSection(g1,g0) - connDiffSection(g2,g0)`, with only the fixed
dimension factor. The proof reuses the existing two slot-extension
factorization; it adds no state regularity or smallness hypothesis.

Focused verification and the targeted exact refresh pass.

## 2026-07-31 - exact fixed-background DLa core

`lieBgLow`, `lieBgCore`, and `dlaBg_eq` expose the existing fixed-background
normal form without introducing Sobolev or ball parameters.  The companion
identity `lieBgLow_sub` cancels all state-independent terms before estimating
and leaves exactly three arms: one fixed lifted connection operator acting on
the moving connection difference and two moving lifted operators acting on the
fixed background connection difference.

This is the algebraic input for the ShortTime `DLa` H1 pair estimate.  The
reverse raised endomorphism in `lieBgCore` is affine in the tied metric state,
so the route uses only the H2 state difference and has no D4 leak.  Persistent
LSP elaboration reports no new errors.  The targeted exact refresh passes after
reducing Lean concurrency; the first attempt exhausted memory while the large
LSP worker was resident, not because of a source or proof error.
