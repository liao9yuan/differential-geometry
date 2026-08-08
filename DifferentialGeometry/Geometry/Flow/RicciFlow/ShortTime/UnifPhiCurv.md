# UnifPhiCurv

## Purpose

This module introduces the three-dimensional class-first interface for the
fixed curvature coefficient produced by the Ricci--DeTurck top-order split.
The coefficient is controlled using only uniform metric equivalence and the
first three background-covariant metric jets.

## Route

`phiCurv_jet_unif` integrates the public pointwise bounds `phiSelf_grid` and
`gradSlot_grid_unif` against the class-uniform volume cap.  Their explicit
nonnegative square-root radii feed `appRS_h2_unif` at valences `(2,4,2)`.
The scalar factor in `phiMetCurvCoeff` is then transferred with the exact
intrinsic `H1` jet identity.  The proof deliberately uses the complementary
`H2`-operator / `H1`-passenger application theorem rather than the stronger
`H2` / `H2` wrapper.

`fixed_curv_h1_unif` composes that coefficient-jet cap with
`appCc_h1_unif`, yielding the class-first spectral `H2 -> H1` action used by
the top-path split.

`curv_pair_abs_unif` consumes that action bound in the diagonal normal form.
The Green/`H1` identity turns the pairing of `L²T` with `K0·LT` into the
`H1` pairing of `LT` and `K0·LT`; the spectral shift then gives the adjacent
`H3(T)` and `H4(T)` factors, and Young's inequality yields
`η·H4(T)² + G·H3(T)²`.  The constant `G` is selected before the class metric.
No radius, fibrewise smallness, or fourth metric-jet hypothesis is used.

The coefficient and action constants are selected from `(gBase, Λ)`, while
the pairing constant also depends on `η`; all are selected before the class
metric varies.
No private low-regularity RHS constant or metricwise compactness choice is
used; the self coefficient uses the public `phiSelfC` and
`phiSelfC_nonneg` package.

## Verification state

Focused Lean verification and direct export passed warning-free with four
threads and the 6 GB cap.  The only source-lane repair was an explicit import of `PhiMetSymmetry`
for the public curvature coefficient names, followed by local simp-linter
cleanup.  Temporary axiom censuses for both public theorems reported only
`propext`, `Classical.choice`, and `Quot.sound`.

The diagonal pairing theorem also passes focused verification.  It reuses the
existing faithful `H1` Green bridge and spectral norm/shift adapters; no new
analytic API is needed.

The definitional identification of the `H1` wrapper of a scalar multiple, the
two-term `h1_jet_sq` normalization, and the `gradSwapCurvCoeff` alias all
elaborated without an additional API.

## Honest project accounting

- Whole HCG compactness project: approximately 3%.
- `ricci_flow_unif_existence`: 0%; it is not yet proved.
- `lowreg_bounds_unif`: 0%; it is not yet proved.
- Class-first joint tame producer: 0%; it is not yet stated and proved.
- The original coefficient-jet and action declarations: proved,
  focused-verified, exported, and axiom-audited (100%).
- `curv_pair_abs_unif`: proved and focused-verified (100%); it was not
  separately export- or axiom-audited in this pass.
- Dedicated uniform-existence supporting machinery after this source brick:
  approximately 92%, reported separately from all theorem endpoints.
