# `LowRegBgH2.lean`

## Role

This module packages the fixed-order `H²` estimates needed to compare the
zero-order Ricci--DeTurck coefficient at a fixed background metric with the
same-background low-base coefficient.  It is part of the analytic machinery
for uniform low-regularity existence; it does not state or prove
`ricci_flow_unif_existence`.

## Verified bricks

- `dlaDiff_h2` packages the public DLa background-difference grid into an
  `H²` bound whose state window ends at `H³`.
- `dlbDiff_h2` packages the public DLb background-difference grid into an
  `H²` bound.
- `insert_h2` proves the insertion-field `H²` estimate from the existing trace,
  connection-difference, and bounded-product estimates.  Its state window ends
  at the `H³` jet.
- `amixDiff_h2` proves the AMix background-difference `H²` estimate.  The proof
  first controls the exact refolded AMix form and then subtracts the two fixed
  backgrounds.
- The private `bgCorrFam`/`bgCorrInt` layer now proves the exact four-way
  background telescope and its path-integral identity.  The general-background
  `C0` coefficient is exactly the same-background `C0`, plus this integral,
  plus one fixed smooth curvature-coefficient difference.
- `bgCorr_h2` aggregates all four component bounds along `realizedFam` and
  transfers the result through the canonical path integral.
- `bgCorrInt_h2` transfers any uniform integrand `H²` bound through the canonical
  path integral, and `fixedBg_h2` closes the state-independent fixed term.
- `lowC0_bg_h2` combines the exact background telescope with the public
  same-background coefficient endpoint.  It gives the complete fixed-background
  `C0` two-jet bound with a state window ending at `H³`.
- `lowC1_bg_h2` packages the public intrinsic order-one path estimate at the
  fixed perturbation radius `δ₀ = 1/3`.  Its state window also ends at `H³`.
  An input bound with `δ ≤ 1/3` is promoted to this common radius before the
  producer is called; this avoids comparing proof-indexed realized paths at two
  different radius witnesses.
- `lowData_bg_coeff` gives one envelope for the complete general-background
  `C0` and `C1` pair.
- `lowA1_bg_bounds` applies the generic action estimates to that same pair and
  proves compatible smooth-core `H3 → H2` and `H2 → H1` bounds.  No `H4` state
  jet or high-Sobolev smallness enters either estimate.

The enlarged file passes persistent-LSP elaboration, the focused Lean check,
and its targeted module refresh.  It contains no `sorry`, `admit`, `axiom`,
`whnf`, or trace option.

## Remaining frontier

The general-background coefficient and first-order action estimates are closed.
The next smallest producer is the exact zero-based remainder split with a fixed
DeTurck background.  The intrinsic action module already proves the needed
identity privately for arbitrary `g_bg`, while its public endpoint specializes
to `g_bg = g`.  The remaining task is therefore a thin canonical exposure of
that exact general-background split, followed by the background-parameterized
time-level data; it is not another coefficient estimate or Ricci algebra
frontier.

## Progress accounting

- `ricci_flow_unif_existence`: theorem remains unstated here and unproved at its
  endpoint, therefore **0%**.
- Fixed-background low-base action: the exact `C0` correction, complete `C0/C1`
  coefficient envelope, and both required smooth-core A1 estimates are verified.
- Dedicated uniform-existence machinery: approximately **73--75%**.  This is
  infrastructure progress, not theorem completion.
