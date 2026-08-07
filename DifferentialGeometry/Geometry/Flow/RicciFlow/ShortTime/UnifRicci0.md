# Class-first order-zero Ricci coefficient

## 2026-08-06 source implementation

`ricci0_h1_unif` is now stated under the public dimension-three interface.  It
fixes the background metric, a class parameter with `1 ≤ Λ`, and a common
fibre-smallness ceiling before the class metric varies.  Its only class inputs
are uniform equivalence and the first two background-covariant metric jets.

The proof composes three existing class-first packages:

- `ricci0_ker_grid_unif` with `h1_grid_unif` gives the affine `H1` kernel bound;
- `trace2_h2_unif` gives the moving pure trace bound, and the four-trace
  reindexing identity costs the explicit factor `2`;
- `appRS_h2_unif` applies that `H2` trace operator to the `H1` kernel.

If `Capp`, `Bt`, `Bk0`, and `Bk1` are the supplied constants, the final
functions are

`B0 R = Capp * (2 * Bt R) * Bk0 R`

and

`B1 R = Capp * (2 * Bt R) * Bk1 R`.

No new assumptions or mathematical frontiers were introduced.  The complete
file passes a warning-free focused Lean check, its module artifact is exported,
and `ricci0_h1_unif` has only the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`.  The kernel-grid argument order and the
final conversion from the mixed-application `H1` norm both elaborated directly.

`ricci0_h1_unif`: proved and verified (100%).  The joint class-first RHS tame
producer that consumes this coefficient remains unstated (0%).
`lowreg_bounds_unif`: 0%. `ricci_flow_unif_existence`: 0%. The whole HCG
compactness project remains approximately 3% complete.
