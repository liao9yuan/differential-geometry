# Ricci connection-difference order-zero kernel jet grid

## 2026-08-06 class-first kernel grid

`ricci0_ker_grid_unif` moves the base metric inside the universal quantifier.
It first selects the class-first connection-difference sequence from
`connDiff_grid_unif`, then uses the existing eight-arm kernel estimate without
changing its constants.  The selected kernel sequence is therefore independent
of both `g₀` and `g₁`.  The former long theorem is retained as a thin
metric-local compatibility wrapper.

The explicit sequence remains

`C l = 376 * CQ l + 6 * CL l`,

where `CQ` is the quadratic connection-difference contribution built from
`appCcGdiag`, the dimension factor, and the supplied class-first sequence, and
`CL l = finrank * CA (l + 1)` is the differentiated connection contribution.
No hypotheses were added.

The complete source now passes a warning-free focused Lean check, the module
artifact is exported, and `ricci0_ker_grid_unif` has only the standard axioms
`propext`, `Classical.choice`, and `Quot.sound`.  The leading `g₀` argument
and the metric-local compatibility wrapper both elaborated without changing
the mathematical route.

`ricci0_ker_grid_unif`: proved and verified (100%).  The class-first order-zero
Ricci H1 composer that consumes it is the next local target and remains 0%.
`lowreg_bounds_unif`: 0%. `ricci_flow_unif_existence`: 0%. The whole HCG
compactness project remains approximately 3% complete.
