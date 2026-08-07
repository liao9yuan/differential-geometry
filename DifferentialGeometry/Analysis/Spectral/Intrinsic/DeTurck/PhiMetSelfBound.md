# PhiMetSelfBound

## Status (2026-08-06)

`phiSelf_grid` is focused-green, warning-free, and directly exported.  It gives the class-independent pointwise
jet cap

```text
phiSelfC i = if i = 0 then 34 * (finrank E)^6 else 0
```

for `deTurckPhiMetTotal g g_bg g - ricciArmPrincipalCoeffPure g g`.
The constant is public so the short-time layer can integrate and simplify it
without depending on a hidden implementation name.

The proof uses `phiMet_reindex`, identifies the self trace-Hessian and pure
Ricci coefficients with input-slot reindexings of the parallel self-cometric
double trace, and uses `ricciSelf_eq` for the self Ricci coefficient.  Input
and output slot permutations preserve the fibre norm of every covariant jet.
The zero-order estimate is the nested squared triangle bound
`2 * (2 * (2 + 2) + 2 * (2 + 2)) + 2 = 34` times the common dimensional
cap; every positive-order term vanishes.

The module was checked and exported with the ordinary four-thread, 6 GB focused profile.
The original source-only draft needed only local elaboration repairs: public
metric-realization namespaces, deterministic heartbeat parity with the lower
self-trace module, and a final set-abbreviation normalization.  No mathematical
hypothesis or constant changed.  A temporary axiom census for `phiSelf_grid`
reported only `propext`, `Classical.choice`, and `Quot.sound`.

## Project accounting

- `phiSelf_grid`: proved, focused-verified, exported, and axiom-audited (100%).
- Class-first joint tame producer: not yet stated (0%).
- `lowreg_bounds_unif`: 0%.
- `ricci_flow_unif_existence`: 0%.
- Dedicated uniform-existence supporting machinery: approximately 99%.
- Whole HCG compactness project: approximately 3%.
