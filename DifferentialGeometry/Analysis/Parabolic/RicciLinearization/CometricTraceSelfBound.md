# Dimension-only self-cometric trace bound

## Status (2026-08-06)

`cometricTrace_rfns` specializes the existing small-perturbation
`traceHessianFib` estimate to the zero perturbation and transports it across
the canonical input-slot reindexing.  Its bound is the pure dimensional
constant `(finrank E)^6`; it contains no metricwise compactness witness.

`ricciSelf_eq` now exposes the absolute self Ricci principal coefficient as
the exact half-scaled sum of two reindexed self-cometric traces minus the
unreindexed trace.  This is the public representation needed to reduce its
positive covariant derivatives to the parallel self-cometric trace; it is the
absolute-self counterpart of the older private principal-difference model
calculation.

Focused verification passed for both public theorems.  The self-Ricci
representation was checked through the public model-fibre evaluation API,
avoiding the mixed-tensor bundle-instance diamond that blocks a direct
`ContMDiffSection` algebra rewrite in this import closure.  The file is now the
verified lower-layer input for the dimension-only `phiMet` self cancellation
and the class-first curvature coefficient producer.  Direct export passed,
and both public theorems depend only on `propext`, `Classical.choice`, and
`Quot.sound`.

`cometricTrace_rfns_p` extends the dimension-only estimate to every passenger
rank `p`.  Its proof identifies the rank-`p+1` trace with one slot extension of
the rank-`p` trace followed by the fixed three-cycle which moves the new
passenger behind the two contracted slots.  Source reindexing preserves the
fibre norm and slot extension contributes exactly one dimension factor.  The
uniform formula `dim^(p+6)` is intentionally loose at ranks zero and one, but
is independent of the metric and is sufficient for the class-first moving
trace package.

The rank-generic extension now passes focused verification and direct export
without warnings.  Its initial source draft represented the three-cycle with
numeric `Fin` coercions; replacing those by explicit indices removed the
modulo-normalization ambiguity without changing the statement or constant.
The axiom census for `cometricTrace_rfns_p` contains only `propext`,
`Classical.choice`, and `Quot.sound`.

This is supporting infrastructure only.  The class-first joint tame producer,
`lowreg_bounds_unif`, and `ricci_flow_unif_existence` remain unproved (0% as
theorems); dedicated uniform-existence infrastructure remains about 99%, and
the whole HCG compactness project remains about 3%.
