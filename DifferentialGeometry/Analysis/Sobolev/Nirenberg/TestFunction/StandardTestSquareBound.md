# Standard test square bound

## Route

`stdTest_sq_bound` is the witness-native Euclidean square estimate for an `L2`
function `u` with an explicit `L2` weak partial derivative `g`.  It applies the
nonsmooth local difference-quotient energy theorem to the cutoff product
`eta^2 * diffQuot u`, using the existing weak product producer, and then
integrates the standard pointwise cutoff algebra.  The derivative term on the
right is `diffQuot g`; no classical derivative of `u` is assumed.

The similarly named test function in `DiffQuotTestFunction.lean` is the
translated inner cutoff product, while this result concerns the standard outer
difference quotient in `NirenbergTestFunction.nirenbergTestFunction`.  A first
smooth-only draft was removed because it could not consume a native weak-gradient
witness.

## Verification

Focused verification and the downstream-required named module refresh both
passed without warnings.  Two module-build whitespace diagnostics were fixed
mechanically before the final refresh.  The source contains no `sorry`,
`admit`, or new axioms.

## Project position

The theorem and its dedicated square-bound machinery are complete (100%).  It
is one producer for the compact-free, witness-native H2 estimate chain (roughly
5% of that larger chain); downstream replacement of the chart-specific square
discharge remains separate integration work and is 0% in this file.
