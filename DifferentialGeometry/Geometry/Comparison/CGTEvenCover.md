# CGTEvenCover

## 2026-07-27 inverse-fiber injection

`intrFiber g hEnorm p q r` is the actual inverse fiber of the intrinsic framed
exponential over `q`, restricted to the model ball of radius `r`.

`exists_fiber_inj` transports this fiber from the basepoint to a nearby target
along one selected short flat path.  The endpoint of the lifted concatenation
lies in the enlarged ball.  If two transported endpoints agree,
`IntrFrameLift.end_eq_of_append` cancels the common suffix and the explicit
radial lifts recover equality of the original vectors.

`fiber_encard_le` is the extended-cardinality corollary.  No path quotient,
global sheet selector, covering-space hypothesis, or short-homotopy witness is
introduced.

Focused verification and the targeted artifact refresh are green.  Paper
Lemma 4.5 is theorem 100% and dedicated machinery 100%.  The next genuine
frontier is paper Lemma 4.6: strict convexity and a unique finite-family center
on the small pullback ball, followed by the fixed-point-free propeller
argument.  `intrLoop_ge_cgt`, the sequence-level injectivity-decay producer,
and unconditional metric compactness remain theorem 0%.  Dedicated pointwise
CGT machinery is now about 50–55%; whole HCG supporting machinery remains
about 61%.
