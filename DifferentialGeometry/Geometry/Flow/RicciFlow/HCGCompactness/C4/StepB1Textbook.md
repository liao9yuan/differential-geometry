# StepB1Textbook

## Role

`MetricCompactBase.exists_b1` is the textbook-facing MSM135 Chapter 4 Step B1
endpoint. It selects one master subsequence before quantifying over the
positive source-ball radius, the tolerance in `(0,1)`, and the finite
derivative order.

The comparison map is an honest `PartialDiffeomorph`. Its source contains the
closed source ball, it preserves the basepoint, and
`BookApproxIsoPartialData` records the forward and inverse approximate-isometry
estimates. The statement is deliberately ball-to-image and does not assert a
global diffeomorphism between the manifolds.

## Route

The proof combines `MetricCompactBase.exists_b1_raw`, which supplies one
master subsequence and all five raw comparison fields, with
`stepB1_of_raw`, which packages each sufficiently late comparison map as the
partial diffeomorphism used by the book statement. No new geometric input or
consumer-side assumption is added.

## Verification and accounting

- Textbook `MetricCompactBase.exists_b1`: focused verification passes, so the
  theorem and its proof body are complete.  Its exact artifact refresh is
  blocked by two source-newer H6 migration errors in the imported
  `StepCStageComparison`, not by this theorem.
- Canonical raw producer: 100%.
- Dedicated selected-route B1 machinery: 100%.
- Conditional Theorem 3.9 remains separately complete.
- Unconditional Theorem 3.9 and the Hamilton compactness application remain
  separate producer frontiers.

Strict accounting: textbook B1 is theorem-level 100% at the source/focused
level and its dedicated machinery is 100%; exact-current export is pending the
shared upstream repair.  Whole HCG supporting machinery is approximately
72--75%, while the unconditional compactness endpoints remain theorem-level
0% until their native `MetricCompactBase` producer is assembled.
