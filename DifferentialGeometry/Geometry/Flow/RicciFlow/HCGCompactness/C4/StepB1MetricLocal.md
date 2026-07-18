# StepB1MetricLocal status

## 2026-07-16: buffered moving-source coefficient tail

Status: focused verification passed, with no `sorry`, `admit`, or warnings.

This file closes the moving-source localization layer between
`StepB1MetricBridge` and the later intrinsic metric-error bridge.

- `HasSuppConvData.source_stay` converts a convergent sequence of coordinate
  centers with one fixed closed-ball buffer and source membership at radius
  `R` into fixed neighborhoods `V ⊂⊂ W ⊂ interior C0`.  The corresponding
  inverse normal charts eventually map `W` into every prescribed larger
  source ball of radius `S`, for `R < S`.
- `HasStageJetData.pb_buf_tail` uses a bad-sequence argument, compactness of
  `C0`, `source_stay`, and `HasStageJetData.pb_conv`.  For one fixed live source
  chart and positive buffer radius, it gives a single rectangular `(k,l)` tail
  for all derivative orders `j ≤ p`.  Its conclusion compares the actual
  target-stage normal metric pulled back by the actual stage comparison map
  directly with the source-stage normal metric.
- `HasStageJetData.pb_local_tail` consumes the producer-owned `buffer_cover`,
  applies `pb_buf_tail` once per live source chart, and takes a finite maximum
  of their thresholds.  Every point of the smaller source ball therefore has a
  buffered source-chart witness satisfying the coefficient estimate on one
  common two-stage tail.

The theorem is intentionally not stated for every arbitrary point of
`interior C0`.  A bad sequence of such points may approach the boundary, so
the fixed `V ⊂⊂ W` required by `pb_conv` need not exist.  The retained
closed-ball buffer is exactly the honest premise produced by `buffer_cover`;
no stage-family stay assumption or new compactness-input field was added.

## Remaining frontier and accounting

The Euclidean moving-source coefficient sublane in this file is complete
(100%).  The next independent analytic frontier is the chart-coefficient to
intrinsic `tensor02CovDerivNormWith` conversion, followed by the corresponding
exact-local-inverse estimate.  Those results are not claimed here.

- `StepB1RawInput` producer theorem: stated and partially filled, but still 0%
  at theorem level while its two metric fields contain `sorry`.  Its dedicated
  concrete record-field machinery is approximately 60% complete.
- Dedicated B/C machinery: approximately 98%.
- Chapter 4 machinery: approximately 90%.
- Whole HCG machinery: approximately 60%.
- Textbook B1 and compactness endpoints: 0% until their Lean theorem bodies are
  stated and proved from the concrete producer.
