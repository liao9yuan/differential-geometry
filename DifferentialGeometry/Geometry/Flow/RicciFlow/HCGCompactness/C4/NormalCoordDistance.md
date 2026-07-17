# Normal-coordinate distance bridge

## Scope

`NormalCoordMetricEquivOn.symm_dist_le` is the reusable H6 upper-distance
bridge.  It pushes the Euclidean line segment between two controlled normal
coordinates through the inverse normal chart, bounds its Riemannian path
length by the upper half of `NormalCoordMetricEquivOn`, and converts the
Riemannian extended distance to the selected proper metric with
`ProperMetricOn.realizes`.

The theorem is deliberately segment-local.  It adds no convexity, radius, or
endpoint assumption beyond containment of the requested segment in the H6
region and containment of that region in the normal-chart target.

## Verification

Focused verification passed without warnings.

## Project accounting

- This reusable distance lemma: 100% (stated, proved, and focused-green).
- The source-local moving-root-to-center identification that consumes it: not
  completed here.
- The global all-pairs stage-map theorem: 0% as a theorem until that
  identification is assembled.
- `StepB1RawInput` producer and textbook Step B1: 0% as theorems.
