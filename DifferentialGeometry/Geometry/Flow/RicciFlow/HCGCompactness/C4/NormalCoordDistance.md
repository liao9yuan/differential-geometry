# Normal-coordinate distance bridge

## Scope

`NormalCoordMetricEquivOn.symm_dist_le` is the reusable H6 upper-distance
bridge.  It pushes the Euclidean line segment between two controlled normal
coordinates through the inverse framed normal chart, bounds its Riemannian path
length by the upper half of `NormalCoordMetricEquivOn`, and converts the
Riemannian extended distance to the selected proper metric with
`ProperMetricOn.realizes`.

The theorem is deliberately segment-local.  It adds no convexity, radius, or
endpoint assumption beyond containment of the requested segment in the H6
region and containment of that region in the normal-chart target.

## Verification

The canonical source repair is complete:

- `H6Isometry.normalTrans_dist_le` now uses `framedTransition` and the framed
  source/overlap domains;
- `symm_dist_le` now uses `framedChartAt` / `framedExpDiffeo`;
- `chart_dist_le` now follows the framed chart and its inverse throughout.

After the ordered H6 module refresh, focused verification passes with no
diagnostics.  No targeted build of this distance module was needed.

## Project accounting

- The framed source migration: 100% implemented and focused-green.
- The three reusable framed distance theorems: 100% stated, proved, and
  focused-green.
- The source-local moving-root-to-center identification that consumes it: not
  completed here.
- The global all-pairs stage-map theorem: 0% as a theorem until that
  identification is assembled.
- `StepB1RawInput` producer and textbook Step B1: 0% as theorems.

## 2026-07-28 controlled-chart distance

`NormalBallChart.MetricEquivOn.inv_dist_le` is the provider-independent form
of the chart-distance estimate.  It uses only the controlled partial
diffeomorphism, the pullback metric carried by that chart, half/two metric
equivalence, and containment of the minimizing join in the chart target.
Focused verification passes.

This closes the reusable distance API needed by the H6 provider switch.  The
new lemma is 100%; the Gate 5 consumer/provider substitution remains about
20%; the dedicated H6 producer remains 100%.  It does not prove
`NormalRadiusProfile.le_exp_radius` or the unconditional MSM135 endpoint,
which remain theorem-level 0%.
