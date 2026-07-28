# H6NormalData

## 2026-07-27 intrinsic metric bridge

`H6ChartData.metric_eq_intr` proves that the metric carried by the selected
whole-ball H6 chart is exactly `intrFrameMetric` on its controlled open ball.
The proof uses `H6ChartData.hom_eq` on a neighborhood of each ball point,
transports that equality through `mfderiv`, and then unfolds the two pullback
metrics. No agreement with the legacy selected chart and no new compatibility
assumption is used.

`H6ChartData.radius_le_global` proves that every selected chart ball lies in
the one fixed model ball of radius `d.ratio * hd.mu 0`. Consequently the
all-order producer can be stated for an arbitrary prescribed finite launch
radius, then instantiated at this explicit value; it does not need access to
the hidden radius witness used earlier to construct the local branches.

The zero-order construction is now proof-coherent. `exists_intr_control`
chooses one radius carrying both the intrinsic half/two estimate and the
local-diffeomorphism property. `H6BallData.intr_equiv` retains the estimate on
the exact relative ball used by its chart, and `H6BallData.normal_equiv`
transports it through `metric_eq_intr` to the common
`NormalBallChart.MetricEquivOn` interface. Final assembly will therefore not
choose a second unrelated radius for `metric_equiv`.

Together with `NormalBallChart.MetricDerivBound.of_eqOn`, this closes the final
formal transfer from future intrinsic all-order bounds to
`H6NormalData.metric_deriv`. The lower combined-radius theorem is
focused-green. The updated `H6NormalData` source is also focused-green against
an isolated overlay of the new `H6NormalCoord` artifact. The only real local
diagnostic was that the result-type `let hEnorm` preceded the coordinate
variables in the `intr_equiv` constructor; an explicit `change` to the
half/two estimate restored the intended binder order. The formal project
artifact refresh still awaits the shared exact-writer window.

The remaining mathematical frontier is unchanged: prove one sequence-uniform
fixed-tube bound for all launch-parameter derivatives of the intrinsic
geodesic/Jacobi flow, then derive bounds for `iteratedFDeriv` of
`intrFrameMetric`. Smoothness alone is not such a bound.

Progress accounting: `exists_h6NormalData` is still unstated and therefore 0%
as a theorem. Dedicated all-order metric-jet machinery remains about 35%;
this bridge is a small assembly step. Overall dedicated H6 producer machinery
remains about 55%, and unconditional MSM135 Theorem 3.9 remains 0%.
