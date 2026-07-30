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

## 2026-07-28 final assembly draft

The source now states `exists_h6NormalData`. It reuses the single
`H6BallData` witness, sets the global launch radius to
`d.ratio * hd.mu 0`, and defines the order-`n` metric constant from the
intrinsic full Fréchet-derivative estimate. The half/two estimate comes from
`H6BallData.normal_equiv`; the derivative estimate is transferred from
`intrFrameMetric` by `H6ChartData.metric_eq_intr` and
`NormalBallChart.MetricDerivBound.of_eqOn`. No new radius, chart, or
consumer-side assumption is introduced.

Verification is complete. `exists_h6NormalData` is focused GREEN and exact
GREEN (`3983/3983`) against exact-current `IntrinsicMetricJets`,
`H6MetricJet`, `NormalBallChart`, and `H6NormalCoord` artifacts. The only
failure during final replay was a stale `exists_intr_control` export; refreshing
its canonical owner exposed no local source error.

Current accounting: `exists_h6NormalData` and its dedicated H6
normal-coordinate producer machinery are 100% complete. This does not prove
the independent legacy `NormalRadiusProfile.le_exp_radius`, and it does not by
itself complete the provider substitution in the selected Step B/C consumer.
The unconditional MSM135 endpoint remains 0%.

## 2026-07-29 radius normalization

`exists_h6BallData` now caps the launch radius by `min r₀ 1`. The resulting
construction theorem `h6Ratio_mu0_le_half` proves
`h6Ratio r₁ * hd.mu 0 ≤ 1 / 2`, and the field `ratio_mu0_le` carries this
genuine fact through `H6BallData`, `H6ChartData`, and therefore
`H6NormalData`. The smaller chart balls remain inside the original
`exists_intr_control` ball, so the existing local-diffeomorphism and half/two
metric estimates are unchanged.

Focused and exact verification are GREEN (`3983/3983`). The next consumer is
the H6 target-stage membership/decode proof in `StepCStageComparison`; it may
now use the retained normalization to close the exponential pair-radius bound.

The dedicated H6 producer remains 100%. This strengthening removes the current
Gate 5 quantitative producer blocker but does not itself close provider
substitution or the unconditional MSM135 endpoint, which remains theorem-level
0%.

## 2026-07-29 subsequence transport

`H6NormalData.subseq` now transports the complete controlled chart family,
including its branch radii, metric bounds, and normalized ratio, to an
arbitrary subsequence. This is the producer-side bridge used by the finite
transition diagonal in `StepCProducersH6`.

Focused verification is GREEN and the producer artifact is exact-current
(`3983/3983`). `exists_h6NormalData` remains 100%. Gate 5 provider substitution
is now complete in the downstream H6 support/readout modules; the unconditional
MSM135 endpoint is still unstated and therefore 0%, and whole-HCG supporting
machinery is about 70%.
