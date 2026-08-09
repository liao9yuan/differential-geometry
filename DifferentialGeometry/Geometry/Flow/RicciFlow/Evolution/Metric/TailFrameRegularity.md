# TailFrameRegularity

This module packages the full metric-frame spacetime regularity available on a
strictly positive tail of a Ricci-flow solution.

The key point is that the new closed-left carrier `[t0, omega)` lies inside the
original regular interval `(alpha, omega)`.  Therefore the original solution's
joint metric-frame smoothness applies even at the new left endpoint.  The
fixed-base space/time derivative field is supplied by the Ricci-flow equation
and `metricFrameComp_fixedBaseSwap_of_solution`.

Status: focused verification passed. The theorem constructs the positive-tail
metric-frame spacetime regularity package from `IsSolutionOn`; it does not
assume that package as a new blackbox.

## `tailCoordFrameReg` — the same package for the chart inverse (ruling R11)

`tailFrameSpaceReg` is stated for the zero-extended `localFrameInv`, whose
off-`u` cutoff was historically needed to satisfy the *global*
`inverseMetricDerivative` field.  Under ruling R11 that field is `u`-local
(`InvMetricDerivLocal`), which unlocks the observation that **four of the six
fields of `MetricFrameSpacetimeRegularityInFrameOnLocal` never mention the
inverse components at all**.  So the package transfers between inverse-component
families by supplying only the two that do:

- `MetricFrameSpacetimeRegularityInFrameOnLocal.congrInv` (`Metric/Basic.lean`)
  swaps `(gInv, gInvDt)` given `InvMetricLocal` and `InvMetricDerivLocal` for the
  replacement pair;
- `coordInvLocal` (`Metric/Evolution.lean`) and `coordInvDerivLocal`
  (`Metric/InverseSmooth.lean`) supply those two for `coordInv`/`coordInvDt`.

`tailCoordFrameReg` is the three-line composition.  This is what discharges the
`hmetricReg` input of `Rm04Producer`'s evolution endpoints; the consumers live in
`Evolution/Rm04ProducerTail.lean`.

Note that only `metricSmooth` and `frameMetricSpacetimeSmooth` actually need the
tail (they are carrier-level, and the carrier's closed left endpoint must be an
interior time of the ambient solution).  `coordInvDerivLocal` needs no tail at
all: `InvMetricDerivLocal` quantifies over `RegularTime`, and `coordInvSmooth`
already covers `D.regular ×ˢ coordinateFrameSet`.
