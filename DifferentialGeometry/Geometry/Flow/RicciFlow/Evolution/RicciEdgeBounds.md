# RicciEdgeBounds

## Verified producer (2026-07-18)

`ricciEdgeMetric` is proved without `sorry` and passes a warning-free focused
check.  It consumes exactly the joint chart-Gram `C0` regularity already present
in `ricci_flow_forward_unique`.  For every compact initial slab
`Icc a c` with `c < b`, it produces one `Lambda >= 1` such that, simultaneously
for every `t`, point, and tangent vector on that slab,

```text
Lambda^-1 * g(a)(v,v) <= g(t)(v,v) <= Lambda * g(a)(v,v).
```

The proof uses the canonical chart-Gram-to-bundled-tensor continuity bridge.
It bounds the evolving metric on the compact `g(a)`-unit tangent slab and the
initial metric on the compact evolving-unit time slab; combining the two bounds
gives the two-sided constant.  No Ricci bound, PDE integration, uniqueness, or
new endpoint hypothesis is used.

Accounting: this zeroth-order producer is 100%.  The exact theorem
`ricci_flow_forward_unique` remains 0%.  Its initial-edge metric-equivalence
subbrick is now 100%; its fixed-background order-one bound and weighted
order-two bound remain 0%.

## Exact remaining edge producer

The next analytic theorem should consume the same chart-Gram smoothness and
continuity fields plus the existing Ricci PDE field, and prove a short window
`a < c < b` and a constant `A` with

```text
metricCovDerivNorm 1 (g t) (g a) x <= A
sqrt (t - a) * metricCovDerivNorm 2 (g t) (g a) x <= A
```

for every `t in Ioc a c` and `x`.  A suitable public name is
`ricciEdgeDeriv`.  This is the precise order-one/order-two part still missing
from the proposed aggregate `ricci_edge_bounds` package.

## Routes audited for the derivative part

1. **Interior chart compactness.**  Joint `C-infinity` on `Ioo a b` gives
   bounds on each `Icc (a + delta) c`, but direct compactness cannot make them
   uniform as `delta` tends to zero.  `C0` convergence of the coefficients at
   `a` does not control their spatial derivatives.  Classification: invalid
   topological inference; a boundary parabolic estimate is required.
2. **Time shift plus the existing Shi machinery.**  The available
   `movingShiBoundN`/`movingShiBoundSol` first require a uniform curvature bound
   on the whole solution slab and are dimension-three producers.  The exact
   forward-uniqueness hypotheses are dimension-generic and carry no such
   curvature bound.  The repository also has no uniform-in-shift bridge from
   those moving curvature bounds to the displayed fixed-background metric
   derivative estimates.  Classification: missing analytic producer/API, not
   a routine adapter.
3. **Gauge-fixed boundary regularity.**  Ricci-DeTurck or harmonic-map heat-flow
   Schauder estimates would faithfully yield the edge bounds, but the repository
   has no harmonic-map heat-flow existence package, gauge PDE identity, or
   boundary regularity theorem for an arbitrary geometric Ricci flow.
   Classification: substantial parabolic/gauge infrastructure.

No route produced a counterexample to the existing forward-uniqueness
statement.  The obstruction is formalized analytic groundwork, not evidence
that the endpoint statement is false.
