# PointedAction

## Scope

This file implements the RFWS-independent local interfaces for book12
`prop:red-action-convergence`: transport velocity and kinetic energy through a
pointed source map, then integrate explicit scalar and kinetic convergence
along a fixed curve.  It does not state convergence of minimizers, reduced
distances, or mass.

## Native route

- `lVelocity_src_map` is the manifold chain rule at a point where both the
  source curve and the source map are `MDifferentiableAt`.
- `lKinetic_src_pull` combines that chain rule with
  `SourceDomainMetricData.pullback_inner`.
- `lLength_tendsto` is the analytic integration adapter.  It assumes uniform
  convergence of the scalar and kinetic terms on the parameter interval,
  eventual almost-everywhere strong measurability of the resulting densities,
  and an eventual uniform density bound.  Dominated convergence then gives the
  exact L-length limit.
- The source-map differentiability hypothesis is necessary at this generic
  layer: `SourceDomainMetricData` stores arbitrary topology/charted instances,
  so the canonical smoothness of `sourceTargetDiff` is not definitionally
  available for every such package.

Compact confinement is intentionally absent from `lLength_tendsto`: once the
two along-curve terms are explicitly controlled, confinement plays no role in
the interval argument.  It belongs to the missing HCG producer.  That producer
must place the fixed curve in a compact `K`, obtain eventual
`K ⊆ Phi.source k`, upgrade scalar pullback convergence from pointwise to
compact-uniform on the space-time tube, and combine spacetime metric convergence
with a uniform reference-metric speed bound for the fixed curve.

The current `SmoothCGHConverges` API does not provide those last two uniform
inputs.  Its scalar convergence is pointwise in spacetime, and the reference
metric used by spacetime metric convergence has no packaged uniform control on
a fixed curve's speed.  Therefore `SmoothCGHConverges` alone is not advertised
as an action-convergence theorem.

## Verification and progress

The first focused check stopped at a syntax error: lines 58, 82, and 115 used
the non-project notation `𝓥(Real, Real)` instead of the established
real model notation `𝓘(Real, Real)`.  After correcting those three occurrences,
the focused retry passed without warnings.

The two pullback declarations remain verified.  After the redundant
statement-level `densityLim` let was removed, `lLength_tendsto` passed focused
verification without warnings and its named module refresh also passed.  This
analytic integration endpoint is therefore **100%** complete.  The missing
cross-flow HCG uniform producer remains **0%**: the exact blocker is
compact-uniform scalar pullback convergence together with uniform
reference-speed control on the fixed curve.

The separate reduced-density total-mass/no-mass-loss endpoint also remains
open.  Fixed-curve action convergence does not supply chart tightness, compact
ball capture, or control of the mass outside transported compact sets.

At the authoritative phase level, P2a is **100%**.  This integration endpoint
is one P2c brick; broader P2c interfaces and the independent P2b producer lane
must be counted separately.  The whole P0--P9 Poincare program remains about
**15--25%** complete.

The named module refresh is current for all three declarations in this file.
The downstream direct axiom audit for `lLength_tendsto` remains pending.
