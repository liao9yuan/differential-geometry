# `Naturality.lean`

## Status

Verified warning-free.  The file is the native fixed-diffeomorphism naturality
layer above `Exp.lean`; it contains no placeholders or new assumptions.

The action-level additions recorded below also pass focused verification
without warnings.  Their named module refresh and the unified P2 audit are
also green.

The first coordinated focused check of the 2026-08-30 open-restriction
addition failed on two local elaboration issues: a mistyped real-model notation
and a restricted metric projection that needed explicit definitional exposure.
The coordinated retry then reached only a reflexive `0 = 0` goal in the
nondifferentiable velocity branch and one unused-section-variable warning.
After those repairs, the next focused check elaborated every declaration and
reported only the same unused ambient instances on the private velocity helper.
Those instances were omitted, and the final coordinated focused check passed
without warnings.  The open-restriction declaration is now verified together
with the earlier declarations.

## Intended chain

- `lRegAccel_pull` transports the regularized acceleration using scalar,
  gradient, Ricci, and pullback-metric naturality.
- `isLRegCurve_pull` transports a single regularized-curve witness using
  `chartRep_map_diff` and `covAlong_natMDiff`.
- `lRegDomain_pull` uses both directions of the diffeomorphism and the native
  pullback composition law to identify maximal witness domains.
- `lRegCurve_pull`, `lExpDomain_pull`, and `lExp_pull` use witness uniqueness to
  identify the chosen totalized curve and L-exponential map.

No new class, wrapper assumption, or parallel geometric definition is
introduced.  The single-witness theorem is directional; maximal-domain equality
uses the inverse diffeomorphism genuinely.

## 2026-08-29 action-level adapters

- `lDensity_pull` identifies the L-density of a curve in a pulled-back solution
  with the L-density of its image under the fixed diffeomorphism.
- `lLength_pull` integrates that pointwise identity on an arbitrary oriented
  interval, with no integrability hypothesis required for the covariance law.
- These are fixed-diffeomorphism smooth-flow adapters only.  They do not assert
  open-embedding locality, restricted-domain equality, time-dependent pullback
  invariance, or pointed action convergence.
- Static review found no same-name or same-shape theorem in the live native
  tree.  The first focused check failed because the declarations incorrectly
  omitted `[I.Boundaryless]`, while their use of `lVelocity_pull` needs the
  induced `BoundarylessManifold I M` instance.  Retaining that real assumption
  fixed the issue, and the authorized focused retry passed without warnings.

## Proof record

The acceleration proof pairs both sides with the target metric.  Pullback-metric
evaluation, scalar pullback, gradient pullback, and Ricci pullback reduce the
identity to the existing `lRegAccel_inner` formula.  This avoids introducing a
new metric-sharp transport wrapper.

The mapped velocity identity is proved without a differentiability hypothesis:
the chain rule handles differentiable points, while a hypothetical
differentiable mapped curve pulls back through the inverse diffeomorphism and
contradicts source nondifferentiability.  Consequently `chartRep_map_diff` can
be applied to the exact L-velocity field, not merely an eventually equal
surrogate.

For maximality, pulling the pulled-back solution through the inverse
diffeomorphism recovers the original solution by `pullbackMetric_trans` and
`pullbackMetric_refl`.  This supplies both witness directions.  The totalized
curve is then identified on witness intervals by `lRegCurve_eqOn`; outside the
common maximal domain both curves reduce to their base points.

Focused verification, the named module refresh, and the unified P2 audit all
passed without warnings.  No mathematical, API, coercion, or tooling blocker
remains.

## 2026-08-30 open-restriction locality

- `lLength_restrict` identifies the raw L-length in an open-restricted solution
  with the ambient L-length of the subtype-valued curve.  It assumes neither a
  solution predicate nor curve regularity, time-carrier conditions, curvature
  bounds, or compactness.
- The private velocity step treats both differentiable and nondifferentiable
  points.  In the reverse direction, a local smooth retraction onto the open
  subtype shows that differentiability of the ambient coercion forces
  differentiability of the subtype-valued curve.
- The density identity then uses the native scalar restriction theorem, the
  restricted-metric inner-product identity, and the exact velocity identity;
  interval integration gives the public result.
- Static dependency review found the new `OpenRestriction` import acyclic.  No
  placeholder, new class, notation, or frontier assumption was introduced.
- The first focused check failed because the new helper accidentally used
  `𝑐(Real, Real)` instead of the native real model and because
  `restrictOpen_inner` could not match through the restricted solution's metric
  projection.  The source now uses the native model and explicitly exposes the
  restricted metric before rewriting.  The second check reduced the remaining
  nondifferentiable branch to `0 = 0` and reported that the local smooth
  retraction helper carried unused ambient manifold instances; a terminal
  reflexivity step and the corresponding explicit omissions now resolve those
  local issues.  The subsequent check elaborated the complete file and found
  only the analogous unused instances on the private velocity helper; those
  omissions were then applied.  The final single-thread focused check passed
  without warnings.  No module refresh or build was run or needed.

## Project position

The original six naturality declarations, the two fixed-diffeomorphism action
adapters, and the open-restriction L-length producer are complete (100%).  Their
dedicated naturality/locality infrastructure is complete (100%).  This closes
fixed-diffeomorphism naturality and raw open-subflow action locality, but the
broader P2b and P2c package endpoints remain unstated and therefore 0%.
Compact ordinary-flow P2a, including `redVolume_anti`, remains 100%; P2d and
the P3 asymptotic-shrinker endpoint remain 0%.  Whole P0--P9 infrastructure
remains approximately 15--25%.
