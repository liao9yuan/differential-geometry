# MinimizingRay

## Scope

This file owns the ordinary Riemannian minimizing-ray predicate and its
existence theorem.  It is independent of Busemann functions and of the P1d
Toponogov lane.

## Public API

- `IsMinimizingRay g p gamma` records the basepoint, the geodesic equation on
  nonnegative times, and exact pairwise Riemannian distance
  `edist (gamma s) (gamma t) = ENNReal.ofReal (t - s)` for
  `0 <= s <= t`.  The distance identity already records unit-speed
  parametrization, so there is no duplicate derivative-speed field.
- `exists_minRay g hEnorm p` constructs such a ray from completeness,
  connectedness, and noncompactness.

## Route

Three native routes were compared: a direct metric-geodesic-ray theorem, an
Arzela--Ascoli limit of finite minimizing curves, and compactness of unit
initial directions.  No ready-made metric ray theorem was found.  The selected
route uses the compact unit sphere of initial directions and a decreasing
family of closed sets whose directions minimize through radii `n + 1`.

The implementation realizes the needed Hopf--Rinow compactness directly: the
compact metric-length ball in one tangent space maps continuously under the
intrinsic exponential, and `minExp_of_ne_top` shows that this image covers the
corresponding closed intrinsic distance ball.  Noncompactness therefore gives
a point outside every such ball, without changing the ambient metric-space
instances.  Finite endpoint minimizers give a nonempty direction set at every
radius.  Compact intersection gives a single direction minimizing at all
integer radii, and the triangle inequality propagates this first to every
nonnegative radial time and then to every forward subsegment.  Only continuity
of `expMapIntrinsic` at each fixed scaled initial vector is needed; the larger
joint-continuity theorem is not used.

The durable dependency chain is:

1. `gLenBall_isCompact`, `expMapIntrinsic_continuous`, and
   `minExp_of_ne_top` give compact closed intrinsic distance balls.
2. `NoncompactSpace` supplies a point outside every such ball; its finite
   endpoint minimizer supplies a unit initial direction minimizing to the
   prescribed radius.
3. Compactness of `gUnitSphere` and the decreasing closed sets `K n` give one
   direction minimizing through all integer radii.
4. `radial_eq_of_end` and `pair_eq_of_radial` propagate endpoint minimality to
   every nonnegative radial time and then every forward subsegment.
5. `intrinsicGeodesic_smul` identifies the exponential curve with the native
   intrinsic geodesic, yielding `exists_minRay`.

## Verification and project status

The first focused elaboration failed before theorem verification.  It exposed
syntax/API issues rather than a mathematical obstruction: an illegal scoped
attribute on the predicate, an addition-side mismatch, a brittle attempt to
transport completeness between metric structures, a missing boundedness API,
and local-definition rewrite mismatches.  The source was repaired statically by
removing the metric-structure transport, proving compactness of intrinsic
closed balls directly, using explicit ENNReal comparisons, and avoiding the
shadowed rewrites.

The second focused elaboration also stopped locally.  Its remaining failures
were instance-discipline issues: the projection declarations still require the
finite-dimensional instance; the radial helper needed to omit only the unused
tangent-bundle separation instance; and the predicate had elaborated with the
default `Tensor0S` tangent norm while its producer deliberately uses the
Riemannian-bundle norm.  The predicate now lives in a local section with the
default tangent norm instances disabled, so the predicate and producer follow
the same instance path, while the projection and helper `omit` lists match the
reported dependencies.

After these repairs, the third focused verification passed without warnings,
and the explicitly named module refresh also passed.  The source is free of
`sorry`; `IsMinimizingRay`, its projections, and `exists_minRay` are now a
verified producer API.  The four P1c endpoints remain 0/4 because this ray
producer is prerequisite machinery for the Busemann endpoint, not one of
those four endpoints itself.
