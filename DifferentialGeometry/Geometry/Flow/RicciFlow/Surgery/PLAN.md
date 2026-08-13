# Surgery and RFWS plan

This is the running plan for phases B8--B9 of `POINCARE_PLAN.md`.  The route
follows Morgan--Tian's `surgery.tex`, but uses event presentations first and
constructs the exotic total surgery spacetime only after the local event API
is stable.

## Scope ruling

The geometric and analytic surgery construction is in scope.  Pure
three-manifold topology remains an explicit final input.  This lane must model
changing manifolds honestly: neither one fixed manifold nor an unstructured
dependent sum of time slices is an acceptable RFWS representation.

## S0: event and spacetime foundations

### S0a. Smooth event seam

Represent one event by two independent manifold types, open event
neighborhoods, a smooth diffeomorphism between those neighborhoods, and a
retained subset of the old neighborhood.  Derive the retained post-region,
discarded region, created region, and their equivalence.

Target: `Surgery/Seam.lean`.

Status: complete and focused-green, with no placeholders.

### S0b. Metric seam

Add a separate predicate asserting that the event identification is an
isometry on the retained region.  Reuse metric restriction and pullback APIs;
do not add metric data to `SurgerySeam`.

Target: `Surgery/MetricSeam.lean`.

Status: source-written; focused verification pending.

### S0c. Smooth slabs and event

Reuse `SolutionOn` and `IsSolutionOn` for each fixed-manifold interval between
events.  Package an event time, the two adjacent slabs, and a metric seam.
Extract generic open-restriction and pullback solution APIs from their current
HCG location only when this consumer needs them.

Target: `Surgery/Event.lean`.

### S0d. Event diagram

Build a locally finite, time-ordered diagram of smooth slabs and surgery
events.  Define time restriction, translation, parabolic scaling, and
concatenation at this presentation level.  Prove these operations preserve the
event equations.

### S0e. Total spacetime realization

Morgan--Tian's total surgery spacetime contains a genuinely exotic type-three
chart.  It is not an ordinary manifold-with-boundary chart.  Only after the
event diagram works should we choose between:

1. a custom atlas with ordinary, exposed-boundary, and exotic chart kinds; or
2. a realization theorem from the event diagram into a stratified smooth
   spacetime interface.

The horizontal bundle, horizontal metric, slice curvature, and
`Lie_chi G = -2 Ric` equation belong after this realization layer.  Derived
objects such as time slices, regular times, horizontal Levi--Civita connection,
and curvature must not be stored redundantly as fields.

## S1: local surgery metric

After S0b is stable, formalize the local delta-neck surgery metric:

1. round cylinder and standard cap data;
2. the universal bump functions and conformal factor;
3. metric interpolation on the overlap;
4. smoothness and positive-definiteness;
5. exact agreement with the old neck and the new cap on their respective
   regions.

This phase may assume a supplied delta-neck.  Producing the neck at a singular
time belongs to the later controlled-flow induction.

## S2: local geometric estimates

Prove the conformal curvature identities and the four Morgan--Tian local
surgery conclusions: preservation of pinching, positive sectional curvature
on the cap, the distance-decreasing comparison map, and high-order closeness
to the rescaled standard cap.

## S3: controlled RFWS

Only after reduced geometry, kappa-solutions, the standard solution, and
generalized-flow compactness are available should this lane prove neck
selection, surgery-stable noncollapse, canonical-neighborhood propagation,
nonaccumulation of surgery times, and global controlled RFWS existence.

## Dependency and stop rules

- Never encode all slabs as `SolutionOn` on one fixed manifold.
- Never use `DirectLimitManifold` as the event model: nested open exhaustion is
  not deletion plus cap creation.
- Never turn neck, pinching, or noncollapse conclusions into fields of a data
  structure.
- Stop before a custom exotic-atlas foundation if the event presentation has
  not yet demonstrated the exact consumers it must support.

## Honest status

- RFWS and controlled-flow endpoint theorems: unstated, therefore 0%.
- S0 dedicated machinery: approximately 10--15% once `Seam.lean` verifies.
- Local surgery metric theorem: unstated, therefore 0%.
- Whole surgery phase: approximately 1--2% infrastructure.
- Whole post-HCG Poincare program: approximately 15--20%.
