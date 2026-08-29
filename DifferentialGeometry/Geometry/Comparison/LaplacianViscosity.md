# LaplacianViscosity

## Scope

This module is the canonical lower-test viscosity layer immediately above
`DistanceBarrier`.  It defines pointwise and set-level predicates for
`Delta u <= b` and contains only the barrier-to-viscosity conversion. It does
not add local-uniform stability, a distributional predicate, or a weak bridge.

The sign convention is deliberate: a smooth test `psi` touches `u` from below,
so an upper barrier `phi` makes `phi - psi` attain a local minimum at the
contact point.  The native spatial-minimum theorem therefore gives
`0 <= Delta (phi - psi)`, hence `Delta psi <= Delta phi`.

## Native proof route

`IsLapLEBarrierAt.to_viscosity` consumes the epsilon-relaxed barrier directly.
It forms the local minimum from the two eventual support inequalities, derives
the finite-order nearby differentiability and gradient regularity required by
the native Laplacian-minimum theorem, and uses the Levi-Civita metric
compatibility producer.  The pointwise Laplacian subtraction theorem then
compares the lower test with the barrier.  Letting the positive barrier error
tend to zero yields the exact viscosity bound.

The minimum step keeps the contact point explicit through
`I.IsInteriorPoint x`; it does not silently discharge this proof inside the
adapter.  The ambient boundaryless model instance is still required by the
current global `LeviCivita` construction.  The vector-bundle regularity
assumptions are exactly those consumed by the native spatial-minimum theorem.

## Verification and project status

The source is written without `sorry`, new axioms, classes, instances, or
notation.  The first coordinated focused check proved every declaration but
reported four unused section instances on
`IsLapLEBarrierAt.to_viscosity`: `NeZero (Module.finrank Real E)`,
`I.Boundaryless`, `T2Space M`, and `SigmaCompactSpace M`.  The theorem now has
that exact `omit` list before its docstring.  The second focused check passed
without warnings, and the explicitly named module refresh also passed
(`3945/3945`).  The pointwise and set-level viscosity predicates and the
barrier-to-viscosity conversion are therefore checked, warning-free,
and `sorry`-free source infrastructure.

The barrier-to-viscosity bridge itself is complete (100%).  The formal P1c
Laplacian-comparison endpoint remains unstated or unproved at 0%: the checked
bridge is dedicated infrastructure and does not yet pass locally uniform
limits or produce the intrinsic distributional inequality.  Local-uniform
viscosity stability and the viscosity-to-distributional bridge remain separate
missing layers at 0%, and the formal Busemann and splitting endpoints also
remain 0%.
