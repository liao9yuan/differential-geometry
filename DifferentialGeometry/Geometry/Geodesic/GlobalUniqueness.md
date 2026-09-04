# Global geodesic-vector-field uniqueness

## Role

`gvf_eqOn` is the canonical uniqueness producer for the global
`geodesicVectorField`.  It is intentionally independent of the fixed-chart
maximal-geodesic witness.

## Mathematical route

The proof reuses `geodesicVF_smooth` and Mathlib's local uniqueness theorem
`isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless`.  Local equality
is propagated across an open preconnected real-time domain by separating the
equality and inequality loci into relatively open pieces.  The Hausdorff
hypothesis on the tangent bundle is used only for openness of the inequality
locus.

The existing chart-specific clopen proof in `PreconnectedPropagation.lean` was
used as a local pattern; its chart-source assumption and chart vector field are
not copied into the new API.

## Verification

The import was lowered from `CrossVFReduction` to `GlobalVectorField`, with
Mathlib's generic integral-curve uniqueness imported directly.  Focused
verification passed without warnings, and the explicit named refresh passed
for the forthcoming `MaximalInterval` consumer.  The theorem contains no
`sorry` or new axiom.

## Project status

`gvf_eqOn` itself is complete (100%).  The maximal-witness migration is a
separate support step now unblocked by the acyclic import.  P1a still has seven
of eight project-used endpoints checked (87.5%); the remaining compact-closure
Bishop endpoint itself remains not started (0%).
