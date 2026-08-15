# Intrinsic exponential globalization

## Scope

`exists_geo_eqOn_Icc` globalizes a continuous geodesic segment on a complete
Riemannian manifold.  Given `a ≤ b`, `ContinuousOn γ (Icc a b)`, and the
geodesic equation on that closed interval, it produces a globally smooth
geodesic agreeing with `γ` throughout the interval.

## Proof route

The degenerate interval uses the constant geodesic.  For `a < b`, the proof
translates the midpoint to time zero, initializes the complete intrinsic
geodesic with the segment's position and velocity, and applies
`geo_eqOn_of_init` on the translated open interval.  Continuity and
`closure_Ioo` extend the agreement to both endpoints before translating back.

This is the reusable bridge between closed-segment geodesic predicates and
the library's global smooth-geodesic comparison theorems.  It does not assume
that the segment is minimizing.

## Verification

Focused, targeted, and full-project verification passed without a new warning
or placeholder.  Direct axiom verification of `exists_geo_eqOn_Icc` found only
`propext`, `Classical.choice`, and `Quot.sound`.
