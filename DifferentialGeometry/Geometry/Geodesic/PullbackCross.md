# PullbackCross

## Role

This module is the canonical cross-model naturality bridge for geodesics under
a diffeomorphism equipped with the pullback metric.

## Current state

`geoEq_mapCrossAt` and `geodesicOn_mapLocal` are complete.  They consume the
pointwise along-curve naturality theorem `covAlong_natCrossAt`, identify
pushed-forward velocities as a germ by the manifold derivative chain rule, and
transfer the moving-foot geodesic equation using only a fixed `C²`
neighborhood.  Thus a geodesic and a `C∞` curve on an open time set transport
without any global curve extension.

`geoEq_mapCross`, `geodesic_mapCross`, and `geodesicOn_mapCross` remain as the
globally smooth compatibility wrappers.

Focused verification and the targeted module refresh passed without local
warnings, `sorry`, or `admit`.

The locality gap is closed and consumed by
`NormalPhaseEndpoint.normal_end_eq_intr`; cross-model geodesic naturality is no
longer on the B1 frontier.

## Project position

The cross-model geodesic naturality producer and the normal-coordinate endpoint
bridge are complete (100%).  `exists_normal_diag` now packages the quantitative
model branch and exact `diagExp` square; `normal_inv_eq` gives the compatibility
criterion with `diagExpInv`.  `StepB1RawInput` and textbook B1 remain 0%;
dedicated normal-branch machinery is about 85%, Step B/B1 infrastructure about
72%, Chapter 4 machinery about 69%, and whole HCG infrastructure about 49%.

## 2026-07-28 reflected geodesic equation

Added `geoEq_of_mapCrossAt`, the converse pointwise naturality theorem: if a
curve mapped by a cross-model diffeomorphism is geodesic for the target metric,
then the source curve is geodesic for the pullback metric.  The proof uses the
injective derivative equivalence and the existing covariant-derivative
naturality theorem; it introduces no parallel local-isometry predicate.

Focused verification passed without diagnostics.  The theorem and its
dedicated cross-model machinery are 100%.  It is supporting infrastructure for
the now-complete localized Whitehead producer; `intrCore_jensen` remains
theorem-level 0% with about 93% dedicated machinery, and whole HCG supporting
machinery is about 62%.
