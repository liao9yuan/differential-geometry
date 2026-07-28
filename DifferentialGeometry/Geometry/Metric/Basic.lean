import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

set_option autoImplicit false

/-!
# DifferentialGeometry metrics

This file contains the DifferentialGeometry-facing alias for smooth Riemannian metrics.
It is not a realized object; realized metric families import this definition.
-/

namespace DifferentialGeometry

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]

/-- DifferentialGeometry-facing alias for a smooth Riemannian metric on `TM`. -/
abbrev SmoothRiemannianMetric
    (I : ModelWithCorners Real E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M -> Type _)

/-- Two smooth Riemannian metrics are equal when their fiberwise inner
products agree. -/
@[ext]
theorem SmoothRiemannianMetric.ext_inner
    {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {g h : SmoothRiemannianMetric I M}
    (hinner : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = h.inner x v w) :
    g = h := by
  obtain ⟨gi, gs, gp, gb, gc⟩ := g
  obtain ⟨hi, hs, hp, hb, hc⟩ := h
  have hfield : gi = hi :=
    funext fun x =>
      ContinuousLinearMap.ext fun v =>
        ContinuousLinearMap.ext fun w => hinner x v w
  subst hfield
  rfl

end DifferentialGeometry
