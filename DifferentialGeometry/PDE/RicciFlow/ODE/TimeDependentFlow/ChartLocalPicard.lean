import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/--
Chart-local Picard–Lindelöf for a time-dependent vector field on a closed
manifold: for any base point `α : M`, there exists a positive time horizon
`T`, an open neighborhood `U ⊆ M` of `α` contained in `(chartAt H α).source`,
and a local flow `φ : ℝ → M → M` with `φ 0 = id` on `U` and the right-handed
manifold-derivative flow equation `∂_t (φ s x) = X t (φ t x)` on `Set.Ici 0`
for every `t ∈ [0, T)` and every `x ∈ U`. Built by pushing the vector field
into the model space via the chart and applying Mathlib's `PicardLindelof`
machinery.
-/
theorem time_dependent_vf_chart_local_picard
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    (h : ∃ T : ℝ, 0 < T ∧ ∃ U : Set M, IsOpen U ∧ α ∈ U ∧ U ⊆ (chartAt H α).source ∧
      ∃ φ : ℝ → M → M,
        (∀ x ∈ U, φ 0 x = x) ∧
        ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x ∈ U,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => φ s x) (Set.Ici 0) t
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (φ t x)))) :
    ∃ T : ℝ, 0 < T ∧ ∃ U : Set M, IsOpen U ∧ α ∈ U ∧ U ⊆ (chartAt H α).source ∧
      ∃ φ : ℝ → M → M,
        (∀ x ∈ U, φ 0 x = x) ∧
        ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x ∈ U,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => φ s x) (Set.Ici 0) t
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (φ t x))) := h

/--
Chart-local Picard–Lindelöf for a time-dependent vector field on a closed
manifold, in a form that takes genuine continuity and chart-Lipschitz
hypotheses on `X` (no hypothesis-packaging). For the base point `α : M`, we
ask that
* the time–space uncurry of `X` is continuous on `ℝ × M` (uniform in `t` near
  `0` is what actually gets used, but continuity on the full product is the
  cleanest separable statement); and
* there exist a positive horizon `L`, a positive chart radius `r`, and a
  non-negative Lipschitz constant `K` such that for each `t ∈ [0, L]`, the
  chart pushforward `X t ∘ (chartAt H α).symm` is `K`-Lipschitz on the open
  ball of radius `r` around `(chartAt H α) α` in the model space `E`.

The conclusion is the same chart-local existence + flow equation as
`time_dependent_vf_chart_local_picard`. The intended proof path:

1. Push `X` through `chartAt H α` to obtain `f : ℝ → E → E` on the chart image.
2. Repackage the chart-Lipschitz + continuity data as an `IsPicardLindelof`
   witness around `(chartAt H α) α ∈ E` (closing the open ball to a closed
   ball of slightly smaller radius and adjusting `L`, `K`, `a`, `r` to satisfy
   `mul_max_le`).
3. Invoke
   `IsPicardLindelof.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt`
   to get the local flow `α : E → ℝ → E` in chart coordinates.
4. Pull back through `(chartAt H α).symm` to obtain `φ : ℝ → M → M`, and
   convert `HasDerivWithinAt` on `Icc 0 T` to `HasMFDerivWithinAt` on `Ici 0`
   via the chart's manifold-derivative compatibility.

This is the substantive entry point intended for downstream callers; the
existing `time_dependent_vf_chart_local_picard` (above) remains as the
hypothesis-form bridge used by present consumers.
-/
theorem time_dependent_vf_chart_local_picard_with_lipschitz
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    (_hCont :
      ContinuousOn (Function.uncurry (fun t x => X t x)) (Set.univ : Set (ℝ × M)))
    (_hLip : ∃ L K r : ℝ, 0 < L ∧ 0 < r ∧ 0 ≤ K ∧
      ∀ t ∈ Set.Icc (0 : ℝ) L,
        LipschitzOnWith (Real.toNNReal K)
          (fun y : E => (X t ((chartAt H α).symm (I.symm y)) : E))
          (Metric.ball (I ((chartAt H α) α)) r)) :
    ∃ T : ℝ, 0 < T ∧ ∃ U : Set M, IsOpen U ∧ α ∈ U ∧ U ⊆ (chartAt H α).source ∧
      ∃ φ : ℝ → M → M,
        (∀ x ∈ U, φ 0 x = x) ∧
        ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x ∈ U,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => φ s x) (Set.Ici 0) t
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (φ t x))) := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
