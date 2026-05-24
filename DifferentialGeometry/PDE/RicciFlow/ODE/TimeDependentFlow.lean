import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartLocalPicard
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.PointwiseLocal
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.UniformExistence
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.Glue
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.Bijective
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.MFDerivPackage

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/--
For a time-dependent vector field `X` on a closed manifold, the integral
flow exists for a positive time horizon as a family of smooth diffeomorphisms
`Φ : ℝ → M ≃ₘ⟮I, I⟯ M`, with `Φ 0 = id` and the pointwise flow equation
`∂_t (Φ s x) = X t (Φ t x)` (formulated as a manifold derivative on
`Set.Ici 0`) for every `t ∈ [0, T)` and every `x : M`.

This is the headline statement consumed by the diffeomorphism-pullback step
of the Ricci-flow short-time existence assembly. The proof is built from the
chart-local Picard–Lindelöf / smoothness / bijectivity / gluing layers in the
`TimeDependentFlow/` subdirectory.
-/
theorem time_dependent_vf_globalflow_on_closed_mfd
    (X : ℝ → ∀ x : M, TangentSpace I x) :
    ∃ T : ℝ, 0 < T ∧
      ∃ Φ : ℝ → M ≃ₘ⟮I, I⟯ M,
        Φ 0 = Diffeomorph.refl I M ∞ ∧
        ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ s) x) (Set.Ici 0) t
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t ((Φ t) x))) := by
  -- Bare-function global flow on a positive horizon.
  obtain ⟨T, hT_pos, Φ_raw, hInit, hFlow⟩ :=
    time_dependent_vf_global_flow_glue (M := M) X
  -- Smoothness in space of every slice `Φ_raw t` for `t < T`.
  have hSmooth : ∀ t : ℝ, t < T → ContMDiff I I ∞ (Φ_raw t) :=
    time_dependent_vf_flow_smooth_in_space (M := M) X T hT_pos Φ_raw hInit hFlow
  -- Bijectivity of every slice together with a smooth inverse `Ψ_raw t`.
  obtain ⟨Ψ_raw, hBij⟩ :=
    time_dependent_vf_flow_bijective_and_inverse_smooth (M := M) X T hT_pos Φ_raw hInit hFlow
  -- Per-time diffeomorphism: glue the data above into a `Diffeomorph` on
  -- `[0, T)` and use `Diffeomorph.refl` as a placeholder on `[T, ∞) ∪ (-∞, 0)`
  -- (only `[0, T)` is exercised by the goal).
  let Φ_diffeo : ℝ → (M ≃ₘ⟮I, I⟯ M) := fun t =>
    if ht : t < T then
      { toEquiv :=
          { toFun := Φ_raw t
            invFun := Ψ_raw t
            left_inv := (hBij t ht).2.2
            right_inv := (hBij t ht).2.2.rightInverse_of_surjective
              (hBij t ht).1.surjective }
        contMDiff_toFun := hSmooth t ht
        contMDiff_invFun := (hBij t ht).2.1 }
    else Diffeomorph.refl I M ∞
  -- Coercion of `Φ_diffeo t x` agrees with `Φ_raw t x` whenever `t < T`.
  have hCoerce : ∀ t : ℝ, t < T → ∀ x : M, (Φ_diffeo t) x = Φ_raw t x := by
    intro t ht x
    simp only [Φ_diffeo, dif_pos ht]
    rfl
  refine ⟨T, hT_pos, Φ_diffeo, ?_, ?_⟩
  · -- Initial condition `Φ_diffeo 0 = Diffeomorph.refl`.
    apply Diffeomorph.ext
    intro x
    have : (Φ_diffeo 0) x = Φ_raw 0 x := hCoerce 0 hT_pos x
    have : (Φ_diffeo 0) x = x := by rw [this]; exact hInit x
    simpa using this
  · -- Flow equation on `[0, T)`.
    intro t ht x
    have htT : t < T := ht.2
    -- Pointwise flow equation supplied by `time_dependent_vf_global_flow_glue`.
    have hFlow_raw : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ_raw s x)
        (Set.Ici (0 : ℝ)) t
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (Φ_raw t x))) := hFlow t ht x
    -- Neighbourhood `Set.Ico 0 T` of `t` inside `Set.Ici 0`.
    have hIco_mem : Set.Ico (0 : ℝ) T ∈ nhdsWithin t (Set.Ici (0 : ℝ)) := by
      have hOpen : IsOpen (Set.Iio T) := isOpen_Iio
      have hIio : Set.Iio T ∈ 𝓝 t := hOpen.mem_nhds htT
      have hInter : Set.Ici (0 : ℝ) ∩ Set.Iio T ∈ nhdsWithin t (Set.Ici (0 : ℝ)) :=
        inter_mem_nhdsWithin (Set.Ici (0 : ℝ)) hIio
      have heq : Set.Ici (0 : ℝ) ∩ Set.Iio T = Set.Ico (0 : ℝ) T := by
        ext s; simp [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici, Set.mem_Ico]
      rw [← heq]; exact hInter
    -- On the neighbourhood, `Φ_diffeo s x = Φ_raw s x`.
    have hEv : (fun s : ℝ => (Φ_diffeo s) x) =ᶠ[nhdsWithin t (Set.Ici (0 : ℝ))]
        (fun s : ℝ => Φ_raw s x) := by
      refine Filter.eventually_of_mem hIco_mem ?_
      intro u hu
      exact hCoerce u hu.2 x
    -- The function values at `t` agree.
    have hAt : (fun s : ℝ => (Φ_diffeo s) x) t = (fun s : ℝ => Φ_raw s x) t :=
      hCoerce t htT x
    -- Transport the flow equation along the coercion equality.
    have hgoal : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_diffeo s) x)
        (Set.Ici (0 : ℝ)) t
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (Φ_raw t x))) :=
      hFlow_raw.congr_of_eventuallyEq hEv hAt
    -- Rewrite `(Φ_diffeo t) x` for the linear-map argument.
    have hΦt : (Φ_diffeo t) x = Φ_raw t x := hCoerce t htT x
    rw [hΦt]; exact hgoal

end DifferentialGeometry.PDE.RicciFlow.ODE
