import DifferentialGeometry.Geometry.Topology.EmbeddedSlice
import DifferentialGeometry.Geometry.Coordinates.LocalDiffeoIFT
import Mathlib.Analysis.Normed.Module.Complemented

open Set Topology
open scoped ContDiff Manifold

noncomputable section

namespace DifferentialGeometry
namespace Geometry

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_slice_image [CompleteSpace E] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F]
    {f : F → E} {U : Set F} {a : F}
    (hU : IsOpen U) (ha : a ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hinj : Function.Injective (fderiv ℝ f a)) :
    ∃ V : Set F, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧ Set.InjOn f V ∧
      IsEmbeddedSlice 𝓘(ℝ, E) (Module.finrank ℝ F) (f '' V) := by
  let D : F →L[ℝ] E := fderiv ℝ f a
  let R : Submodule ℝ E := D.range
  have hRclosed : IsClosed (R : Set E) := R.closed_of_finiteDimensional
  obtain ⟨Q, hRQ⟩ : ∃ Q : Submodule ℝ E, IsCompl R Q := R.exists_isCompl
  have hQclosed : IsClosed (Q : Set E) := Q.closed_of_finiteDimensional
  let eD : F ≃L[ℝ] R := D.equivRange hinj hRclosed
  let eRQ : (R × Q) ≃L[ℝ] E :=
    R.prodEquivOfClosedCompl Q hRQ hRclosed hQclosed
  let e : (F × Q) ≃L[ℝ] E :=
    (eD.prodCongr (ContinuousLinearEquiv.refl ℝ Q)).trans eRQ
  let j : F →L[ℝ] E :=
    (e : (F × Q) →L[ℝ] E).comp (ContinuousLinearMap.inl ℝ F Q)
  have he_apply (z : F × Q) : e z = D z.1 + (z.2 : E) := by
    simp only [e, eRQ, eD, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.prodCongr_apply,
      Submodule.coe_prodEquivOfClosedCompl,
      Submodule.coe_prodEquivOfIsCompl']
    rfl
  have hj_apply (x : F) : j x = D x := by
    change e (x, 0) = D x
    simpa using he_apply (x, (0 : Q))
  let aug : F × Q → E := fun z ↦ f z.1 + (z.2 : E)
  have hfa : DifferentiableAt ℝ f a :=
    (hf.contDiffAt (hU.mem_nhds ha)).differentiableAt (by simp)
  have haug_deriv : HasFDerivAt aug (e : (F × Q) →L[ℝ] E) (a, 0) := by
    have hleft := hfa.hasFDerivAt.comp (a, (0 : Q))
      (ContinuousLinearMap.fst ℝ F Q).hasFDerivAt
    have hright : HasFDerivAt (fun z : F × Q ↦ (z.2 : E))
        (Q.subtypeL.comp (ContinuousLinearMap.snd ℝ F Q)) (a, 0) :=
      (Q.subtypeL.comp (ContinuousLinearMap.snd ℝ F Q)).hasFDerivAt
    convert hleft.add hright using 1
  let H : E → E := fun y ↦ aug (e.symm y)
  let b : E := j a
  have he_symm_b : e.symm b = (a, 0) := by
    change e.symm (e (a, 0)) = (a, 0)
    exact e.symm_apply_apply (a, 0)
  have hH_deriv : HasFDerivAt H (ContinuousLinearMap.id ℝ E) b := by
    have haug_deriv' : HasFDerivAt aug (e : (F × Q) →L[ℝ] E) (e.symm b) := by
      rw [he_symm_b]
      exact haug_deriv
    have hcomp := haug_deriv'.comp b e.symm.hasFDerivAt
    convert hcomp using 1
    ext y
    exact (e.apply_symm_apply y).symm
  let W₀ : Set E := e.symm ⁻¹' (U ×ˢ (Set.univ : Set Q))
  have hW₀open : IsOpen W₀ :=
    (hU.prod isOpen_univ).preimage e.symm.continuous
  have hbW₀ : b ∈ W₀ := by
    change e.symm b ∈ U ×ˢ (Set.univ : Set Q)
    rw [he_symm_b]
    exact ⟨ha, Set.mem_univ 0⟩
  have haug_smooth : ContDiffOn ℝ ∞ aug (U ×ˢ (Set.univ : Set Q)) := by
    exact (hf.comp contDiffOn_fst fun _ hz ↦ hz.1).add
      (Q.subtypeL.contDiff.comp contDiff_snd).contDiffOn
  have hH_smooth : ContDiffOn ℝ ∞ H W₀ := by
    exact haug_smooth.comp e.symm.contDiff.contDiffOn fun _ hy ↦ hy
  have hD_cont : ContinuousAt (fderiv ℝ H) b :=
    (hH_smooth.contDiffAt (hW₀open.mem_nhds hbW₀)).continuousAt_fderiv (by simp)
  have hInv_open : IsOpen {L : E →L[ℝ] E | L.IsInvertible} := by
    simpa only [ContinuousLinearMap.IsInvertible] using
      (ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := E) (F := E))
  have hInv_b : fderiv ℝ H b ∈ {L : E →L[ℝ] E | L.IsInvertible} := by
    rw [hH_deriv.fderiv]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  have hInv_nhds : (fderiv ℝ H) ⁻¹' {L : E →L[ℝ] E | L.IsInvertible} ∈ 𝓝 b :=
    hD_cont.preimage_mem_nhds (hInv_open.mem_nhds hInv_b)
  have hboth : W₀ ∩ (fderiv ℝ H) ⁻¹'
      {L : E →L[ℝ] E | L.IsInvertible} ∈ 𝓝 b :=
    Filter.inter_mem (hW₀open.mem_nhds hbW₀) hInv_nhds
  obtain ⟨W, hWsub, hWopen, hbW⟩ := mem_nhds_iff.mp hboth
  have hH_W : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ H W :=
    (hH_smooth.mono (hWsub.trans inter_subset_left)).contMDiffOn
  have hH_inv : ∀ y ∈ W,
      (fderiv ℝ (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, E) y H)
        (extChartAt 𝓘(ℝ, E) y y)).IsInvertible := by
    intro y hy
    have hyInv : (fderiv ℝ H y).IsInvertible := (hWsub hy).2
    simpa only [writtenInExtChartAt, extChartAt_self_eq, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq] using hyInv
  obtain ⟨Θ, hbΘ, hΘW, hΘeq⟩ :=
    Coordinates.hlocAt_infty' (I := 𝓘(ℝ, E)) (J := 𝓘(ℝ, E))
      hWopen hbW hH_W hH_inv
  let V : Set F := j ⁻¹' Θ.source
  have hVopen : IsOpen V := Θ.open_source.preimage j.continuous
  have haV : a ∈ V := hbΘ
  have hVsub : V ⊆ U := by
    intro x hx
    have hxW₀ : j x ∈ W₀ := (hWsub (hΘW hx)).1
    change e.symm (j x) ∈ U ×ˢ (Set.univ : Set Q) at hxW₀
    have hej : e.symm (j x) = (x, 0) := by
      change e.symm (e (x, 0)) = (x, 0)
      exact e.symm_apply_apply (x, 0)
    rw [hej] at hxW₀
    exact hxW₀.1
  have hHj (x : F) : H (j x) = f x := by
    change aug (e.symm (j x)) = f x
    change aug (e.symm (e (x, 0))) = f x
    rw [e.symm_apply_apply]
    change f x + (0 : E) = f x
    rw [add_zero]
  have hΘj (x : F) (hx : x ∈ V) : Θ (j x) = f x := by
    rw [← hHj x]
    exact (hΘeq hx).symm
  have hfinj : Set.InjOn f V := by
    intro x hx y hy hxy
    apply hinj
    rw [← hj_apply x, ← hj_apply y]
    apply Θ.toPartialEquiv.injOn hx hy
    rw [hΘj x hx, hΘj y hy, hxy]
  let A : AffineSubspace ℝ E := R.toAffineSubspace
  have hΘimage : Θ.toPartialEquiv.IsImage (A : Set E) (f '' V) := by
    intro x hxΘ
    constructor
    · rintro ⟨u, huV, hfu⟩
      change x ∈ R
      have hxu : x = j u := by
        apply Θ.toPartialEquiv.injOn hxΘ huV
        rw [hΘj u huV, hfu]
      rw [hxu, hj_apply]
      exact D.mem_range_self u
    · intro hxA
      change x ∈ R at hxA
      obtain ⟨u, hu⟩ := hxA
      have hjx : j u = x := by
        rw [hj_apply]
        exact hu
      have huV : u ∈ V := by
        change j u ∈ Θ.source
        rwa [hjx]
      exact ⟨u, huV, by rw [← hΘj u huV, hjx]⟩
  have hslice : IsEmbeddedSlice 𝓘(ℝ, E) (Module.finrank ℝ F) (f '' V) := by
    intro x hx
    obtain ⟨u, huV, rfl⟩ := hx
    refine ⟨Θ.symm, A, inferInstance, ?_, ?_, hΘimage.symm⟩
    · change f u ∈ Θ.target
      rw [← hΘj u huV]
      exact Θ.toPartialEquiv.map_source huV
    · rw [show A.direction = R by
        simp only [A, Submodule.toAffineSubspace_direction]]
      exact eD.finrank_eq.symm
  exact ⟨V, hVopen, haV, hVsub, hfinj, hslice⟩

end Geometry
end DifferentialGeometry
