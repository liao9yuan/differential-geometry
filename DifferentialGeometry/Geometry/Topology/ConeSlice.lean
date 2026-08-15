import DifferentialGeometry.Geometry.Topology.ImmersedSlice
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

open Set Topology
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace DifferentialGeometry
namespace Geometry

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

def coneDeriv (L : F →L[ℝ] E) (v : E) (t : ℝ) : F × ℝ →L[ℝ] E :=
  t • (L.comp (ContinuousLinearMap.fst ℝ F ℝ)) +
    (ContinuousLinearMap.snd ℝ F ℝ).smulRight v

theorem hasFDerivAt_cone {f : F → E} {L : F →L[ℝ] E} {a : F} {t : ℝ}
    (hf : HasFDerivAt f L a) :
    HasFDerivAt (fun z : F × ℝ ↦ z.2 • f z.1) (coneDeriv L (f a) t) (a, t) := by
  have hleft := hf.comp (a, t) (ContinuousLinearMap.fst ℝ F ℝ).hasFDerivAt
  have hright : HasFDerivAt (fun z : F × ℝ ↦ z.2)
      (ContinuousLinearMap.snd ℝ F ℝ) (a, t) :=
    (ContinuousLinearMap.snd ℝ F ℝ).hasFDerivAt
  convert hright.smul hleft using 1

theorem coneDeriv_injective {L : F →L[ℝ] E} {v : E} {t : ℝ}
    (hL : Function.Injective L) (ht : t ≠ 0) (htrans : v ∉ L.range) :
    Function.Injective (coneDeriv L v t) := by
  intro z w hzw
  have hzero : coneDeriv L v t (z - w) = 0 := by
    rw [map_sub, hzw, sub_self]
  have hker : ∀ y : F × ℝ, coneDeriv L v t y = 0 → y = 0 := by
    intro y hy
    have hy_formula : t • L y.1 + y.2 • v = 0 := by
      simpa only [coneDeriv, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smulRight_apply] using hy
    have hy2 : y.2 = 0 := by
      by_contra hy2
      have hscaled : y.2 • v ∈ L.range := by
        have heq : y.2 • v = -(t • L y.1) := by
          apply (eq_neg_iff_add_eq_zero).2
          simpa only [add_comm] using hy_formula
        rw [heq]
        exact L.range.neg_mem (L.range.smul_mem t (L.mem_range_self y.1))
      have hv_range : v ∈ L.range := by
        have hres := L.range.smul_mem y.2⁻¹ hscaled
        simpa only [smul_smul, inv_mul_cancel₀ hy2, one_smul] using hres
      exact htrans hv_range
    have hyL : L y.1 = 0 := by
      rw [hy2, zero_smul, add_zero] at hy_formula
      exact (smul_eq_zero.mp hy_formula).resolve_left ht
    have hy1 : y.1 = 0 := by
      apply hL
      simpa only [map_zero] using hyL
    exact Prod.ext hy1 hy2
  exact sub_eq_zero.mp (hker (z - w) hzero)

theorem radial_not_range {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] {f : F → G} {a : F}
    (hf : DifferentiableAt ℝ f a)
    (hmin : IsLocalMin (fun x ↦ ‖f x‖ ^ 2) a) (hfa : f a ≠ 0) :
    f a ∉ (fderiv ℝ f a).range := by
  intro hra
  obtain ⟨v, hv⟩ := hra
  have hzero : 2 • (innerSL ℝ (f a)).comp (fderiv ℝ f a) = 0 :=
    hmin.hasFDerivAt_eq_zero hf.hasFDerivAt.norm_sq
  have happ := congrArg (fun L : F →L[ℝ] ℝ ↦ L v) hzero
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, ContinuousLinearMap.zero_apply] at happ
  have heq : 2 • ⟪f a, (fderiv ℝ f a) v⟫_ℝ = 2 • ⟪f a, f a⟫_ℝ :=
    congrArg (fun z : G ↦ 2 • ⟪f a, z⟫_ℝ) hv
  have happ' : 2 • ⟪f a, f a⟫_ℝ = 0 := heq.symm.trans happ
  have hinner : ⟪f a, f a⟫_ℝ = 0 := by
    rw [two_smul] at happ'
    linarith
  exact hfa (inner_self_eq_zero.mp hinner)

omit [NormedSpace ℝ F] in
theorem radial_local_min {G Y : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [PseudoMetricSpace Y]
    {f : F → G} {B : G → Y} {U : Set F} {a : F} {q : Y} {S : Set Y}
    (hU : U ∈ 𝓝 a) (hmap : Set.MapsTo (fun x ↦ B (f x)) U S)
    (hmin : IsMinOn (fun y ↦ dist q y) S (B (f a)))
    (hrad : ∀ x ∈ U, dist q (B (f x)) = ‖f x‖) :
    IsLocalMin (fun x ↦ ‖f x‖ ^ 2) a := by
  apply (show IsMinOn (fun x ↦ ‖f x‖ ^ 2) U a from ?_).isLocalMin hU
  intro x hx
  change ‖f a‖ ^ 2 ≤ ‖f x‖ ^ 2
  rw [sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [← hrad a (mem_of_mem_nhds hU), ← hrad x hx]
  exact hmin (hmap hx)

theorem exists_cone_slice [CompleteSpace E] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F]
    {f : F → E} {U : Set F} {a : F} {J : Set ℝ} {t₀ : ℝ}
    (hU : IsOpen U) (ha : a ∈ U) (hJ : IsOpen J) (htJ : t₀ ∈ J)
    (hf : ContDiffOn ℝ ∞ f U)
    (hinj : Function.Injective (fderiv ℝ f a)) (ht₀ : t₀ ≠ 0)
    (htrans : f a ∉ (fderiv ℝ f a).range) :
    let cone : F × ℝ → E := fun z ↦ z.2 • f z.1
    ∃ V : Set (F × ℝ), IsOpen V ∧ (a, t₀) ∈ V ∧ V ⊆ U ×ˢ J ∧
      Set.InjOn cone V ∧
        IsEmbeddedSlice 𝓘(ℝ, E) (Module.finrank ℝ F + 1) (cone '' V) := by
  let cone : F × ℝ → E := fun z ↦ z.2 • f z.1
  let D : F →L[ℝ] E := fderiv ℝ f a
  have hfa : DifferentiableAt ℝ f a :=
    (hf.contDiffAt (hU.mem_nhds ha)).differentiableAt (by simp)
  have hcone_deriv : HasFDerivAt cone (coneDeriv D (f a) t₀) (a, t₀) :=
    hasFDerivAt_cone hfa.hasFDerivAt
  have hcone_inj : Function.Injective (fderiv ℝ cone (a, t₀)) := by
    rw [hcone_deriv.fderiv]
    exact coneDeriv_injective hinj ht₀ htrans
  have hcone_smooth : ContDiffOn ℝ ∞ cone (U ×ˢ J) := by
    exact contDiffOn_snd.smul (hf.comp contDiffOn_fst fun _ hz ↦ hz.1)
  obtain ⟨V, hVopen, hbaseV, hVsub, hVin, hslice⟩ :=
    exists_slice_image (E := E) (F := F × ℝ) (f := cone)
      (U := U ×ˢ J) (a := (a, t₀)) (hU.prod hJ) ⟨ha, htJ⟩
      hcone_smooth hcone_inj
  refine ⟨V, hVopen, hbaseV, hVsub, hVin, ?_⟩
  simpa only [Module.finrank_prod, Module.finrank_self, add_comm] using hslice

theorem exists_cone_image [CompleteSpace E] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {f : F → E} {U : Set F} {a : F} {J : Set ℝ} {t₀ : ℝ}
    (B : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (hU : IsOpen U) (ha : a ∈ U) (hJ : IsOpen J) (htJ : t₀ ∈ J)
    (hf : ContDiffOn ℝ ∞ f U)
    (hinj : Function.Injective (fderiv ℝ f a)) (ht₀ : t₀ ≠ 0)
    (htrans : f a ∉ (fderiv ℝ f a).range)
    (hbase : t₀ • f a ∈ B.source) :
    let cone : F × ℝ → E := fun z ↦ z.2 • f z.1
    ∃ V : Set (F × ℝ), IsOpen V ∧ (a, t₀) ∈ V ∧ V ⊆ U ×ˢ J ∧
      cone '' V ⊆ B.source ∧
        IsEmbeddedSlice I (Module.finrank ℝ F + 1) (B '' (cone '' V)) := by
  let cone : F × ℝ → E := fun z ↦ z.2 • f z.1
  let D : F →L[ℝ] E := fderiv ℝ f a
  have hfa : DifferentiableAt ℝ f a :=
    (hf.contDiffAt (hU.mem_nhds ha)).differentiableAt (by simp)
  have hcone_deriv : HasFDerivAt cone (coneDeriv D (f a) t₀) (a, t₀) :=
    hasFDerivAt_cone hfa.hasFDerivAt
  have hcone_inj : Function.Injective (fderiv ℝ cone (a, t₀)) := by
    rw [hcone_deriv.fderiv]
    exact coneDeriv_injective hinj ht₀ htrans
  have hcone_smooth : ContDiffOn ℝ ∞ cone (U ×ˢ J) := by
    exact contDiffOn_snd.smul (hf.comp contDiffOn_fst fun _ hz ↦ hz.1)
  let W : Set (F × ℝ) := (U ×ˢ J) ∩ cone ⁻¹' B.source
  have hWopen : IsOpen W :=
    hcone_smooth.continuousOn.isOpen_inter_preimage (hU.prod hJ) B.open_source
  have hbaseW : (a, t₀) ∈ W := ⟨⟨ha, htJ⟩, hbase⟩
  obtain ⟨V, hVopen, hbaseV, hVsub, _, hslice⟩ :=
    exists_slice_image (E := E) (F := F × ℝ) (f := cone)
      (U := W) (a := (a, t₀)) hWopen hbaseW
      (hcone_smooth.mono inter_subset_left) hcone_inj
  have hVprod : V ⊆ U ×ˢ J := hVsub.trans inter_subset_left
  have hVsource : cone '' V ⊆ B.source := by
    rintro _ ⟨z, hzV, rfl⟩
    exact (hVsub hzV).2
  refine ⟨V, hVopen, hbaseV, hVprod, hVsource, ?_⟩
  have hslice' := hslice.image B hVsource
  simpa only [Module.finrank_prod, Module.finrank_self, add_comm] using hslice'

end Geometry
end DifferentialGeometry
