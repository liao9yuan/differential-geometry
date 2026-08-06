import DifferentialGeometry.Tensor.Alternating.Bundle
import DifferentialGeometry.Tensor.Alternating.Wedge
import DifferentialGeometry.Tensor.Exterior.Model
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

noncomputable section

open Bundle Set ContinuousAlternatingMap Function Filter
open scoped Topology Manifold ContDiff Bundle

namespace DifferentialGeometry

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  (IM : ModelWithCorners ℝ EM HM)
  (M : Type*) [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ⊤ M]
  (k : ℕ)

structure DifferentialForm where
  toFun : (x : M) →
    Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ) x
  contMDiff_toFun : ContMDiff IM (IM.prod 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ)) ⊤
    (fun x => TotalSpace.mk' (EM [⋀^Fin k]→L[ℝ] ℝ) x (toFun x))

namespace DifferentialForm

variable {IM M k}

instance : CoeFun (DifferentialForm IM M k) (fun _ => (x : M) →
    Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ) x) where
  coe := DifferentialForm.toFun

instance fiberNeg (x : M) : Neg
    (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ) x) := by
  dsimp [Bundle.continuousAlternatingMap]
  exact inferInstance

instance fiberSub (x : M) : Sub
    (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ) x) := by
  dsimp [Bundle.continuousAlternatingMap]
  exact inferInstance

instance fiberZSMul (x : M) : SMul ℤ
    (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ) x) := by
  dsimp [Bundle.continuousAlternatingMap]
  exact inferInstance

set_option backward.isDefEq.respectTransparency false in
@[instance_reducible]
private def seminormedAddCommGroupTangentSpace (x : M) : SeminormedAddCommGroup (TangentSpace IM x) :=
  inferInstanceAs (SeminormedAddCommGroup EM)

attribute [local instance] seminormedAddCommGroupTangentSpace

set_option backward.isDefEq.respectTransparency false in
@[instance_reducible]
private def normedAddCommGroupTangentSpace (x : M) : NormedAddCommGroup (TangentSpace IM x) :=
  inferInstanceAs (NormedAddCommGroup EM)

attribute [local instance] normedAddCommGroupTangentSpace

set_option backward.isDefEq.respectTransparency false in
@[instance_reducible]
private def normedSpaceTangentSpace (x : M) : NormedSpace ℝ (TangentSpace IM x) :=
  inferInstanceAs (NormedSpace ℝ EM)

attribute [local instance] normedSpaceTangentSpace

@[ext]
theorem ext {α β : DifferentialForm IM M k} (h : ∀ x, α x = β x) : α = β := by
  cases α
  cases β
  congr
  funext x
  exact h x

private lemma contMDiff_add_section {s t : (x : M) →
    Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ) x}
    (hs : ContMDiff IM (IM.prod 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ)) ⊤
      (fun x => TotalSpace.mk' (EM [⋀^Fin k]→L[ℝ] ℝ) x (s x)))
    (ht : ContMDiff IM (IM.prod 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ)) ⊤
      (fun x => TotalSpace.mk' (EM [⋀^Fin k]→L[ℝ] ℝ) x (t x))) :
    ContMDiff IM (IM.prod 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ)) ⊤
      (fun x => TotalSpace.mk' (EM [⋀^Fin k]→L[ℝ] ℝ) x (s x + t x)) := by
  intro x₀
  let e := trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀
  rw [Bundle.Trivialization.contMDiffAt_section_iff e
    (mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀)]
  have hs' : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ) ⊤ (fun x => (e ⟨x, s x⟩).2) x₀ := by
    exact (Bundle.Trivialization.contMDiffAt_section_iff e
      (mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀)).mp
      (hs x₀)
  have ht' : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ) ⊤ (fun x => (e ⟨x, t x⟩).2) x₀ := by
    exact (Bundle.Trivialization.contMDiffAt_section_iff e
      (mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀)).mp
      (ht x₀)
  refine (hs'.add ht').congr_of_eventuallyEq ?_
  exact eventually_of_mem (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀))
    (fun x hx => (e.linear ℝ hx).map_add (s x) (t x))

private lemma contMDiff_smul_section (c : ℝ) {s : (x : M) →
    Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ) x}
    (hs : ContMDiff IM (IM.prod 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ)) ⊤
      (fun x => TotalSpace.mk' (EM [⋀^Fin k]→L[ℝ] ℝ) x (s x))) :
    ContMDiff IM (IM.prod 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ)) ⊤
      (fun x => TotalSpace.mk' (EM [⋀^Fin k]→L[ℝ] ℝ) x (c • s x)) := by
  intro x₀
  let e := trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀
  rw [Bundle.Trivialization.contMDiffAt_section_iff e
    (mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀)]
  have hs' : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ) ⊤ (fun x => (e ⟨x, s x⟩).2) x₀ := by
    exact (Bundle.Trivialization.contMDiffAt_section_iff e
      (mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀)).mp
      (hs x₀)
  refine ((contMDiffAt_const : ContMDiffAt IM 𝓘(ℝ, ℝ) ⊤ (fun _ : M => c) x₀).smul hs').congr_of_eventuallyEq ?_
  exact eventually_of_mem (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀))
    (fun x hx => (e.linear ℝ hx).map_smul c (s x))

private lemma contMDiff_zero_section :
    ContMDiff IM (IM.prod 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ)) ⊤
      (fun x => TotalSpace.mk' (EM [⋀^Fin k]→L[ℝ] ℝ) x (0 : Bundle.continuousAlternatingMap ℝ (Fin k) EM
        (TangentSpace IM) ℝ (Bundle.Trivial M ℝ) x)) := by
  intro x₀
  let e := trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀
  rw [Bundle.Trivialization.contMDiffAt_section_iff e
    (mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀)]
  refine (contMDiffAt_const (c := (0 : EM [⋀^Fin k]→L[ℝ] ℝ))).congr_of_eventuallyEq ?_
  exact eventually_of_mem (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀))
    (fun x hx => (e.linear ℝ hx).map_zero)


instance instZero : Zero (DifferentialForm IM M k) :=
  ⟨⟨fun _ => 0, contMDiff_zero_section (IM := IM) (M := M) (k := k)⟩⟩

instance instAdd : Add (DifferentialForm IM M k) :=
  ⟨fun α β => ⟨fun x => α x + β x,
    contMDiff_add_section (IM := IM) (M := M) (k := k) α.contMDiff_toFun β.contMDiff_toFun⟩⟩

instance instNeg : Neg (DifferentialForm IM M k) :=
  ⟨fun α => ⟨fun x => (-1 : ℝ) • α x,
    contMDiff_smul_section (IM := IM) (M := M) (k := k) (-1 : ℝ) α.contMDiff_toFun⟩⟩

instance instSub : Sub (DifferentialForm IM M k) :=
  ⟨fun α β => ⟨fun x => α x + (-1 : ℝ) • β x,
    contMDiff_add_section (IM := IM) (M := M) (k := k) α.contMDiff_toFun
      (contMDiff_smul_section (IM := IM) (M := M) (k := k) (-1 : ℝ) β.contMDiff_toFun)⟩⟩

instance instSMul : SMul ℝ (DifferentialForm IM M k) :=
  ⟨fun c α => ⟨fun x => c • α x,
    contMDiff_smul_section (IM := IM) (M := M) (k := k) c α.contMDiff_toFun⟩⟩

@[simp] theorem zero_apply (x : M) : (0 : DifferentialForm IM M k) x = 0 := rfl
@[simp] theorem add_apply (α β : DifferentialForm IM M k) (x : M) : (α + β) x = α x + β x := rfl
@[simp] theorem neg_apply (α : DifferentialForm IM M k) (x : M) : (-α) x = (-1 : ℝ) • α x := rfl
@[simp] theorem sub_apply (α β : DifferentialForm IM M k) (x : M) : (α - β) x = α x + (-1 : ℝ) • β x := rfl
@[simp] theorem smul_apply (c : ℝ) (α : DifferentialForm IM M k) (x : M) : (c • α) x = c • α x := rfl

instance instAddCommGroup : AddCommGroup (DifferentialForm IM M k) :=
  { zero := 0
    add := (· + ·)
    neg := Neg.neg
    sub := Sub.sub
    nsmul := fun n α => ⟨fun x => (n : ℝ) • α x,
      contMDiff_smul_section (IM := IM) (M := M) (k := k) (n : ℝ) α.contMDiff_toFun⟩
    zsmul := fun z α => ⟨fun x => (z : ℝ) • α x,
      contMDiff_smul_section (IM := IM) (M := M) (k := k) (z : ℝ) α.contMDiff_toFun⟩
    add_assoc := by intro a b c; ext x; simp [add_assoc]
    zero_add := by intro a; ext x; simp
    add_zero := by intro a; ext x; simp
    nsmul_zero := by intro a; ext x; simp
    nsmul_succ := by intro n a; ext x; simp [Nat.cast_succ, add_smul]
    add_comm := by intro a b; ext x; simp [add_comm]
    neg_add_cancel := by
      intro a
      ext x
      simp only [add_apply, neg_apply, zero_apply]
      nth_rw 2 [show a x = (1 : ℝ) • a x from (one_smul ℝ (a x)).symm]
      rw [← add_smul]
      norm_num
    sub_eq_add_neg := by intro a b; ext x; rfl
    zsmul_zero' := by intro a; ext x; simp
    zsmul_succ' := by intro n a; ext x; simp [Nat.cast_succ, add_smul]
    zsmul_neg' := by
      intro n a
      ext x
      simp [Int.negSucc_eq, Nat.cast_succ, smul_smul] }

instance instModule : Module ℝ (DifferentialForm IM M k) :=
  { smul := (· • ·)
    smul_zero := by intro c; ext x; simp
    zero_smul := by intro a; ext x; simp
    smul_add := by intro c a b; ext x; simp [smul_add]
    add_smul := by intro c d a; ext x; simp [add_smul]
    mul_smul := by intro c d a; ext x; simp [mul_smul]
    one_smul := by intro a; ext x; simp }

private lemma altTriv_apply (m : ℕ) (x₀ x : M)
    (L : Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ) x) :
    (trivializationAt (EM [⋀^Fin m]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀ ⟨x, L⟩).2 =
      L.compContinuousLinearMap ((trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x) := by
  change (Pretrivialization.continuousAlternatingMap ℝ (Fin m)
      (trivializationAt EM (TangentSpace IM) x₀) (trivializationAt ℝ (Bundle.Trivial M ℝ) x₀)
      ⟨x, L⟩).2 = L.compContinuousLinearMap ((trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x)
  rw [Pretrivialization.continuousAlternatingMap_apply]
  ext v
  simp

noncomputable def wedge {k l : ℕ} (α : DifferentialForm IM M k)
    (β : DifferentialForm IM M l) : DifferentialForm IM M (k + l) :=
  ⟨fun x => ContinuousAlternatingMap.wedge_product (α x) (β x) (ContinuousLinearMap.mul ℝ ℝ), by
    intro x₀
    let e := trivializationAt (EM [⋀^Fin (k + l)]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin (k + l)) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x₀
    rw [Bundle.Trivialization.contMDiffAt_section_iff e
      (mem_baseSet_trivializationAt (EM [⋀^Fin (k + l)]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin (k + l)) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀)]
    have hα : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ) ⊤ (fun x =>
        (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀ ⟨x, α x⟩).2) x₀ := by
      exact (Bundle.Trivialization.contMDiffAt_section_iff
        (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀)
        (mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀)).mp (α.contMDiff_toFun x₀)
    have hβ : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin l]→L[ℝ] ℝ) ⊤ (fun x =>
        (trivializationAt (EM [⋀^Fin l]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀ ⟨x, β x⟩).2) x₀ := by
      exact (Bundle.Trivialization.contMDiffAt_section_iff
        (trivializationAt (EM [⋀^Fin l]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀)
        (mem_baseSet_trivializationAt (EM [⋀^Fin l]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀)).mp (β.contMDiff_toFun x₀)
    let W : (EM [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (EM [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ]
        (EM [⋀^Fin (k + l)]→L[ℝ] ℝ) :=
      wedge_productL (ContinuousLinearMap.mul ℝ ℝ)
    have hW : ContMDiffAt IM 𝓘(ℝ, (EM [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (EM [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ]
        (EM [⋀^Fin (k + l)]→L[ℝ] ℝ)) ⊤ (fun _ : M => W) x₀ :=
      contMDiffAt_const
    refine ((hW.clm_apply hα).clm_apply hβ).congr_of_eventuallyEq ?_
    exact eventually_of_mem (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt
        (EM [⋀^Fin (k + l)]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin (k + l)) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀))
      (fun x hx => by
        change ((trivializationAt (EM [⋀^Fin (k + l)]→L[ℝ] ℝ)
            (Bundle.continuousAlternatingMap ℝ (Fin (k + l)) EM (TangentSpace IM) ℝ
              (Bundle.Trivial M ℝ)) x₀)
            ⟨x, ContinuousAlternatingMap.wedge_product (α x) (β x) (ContinuousLinearMap.mul ℝ ℝ)⟩).2 =
          W ((trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
              (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
                (Bundle.Trivial M ℝ)) x₀) ⟨x, α x⟩).2
            ((trivializationAt (EM [⋀^Fin l]→L[ℝ] ℝ)
              (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
                (Bundle.Trivial M ℝ)) x₀) ⟨x, β x⟩).2
        rw [altTriv_apply (m := k + l) (IM := IM) (M := M) (x₀ := x₀) (x := x)
          (L := ContinuousAlternatingMap.wedge_product (α x) (β x) (ContinuousLinearMap.mul ℝ ℝ)),
          altTriv_apply (m := k) (IM := IM) (M := M) (x₀ := x₀) (x := x) (L := α x),
          altTriv_apply (m := l) (IM := IM) (M := M) (x₀ := x₀) (x := x) (L := β x)]
        rw [show W ((α x).compContinuousLinearMap ((trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x))
              ((β x).compContinuousLinearMap ((trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x)) =
              ContinuousAlternatingMap.wedge_product ((α x).compContinuousLinearMap
                ((trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x))
                ((β x).compContinuousLinearMap ((trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x))
                (ContinuousLinearMap.mul ℝ ℝ) from by
          simp [W, wedge_productL_apply]]
        exact (DifferentialGeometry.DifferentialForm.wedge_product_compContinuousLinearMap
          (E := TangentSpace IM x) (E' := TangentSpace IM x)
          (g := α x) (h := β x) (A := (trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x)))⟩

notation α " ∧ " β => DifferentialForm.wedge α β

end DifferentialForm

end DifferentialGeometry

end
