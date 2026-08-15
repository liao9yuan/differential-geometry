import DifferentialGeometry.Geometry.Coordinates.ChartRegistration
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Nat.Lattice
import Mathlib.Topology.LocallyClosed

open Set Topology
open scoped ContDiff Manifold Set.Notation

noncomputable section

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def IsEmbeddedSlice (I : ModelWithCorners ℝ E H) (d : ℕ) (N : Set M) : Prop :=
  ∀ x ∈ N,
    ∃ (Φ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
      (A : AffineSubspace ℝ E),
      FiniteDimensional ℝ A.direction ∧
        x ∈ Φ.source ∧
        Module.finrank ℝ A.direction = d ∧
        Φ.toPartialEquiv.IsImage N (A : Set E)

def sliceDims (I : ModelWithCorners ℝ E H) (C : Set M) : Set ℕ :=
  {d | ∃ N : Set M, N.Nonempty ∧ N ⊆ C ∧ IsEmbeddedSlice I d N}

noncomputable def maxSliceDim (I : ModelWithCorners ℝ E H) (C : Set M) : ℕ :=
  sSup (sliceDims I C)

def maxSliceLocus (I : ModelWithCorners ℝ E H) (C : Set M) : Set M :=
  {x | ∃ N : Set M, x ∈ N ∧ N ⊆ C ∧ IsEmbeddedSlice I (maxSliceDim I C) N}

private noncomputable def extChartPD [I.Boundaryless] [IsManifold I ∞ M]
    (x : M) : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by
    simpa only [extChartAt_source] using
      (contMDiffOn_extChartAt (I := I) (x := x))
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

namespace IsEmbeddedSlice

theorem of_affine_subspace (A : AffineSubspace ℝ E)
    [FiniteDimensional ℝ A.direction] :
    IsEmbeddedSlice 𝓘(ℝ, E) (Module.finrank ℝ A.direction) (A : Set E) := by
  intro x hx
  let Φ := (Diffeomorph.refl 𝓘(ℝ, E) E ∞).toPartialDiffeomorph
  refine ⟨Φ, A, inferInstance, ?_, rfl, ?_⟩
  · exact Set.mem_univ x
  · intro y _
    change (y ∈ (A : Set E) ↔ y ∈ (A : Set E))
    exact Iff.rfl

theorem singleton [I.Boundaryless] [IsManifold I ∞ M] (x : M) :
    IsEmbeddedSlice I 0 ({x} : Set M) := by
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst y
  let Φ := extChartPD (I := I) x
  let A := AffineSubspace.mk' (Φ x) (⊥ : Submodule ℝ E)
  have hxΦ : x ∈ Φ.source := mem_extChartAt_source x
  have hAfin : FiniteDimensional ℝ A.direction := by
    dsimp only [A]
    rw [AffineSubspace.direction_mk']
    infer_instance
  refine ⟨Φ, A, hAfin, hxΦ, ?_, ?_⟩
  · rw [AffineSubspace.direction_mk', finrank_bot]
  · intro y hy
    change Φ y ∈ AffineSubspace.mk' (Φ x) (⊥ : Submodule ℝ E) ↔
      y ∈ ({x} : Set M)
    rw [AffineSubspace.mem_mk', Submodule.mem_bot, vsub_eq_zero_iff_eq,
      Set.mem_singleton_iff]
    exact ⟨fun h ↦ Φ.toPartialEquiv.injOn hy hxΦ h, fun h ↦ congrArg Φ h⟩

theorem dim_le [FiniteDimensional ℝ E] {N : Set M} {d : ℕ}
    (hN : IsEmbeddedSlice I d N) (hne : N.Nonempty) :
    d ≤ Module.finrank ℝ E := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨_, A, hAfin, _, hdim, _⟩ := hN x hx
  letI : FiniteDimensional ℝ A.direction := hAfin
  rw [← hdim]
  exact A.direction.finrank_le

theorem image
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {S : Set M} {d : ℕ} (hS : IsEmbeddedSlice I d S)
    (Φ : PartialDiffeomorph I J M N ∞) (hsub : S ⊆ Φ.source) :
    IsEmbeddedSlice J d (Φ '' S) := by
  intro y hy
  obtain ⟨x, hxS, rfl⟩ := hy
  obtain ⟨c, A, hAfin, hxc, hdim, himage⟩ := hS x hxS
  have hxΦ : x ∈ Φ.source := hsub hxS
  let Ψ : PartialDiffeomorph J 𝓘(ℝ, E) N E ∞ :=
    { toPartialEquiv := Φ.symm.toPartialEquiv.trans c.toPartialEquiv
      open_source := by
        have hsrc : (Φ.symm.toPartialEquiv.trans c.toPartialEquiv).source =
            Φ.target ∩ (Φ.symm : N → M) ⁻¹' c.source := rfl
        rw [hsrc]
        exact Φ.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
          Φ.open_target c.open_source
      open_target := by
        have htgt : (Φ.symm.toPartialEquiv.trans c.toPartialEquiv).target =
            c.target ∩ (c.symm : E → M) ⁻¹' Φ.source := by
          rw [PartialEquiv.trans_target]
          rfl
        rw [htgt]
        exact c.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
          c.open_target Φ.open_source
      contMDiffOn_toFun := by
        have hsrc : (Φ.symm.toPartialEquiv.trans c.toPartialEquiv).source =
            Φ.target ∩ (Φ.symm : N → M) ⁻¹' c.source := rfl
        rw [hsrc]
        exact c.contMDiffOn_toFun.comp
          (Φ.symm.contMDiffOn_toFun.mono inter_subset_left) (fun _ hz ↦ hz.2)
      contMDiffOn_invFun := by
        have htgt : (Φ.symm.toPartialEquiv.trans c.toPartialEquiv).target =
            c.target ∩ (c.symm : E → M) ⁻¹' Φ.source := by
          rw [PartialEquiv.trans_target]
          rfl
        rw [htgt]
        exact Φ.contMDiffOn_toFun.comp
          (c.symm.contMDiffOn_toFun.mono inter_subset_left) (fun _ hz ↦ hz.2) }
  refine ⟨Ψ, A, hAfin, ?_, hdim, ?_⟩
  · change Φ x ∈ Φ.target ∩ (Φ.symm : N → M) ⁻¹' c.source
    refine ⟨Φ.toPartialEquiv.map_source hxΦ, ?_⟩
    change Φ.toPartialEquiv.symm (Φ.toPartialEquiv x) ∈ c.source
    rw [Φ.toPartialEquiv.left_inv hxΦ]
    exact hxc
  · intro z hz
    have hzΦ : z ∈ Φ.target := hz.1
    have hzc : (Φ.symm : N → M) z ∈ c.source := hz.2
    change c ((Φ.symm : N → M) z) ∈ A ↔ z ∈ Φ '' S
    constructor
    · intro hzA
      have hzS := (himage.apply_mem_iff hzc).1 hzA
      exact ⟨(Φ.symm : N → M) z, hzS, Φ.toPartialEquiv.right_inv hzΦ⟩
    · rintro ⟨u, huS, rfl⟩
      apply (himage.apply_mem_iff hzc).2
      change Φ.toPartialEquiv.symm (Φ.toPartialEquiv u) ∈ S
      rw [Φ.toPartialEquiv.left_inv (hsub huS)]
      exact huS

theorem image_smul {S : Set E} {d : ℕ}
    (hS : IsEmbeddedSlice 𝓘(ℝ, E) d S) {t : ℝ} (ht : t ≠ 0) :
    IsEmbeddedSlice 𝓘(ℝ, E) d ((fun x : E ↦ t • x) '' S) := by
  let e : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 t ht)
  have hsub : S ⊆ e.toDiffeomorph.toPartialDiffeomorph.source := by
    intro x _
    exact Set.mem_univ x
  simpa only [e, ContinuousLinearEquiv.coe_toDiffeomorph,
    ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def] using
      hS.image e.toDiffeomorph.toPartialDiffeomorph hsub

theorem inter_open {S U : Set M} {d : ℕ}
    (hS : IsEmbeddedSlice I d S) (hU : IsOpen U) :
    IsEmbeddedSlice I d (S ∩ U) := by
  rintro x ⟨hxS, hxU⟩
  obtain ⟨c, A, hAfin, hxc, hdim, himage⟩ := hS x hxS
  let e := c.toOpenPartialHomeomorph
  let s := c.source ∩ U
  have hs : IsOpen s := c.open_source.inter hU
  have hse : s ⊆ e.source := inter_subset_left
  let Φ :=
    DifferentialGeometry.Tensor.Coordinates.PartialDiffeomorph.ofOpenPartialHomeomorphRestr
      e s hs hse (c.contMDiffOn_toFun.mono inter_subset_left)
        (c.contMDiffOn_invFun.mono (by
          rintro y ⟨z, hz, rfl⟩
          exact c.map_source' hz.1))
  refine ⟨Φ, A, hAfin, ⟨hxc, hxU⟩, hdim, ?_⟩
  intro y hy
  change c y ∈ A ↔ y ∈ S ∩ U
  constructor
  · intro hyA
    exact ⟨(himage.apply_mem_iff hy.1).1 hyA, hy.2⟩
  · intro hySU
    exact (himage.apply_mem_iff hy.1).2 hySU.1

theorem image_inter
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {S : Set M} {d : ℕ} (hS : IsEmbeddedSlice I d S)
    (Φ : PartialDiffeomorph I J M N ∞) :
    IsEmbeddedSlice J d (Φ '' (S ∩ Φ.source)) :=
  (hS.inter_open Φ.open_source).image Φ inter_subset_right

theorem exists_param {S : Set E} {d : ℕ}
    (hS : IsEmbeddedSlice 𝓘(ℝ, E) d S) {x : E} (hx : x ∈ S) :
    ∃ (L : Submodule ℝ E) (U : Set L) (f : L → E) (W : Set E),
      FiniteDimensional ℝ L ∧ Module.finrank ℝ L = d ∧
        IsOpen U ∧ (0 : L) ∈ U ∧ ContDiffOn ℝ ∞ f U ∧
        Function.Injective (fderiv ℝ f 0) ∧ f 0 = x ∧
        IsOpen W ∧ x ∈ W ∧ f '' U = W ∩ S := by
  obtain ⟨c, A, hAfin, hxc, hdim, himage⟩ := hS x hx
  let L : Submodule ℝ E := A.direction
  letI : FiniteDimensional ℝ L := hAfin
  have hcxA : c x ∈ A := (himage.apply_mem_iff hxc).2 hx
  let affine : L → E := fun v ↦ (v : E) + c x
  let U : Set L := affine ⁻¹' c.target
  let f : L → E := fun v ↦ c.symm (affine v)
  have haffine_cont : Continuous affine :=
    L.subtypeL.continuous.add continuous_const
  have hUopen : IsOpen U := c.open_target.preimage haffine_cont
  have hcx_target : c x ∈ c.target := c.toPartialEquiv.map_source hxc
  have hzeroU : (0 : L) ∈ U := by
    change (0 : E) + c x ∈ c.target
    simpa only [zero_add] using hcx_target
  have haffine_smooth : ContDiff ℝ ∞ affine :=
    L.subtypeL.contDiff.add contDiff_const
  have hf_smooth : ContDiffOn ℝ ∞ f U := by
    exact c.symm.contMDiffOn_toFun.contDiffOn.comp haffine_smooth.contDiffOn
      (fun _ hv ↦ hv)
  have hc_local : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (c.symm : E → E) (c x) :=
    c.symm.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ hcx_target
  have hc_inj : Function.Injective (fderiv ℝ (c.symm : E → E) (c x)) := by
    rw [← mfderiv_eq_fderiv]
    exact (hc_local.mfderivToContinuousLinearEquiv (by simp)).injective
  have haffine_deriv : HasFDerivAt affine L.subtypeL 0 :=
    L.subtypeL.hasFDerivAt.add_const (c x)
  have hc_diff : DifferentiableAt ℝ (c.symm : E → E) (c x) :=
    hc_local.mdifferentiableAt (by simp) |>.differentiableAt
  have hf_deriv : HasFDerivAt f
      ((fderiv ℝ (c.symm : E → E) (c x)).comp L.subtypeL) 0 := by
    have hc_at_affine : HasFDerivAt (c.symm : E → E)
        (fderiv ℝ (c.symm : E → E) (c x)) (affine 0) := by
      have haffine_zero : affine 0 = c x := by
        change ((0 : L) : E) + c x = c x
        rw [Submodule.coe_zero, zero_add]
      rw [haffine_zero]
      exact hc_diff.hasFDerivAt
    exact hc_at_affine.comp 0 haffine_deriv
  have hf_inj : Function.Injective (fderiv ℝ f 0) := by
    rw [hf_deriv.fderiv]
    exact hc_inj.comp (Submodule.subtype_injective L)
  have hf_zero : f 0 = x := by
    change c.symm ((0 : E) + c x) = x
    rw [zero_add]
    exact c.toPartialEquiv.left_inv hxc
  have hf_image : f '' U = c.source ∩ S := by
    apply Set.Subset.antisymm
    · rintro _ ⟨v, hvU, rfl⟩
      have hfv_source : c.symm (affine v) ∈ c.source :=
        c.symm.toPartialEquiv.map_source hvU
      refine ⟨hfv_source, ?_⟩
      apply (himage.apply_mem_iff hfv_source).1
      change c.toPartialEquiv (c.toPartialEquiv.symm (affine v)) ∈ A
      rw [c.toPartialEquiv.right_inv hvU]
      change (v : E) + c x ∈ A
      simpa only [vadd_eq_add] using
        A.vadd_mem_of_mem_direction v.property hcxA
    · rintro y ⟨hyc, hyS⟩
      have hcyA : c y ∈ A := (himage.apply_mem_iff hyc).2 hyS
      let v : L := ⟨c y - c x, by
        change c y - c x ∈ A.direction
        simpa only [vsub_eq_sub] using
          A.vsub_mem_direction hcyA hcxA⟩
      have haffine_v : affine v = c y := by
        change (c y - c x) + c x = c y
        exact sub_add_cancel (c y) (c x)
      have hvU : v ∈ U := by
        change affine v ∈ c.target
        rw [haffine_v]
        exact c.toPartialEquiv.map_source hyc
      refine ⟨v, hvU, ?_⟩
      change c.toPartialEquiv.symm (affine v) = y
      rw [haffine_v]
      exact c.toPartialEquiv.left_inv hyc
  exact ⟨L, U, f, c.source, inferInstance, hdim, hUopen, hzeroU,
    hf_smooth, hf_inj, hf_zero, c.open_source, hxc, hf_image⟩

theorem of_is_open [I.Boundaryless] [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] {N : Set M} (hN : IsOpen N) :
    IsEmbeddedSlice I (Module.finrank ℝ E) N := by
  intro x hx
  let c := extChartPD (I := I) x
  let e := c.toOpenPartialHomeomorph
  let s := e.source ∩ N
  have hs : IsOpen s := c.open_source.inter hN
  have hse : s ⊆ e.source := inter_subset_left
  let Φ :=
    DifferentialGeometry.Tensor.Coordinates.PartialDiffeomorph.ofOpenPartialHomeomorphRestr
      e s hs hse (c.contMDiffOn_toFun.mono inter_subset_left)
        (c.contMDiffOn_invFun.mono (by
          rintro y ⟨z, hz, rfl⟩
          exact c.map_source' hz.1))
  refine ⟨Φ, ⊤, inferInstance, ?_, ?_, ?_⟩
  · exact ⟨mem_extChartAt_source x, hx⟩
  · rw [AffineSubspace.direction_top, finrank_top]
  · intro y hy
    change ((Φ : M → E) y ∈ (⊤ : AffineSubspace ℝ E) ↔ y ∈ N)
    constructor
    · intro _
      exact hy.2
    · intro _
      exact AffineSubspace.mem_top ℝ E (Φ y)

theorem of_germ {S : Set M} {d : ℕ}
    (h : ∀ x ∈ S,
      ∃ (N U : Set M), IsEmbeddedSlice I d N ∧ IsOpen U ∧
        x ∈ U ∧ x ∈ N ∧ U ∩ S = U ∩ N) :
    IsEmbeddedSlice I d S := by
  intro x hxS
  obtain ⟨N, U, hN, hU, hxU, hxN, heq⟩ := h x hxS
  obtain ⟨c, A, hAfin, hxc, hdim, himage⟩ := hN x hxN
  let e := c.toOpenPartialHomeomorph
  let s := c.source ∩ U
  have hs : IsOpen s := c.open_source.inter hU
  have hse : s ⊆ e.source := inter_subset_left
  let Φ :=
    DifferentialGeometry.Tensor.Coordinates.PartialDiffeomorph.ofOpenPartialHomeomorphRestr
      e s hs hse (c.contMDiffOn_toFun.mono inter_subset_left)
        (c.contMDiffOn_invFun.mono (by
          rintro y ⟨z, hz, rfl⟩
          exact c.map_source' hz.1))
  refine ⟨Φ, A, hAfin, ⟨hxc, hxU⟩, hdim, ?_⟩
  intro y hy
  change c y ∈ (A : Set E) ↔ y ∈ S
  rw [himage.apply_mem_iff hy.1]
  have hmem : y ∈ S ↔ y ∈ N := by
    have hmem' := Set.ext_iff.mp heq y
    simpa only [Set.mem_inter_iff, hy.2, true_and] using hmem'
  exact hmem.symm

theorem is_open [FiniteDimensional ℝ E] {N : Set M}
    (hN : IsEmbeddedSlice I (Module.finrank ℝ E) N) : IsOpen N := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨Φ, A, _, hxΦ, hdim, himage⟩ := hN x hx
  have hxA : Φ x ∈ A := (himage.apply_mem_iff hxΦ).2 hx
  have hdir : A.direction = ⊤ := Submodule.eq_top_of_finrank_eq hdim
  have hA : A = ⊤ :=
    (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨Φ x, hxA⟩).1 hdir
  refine Filter.mem_of_superset (Φ.open_source.mem_nhds hxΦ) ?_
  intro y hy
  exact (himage.apply_mem_iff hy).1 (by
    rw [hA]
    exact AffineSubspace.mem_top ℝ E (Φ y))

theorem is_locally_closed {N : Set M} {d : ℕ}
    (hN : IsEmbeddedSlice I d N) : IsLocallyClosed N := by
  refine ((isLocallyClosed_tfae N).out 2 0).mp ?_
  intro x hx
  obtain ⟨Φ, A, hAfin, hxΦ, _, himage⟩ := hN x hx
  refine ⟨Φ.source, Φ.open_source.mem_nhds hxΦ, ?_⟩
  letI : FiniteDimensional ℝ A.direction := hAfin
  have hcont : Continuous (Φ.source.restrict (Φ : M → E)) :=
    Φ.contMDiffOn_toFun.continuousOn.restrict
  have heq : Φ.source ↓∩ N =
      (Φ.source.restrict (Φ : M → E)) ⁻¹' (A : Set E) := by
    ext y
    exact (himage.apply_mem_iff y.property).symm
  rw [heq]
  exact A.closed_of_finiteDimensional.preimage hcont

end IsEmbeddedSlice

theorem slice_dims_nonempty [I.Boundaryless] [IsManifold I ∞ M]
    {C : Set M} (hC : C.Nonempty) : (sliceDims I C).Nonempty := by
  obtain ⟨x, hxC⟩ := hC
  exact ⟨0, {x}, Set.singleton_nonempty x, Set.singleton_subset_iff.mpr hxC,
    IsEmbeddedSlice.singleton x⟩

theorem slice_dims_bdd [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E H)
    (C : Set M) : BddAbove (sliceDims I C) := by
  refine ⟨Module.finrank ℝ E, ?_⟩
  rintro d ⟨N, hNne, _, hN⟩
  exact hN.dim_le hNne

theorem max_slice_dim_mem [I.Boundaryless] [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] {C : Set M} (hC : C.Nonempty) :
    maxSliceDim I C ∈ sliceDims I C :=
  Nat.sSup_mem (slice_dims_nonempty (I := I) hC) (slice_dims_bdd I C)

theorem le_max_slice_dim [FiniteDimensional ℝ E] {C : Set M} {d : ℕ}
    (hd : d ∈ sliceDims I C) : d ≤ maxSliceDim I C :=
  le_csSup (slice_dims_bdd I C) hd

theorem exists_max_slice [I.Boundaryless] [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] {C : Set M} (hC : C.Nonempty) :
    ∃ N : Set M, N.Nonempty ∧ N ⊆ C ∧ IsEmbeddedSlice I (maxSliceDim I C) N :=
  max_slice_dim_mem (I := I) hC

theorem max_slice_nonempty [I.Boundaryless] [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] {C : Set M} (hC : C.Nonempty) :
    (maxSliceLocus I C).Nonempty := by
  obtain ⟨N, hNne, hNC, hN⟩ := exists_max_slice (I := I) hC
  obtain ⟨x, hxN⟩ := hNne
  exact ⟨x, N, hxN, hNC, hN⟩

theorem max_slice_subset {C : Set M} : maxSliceLocus I C ⊆ C := by
  rintro x ⟨N, hxN, hNC, _⟩
  exact hNC hxN

end Geometry
end DifferentialGeometry
