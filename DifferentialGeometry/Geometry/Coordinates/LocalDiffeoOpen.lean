import DifferentialGeometry.Geometry.Coordinates.PartialDiffeomorphOpens

set_option autoImplicit false

/-!
# Local diffeomorphisms on open subtypes

This file converts a local diffeomorphism on an ambient open set into a
global local diffeomorphism whose source is the corresponding open subtype.
-/

noncomputable section

namespace DifferentialGeometry

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
variable {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners Real F H'}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- A smooth local diffeomorphism on an open set restricts to a smooth local
diffeomorphism whose source is the corresponding open subtype. -/
theorem hloc_restrict_open
    {f : M → N} (U : Opens M)
    (hf : IsLocalDiffeomorphOn I J ∞ f U) :
    IsLocalDiffeomorph I J ∞ (fun x : U => f x) := by
  intro x
  obtain ⟨Φ, hxΦ, hΦeq⟩ := hf x
  let hU : Nonempty U := ⟨x⟩
  let e : OpenPartialHomeomorph U N :=
    Φ.toOpenPartialHomeomorph.subtypeRestr hU
  let Ψ : PartialDiffeomorph I J U N ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := by
        intro y hy
        have hyΦ : (y : M) ∈ Φ.source := by
          simpa only [e, OpenPartialHomeomorph.subtypeRestr_source] using hy
        have hΦ :
            ContMDiffAt I J ∞ (Φ : M → N) (y : M) :=
          Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hyΦ)
        have hrest :
            ContMDiffAt I J ∞ (fun z : U => (Φ : M → N) z) y :=
          contMDiffAt_subtype_iff.mpr hΦ
        simpa only [e, OpenPartialHomeomorph.subtypeRestr_coe,
          Set.restrict_apply] using hrest.contMDiffWithinAt
      contMDiffOn_invFun := by
        intro y hy
        have hyΦ : y ∈ Φ.target :=
          Φ.toOpenPartialHomeomorph.subtypeRestr_target_subset hU hy
        have hΦ :
            ContMDiffAt J I ∞ (Φ.symm : N → M) y :=
          Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hyΦ)
        have heq :
            (Φ.symm : N → M) =ᶠ[𝓝 y]
              (fun z => ((e.symm : N → U) z : M)) :=
          Filter.eventuallyEq_of_mem (e.open_target.mem_nhds hy) fun z hz => by
            simpa only [Function.comp_apply] using
              Φ.toOpenPartialHomeomorph.subtypeRestr_symm_eqOn hU hz
        have hcoe :
            ContMDiffAt J I ∞
              (fun z => ((e.symm : N → U) z : M)) y :=
          hΦ.congr_of_eventuallyEq heq.symm
        have hsub :
            ContMDiffAt J I ∞ (e.symm : N → U) y :=
          codRestr_contMDiffAt
            (V := U) (fun z => ((e.symm : N → U) z).property) hcoe
        exact hsub.contMDiffWithinAt }
  refine ⟨Ψ, ?_, ?_⟩
  · change x ∈ e.source
    simpa only [e, OpenPartialHomeomorph.subtypeRestr_source] using hxΦ
  · intro y hy
    have hyΦ : (y : M) ∈ Φ.source := by
      change y ∈ e.source at hy
      simpa only [e, OpenPartialHomeomorph.subtypeRestr_source] using hy
    change f y = e y
    simpa only [e, OpenPartialHomeomorph.subtypeRestr_coe,
      Set.restrict_apply] using hΦeq hyΦ

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace Real G]
variable {H'' : Type*} [TopologicalSpace H'']
  {K : ModelWithCorners Real G H''}
variable {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- The composite of two local diffeomorphisms is a local diffeomorphism. -/
theorem hloc_comp
    {k : WithTop ℕ∞} {f : M → N} {g : N → P}
    (hg : IsLocalDiffeomorph J K k g)
    (hf : IsLocalDiffeomorph I J k f) :
    IsLocalDiffeomorph I K k (g ∘ f) := by
  intro x
  obtain ⟨Φ, hxΦ, hfΦ⟩ := hf x
  obtain ⟨Ψ, hfxΨ, hgΨ⟩ := hg (f x)
  have hΦxΨ : Φ x ∈ Ψ.source := by
    rw [← hfΦ hxΦ]
    exact hfxΨ
  let e : OpenPartialHomeomorph M P :=
    Φ.toOpenPartialHomeomorph.trans Ψ.toOpenPartialHomeomorph
  let Θ : PartialDiffeomorph I K M P k :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := by
        rw [show e.source =
            Φ.source ∩ Φ ⁻¹' Ψ.source by
          exact OpenPartialHomeomorph.trans_source _ _]
        exact Ψ.contMDiffOn_toFun.comp
          (Φ.contMDiffOn_toFun.mono inter_subset_left)
          (fun _ hy => hy.2)
      contMDiffOn_invFun := by
        rw [show e.target =
            Ψ.target ∩ Ψ.symm ⁻¹' Φ.target by
          exact OpenPartialHomeomorph.trans_target _ _]
        exact Φ.contMDiffOn_invFun.comp
          (Ψ.contMDiffOn_invFun.mono inter_subset_left)
          (fun _ hy => hy.2) }
  refine ⟨Θ, ?_, ?_⟩
  · change x ∈ e.source
    rw [show e.source =
        Φ.source ∩ Φ ⁻¹' Ψ.source by
      exact OpenPartialHomeomorph.trans_source _ _]
    exact ⟨hxΦ, hΦxΨ⟩
  · intro y hy
    change y ∈ e.source at hy
    have hy' : y ∈ Φ.source ∩ Φ ⁻¹' Ψ.source := by
      rwa [show e.source =
          Φ.source ∩ Φ ⁻¹' Ψ.source by
        exact OpenPartialHomeomorph.trans_source _ _] at hy
    change g (f y) = e y
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      hfΦ hy'.1, hgΨ hy'.2]
    rfl

section InjectiveGlue

open Function

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜']
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜' E']
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜' F']
  {H₁ : Type*} [TopologicalSpace H₁]
  {G₁ : Type*} [TopologicalSpace G₁]
  {I' : ModelWithCorners 𝕜' E' H₁}
  {J' : ModelWithCorners 𝕜' F' G₁}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H₁ M']
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G₁ N']
  {n : WithTop ℕ∞}

/-- An injective local diffeomorphism on an open set restricts to a partial
diffeomorphism with exactly that source and its image as target. -/
theorem exists_diffeo_of_injOn [Nonempty M']
    {f : M' → N'} {s : Set M'}
    (hf : IsLocalDiffeomorphOn I' J' n f s)
    (hs : IsOpen s) (hinj : InjOn f s) :
    ∃ Φ : PartialDiffeomorph I' J' M' N' n,
      Φ.source = s ∧ Φ.target = f '' s ∧ EqOn Φ f s := by
  classical
  have htgt : IsOpen (f '' s) := by
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨φ, hxφ, hEq⟩ := hf ⟨x, hx⟩
    refine ⟨φ '' (s ∩ φ.source), ?_, ?_, ⟨x, ⟨hx, hxφ⟩, (hEq hxφ).symm⟩⟩
    · rintro z ⟨x', ⟨hx's, hx'φ⟩, rfl⟩
      exact ⟨x', hx's, hEq hx'φ⟩
    · exact φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source
        (hs.inter φ.open_source) inter_subset_right
  have hinv : ContMDiffOn J' I' n (invFunOn f s) (f '' s) := by
    apply contMDiffOn_of_locally_contMDiffOn
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨φ, hxφ, hEq⟩ := hf ⟨x, hx⟩
    refine ⟨φ '' (s ∩ φ.source),
      φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source
        (hs.inter φ.open_source) inter_subset_right,
      ⟨x, ⟨hx, hxφ⟩, (hEq hxφ).symm⟩, ?_⟩
    have hsub : φ '' (s ∩ φ.source) ⊆ φ.target := by
      rintro z ⟨x', ⟨_, hx'φ⟩, rfl⟩
      exact φ.toPartialEquiv.map_source hx'φ
    refine ((φ.symm.contMDiffOn.mono hsub).mono inter_subset_right).congr ?_
    rintro z ⟨-, x', ⟨hx's, hx'φ⟩, rfl⟩
    have h2 : f x' = φ x' := hEq hx'φ
    have hmem : invFunOn f s (φ x') ∈ s :=
      invFunOn_mem ⟨x', hx's, h2⟩
    have happ : f (invFunOn f s (φ x')) = φ x' :=
      invFunOn_eq ⟨x', hx's, h2⟩
    have h1 : φ.toPartialEquiv.symm (φ x') = x' :=
      φ.toPartialEquiv.left_inv hx'φ
    change invFunOn f s (φ x') = φ.toPartialEquiv.symm (φ x')
    rw [h1]
    exact hinj hmem hx's (by rw [happ, h2])
  refine ⟨{
    toFun := f
    invFun := invFunOn f s
    source := s
    target := f '' s
    map_source' := fun x hx => ⟨x, hx, rfl⟩
    map_target' := fun y ⟨x', hx', hxy⟩ =>
      invFunOn_mem ⟨x', hx', hxy⟩
    left_inv' := fun x hx => hinj.leftInvOn_invFunOn hx
    right_inv' := fun y ⟨x', hx', hxy⟩ =>
      invFunOn_eq ⟨x', hx', hxy⟩
    open_source := hs
    open_target := htgt
    contMDiffOn_toFun := hf.contMDiffOn
    contMDiffOn_invFun := hinv }, rfl, rfl, fun x _ => rfl⟩

end InjectiveGlue

end DifferentialGeometry
