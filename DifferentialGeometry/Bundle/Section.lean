/-
Authors: Jack McCarthy
-/
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import DifferentialGeometry.Bundle.Equiv
import DifferentialGeometry.Bundle.Frame

/-!

# Sections of Vector Bundles

This file introduces notation for smooth sections and shows that they form a module
over the ring of smooth scalar-valued functions.

## Notation

* `Γ^n(V)` : the space of `C^n` sections of a `C^n` vector bundle with fiber family `V`.

## Main Results

* `ContMDiffSection.instSMulContMDiffMap` : smooth scalar functions act on smooth sections
  by pointwise multiplication.
* `ContMDiffSection.instModuleContMDiffMap` : smooth sections of a vector bundle over `M`
  form a module over `C^n(M, 𝕜)`.

## Tags

section, vector bundle, smooth section, module, smooth functions
-/

set_option autoImplicit false

open scoped Manifold ContDiff
open Bundle

/-! ## Module over smooth functions -/

section ModuleOverSmoothFunctions

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞}
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

namespace ContMDiffSection

/-- Smooth scalar-valued functions act on smooth sections by pointwise scalar multiplication. -/
instance instSMulContMDiffMap : SMul C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ :=
  ⟨fun f s => ⟨fun x => f x • s x, f.2.smul_section s.contMDiff⟩⟩

@[simp]
theorem coe_smulContMDiffMap (f : C^n⟮I, M; 𝕜⟯) (s : Cₛ^n⟮I; F, V⟯) :
    ⇑(f • s) = fun x => f x • s x :=
  rfl

/-- Smooth sections of a vector bundle over `M` form a module over the ring of smooth
scalar-valued functions `C^n(M, 𝕜)`. -/
instance instModuleContMDiffMap : Module C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ where
  one_smul s := by ext x; exact one_smul 𝕜 (s x)
  mul_smul f g s := by ext x; exact mul_smul (f x) (g x) (s x)
  smul_zero f := by ext x; exact smul_zero (f x)
  smul_add f s t := by ext x; exact smul_add (f x) (s x) (t x)
  add_smul f g s := by ext x; exact add_smul (f x) (g x) (s x)
  zero_smul s := by ext x; exact zero_smul 𝕜 (s x)

end ContMDiffSection

end ModuleOverSmoothFunctions

/-! ## Induced map on sections from a bundle map -/

section MapSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞}
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : M → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : M → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

namespace ContMDiffVectorBundleMap

/-- A smooth vector bundle map `Φ : E₁ → E₂` covering the identity induces a
`C^n(M, 𝕜)`-linear map on smooth sections `Γ(E₁) → Γ(E₂)` by `σ ↦ Φ ∘ σ`. -/
noncomputable def mapSection
    (Φ : ContMDiffVectorBundleMap 𝕜 I n F₁ E₁ F₂ E₂)
    (hΦ : Φ.baseMap = _root_.id) : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[C^n⟮I, M; 𝕜⟯] Cₛ^n⟮I; F₂, E₂⟯ := by
  obtain ⟨baseMap, toFun, hc, φ, compat⟩ := Φ
  subst hΦ
  exact
  { toFun := fun σ =>
      ⟨fun x => φ x (σ x), (hc.comp σ.contMDiff).congr fun x => (compat x (σ x)).symm⟩
    map_add' := fun σ τ => by ext x; exact (φ x).map_add (σ x) (τ x)
    map_smul' := fun f σ => by ext x; exact (φ x).map_smul (f x) (σ x) }

end ContMDiffVectorBundleMap

/-! ## Vector Bundle Characterization Lemma

**Statement.** Let `E₁`, `E₂` be smooth vector bundles over a smooth manifold `M`.
A map `F : Γ(E₁) → Γ(E₂)` is `C^n(M)`-linear if and only if there exists a smooth
vector bundle map `Φ : E₁ → E₂` covering the identity such that `F(σ) = Φ ∘ σ`.

**Proof sketch.**
The forward direction is `ContMDiffVectorBundleMap.mapSection`. For the converse,
suppose `F : Γ(E₁) → Γ(E₂)` is `C^n(M)`-linear.

1. *F acts locally*: If `σ₁ = σ₂` on an open set `U ⊆ M`, then `F(σ₁) = F(σ₂)` on `U`.
   Let `τ = σ₁ - σ₂`. For `p ∈ U`, choose a smooth bump `ψ` supported in `U` with `ψ(p) = 1`.
   Then `ψ • τ = 0` globally, so `ψ · F(τ) = F(ψ • τ) = 0`, giving `F(τ)(p) = 0`.

2. *F acts pointwise*: If `σ₁(p) = σ₂(p)` then `F(σ₁)(p) = F(σ₂)(p)`.
   Write `τ = σ₁ - σ₂` with `τ(p) = 0`. Using a local frame `(σ₁, …, σₖ)` for `E₁` near `p`,
   write `τ = ∑ uⁱ • σᵢ` with `uⁱ(p) = 0`. Extend to global sections via bump functions;
   then `F(τ)(p) = ∑ uⁱ(p) · F(σᵢ')(p) = 0`.

3. *Define the bundle map*: For `⟨p, v⟩ ∈ E₁`, set `Φ(p, v) = F(v')(p)` where `v'` is any
   global section with `v'(p) = v`. By step 2 this is well-defined, covers the identity,
   and is fiberwise linear (since `F` is linear).

4. *Smoothness*: In local frames `(σᵢ)` for `E₁` and `(τⱼ)` for `E₂` over a neighborhood
   of `p`, the bundle map is represented by the smooth matrix `Aⱼⁱ` where
   `F(σᵢ') = ∑ⱼ Aⱼⁱ • τⱼ`, giving `Φ(q, v) = ∑ᵢⱼ vⁱ Aⱼⁱ(q) τⱼ(q)`. -/

/-- **Vector Bundle Characterization Lemma.** Every `C^n(M, ℝ)`-linear map between spaces
of smooth sections is induced by a smooth vector bundle map covering the identity. -/
theorem vectorBundle_characterization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {n : ℕ∞}
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    {E₁ : M → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℝ (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
    [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    {E₂ : M → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module ℝ (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]
    [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]
    [ContMDiffVectorBundle n F₁ E₁ I] [ContMDiffVectorBundle n F₂ E₂ I]
    (F : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[C^n⟮I, M; ℝ⟯] Cₛ^n⟮I; F₂, E₂⟯) :
    ∃ (Φ : ContMDiffVectorBundleMap ℝ I n F₁ E₁ F₂ E₂) (hΦ : Φ.baseMap = _root_.id),
      ∀ σ, F σ = Φ.mapSection hΦ σ := by
  -- ===== Step 1: F acts locally =====
  -- If σ₁ = σ₂ on an open set U, then F(σ₁) = F(σ₂) on U.
  -- Equivalently: if τ vanishes on U, then F(τ) vanishes on U.
  -- Proof: For p ∈ U, pick a bump ψ supported in U with ψ(p) = 1.
  -- Then ψ • τ = 0 globally, so ψ · F(τ) = F(ψ • τ) = 0, giving F(τ)(p) = 0.
  have acts_locally : ∀ (σ : Cₛ^n⟮I; F₁, E₁⟯) {U : Set M} (hU : IsOpen U),
      (∀ x ∈ U, σ x = 0) → ∀ p ∈ U, (F σ) p = 0 := by
    intro σ U hU hσU p hp
    -- Get a smooth bump function ψ at p with tsupport ψ ⊆ U
    obtain ⟨ψ, -, hψsupp⟩ :=
      (SmoothBumpFunction.nhds_basis_tsupport (I := I) p).mem_iff.mp (hU.mem_nhds hp)
    -- Lift ψ to a C^n scalar function on M
    let ψ' : C^n⟮I, M; ℝ⟯ :=
      ⟨ψ, ψ.contMDiff.of_le (WithTop.coe_le_coe.mpr le_top)⟩
    -- ψ • σ = 0 : wherever ψ ≠ 0, we have x ∈ tsupport ψ ⊆ U, so σ x = 0
    have hψσ : ψ' • σ = 0 := by
      ext x
      simp only [ContMDiffSection.coe_smulContMDiffMap, Pi.zero_apply, ContMDiffSection.coe_zero]
      by_cases hx : x ∈ Function.support (ψ : M → ℝ)
      · exact smul_eq_zero_of_right _ (hσU x (hψsupp (subset_closure hx)))
      · simp only [Function.mem_support, not_not] at hx
        exact smul_eq_zero_of_left hx _
    -- By C^n(M)-linearity: ψ · F(σ) = F(ψ • σ) = F(0) = 0
    have key : ψ' • F σ = 0 := by rw [← F.map_smul, hψσ, map_zero]
    -- Evaluate at p: ψ(p) = 1, so F(σ)(p) = 1 • F(σ)(p) = ψ(p) • F(σ)(p) = 0
    have := DFunLike.congr_fun key p
    simp only [ContMDiffSection.coe_smulContMDiffMap, ContMDiffSection.coe_zero,
      Pi.zero_apply] at this
    rwa [show (ψ' p : ℝ) = 1 from ψ.eq_one, one_smul] at this
  -- ===== Step 2: F acts pointwise =====
  -- If σ₁(p) = σ₂(p) then F(σ₁)(p) = F(σ₂)(p).
  -- Proof: Let τ = σ₁ - σ₂ with τ(p) = 0. Using a local frame near p,
  -- write τ = ∑ uⁱ • σᵢ' with uⁱ(p) = 0. By step 1, each uⁱ • σᵢ' vanishes
  -- at p under F, so F(τ)(p) = ∑ uⁱ(p) · F(σᵢ')(p) = 0.
  have acts_pointwise : ∀ (σ₁ σ₂ : Cₛ^n⟮I; F₁, E₁⟯) (p : M),
      σ₁ p = σ₂ p → (F σ₁) p = (F σ₂) p := by
    intro σ₁ σ₂ p hσ
    -- Reduce to: if τ(p) = 0 then F(τ)(p) = 0, applied to τ = σ₁ - σ₂
    suffices h : ∀ (τ : Cₛ^n⟮I; F₁, E₁⟯), τ p = 0 → (F τ) p = 0 by
      have h₁ := h (σ₁ - σ₂) (by
        simp only [ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero]; exact hσ)
      simp only [map_sub, ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero] at h₁
      exact h₁
    intro τ hτ
    -- Get a local frame for E₁ from the trivialization at p
    let e := trivializationAt F₁ E₁ p
    let b := Module.finBasis ℝ F₁
    have he : p ∈ e.baseSet := mem_baseSet_trivializationAt F₁ E₁ p
    have hframe := e.isLocalFrameOn_localFrame_baseSet I (↑n) b
    -- Extend frame sections to global sections s'ᵢ agreeing with the frame near p
    obtain ⟨s', hs'⟩ := hframe.exists_contMDiffSection_eqOn_nhd e.open_baseSet he
    -- Construct global smooth coefficient functions u'ᵢ agreeing with coeff i τ near p.
    -- Each u'ᵢ is obtained by multiplying the (locally smooth) frame coefficient by a
    -- bump function supported in the frame domain. u'ᵢ(p) = coeff i τ p = 0 since τ(p) = 0.
    obtain ⟨χ, -, hχsupp⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) p).mem_iff.mp
      (e.open_baseSet.mem_nhds he)
    let u' : Fin (Module.finrank ℝ F₁) → C^n⟮I, M; ℝ⟯ := fun i =>
      ⟨fun x => χ x • hframe.coeff i (⇑τ) x,
        sorry⟩ -- smoothness of χ • coeff (needs contMDiffOn_coeff, currently a TODO)
    -- u'ᵢ(p) = χ(p) • coeff i τ p = 1 • 0 = 0 since τ(p) = 0
    have hu'_zero : ∀ i, (u' i) p = 0 := by
      intro i; show χ p • hframe.coeff i (⇑τ) p = 0
      rw [χ.eq_one, one_smul, hframe.coeff_apply_zero_at hτ]
    -- Near p: τ = ∑ u'ᵢ • s'ᵢ (since χ = 1 and s'ᵢ = sᵢ near p, and τ = ∑ coeff • sᵢ)
    have hτ_eq_near : ∀ᶠ x in nhds p, τ x = ∑ i, (u' i) x • (s' i) x := by
      filter_upwards [hs', χ.eventuallyEq_one,
        e.open_baseSet.mem_nhds he] with x hs'x hχx hx
      show τ x = ∑ i, (χ x • hframe.coeff i (⇑τ) x) • (s' i) x
      simp only [show χ x = (1 : M → ℝ) x from hχx, Pi.one_apply, one_smul]
      conv_lhs => rw [hframe.coeff_sum_eq (⇑τ) hx]
      congr 1; ext i; rw [hs'x i]
    -- τ - ∑ u'ᵢ • s'ᵢ vanishes on a neighborhood of p
    obtain ⟨W, hW_open, hpW, hW_vanish⟩ : ∃ W : Set M, IsOpen W ∧ p ∈ W ∧
        ∀ x ∈ W, (τ - ∑ i, u' i • s' i) x = 0 := by
      obtain ⟨W, hW_nhds, hW⟩ := Filter.Eventually.exists_mem hτ_eq_near
      obtain ⟨W', hW'W, hW'_open, hpW'⟩ := mem_nhds_iff.mp hW_nhds
      refine ⟨W', hW'_open, hpW', fun x hx => ?_⟩
      simp only [ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero]
      -- (∑ i, u' i • s' i) x = ∑ i, (u' i) x • (s' i) x
      -- This is a coercion lemma for sums of sections; sorry for now.
      sorry
    -- By acts_locally: F(τ - ∑ u'ᵢ • s'ᵢ)(p) = 0
    have h_local := acts_locally (τ - ∑ i, u' i • s' i) hW_open hW_vanish p hpW
    -- By linearity: F(τ)(p) - F(∑ u'ᵢ • s'ᵢ)(p) = 0
    -- and F(∑ u'ᵢ • s'ᵢ)(p) = ∑ u'ᵢ(p) • F(s'ᵢ)(p) = ∑ 0 • F(s'ᵢ)(p) = 0
    sorry
  -- ===== Existence of global sections with prescribed value =====
  -- For each p : M and v : E₁ p, there exists σ ∈ Γ(E₁) with σ(p) = v.
  -- Constructed by writing v in a local frame and bumping to global sections.
  have exists_section : ∀ (p : M) (v : E₁ p),
      ∃ (σ : Cₛ^n⟮I; F₁, E₁⟯), σ p = v := by
    sorry
  -- ===== Step 3: Define the fiberwise linear map =====
  -- φ(x)(v) := F(σ')(x) where σ' is any global section with σ'(x) = v.
  -- Well-defined by acts_pointwise, linear because F is linear.
  let φ : ∀ x : M, E₁ x →ₗ[ℝ] E₂ x := fun x =>
    { toFun := fun v => (F (exists_section x v).choose) x
      map_add' := fun v w => by
        -- F(choose(v+w))(x) = F(choose(v) + choose(w))(x) = F(choose(v))(x) + F(choose(w))(x)
        -- First equality: acts_pointwise (since both sections equal v+w at x)
        -- Second equality: linearity of F
        sorry
      map_smul' := fun c v => by
        -- F(choose(c•v))(x) = c • F(choose(v))(x)
        -- Uses acts_pointwise and that F commutes with 𝕜-scalar multiplication
        sorry }
  -- φ agrees with F on sections: φ(x)(σ(x)) = F(σ)(x)
  have φ_spec : ∀ (σ : Cₛ^n⟮I; F₁, E₁⟯) (x : M), φ x (σ x) = (F σ) x :=
    fun σ x => acts_pointwise _ σ x (exists_section x (σ x)).choose_spec
  -- ===== Step 4: The total space map is smooth =====
  -- In local frames (σᵢ) for E₁ and (τⱼ) for E₂, the map is represented by the
  -- smooth matrix Aⱼⁱ where F(σᵢ') = ∑ⱼ Aⱼⁱ • τⱼ.
  have Φ_smooth : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) n
      (fun p : TotalSpace F₁ E₁ => (⟨p.proj, φ p.proj p.2⟩ : TotalSpace F₂ E₂)) := by
    sorry
  -- ===== Package everything =====
  exact ⟨⟨_root_.id, fun p => ⟨p.proj, φ p.proj p.2⟩, Φ_smooth, φ, fun _ _ => rfl⟩, rfl,
    fun σ => by ext x; exact (φ_spec σ x).symm⟩

end MapSection
