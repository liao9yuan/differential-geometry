/-
Authors: Jack McCarthy
-/
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
import DifferentialGeometry.Bundle.Zero
import Mathlib.Geometry.Manifold.VectorBundle.Basic

set_option autoImplicit false

/-!
# Vector Bundle Maps and Equivalences

A vector bundle map between vector bundles `E₁` over `B₁` and `E₂` over `B₂` is a
continuous map between total spaces that sends fibers linearly into fibers, covering
some base map `baseMap : B₁ → B₂`.

A vector bundle equivalence strengthens this to a homeomorphism with fiberwise linear
equivalences. The `C^n` variants require smoothness.

The base map is stored as a field rather than a parameter, since it is determined by
the total space map. The lemma `baseMap_eq` recovers it as
`fun x => (toFun ⟨x, 0⟩).proj`.

## Main Definitions

* `VectorBundleMap` : a continuous, fiberwise-linear map between vector bundles.
* `VectorBundleEquiv` : a vector bundle isomorphism.
* `ContMDiffVectorBundleMap` : a `C^n` vector bundle map.
* `ContMDiffVectorBundleEquiv` : a `C^n` vector bundle equivalence.

## Tags

vector bundle, map, equivalence, isomorphism, diffeomorphism
-/

open Bundle

/-! ## Vector bundle maps -/

/-- A vector bundle map from `E₁` over `B₁` to `E₂` over `B₂`. -/
structure VectorBundleMap
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {B₁ : Type*} [TopologicalSpace B₁] {B₂ : Type*} [TopologicalSpace B₂]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (E₁ : B₁ → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (E₂ : B₂ → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] where
  /-- The base map covered by this bundle map. -/
  baseMap : B₁ → B₂
  /-- The underlying continuous map between total spaces. -/
  toFun : TotalSpace F₁ E₁ → TotalSpace F₂ E₂
  /-- The total space map is continuous. -/
  continuous_toFun : Continuous toFun
  /-- A family of linear maps between the fibers. -/
  fiberLinearMap : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)
  /-- The map acts fiberwise via `fiberLinearMap`. -/
  fiber_compat : ∀ (x : B₁) (v : E₁ x),
    toFun ⟨x, v⟩ = ⟨baseMap x, fiberLinearMap x v⟩

namespace VectorBundleMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B₁ : Type*} [TopologicalSpace B₁]
  {B₂ : Type*} [TopologicalSpace B₂]
  {B₃ : Type*} [TopologicalSpace B₃]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₃ : B₃ → Type*} [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)]

/-- Construct a `VectorBundleMap` without specifying the base map, deriving it as
`fun x => (Φ ⟨x, 0⟩).proj`. -/
def mk'
    (Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂) (hΦ : Continuous Φ)
    (φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ ((Φ ⟨x, 0⟩).proj))
    (hcompat : ∀ (x : B₁) (v : E₁ x),
      Φ ⟨x, v⟩ = ⟨(Φ ⟨x, 0⟩).proj, φ x v⟩) :
    VectorBundleMap 𝕜 F₁ E₁ F₂ E₂ where
  baseMap x := (Φ ⟨x, 0⟩).proj
  toFun := Φ
  continuous_toFun := hΦ
  fiberLinearMap := φ
  fiber_compat := hcompat

@[ext]
theorem ext (A B : VectorBundleMap 𝕜 F₁ E₁ F₂ E₂)
    (h : A.toFun = B.toFun) : A = B := by
  obtain ⟨f_A, Φ_A, _, φ_A, hA⟩ := A
  obtain ⟨f_B, Φ_B, _, φ_B, hB⟩ := B
  simp only at h
  subst h
  have hf : f_A = f_B := by
    ext x
    have h1 := hA x 0; have h2 := hB x 0
    simp only [map_zero] at h1 h2
    rw [h1] at h2
    exact congrArg TotalSpace.proj h2
  subst hf
  simp only [mk.injEq, heq_eq_eq, true_and]
  ext x v
  have h1 := hA x v; rw [hB] at h1
  exact TotalSpace.mk_inj.mp h1.symm

/-- The base map equals the projection of the total space map on the zero section. -/
theorem baseMap_eq (f : VectorBundleMap 𝕜 F₁ E₁ F₂ E₂) (x : B₁) :
    f.baseMap x = (f.toFun ⟨x, 0⟩).proj := by
  simp [f.fiber_compat, map_zero]

/-- The base map of a vector bundle map is continuous, since it factors as
`π₂ ∘ Φ ∘ zeroSection` and the zero section is continuous. -/
theorem baseMapContinuous
    [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]
    (f : VectorBundleMap 𝕜 F₁ E₁ F₂ E₂) : Continuous f.baseMap := by
  have h : f.baseMap = TotalSpace.proj ∘ f.toFun ∘ zeroSection F₁ E₁ := by
    ext x; simp [baseMap_eq, zeroSection]
  rw [h]
  exact (FiberBundle.continuous_proj F₂ E₂).comp
    (f.continuous_toFun.comp (continuous_zeroSection 𝕜))

@[simp]
theorem proj_eq (f : VectorBundleMap 𝕜 F₁ E₁ F₂ E₂) (p : TotalSpace F₁ E₁) :
    (f.toFun p).proj = f.baseMap p.proj := by
  obtain ⟨x, v⟩ := p; simp [f.fiber_compat]

@[simp]
theorem toFun_apply (f : VectorBundleMap 𝕜 F₁ E₁ F₂ E₂) (x : B₁) (v : E₁ x) :
    f.toFun ⟨x, v⟩ = ⟨f.baseMap x, f.fiberLinearMap x v⟩ :=
  f.fiber_compat x v

def id : VectorBundleMap 𝕜 F₁ E₁ F₁ E₁ where
  baseMap := _root_.id
  toFun := _root_.id
  continuous_toFun := continuous_id
  fiberLinearMap _ := LinearMap.id
  fiber_compat _ _ := rfl

def comp (g : VectorBundleMap 𝕜 F₂ E₂ F₃ E₃) (f : VectorBundleMap 𝕜 F₁ E₁ F₂ E₂) :
    VectorBundleMap 𝕜 F₁ E₁ F₃ E₃ where
  baseMap := g.baseMap ∘ f.baseMap
  toFun := g.toFun ∘ f.toFun
  continuous_toFun := g.continuous_toFun.comp f.continuous_toFun
  fiberLinearMap x := (g.fiberLinearMap (f.baseMap x)).comp (f.fiberLinearMap x)
  fiber_compat x v := by
    simp only [Function.comp_apply, f.fiber_compat, g.fiber_compat, LinearMap.comp_apply]

end VectorBundleMap

/-! ## Vector bundle equivalences -/

/-- A vector bundle equivalence between bundles `E₁` over `B₁` and `E₂` over `B₂`. -/
structure VectorBundleEquiv
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {B₁ : Type*} [TopologicalSpace B₁] {B₂ : Type*} [TopologicalSpace B₂]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (E₁ : B₁ → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (E₂ : B₂ → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] where
  /-- The base map covered by this bundle equivalence. -/
  baseMap : B₁ → B₂
  /-- The underlying homeomorphism between total spaces. -/
  toHomeomorph : TotalSpace F₁ E₁ ≃ₜ TotalSpace F₂ E₂
  /-- A family of linear equivalences between the fibers. -/
  fiberLinearEquiv : ∀ x : B₁, E₁ x ≃ₗ[𝕜] E₂ (baseMap x)
  /-- The homeomorphism acts fiberwise via `fiberLinearEquiv`. -/
  fiber_compat : ∀ (x : B₁) (v : E₁ x),
    toHomeomorph ⟨x, v⟩ = ⟨baseMap x, fiberLinearEquiv x v⟩

namespace VectorBundleEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B₁ : Type*} [TopologicalSpace B₁]
  {B₂ : Type*} [TopologicalSpace B₂]
  {B₃ : Type*} [TopologicalSpace B₃]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₃ : B₃ → Type*} [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)]

/-- Construct a `VectorBundleEquiv` without specifying the base map, deriving it as
`fun x => (Φ ⟨x, 0⟩).proj`. -/
def mk'
    (Φ : TotalSpace F₁ E₁ ≃ₜ TotalSpace F₂ E₂)
    (φ : ∀ x : B₁, E₁ x ≃ₗ[𝕜] E₂ ((Φ ⟨x, 0⟩).proj))
    (hcompat : ∀ (x : B₁) (v : E₁ x),
      Φ ⟨x, v⟩ = ⟨(Φ ⟨x, 0⟩).proj, φ x v⟩) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂ where
  baseMap x := (Φ ⟨x, 0⟩).proj
  toHomeomorph := Φ
  fiberLinearEquiv := φ
  fiber_compat := hcompat

@[ext]
theorem ext (A B : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂)
    (h : A.toHomeomorph = B.toHomeomorph) : A = B := by
  obtain ⟨f_A, Φ_A, φ_A, hA⟩ := A
  obtain ⟨f_B, Φ_B, φ_B, hB⟩ := B
  simp only at h; subst h
  have hf : f_A = f_B := by
    ext x
    have h₁ := hA x 0; have h₂ := hB x 0
    simp only [map_zero] at h₁ h₂
    rw [h₁] at h₂; exact congrArg TotalSpace.proj h₂
  subst hf; congr 1
  ext x v
  have h₁ := hA x v; rw [hB] at h₁
  exact TotalSpace.mk_inj.mp h₁.symm

theorem baseMap_eq (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (x : B₁) :
    e.baseMap x = (e.toHomeomorph ⟨x, 0⟩).proj := by
  simp [e.fiber_compat, map_zero]

/-- The base map of a vector bundle equivalence is bijective. -/
theorem baseMapBijective (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) :
    Function.Bijective e.baseMap := by
  constructor
  · intro x₁ x₂ h
    have h₁ := e.fiber_compat x₁ 0
    have h₂ := e.fiber_compat x₂ 0
    simp only [map_zero] at h₁ h₂
    have hinj := e.toHomeomorph.injective (h₁.trans (by rw [h]) |>.trans h₂.symm)
    exact congrArg TotalSpace.proj hinj
  · intro y
    obtain ⟨⟨x, v⟩, hxv⟩ := e.toHomeomorph.surjective ⟨y, 0⟩
    have := e.fiber_compat x v
    rw [this] at hxv
    exact ⟨x, congrArg TotalSpace.proj hxv⟩

@[simp]
theorem proj_eq (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (p : TotalSpace F₁ E₁) :
    (e.toHomeomorph p).proj = e.baseMap p.proj := by
  obtain ⟨x, v⟩ := p; simp [e.fiber_compat]

@[simp]
theorem toHomeomorph_apply (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (x : B₁) (v : E₁ x) :
    e.toHomeomorph ⟨x, v⟩ = ⟨e.baseMap x, e.fiberLinearEquiv x v⟩ :=
  e.fiber_compat x v

/-- A `VectorBundleEquiv` gives a `VectorBundleMap` in the forward direction. -/
def toVectorBundleMap (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) :
    VectorBundleMap 𝕜 F₁ E₁ F₂ E₂ where
  baseMap := e.baseMap
  toFun := e.toHomeomorph
  continuous_toFun := e.toHomeomorph.continuous
  fiberLinearMap x := (e.fiberLinearEquiv x).toLinearMap
  fiber_compat x v := e.fiber_compat x v

def refl : VectorBundleEquiv 𝕜 F₁ E₁ F₁ E₁ where
  baseMap := _root_.id
  toHomeomorph := Homeomorph.refl _
  fiberLinearEquiv x := LinearEquiv.refl 𝕜 (E₁ x)
  fiber_compat _ _ := rfl

def symm (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) :
    VectorBundleEquiv 𝕜 F₂ E₂ F₁ E₁ where
  baseMap y := (e.toHomeomorph.symm ⟨y, 0⟩).proj
  toHomeomorph := e.toHomeomorph.symm
  fiberLinearEquiv y :=
    -- x := (Φ⁻¹ ⟨y, 0⟩).proj, and e.baseMap x = y
    let x := (e.toHomeomorph.symm ⟨y, 0⟩).proj
    have hx : e.baseMap x = y := by
      have := e.proj_eq (e.toHomeomorph.symm ⟨y, 0⟩)
      rw [e.toHomeomorph.apply_symm_apply] at this; exact this.symm
    (hx ▸ e.fiberLinearEquiv x).symm
  fiber_compat y v := by
    have key : ∀ (x : B₁) (hx : e.baseMap x = y),
        (⟨y, v⟩ : TotalSpace F₂ E₂) =
        ⟨e.baseMap x, e.fiberLinearEquiv x ((hx ▸ e.fiberLinearEquiv x).symm v)⟩ := by
      intro x hx; subst hx; simp [LinearEquiv.apply_symm_apply]
    apply e.toHomeomorph.injective
    rw [e.toHomeomorph.apply_symm_apply, e.toHomeomorph_apply]
    exact key _ _

def trans (e₁₂ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (e₂₃ : VectorBundleEquiv 𝕜 F₂ E₂ F₃ E₃) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₃ E₃ where
  baseMap := e₂₃.baseMap ∘ e₁₂.baseMap
  toHomeomorph := e₁₂.toHomeomorph.trans e₂₃.toHomeomorph
  fiberLinearEquiv x := (e₁₂.fiberLinearEquiv x).trans (e₂₃.fiberLinearEquiv (e₁₂.baseMap x))
  fiber_compat x v := by
    simp only [Homeomorph.trans_apply, e₁₂.fiber_compat, e₂₃.fiber_compat,
      LinearEquiv.trans_apply, Function.comp]

end VectorBundleEquiv

/-! ## Bijective bundle maps are equivalences -/

/- Proof sketch
1. Note since π₂ ∘ F = π₁, applying F⁻¹ to both sides immediately yields π₁ ∘ F⁻¹ = π₂
2. For any x in M, the (fiberLinearMap x) : E₁ x → E₂ x must be bijective since F is bijectve. Thus, it is a linear equivalence.
3. Pick any ⟨x,v⟩ in E2. It now suffices to show that F^-1 is continuous at ⟨x,v⟩
4. For any x in M, we may choose local trivialization e₁ and e₂ for E₁, E₂ at x. We show that F is continuous on π₂⁻¹(U) where U = e₁.sournce ∩ e₂.source is an open set in M.
5. Note that (e₂ ∘ F ∘ e₁.symm) : U × F₁ → U × F₂ must be continuous and takes the form ⟨q,v⟩ ↦ ⟨q, A(q) v) where A : U → (F₁ ≃ F₂) is continuous.
6. Therefore, (e₁ ∘ F.inv ∘ e₂.symm) : U × F₂ → U × F₁ is cotinuous since it takes the form ⟨q, v⟩ ↦ ⟨q, A⁻¹(q) v⟩ and the inverse map on matrices is smooth (this requires assuming that F₁, F₂ are finite dimesnional)
7. Thus, F.inv is continuous at ⟨x,v⟩ since e₁ and e₂ are homeomorphisms around ⟨x,v⟩
-/
/-- A bijective vector bundle map is a vector bundle equivalence. The inverse total space
map is continuous by the open mapping theorem (a continuous bijection from a compact space,
or more generally by the structure of fiber bundle total spaces), and the fiberwise linear
maps are promoted to linear equivalences by the fiberwise bijectivity. -/
noncomputable def VectorBundleMap.toVectorBundleEquiv {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜]
    {B : Type*} [TopologicalSpace B]
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
    {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
    [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
    {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
    (f : VectorBundleMap 𝕜 F₁ E₁ F₂ E₂)
    (hid : f.baseMap = _root_.id)
    (hbij : Function.Bijective f.toFun) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂ := by
  -- Destructure and subst
  obtain ⟨bm, Φ, hΦ_cont, φ, hcompat⟩ := f
  simp only at hid; subst hid
  change Function.Bijective Φ at hbij
  have hcompat' : ∀ x v, Φ ⟨x, v⟩ = ⟨x, φ x v⟩ :=
    fun x v => by simpa [_root_.id] using hcompat x v
  -- φ bijectivity
  have hφ_bij : ∀ x, Function.Bijective (φ x) := by
    intro x; exact ⟨fun v w hvw =>
      TotalSpace.mk_inj.mp (hbij.1 (by rw [hcompat' x v, hcompat' x w, hvw])),
      fun w => by
        obtain ⟨⟨y, v⟩, hv⟩ := hbij.2 (⟨x, w⟩ : TotalSpace F₂ E₂)
        rw [hcompat' y v] at hv
        have hy : y = x := congrArg TotalSpace.proj hv
        subst hy
        exact ⟨v, TotalSpace.mk_inj.mp hv⟩⟩
  set Φ_equiv := Equiv.ofBijective Φ hbij
  have hproj : ∀ p, (Φ_equiv.symm p).proj = p.proj := fun p => by
    have h1 : Φ (Φ_equiv.symm p) = p := Φ_equiv.apply_symm_apply p
    rw [hcompat' (Φ_equiv.symm p).proj (Φ_equiv.symm p).snd] at h1
    exact congrArg TotalSpace.proj h1
  have hcompat_inv : ∀ x w, Φ_equiv.symm ⟨x, w⟩ =
      ⟨x, ((LinearEquiv.ofBijective (φ x) (hφ_bij x)).symm w : E₁ x)⟩ := by
    intro x w; apply Φ_equiv.injective; rw [Φ_equiv.apply_symm_apply]
    change ⟨x, w⟩ = Φ ⟨x, (LinearEquiv.ofBijective (φ x) (hφ_bij x)).symm w⟩
    rw [hcompat']; congr 1
    exact ((LinearEquiv.ofBijective (φ x) (hφ_bij x)).apply_symm_apply w).symm
  -- Φ⁻¹ continuity
  have hΦ_inv_cont : Continuous Φ_equiv.symm := by
    rw [continuous_iff_continuousAt]; intro ⟨x, w⟩
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨by simp only [hproj]; exact (FiberBundle.continuous_proj F₂ E₂).continuousAt, ?_⟩
    simp only [hproj]
    set e₁ := trivializationAt F₁ E₁ x; set e₂ := trivializationAt F₂ E₂ x
    have hx₁ := mem_baseSet_trivializationAt F₁ E₁ x
    have hx₂ := mem_baseSet_trivializationAt F₂ E₂ x
    have he₂_source : ⟨x, w⟩ ∈ e₂.source := e₂.mem_source.mpr hx₂
    set G : B × F₂ → B × F₁ := fun p =>
      e₁ (Φ_equiv.symm (e₂.toOpenPartialHomeomorph.symm p))
    classical
    set A : B → (F₁ →L[𝕜] F₂) := fun q =>
      if hq : q ∈ e₁.baseSet ∧ q ∈ e₂.baseSet then
        LinearMap.toContinuousLinearMap
          ((e₂.continuousLinearEquivAt 𝕜 q hq.2).toLinearMap.comp
            ((φ q).comp (e₁.continuousLinearEquivAt 𝕜 q hq.1).symm.toLinearMap))
      else 0
    -- A agrees with the trivialized forward map on the overlap
    have hA_apply : ∀ (q : B) (hq₁ : q ∈ e₁.baseSet) (hq₂ : q ∈ e₂.baseSet) (v : F₁),
        A q v = (e₂ (Φ (e₁.toOpenPartialHomeomorph.symm (q, v)))).2 := by
      intro q hq₁ hq₂ v
      simp only [A, dif_pos (show q ∈ e₁.baseSet ∧ q ∈ e₂.baseSet from ⟨hq₁, hq₂⟩),
        LinearMap.coe_toContinuousLinearMap, LinearMap.comp_apply,
        ContinuousLinearEquiv.coe_toLinearEquiv]
      conv_rhs =>
        rw [e₁.symm_apply_eq_mk_continuousLinearEquivAt_symm (R := 𝕜) q hq₁ v,
            hcompat',
            congrArg Prod.snd
              (e₂.apply_eq_prod_continuousLinearEquivAt 𝕜 q hq₂ _)]
      rfl
    -- A is continuous at x (pointwise → operator via basis embedding)
    have hA_cont : ContinuousAt A x := by
      have hAv_cont : ∀ v, ContinuousAt (fun q => A q v) x := by
        intro v
        suffices ContinuousAt
            (fun q => (e₂ (Φ (e₁.toOpenPartialHomeomorph.symm (q, v)))).2) x by
          exact this.congr (Filter.eventually_of_mem
            (IsOpen.mem_nhds (e₁.open_baseSet.inter e₂.open_baseSet) ⟨hx₁, hx₂⟩)
            fun q ⟨hq₁, hq₂⟩ => (hA_apply q hq₁ hq₂ v).symm)
        have he₁_symm_cont : ContinuousAt
            (fun q => e₁.toOpenPartialHomeomorph.symm (q, v)) x :=
          (e₁.toOpenPartialHomeomorph.continuousOn_symm.continuousAt
            (e₁.toOpenPartialHomeomorph.open_target.mem_nhds
              (by rw [e₁.target_eq]; exact ⟨hx₁, Set.mem_univ _⟩))).comp
            (ContinuousAt.prodMk continuousAt_id continuousAt_const)
        apply ContinuousAt.snd
        exact (e₂.continuousOn.continuousAt (e₂.open_source.mem_nhds (by
          rw [e₂.mem_source, congrArg TotalSpace.proj (hcompat' _ _),
            e₁.proj_symm_apply (by rw [e₁.target_eq]; exact ⟨hx₁, Set.mem_univ _⟩)]
          exact hx₂))).comp (hΦ_cont.continuousAt.comp he₁_symm_cont)
      haveI : FiniteDimensional 𝕜 (F₁ →L[𝕜] F₂) := ContinuousLinearMap.finiteDimensional
      let bF₁ := Module.finBasis 𝕜 F₁
      let evalBasis : (F₁ →L[𝕜] F₂) →L[𝕜] (Fin (Module.finrank 𝕜 F₁) → F₂) :=
        ContinuousLinearMap.pi (fun i => ContinuousLinearMap.apply 𝕜 F₂ (bF₁ i))
      have evalBasis_inj : Function.Injective evalBasis := fun L₁ L₂ h => by
        ext v; rw [← bF₁.sum_equivFun v]; simp only [map_sum, map_smul]
        congr 1; ext i; exact congrArg _ (congrFun h i)
      rw [(LinearMap.isClosedEmbedding_of_injective (f := evalBasis.toLinearMap)
        (LinearMap.ker_eq_bot.mpr evalBasis_inj)).isEmbedding.continuousAt_iff]
      exact continuousAt_pi.mpr fun i => hAv_cont (bF₁ i)
    -- A(q) is invertible on the overlap — it's a composition of three equivs
    have hA_inv_at : ∀ q, q ∈ e₁.baseSet ∩ e₂.baseSet → (A q).IsInvertible := by
      intro q ⟨hq₁', hq₂'⟩
      -- On the overlap, A q = toCLM (e₂.CLE ∘ₗ φ q ∘ₗ (e₁.CLE)⁻¹)
      -- which is the CLM of a composition of linear equivs, hence invertible.
      simp only [A, dif_pos (show q ∈ e₁.baseSet ∧ q ∈ e₂.baseSet from ⟨hq₁', hq₂'⟩)]
      -- The linear map is a composition of equivs, so it's bijective
      have hbij_lm : Function.Bijective
          ((e₂.continuousLinearEquivAt 𝕜 q hq₂').toLinearMap.comp
            ((φ q).comp (e₁.continuousLinearEquivAt 𝕜 q hq₁').symm.toLinearMap)) :=
        ((e₁.continuousLinearEquivAt 𝕜 q hq₁').symm.toLinearEquiv.trans
          (LinearEquiv.ofBijective (φ q) (hφ_bij q)) |>.trans
          (e₂.continuousLinearEquivAt 𝕜 q hq₂').toLinearEquiv).bijective
      exact ⟨(LinearEquiv.ofBijective _ hbij_lm).toContinuousLinearEquiv, by ext; rfl⟩
    haveI : CompleteSpace F₁ := FiniteDimensional.complete 𝕜 F₁
    have hA_inv_cont : ContinuousAt (ContinuousLinearMap.inverse ∘ A) x :=
      ((hA_inv_at x ⟨hx₁, hx₂⟩).contDiffAt_map_inverse (n := 0)).continuousAt |>.comp
        hA_cont
    -- (q,v) ↦ (q, inverse(A q) v) is continuous
    have hNice_cont : ContinuousAt
        (fun p : B × F₂ => (p.1, (ContinuousLinearMap.inverse (A p.1)) p.2))
        (e₂ ⟨x, w⟩) := by
      apply ContinuousAt.prodMk continuousAt_fst
      have h1 : ContinuousAt (fun p : B × F₂ =>
          ContinuousLinearMap.inverse (A p.1)) (e₂ ⟨x, w⟩) := by
        change ContinuousAt ((ContinuousLinearMap.inverse ∘ A) ∘ Prod.fst) (e₂ ⟨x, w⟩)
        apply ContinuousAt.comp _ continuousAt_fst
        convert hA_inv_cont using 1
        exact e₂.coe_fst' hx₂
      exact h1.clm_apply continuousAt_snd
    -- G equals the nice function near e₂ ⟨x,w⟩
    have hG_eq : (fun p : B × F₂ => (p.1, (ContinuousLinearMap.inverse (A p.1)) p.2))
        =ᶠ[nhds (e₂ ⟨x, w⟩)] G := by
      have hU : (e₁.baseSet ∩ e₂.baseSet) ×ˢ (Set.univ : Set F₂) ∈ nhds (e₂ ⟨x, w⟩) :=
        IsOpen.mem_nhds (e₁.open_baseSet.inter e₂.open_baseSet |>.prod isOpen_univ)
          ⟨⟨e₂.coe_fst he₂_source ▸ hx₁,
            e₂.coe_fst he₂_source ▸ hx₂⟩, Set.mem_univ _⟩
      filter_upwards [hU] with ⟨q, v⟩ ⟨⟨hq₁, hq₂⟩, _⟩
      have hA_inv_q := hA_inv_at q ⟨hq₁, hq₂⟩
      have hAG : ∀ v', A q ((G (q, v')).2) = v' := by
        intro v'
        set p := Φ_equiv.symm (e₂.toOpenPartialHomeomorph.symm (q, v'))
        have hp_proj : p.proj = q :=
          hproj _ |>.trans (e₂.proj_symm_apply (e₂.mem_target.mpr hq₂))
        have hp_mem : p ∈ e₁.source := e₁.mem_source.mpr (hp_proj ▸ hq₁)
        rw [hA_apply q hq₁ hq₂,
            show e₁.toOpenPartialHomeomorph.symm (q, (e₁ p).2) = p from by
              conv_rhs => rw [← e₁.toOpenPartialHomeomorph.left_inv hp_mem]
              congr 1; exact Prod.ext (e₁.coe_fst hp_mem ▸ hp_proj).symm rfl,
            show Φ p = e₂.toOpenPartialHomeomorph.symm (q, v') from
              Φ_equiv.apply_symm_apply _,
            congrArg Prod.snd (e₂.apply_symm_apply' hq₂)]
      ext
      · -- fst: G preserves base
        simp only [G]
        have hΦs := (hproj _).trans
          (e₂.proj_symm_apply (by rw [e₂.target_eq]; exact ⟨hq₂, Set.mem_univ _⟩))
        exact (e₁.coe_fst (e₁.mem_source.mpr (hΦs.symm ▸ hq₁)) |>.trans hΦs).symm
      · exact hA_inv_q.inverse_apply_eq.mpr (hAG v).symm
    -- Factor as Prod.snd ∘ G ∘ e₂
    apply ContinuousAt.congr (continuous_snd.continuousAt.comp
      ((hNice_cont.congr hG_eq).comp (e₂.toOpenPartialHomeomorph.continuousAt he₂_source)))
    filter_upwards [e₂.open_source.mem_nhds he₂_source] with p hp
    simp only [Function.comp, G]
    rw [show e₂.toOpenPartialHomeomorph.symm (e₂ p) = p from
      e₂.toOpenPartialHomeomorph.left_inv hp]
  exact {
    baseMap := _root_.id
    toHomeomorph := ⟨Equiv.ofBijective Φ hbij, hΦ_cont, hΦ_inv_cont⟩
    fiberLinearEquiv := fun x => LinearEquiv.ofBijective (φ x) (hφ_bij x)
    fiber_compat := fun x v => hcompat' x v
  }

/-! ## `C^n` vector bundle equivalences -/

open scoped Manifold

/-- A `C^n` vector bundle equivalence between bundles `E₁` over `B₁` and `E₂` over `B₂`. -/
structure ContMDiffVectorBundleEquiv
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    {HB : Type*} [TopologicalSpace HB]
    (IB : ModelWithCorners 𝕜 EB HB)
    (n : WithTop ℕ∞)
    {B₁ : Type*} [TopologicalSpace B₁] [ChartedSpace HB B₁]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (E₁ : B₁ → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
    [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (E₂ : B₂ → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] where
  baseMap : B₁ → B₂
  toDiffeomorph : Diffeomorph (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂))
    (TotalSpace F₁ E₁) (TotalSpace F₂ E₂) n
  fiberLinearEquiv : ∀ x : B₁, E₁ x ≃ₗ[𝕜] E₂ (baseMap x)
  fiber_compat : ∀ (x : B₁) (v : E₁ x),
    toDiffeomorph ⟨x, v⟩ = ⟨baseMap x, fiberLinearEquiv x v⟩

namespace ContMDiffVectorBundleEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {n : WithTop ℕ∞}
  {B₁ : Type*} [TopologicalSpace B₁] [ChartedSpace HB B₁]
  {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
  {B₃ : Type*} [TopologicalSpace B₃] [ChartedSpace HB B₃]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₃ : B₃ → Type*} [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)] [∀ x, TopologicalSpace (E₃ x)]
  [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]

/-- Construct a `ContMDiffVectorBundleEquiv` without specifying the base map, deriving it as
`fun x => (Φ ⟨x, 0⟩).proj`. -/
def mk'
    (Φ : Diffeomorph (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂))
      (TotalSpace F₁ E₁) (TotalSpace F₂ E₂) n)
    (φ : ∀ x : B₁, E₁ x ≃ₗ[𝕜] E₂ ((Φ ⟨x, 0⟩).proj))
    (hcompat : ∀ (x : B₁) (v : E₁ x),
      Φ ⟨x, v⟩ = ⟨(Φ ⟨x, 0⟩).proj, φ x v⟩) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂ where
  baseMap x := (Φ ⟨x, 0⟩).proj
  toDiffeomorph := Φ
  fiberLinearEquiv := φ
  fiber_compat := hcompat

@[ext]
theorem ext (A B : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (h : A.toDiffeomorph = B.toDiffeomorph) : A = B := by
  obtain ⟨f_A, Φ_A, φ_A, hA⟩ := A
  obtain ⟨f_B, Φ_B, φ_B, hB⟩ := B
  simp only at h; subst h
  have hf : f_A = f_B := by
    ext x
    have h₁ := hA x 0; have h₂ := hB x 0
    simp only [map_zero] at h₁ h₂
    rw [h₁] at h₂; exact congrArg TotalSpace.proj h₂
  subst hf; congr 1
  ext x v
  have h₁ := hA x v; rw [hB] at h₁
  exact TotalSpace.mk_inj.mp h₁.symm

theorem baseMap_eq (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) (x : B₁) :
    e.baseMap x = (e.toDiffeomorph ⟨x, 0⟩).proj := by
  simp [e.fiber_compat, map_zero]

/-- The base map of a `C^n` vector bundle equivalence is bijective. -/
theorem baseMapBijective (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    Function.Bijective e.baseMap := by
  constructor
  · intro x₁ x₂ h
    have h₁ := e.fiber_compat x₁ 0
    have h₂ := e.fiber_compat x₂ 0
    simp only [map_zero] at h₁ h₂
    have hinj := e.toDiffeomorph.injective (h₁.trans (by rw [h]) |>.trans h₂.symm)
    exact congrArg TotalSpace.proj hinj
  · intro y
    obtain ⟨⟨x, v⟩, hxv⟩ := e.toDiffeomorph.surjective ⟨y, 0⟩
    have h := e.fiber_compat x v
    have : (e.toDiffeomorph.toEquiv ⟨x, v⟩) = e.toDiffeomorph ⟨x, v⟩ := rfl
    rw [this, h] at hxv
    exact ⟨x, congrArg TotalSpace.proj hxv⟩

def toVectorBundleEquiv (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂ where
  baseMap := e.baseMap
  toHomeomorph := e.toDiffeomorph.toHomeomorph
  fiberLinearEquiv := e.fiberLinearEquiv
  fiber_compat x v := e.fiber_compat x v

@[simp]
theorem proj_eq (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (p : TotalSpace F₁ E₁) : (e.toDiffeomorph p).proj = e.baseMap p.proj := by
  obtain ⟨x, v⟩ := p; simp [e.fiber_compat]

@[simp]
theorem toDiffeomorph_apply (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (x : B₁) (v : E₁ x) :
    e.toDiffeomorph ⟨x, v⟩ = ⟨e.baseMap x, e.fiberLinearEquiv x v⟩ :=
  e.fiber_compat x v

def refl : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₁ E₁ where
  baseMap := _root_.id
  toDiffeomorph := Diffeomorph.refl (IB.prod 𝓘(𝕜, F₁)) (TotalSpace F₁ E₁) n
  fiberLinearEquiv x := LinearEquiv.refl 𝕜 (E₁ x)
  fiber_compat _ _ := rfl

def symm (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₂ E₂ F₁ E₁ where
  baseMap y := (e.toDiffeomorph.symm ⟨y, 0⟩).proj
  toDiffeomorph := e.toDiffeomorph.symm
  fiberLinearEquiv y :=
    let x := (e.toDiffeomorph.symm ⟨y, 0⟩).proj
    have hx : e.baseMap x = y := by
      have := e.proj_eq (e.toDiffeomorph.symm ⟨y, 0⟩)
      simp [e.toDiffeomorph.apply_symm_apply] at this; exact this.symm
    (hx ▸ e.fiberLinearEquiv x).symm
  fiber_compat y v := by exact e.toVectorBundleEquiv.symm.fiber_compat y v

def trans (e₁₂ : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (e₂₃ : ContMDiffVectorBundleEquiv 𝕜 IB n F₂ E₂ F₃ E₃) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₃ E₃ where
  baseMap := e₂₃.baseMap ∘ e₁₂.baseMap
  toDiffeomorph := e₁₂.toDiffeomorph.trans e₂₃.toDiffeomorph
  fiberLinearEquiv x :=
    (e₁₂.fiberLinearEquiv x).trans (e₂₃.fiberLinearEquiv (e₁₂.baseMap x))
  fiber_compat x v := by
    simp only [Diffeomorph.coe_trans, Function.comp_apply, e₁₂.fiber_compat, e₂₃.fiber_compat,
      LinearEquiv.trans_apply]

end ContMDiffVectorBundleEquiv

/-! ## `C^n` vector bundle maps -/

/-- A `C^n` vector bundle map from `E₁` over `B₁` to `E₂` over `B₂`. -/
structure ContMDiffVectorBundleMap
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    {HB : Type*} [TopologicalSpace HB]
    (IB : ModelWithCorners 𝕜 EB HB)
    (n : WithTop ℕ∞)
    {B₁ : Type*} [TopologicalSpace B₁] [ChartedSpace HB B₁]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (E₁ : B₁ → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
    [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (E₂ : B₂ → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] where
  baseMap : B₁ → B₂
  toFun : TotalSpace F₁ E₁ → TotalSpace F₂ E₂
  contMDiff_toFun : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n toFun
  fiberLinearMap : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)
  fiber_compat : ∀ (x : B₁) (v : E₁ x),
    toFun ⟨x, v⟩ = ⟨baseMap x, fiberLinearMap x v⟩

namespace ContMDiffVectorBundleMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {n : WithTop ℕ∞}
  {B₁ : Type*} [TopologicalSpace B₁] [ChartedSpace HB B₁]
  {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
  {B₃ : Type*} [TopologicalSpace B₃] [ChartedSpace HB B₃]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₃ : B₃ → Type*} [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)] [∀ x, TopologicalSpace (E₃ x)]
  [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]

/-- Construct a `ContMDiffVectorBundleMap` without specifying the base map, deriving it as
`fun x => (Φ ⟨x, 0⟩).proj`. -/
def mk'
    (Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂)
    (hΦ : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n Φ)
    (φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ ((Φ ⟨x, 0⟩).proj))
    (hcompat : ∀ (x : B₁) (v : E₁ x),
      Φ ⟨x, v⟩ = ⟨(Φ ⟨x, 0⟩).proj, φ x v⟩) :
    ContMDiffVectorBundleMap 𝕜 IB n F₁ E₁ F₂ E₂ where
  baseMap x := (Φ ⟨x, 0⟩).proj
  toFun := Φ
  contMDiff_toFun := hΦ
  fiberLinearMap := φ
  fiber_compat := hcompat

@[ext]
theorem ext (A B : ContMDiffVectorBundleMap 𝕜 IB n F₁ E₁ F₂ E₂)
    (h : A.toFun = B.toFun) : A = B := by
  obtain ⟨f_A, Φ_A, _, φ_A, hA⟩ := A
  obtain ⟨f_B, Φ_B, _, φ_B, hB⟩ := B
  simp only at h; subst h
  have hf : f_A = f_B := by
    ext x
    have h₁ := hA x 0; have h₂ := hB x 0
    simp only [map_zero] at h₁ h₂
    rw [h₁] at h₂; exact congrArg TotalSpace.proj h₂
  subst hf; congr 1
  ext x v
  have h₁ := hA x v; rw [hB] at h₁
  exact TotalSpace.mk_inj.mp h₁.symm

theorem baseMap_eq (f : ContMDiffVectorBundleMap 𝕜 IB n F₁ E₁ F₂ E₂) (x : B₁) :
    f.baseMap x = (f.toFun ⟨x, 0⟩).proj := by
  simp [f.fiber_compat, map_zero]

/-- The base map of a `C^n` vector bundle map is `C^n`, since it factors as
`π₂ ∘ Φ ∘ zeroSection`. -/
theorem baseMapContMDiff [ContMDiffVectorBundle n F₁ E₁ IB]
    (f : ContMDiffVectorBundleMap 𝕜 IB n F₁ E₁ F₂ E₂) :
    ContMDiff IB IB n f.baseMap := by
  have h : f.baseMap = TotalSpace.proj ∘ f.toFun ∘ zeroSection F₁ E₁ := by
    ext x; simp [baseMap_eq, zeroSection]
  rw [h]
  have h₁ : ContMDiff IB (IB.prod 𝓘(𝕜, F₁)) n (zeroSection F₁ E₁) :=
    contMDiff_zeroSection 𝕜 E₁
  have h₂ : ContMDiff (IB.prod 𝓘(𝕜, F₂)) IB n (TotalSpace.proj (F := F₂) (E := E₂)) :=
    (contMDiff_proj E₂).of_le le_top
  exact h₂.comp (f.contMDiff_toFun.comp h₁)

def toVectorBundleMap (f : ContMDiffVectorBundleMap 𝕜 IB n F₁ E₁ F₂ E₂) :
    VectorBundleMap 𝕜 F₁ E₁ F₂ E₂ where
  baseMap := f.baseMap
  toFun := f.toFun
  continuous_toFun := f.contMDiff_toFun.continuous
  fiberLinearMap := f.fiberLinearMap
  fiber_compat x v := f.fiber_compat x v

@[simp]
theorem proj_eq (f : ContMDiffVectorBundleMap 𝕜 IB n F₁ E₁ F₂ E₂)
    (p : TotalSpace F₁ E₁) :
    (f.toFun p).proj = f.baseMap p.proj := by
  obtain ⟨x, v⟩ := p; simp [f.fiber_compat]

@[simp]
theorem toFun_apply (f : ContMDiffVectorBundleMap 𝕜 IB n F₁ E₁ F₂ E₂)
    (x : B₁) (v : E₁ x) :
    f.toFun ⟨x, v⟩ = ⟨f.baseMap x, f.fiberLinearMap x v⟩ :=
  f.fiber_compat x v

def id : ContMDiffVectorBundleMap 𝕜 IB n F₁ E₁ F₁ E₁ where
  baseMap := _root_.id
  toFun := _root_.id
  contMDiff_toFun := contMDiff_id
  fiberLinearMap _ := LinearMap.id
  fiber_compat _ _ := rfl

def comp (g : ContMDiffVectorBundleMap 𝕜 IB n F₂ E₂ F₃ E₃)
    (f : ContMDiffVectorBundleMap 𝕜 IB n F₁ E₁ F₂ E₂) :
    ContMDiffVectorBundleMap 𝕜 IB n F₁ E₁ F₃ E₃ where
  baseMap := g.baseMap ∘ f.baseMap
  toFun := g.toFun ∘ f.toFun
  contMDiff_toFun := g.contMDiff_toFun.comp f.contMDiff_toFun
  fiberLinearMap x := (g.fiberLinearMap (f.baseMap x)).comp (f.fiberLinearMap x)
  fiber_compat x v := by
    simp only [Function.comp_apply, f.fiber_compat, g.fiber_compat, LinearMap.comp_apply]

def ofEquiv (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    ContMDiffVectorBundleMap 𝕜 IB n F₁ E₁ F₂ E₂ where
  baseMap := e.baseMap
  toFun := e.toDiffeomorph
  contMDiff_toFun := e.toDiffeomorph.contMDiff
  fiberLinearMap x := (e.fiberLinearEquiv x).toLinearMap
  fiber_compat x v := e.fiber_compat x v

/-- A bijective `C^n` vector bundle map over the identity is a `C^n` vector bundle equiv. -/
noncomputable def toContMDiffVectorBundleEquiv
    {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
    {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
    [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
    [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
    [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]
    (f : ContMDiffVectorBundleMap 𝕜 IB n F₁ E₁ F₂ E₂)
    (hid : f.baseMap = _root_.id)
    (hbij : Function.Bijective f.toFun) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂ := by
  -- Same structure as VectorBundleMap.toVectorBundleEquiv, with ContMDiff replacing Continuous
  obtain ⟨bm, Φ, hΦ_smooth, φ, hcompat⟩ := f
  simp only at hid; subst hid
  change Function.Bijective Φ at hbij
  have hcompat' : ∀ x v, Φ ⟨x, v⟩ = ⟨x, φ x v⟩ :=
    fun x v => by simpa [_root_.id] using hcompat x v
  have hφ_bij : ∀ x, Function.Bijective (φ x) := by
    intro x; exact ⟨fun v w hvw =>
      TotalSpace.mk_inj.mp (hbij.1 (by rw [hcompat' x v, hcompat' x w, hvw])),
      fun w => by
        obtain ⟨⟨y, v⟩, hv⟩ := hbij.2 (⟨x, w⟩ : TotalSpace F₂ E₂)
        rw [hcompat' y v] at hv
        have hy : y = x := congrArg TotalSpace.proj hv
        subst hy
        exact ⟨v, TotalSpace.mk_inj.mp hv⟩⟩
  set Φ_equiv := Equiv.ofBijective Φ hbij
  have hproj : ∀ p, (Φ_equiv.symm p).proj = p.proj := fun p => by
    have h1 : Φ (Φ_equiv.symm p) = p := Φ_equiv.apply_symm_apply p
    rw [hcompat' (Φ_equiv.symm p).proj (Φ_equiv.symm p).snd] at h1
    exact congrArg TotalSpace.proj h1
  have hcompat_inv : ∀ x w, Φ_equiv.symm ⟨x, w⟩ =
      ⟨x, ((LinearEquiv.ofBijective (φ x) (hφ_bij x)).symm w : E₁ x)⟩ := by
    intro x w; apply Φ_equiv.injective; rw [Φ_equiv.apply_symm_apply]
    change ⟨x, w⟩ = Φ ⟨x, (LinearEquiv.ofBijective (φ x) (hφ_bij x)).symm w⟩
    rw [hcompat']; congr 1
    exact ((LinearEquiv.ofBijective (φ x) (hφ_bij x)).apply_symm_apply w).symm
  -- Φ⁻¹ is ContMDiff: same local trivialization argument as the topological case,
  -- but using contMDiffAt_map_inverse (which gives ContDiff n, not just Continuous)
  -- and Bundle.contMDiffAt_totalSpace instead of FiberBundle.continuousAt_totalSpace.
  have hΦ_inv_smooth : ContMDiff (IB.prod 𝓘(𝕜, F₂)) (IB.prod 𝓘(𝕜, F₁)) n
      Φ_equiv.symm := by
    intro ⟨x, w⟩
    rw [Bundle.contMDiffAt_totalSpace]
    refine ⟨by simp only [hproj]; exact (contMDiff_proj E₂).contMDiffAt, ?_⟩
    simp only [hproj]
    set e₁ := trivializationAt F₁ E₁ x; set e₂ := trivializationAt F₂ E₂ x
    have hx₁ := mem_baseSet_trivializationAt F₁ E₁ x
    have hx₂ := mem_baseSet_trivializationAt F₂ E₂ x
    have he₂_source : ⟨x, w⟩ ∈ e₂.source := e₂.mem_source.mpr hx₂
    set G : B × F₂ → B × F₁ := fun p =>
      e₁ (Φ_equiv.symm (e₂.toOpenPartialHomeomorph.symm p))
    classical
    set A : B → (F₁ →L[𝕜] F₂) := fun q =>
      if hq : q ∈ e₁.baseSet ∧ q ∈ e₂.baseSet then
        LinearMap.toContinuousLinearMap
          ((e₂.continuousLinearEquivAt 𝕜 q hq.2).toLinearMap.comp
            ((φ q).comp (e₁.continuousLinearEquivAt 𝕜 q hq.1).symm.toLinearMap))
      else 0
    have hA_apply : ∀ (q : B) (hq₁ : q ∈ e₁.baseSet) (hq₂ : q ∈ e₂.baseSet) (v : F₁),
        A q v = (e₂ (Φ (e₁.toOpenPartialHomeomorph.symm (q, v)))).2 := by
      intro q hq₁ hq₂ v
      simp only [A, dif_pos (show q ∈ e₁.baseSet ∧ q ∈ e₂.baseSet from ⟨hq₁, hq₂⟩),
        LinearMap.coe_toContinuousLinearMap, LinearMap.comp_apply,
        ContinuousLinearEquiv.coe_toLinearEquiv]
      conv_rhs =>
        rw [e₁.symm_apply_eq_mk_continuousLinearEquivAt_symm (R := 𝕜) q hq₁ v,
            hcompat',
            congrArg Prod.snd
              (e₂.apply_eq_prod_continuousLinearEquivAt 𝕜 q hq₂ _)]
      rfl
    -- A is ContMDiff at x (pointwise ContMDiff → operator ContMDiff via basis embedding)
    have hA_contMDiff : ContMDiffAt IB 𝓘(𝕜, F₁ →L[𝕜] F₂) n A x := by
      -- Part 1: Each q ↦ A q v is ContMDiffAt
      have hAv : ∀ v, ContMDiffAt IB 𝓘(𝕜, F₂) n (fun q => A q v) x := by
        intro v
        suffices h : ContMDiffAt IB 𝓘(𝕜, F₂) n
            (fun q => (e₂ (Φ (e₁.toOpenPartialHomeomorph.symm (q, v)))).2) x from
          h.congr_of_eventuallyEq (Filter.eventually_of_mem
            (IsOpen.mem_nhds (e₁.open_baseSet.inter e₂.open_baseSet) ⟨hx₁, hx₂⟩)
            fun q ⟨hq₁, hq₂⟩ => hA_apply q hq₁ hq₂ v)
        -- Composition: Prod.snd ∘ e₂ ∘ Φ ∘ e₁.symm(·, v)
        -- Step 1: e₁.symm(·, v) is ContMDiffAt (smooth triv symm)
        have he₁_tgt : (x, v) ∈ e₁.target := by
          rw [e₁.target_eq]; exact ⟨hx₁, Set.mem_univ _⟩
        have he₁_symm : ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁)) n
            (fun q => e₁.toOpenPartialHomeomorph.symm (q, v)) x := by
          have h1 := e₁.contMDiffOn_symm (n := n) (IB := IB) |>.contMDiffAt
            (e₁.toOpenPartialHomeomorph.open_target.mem_nhds he₁_tgt)
          have h2 : ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁)) n (fun q => (q, v)) x :=
            contMDiffAt_id.prodMk contMDiffAt_const
          exact h1.comp x h2
        -- Step 2: Φ(e₁.symm(x, v)) ∈ e₂.source
        have hmem : Φ (e₁.toOpenPartialHomeomorph.symm (x, v)) ∈ e₂.source := by
          rw [e₂.mem_source, congrArg TotalSpace.proj (hcompat' _ _),
            e₁.proj_symm_apply he₁_tgt]; exact hx₂
        -- Step 3: Compose e₂ ∘ Φ ∘ e₁.symm(·, v) then take .2
        -- Compose step by step using contMDiffAt_of_contMDiffAt_comp pattern
        -- Φ is ContMDiff at e₁.symm(x,v), compose with he₁_symm
        have hΦ_at : ContMDiffAt (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n Φ
            (e₁.toOpenPartialHomeomorph.symm (x, v)) := hΦ_smooth.contMDiffAt
        -- e₂ is ContMDiffAt at Φ(e₁.symm(x,v))
        have he₂_at : ContMDiffAt (IB.prod 𝓘(𝕜, F₂)) (IB.prod 𝓘(𝕜, F₂)) n e₂
            (Φ (e₁.toOpenPartialHomeomorph.symm (x, v))) :=
          e₂.contMDiffOn (n := n) (IB := IB) |>.contMDiffAt
            (e₂.open_source.mem_nhds hmem)
        -- Chain: (e₂ ∘ Φ) at e₁.symm(x,v), then compose with e₁.symm(·,v) at x
        have he₂Φ := he₂_at.comp _ hΦ_at  -- e₂ ∘ Φ at e₁.symm(x,v)
        exact (he₂Φ.comp x he₁_symm).snd
      -- Part 2: Pointwise ContMDiffAt → operator ContMDiffAt
      -- Use basis of F₁ to embed F₁ →L F₂ into (Fin d → F₂) via evaluation.
      -- The embedding is a CLM (hence ContDiff), and injective (hence closed embedding
      -- in finite dim). ContMDiffAt of the composition iff ContMDiffAt of the original.
      haveI : FiniteDimensional 𝕜 (F₁ →L[𝕜] F₂) := ContinuousLinearMap.finiteDimensional
      let bF₁ := Module.finBasis 𝕜 F₁
      let evalBasis : (F₁ →L[𝕜] F₂) →L[𝕜] (Fin (Module.finrank 𝕜 F₁) → F₂) :=
        ContinuousLinearMap.pi (fun i => ContinuousLinearMap.apply 𝕜 F₂ (bF₁ i))
      have evalBasis_inj : Function.Injective evalBasis := fun L₁ L₂ h => by
        ext v; rw [← bF₁.sum_equivFun v]; simp only [map_sum, map_smul]
        congr 1; ext i; exact congrArg _ (congrFun h i)
      have hEmbed := LinearMap.isClosedEmbedding_of_injective (f := evalBasis.toLinearMap)
        (LinearMap.ker_eq_bot.mpr evalBasis_inj)
      -- evalBasis ∘ A is ContMDiffAt (each component is hAv (bF₁ i))
      have hEA : ContMDiffAt IB 𝓘(𝕜, Fin _ → F₂) n (evalBasis ∘ A) x :=
        contMDiffAt_pi_space.mpr fun i => hAv (bF₁ i)
      -- A is ContMDiffAt since evalBasis is a ContDiff closed embedding
      -- evalBasis ∘ A = ContMDiffAt implies A = ContMDiffAt
      -- (evalBasis has a continuous linear left inverse since it's injective between fin-dim spaces)
      haveI : FiniteDimensional 𝕜 (Fin (Module.finrank 𝕜 F₁) → F₂) := inferInstance
      -- Build a continuous left inverse of evalBasis (injective CLM between fin-dim spaces)
      obtain ⟨gLM, hgLM⟩ := evalBasis.toLinearMap.exists_leftInverse_of_injective
        (evalBasis.ker_eq_bot_of_injective evalBasis_inj)
      let g : (Fin (Module.finrank 𝕜 F₁) → F₂) →L[𝕜] (F₁ →L[𝕜] F₂) :=
        ⟨gLM, LinearMap.continuous_of_finiteDimensional _⟩
      have hg : ∀ x, g (evalBasis x) = x := fun x => congr($(hgLM) x)
      -- A = g ∘ evalBasis ∘ A, and g is a CLM (hence ContDiff), so A is ContMDiffAt
      have : A = g ∘ evalBasis ∘ A := by funext q; exact (hg (A q)).symm
      rw [this]
      exact g.contDiff.contMDiff.contMDiffAt.comp _ hEA
    have hA_inv_at : ∀ q, q ∈ e₁.baseSet ∩ e₂.baseSet → (A q).IsInvertible := by
      intro q ⟨hq₁', hq₂'⟩
      simp only [A, dif_pos (show q ∈ e₁.baseSet ∧ q ∈ e₂.baseSet from ⟨hq₁', hq₂'⟩)]
      have hbij_lm : Function.Bijective
          ((e₂.continuousLinearEquivAt 𝕜 q hq₂').toLinearMap.comp
            ((φ q).comp (e₁.continuousLinearEquivAt 𝕜 q hq₁').symm.toLinearMap)) :=
        ((e₁.continuousLinearEquivAt 𝕜 q hq₁').symm.toLinearEquiv.trans
          (LinearEquiv.ofBijective (φ q) (hφ_bij q)) |>.trans
          (e₂.continuousLinearEquivAt 𝕜 q hq₂').toLinearEquiv).bijective
      exact ⟨(LinearEquiv.ofBijective _ hbij_lm).toContinuousLinearEquiv, by ext; rfl⟩
    haveI : CompleteSpace F₁ := FiniteDimensional.complete 𝕜 F₁
    -- inverse ∘ A is ContMDiffAt: inverse is ContDiff at A(x), A is ContMDiffAt
    have hA_inv_contMDiff : ContMDiffAt IB 𝓘(𝕜, F₂ →L[𝕜] F₁) n
        (ContinuousLinearMap.inverse ∘ A) x :=
      ((hA_inv_at x ⟨hx₁, hx₂⟩).contDiffAt_map_inverse (n := n)).contMDiffAt.comp x
        hA_contMDiff
    -- The fiber component equals inverse(A(e₂ p).1) (e₂ p).2 locally.
    -- Factor through e₂ and the Nice function.
    set G : B × F₂ → B × F₁ := fun p =>
      e₁ (Φ_equiv.symm (e₂.toOpenPartialHomeomorph.symm p))
    -- Nice function is ContMDiffAt
    have hNice_smooth : ContMDiffAt (IB.prod 𝓘(𝕜, F₂)) 𝓘(𝕜, F₁) n
        (fun p : B × F₂ => (ContinuousLinearMap.inverse (A p.1)) p.2)
        (e₂ ⟨x, w⟩) := by
      -- inverse ∘ A ∘ fst is ContMDiffAt at e₂ ⟨x,w⟩
      -- fst : B × F₂ → B is contMDiffAt, and (e₂ ⟨x,w⟩).1 = x
      have h1 : ContMDiffAt (IB.prod 𝓘(𝕜, F₂)) 𝓘(𝕜, F₂ →L[𝕜] F₁) n
          (fun p : B × F₂ => ContinuousLinearMap.inverse (A p.1)) (e₂ ⟨x, w⟩) := by
        show ContMDiffAt (IB.prod 𝓘(𝕜, F₂)) 𝓘(𝕜, F₂ →L[𝕜] F₁) n
          ((ContinuousLinearMap.inverse ∘ A) ∘ Prod.fst) (e₂ ⟨x, w⟩)
        apply ContMDiffAt.comp _ _ contMDiffAt_fst
        convert hA_inv_contMDiff using 1
        exact e₂.coe_fst' hx₂
      exact h1.clm_apply contMDiffAt_snd
    -- G equals Nice locally (same hG_eq as topological case)
    have hG_eq_nice : (fun p : B × F₂ =>
        (ContinuousLinearMap.inverse (A p.1)) p.2) =ᶠ[nhds (e₂ ⟨x, w⟩)]
        (fun p => (G p).2) := by
      have hU : (e₁.baseSet ∩ e₂.baseSet) ×ˢ (Set.univ : Set F₂) ∈
          nhds (e₂ ⟨x, w⟩) :=
        IsOpen.mem_nhds (e₁.open_baseSet.inter e₂.open_baseSet |>.prod isOpen_univ)
          ⟨⟨e₂.coe_fst he₂_source ▸ hx₁,
            e₂.coe_fst he₂_source ▸ hx₂⟩, Set.mem_univ _⟩
      filter_upwards [hU] with ⟨q, v⟩ ⟨⟨hq₁, hq₂⟩, _⟩
      have hA_inv_q := hA_inv_at q ⟨hq₁, hq₂⟩
      have hAG : ∀ v', A q ((G (q, v')).2) = v' := by
        intro v'
        set p := Φ_equiv.symm (e₂.toOpenPartialHomeomorph.symm (q, v'))
        have hp_proj : p.proj = q :=
          hproj _ |>.trans (e₂.proj_symm_apply (e₂.mem_target.mpr hq₂))
        have hp_mem : p ∈ e₁.source := e₁.mem_source.mpr (hp_proj ▸ hq₁)
        rw [hA_apply q hq₁ hq₂,
            show e₁.toOpenPartialHomeomorph.symm (q, (e₁ p).2) = p from by
              conv_rhs => rw [← e₁.toOpenPartialHomeomorph.left_inv hp_mem]
              congr 1; exact Prod.ext (e₁.coe_fst hp_mem ▸ hp_proj).symm rfl,
            show Φ p = e₂.toOpenPartialHomeomorph.symm (q, v') from
              Φ_equiv.apply_symm_apply _,
            congrArg Prod.snd (e₂.apply_symm_apply' hq₂)]
      exact hA_inv_q.inverse_apply_eq.mpr (hAG v).symm
    -- G.snd is ContMDiffAt at e₂ ⟨x,w⟩
    have hG_snd_smooth : ContMDiffAt (IB.prod 𝓘(𝕜, F₂)) 𝓘(𝕜, F₁) n
        (fun p => (G p).2) (e₂ ⟨x, w⟩) :=
      hNice_smooth.congr_of_eventuallyEq hG_eq_nice.symm
    have hΦ_inv_mem : Φ_equiv.symm ⟨x, w⟩ ∈ e₁.source := by
      rw [e₁.mem_source, hproj]; exact hx₁
    have he₂_smooth := (e₂.contMDiffOn (n := n) (IB := IB)).contMDiffAt
      (e₂.open_source.mem_nhds he₂_source)
    exact (hG_snd_smooth.comp _ he₂_smooth).congr_of_eventuallyEq
      (by filter_upwards [e₂.open_source.mem_nhds he₂_source] with p hp
          exact congrArg (fun q => (e₁ (Φ_equiv.symm q)).2)
            (e₂.toOpenPartialHomeomorph.left_inv hp).symm)
  exact {
    baseMap := _root_.id
    toDiffeomorph := {
      toEquiv := Φ_equiv
      contMDiff_toFun := hΦ_smooth
      contMDiff_invFun := hΦ_inv_smooth
    }
    fiberLinearEquiv := fun x => LinearEquiv.ofBijective (φ x) (hφ_bij x)
    fiber_compat := fun x v => hcompat' x v
  }

end ContMDiffVectorBundleMap
