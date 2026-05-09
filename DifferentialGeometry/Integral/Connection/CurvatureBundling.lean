import DifferentialGeometry.Integral.Connection.Curvature
import DifferentialGeometry.VectorBundle.Frame
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Bundled trilinear form of the section-level Riemann curvature

The section-level Riemann formula `riemannSec cov X Y Z x` descends, on smooth global sections,
to a continuous trilinear form on the fibres at `x`. This file packages that observation as
`riemannOp cov x : T_x M →L[ℝ] T_x M →L[ℝ] V x →L[ℝ] V x`, together with a well-definedness
lemma, the application formula on smooth sections, and the antisymmetry of the bundled form.

## Main definitions and theorems

* `riemannSec_eq_of_pointwise_eq` — well-definedness of `riemannSec` on smooth global sections
  modulo pointwise agreement at `x`.
* `riemannOp` — the bundled trilinear form `T_x M →L[ℝ] T_x M →L[ℝ] V x →L[ℝ] V x`.
* `riemannOp_apply_smooth` — application formula on smooth sections.
* `riemannOp_swap` — antisymmetry of the bundled form in the first two arguments.
-/

noncomputable section

open Bundle Manifold Set FiberBundle NormedSpace Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

section RiemannOpBundling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [FiniteDimensional ℝ F]

/-! ## Smoothness of the chosen extensions

The chosen smooth extensions `smoothExtensionTangent` / `smoothExtensionFiber` are smooth
since they are defined as the underlying functions of `Cₛ^∞`-sections. -/

/-- The smooth tangent extension is a smooth global section of the tangent bundle. -/
lemma smoothExtensionTangent_contMDiff (x : M) (v : TangentSpace I x) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothExtensionTangent (I := I) x v)) := by
  classical
  set σ : Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    (ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x v).choose with hσ
  change ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b => σ b))
  exact σ.contMDiff

/-- The smooth fibre extension is a smooth global section of `V`. -/
lemma smoothExtensionFiber_contMDiff (x : M) (u : V x) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (smoothExtensionFiber (I := I) (F := F) (V := V) x u)) := by
  classical
  set σ : Cₛ^(⊤ : ℕ∞)⟮I; F, V⟯ :=
    (ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := F) (V := V) x u).choose with hσ
  change ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (fun b => σ b))
  exact σ.contMDiff

/-- The smooth tangent extension is differentiable at every point. -/
lemma smoothExtensionTangent_mdiff (x : M) (v : TangentSpace I x) :
    MDiff (T% (smoothExtensionTangent (I := I) x v)) :=
  (smoothExtensionTangent_contMDiff (I := I) x v).mdifferentiable (by simp)

/-- The smooth fibre extension is differentiable at every point. -/
lemma smoothExtensionFiber_mdiff (x : M) (u : V x) :
    MDiff (T% (smoothExtensionFiber (I := I) (F := F) (V := V) x u)) :=
  (smoothExtensionFiber_contMDiff (I := I) (F := F) (V := V) x u).mdifferentiable (by simp)

/-! ## Smoothness of `covApply` from local hypotheses

A localized version of `covApply_mdifferentiableAt`: smoothness of `cov` (a `C^∞` covariant
derivative) plus smoothness of `Z` globally and `MDifferentiableAt` of `X` at `x` give
`MDifferentiableAt (T% (covApply cov X Z)) x`. The proof uses
`MDifferentiableAt.clm_bundle_apply` to combine the smoothness of the section
`b ↦ cov.toFun Z b` of `Hom(TM, V)` with the smoothness of `X` at `x`. -/

variable {cov : CovariantDerivative I F V}

lemma covApply_mdifferentiableAt_local
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hX : MDiffAt (T% X) x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% Z)) :
    MDiffAt (T% (covApply cov X Z)) x := by
  classical
  -- `b ↦ cov.toFun Z b` is a smooth section of `Hom(TM, V)`.
  have hop : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun b : M => (⟨b, cov.toFun Z b⟩ :
        TotalSpace (E →L[ℝ] F) fun b : M => TangentSpace I b →L[ℝ] V b)) Set.univ :=
    hcov.contMDiff.contMDiff (σ := Z) hZ.contMDiffOn
  have hop_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] F))
      (fun b : M => (⟨b, cov.toFun Z b⟩ :
        TotalSpace (E →L[ℝ] F) fun b : M => TangentSpace I b →L[ℝ] V b)) x :=
    (hop.contMDiffAt (Filter.univ_mem)).mdifferentiableAt (by simp)
  -- Apply `MDifferentiableAt.clm_bundle_apply` at `x` with `v = X` and `ϕ = cov.toFun Z`.
  exact hop_at.clm_bundle_apply (v := X) hX

/-! ## TensorialAt for the X- and Y-slots of `riemannSec`

For smooth global `Y, Z` and a `C^∞` covariant derivative `cov`, the operation
`riemannSec cov · Y Z x` is `TensorialAt I E · x`. This follows immediately from
`riemannSec_add_left` and `riemannSec_smul_left` together with the localized smoothness
of `covApply`. The Y-slot is symmetric. -/

/-- The X-slot operation `riemannSec cov · Y Z x` is `TensorialAt`, given smooth global
`Y` and a smooth `Z` of class `C^{∞+1}`. -/
lemma tensorialAt_X
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (_hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% Z)) :
    TensorialAt I E (Φ := fun X : Π b : M, TangentSpace I b => riemannSec cov X Y Z x) x where
  smul := by
    intro f X hf hX
    classical
    have hcXZ := covApply_mdifferentiableAt_local (cov := cov) hX hZ
    exact riemannSec_smul_left (cov := cov) (f := f) (X := X) (Y := Y) (Z := Z) (x := x)
      hf hX hcXZ
  add := by
    intro X X' hX hX'
    classical
    have hcXZ := covApply_mdifferentiableAt_local (cov := cov) hX hZ
    have hcX'Z := covApply_mdifferentiableAt_local (cov := cov) hX' hZ
    exact riemannSec_add_left (cov := cov) (X := X) (X' := X') (Y := Y) (Z := Z) (x := x)
      hX hX' hcXZ hcX'Z

/-- The Y-slot operation `riemannSec cov X · Z x` is `TensorialAt`, given smooth global
`X` and a smooth `Z` of class `C^{∞+1}`. -/
lemma tensorialAt_Y
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (_hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% Z)) :
    TensorialAt I E (Φ := fun Y : Π b : M, TangentSpace I b => riemannSec cov X Y Z x) x where
  smul := by
    intro f Y hf hY
    classical
    have hcYZ := covApply_mdifferentiableAt_local (cov := cov) hY hZ
    exact riemannSec_smul_right (cov := cov) (f := f) (X := X) (Y := Y) (Z := Z) (x := x)
      hf hY hcYZ
  add := by
    intro Y Y' hY hY'
    classical
    have hcYZ := covApply_mdifferentiableAt_local (cov := cov) hY hZ
    have hcY'Z := covApply_mdifferentiableAt_local (cov := cov) hY' hZ
    exact riemannSec_add_right (cov := cov) (X := X) (Y := Y) (Y' := Y') (Z := Z) (x := x)
      hY hY' hcYZ hcY'Z

/-! ## Pointwise dependence in the X- and Y-slots

By Mathlib's `TensorialAt.pointwise`, the X- and Y-slots of `riemannSec` (for fixed smooth
global `Y`, `Z` resp. `X`, `Z`) depend only on the value of the section at `x`. -/

lemma riemannSec_eq_of_X_eq_at
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X X' Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hX' : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X'))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% Z))
    (hXX' : X x = X' x) :
    riemannSec cov X Y Z x = riemannSec cov X' Y Z x := by
  classical
  have hX_at : MDiffAt (T% X) x := (hX x).mdifferentiableAt (by simp)
  have hX'_at : MDiffAt (T% X') x := (hX' x).mdifferentiableAt (by simp)
  exact (tensorialAt_X (cov := cov) (Y := Y) (Z := Z) hY hZ).pointwise hX_at hX'_at hXX'

lemma riemannSec_eq_of_Y_eq_at
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y Y' : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hY' : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y'))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% Z))
    (hYY' : Y x = Y' x) :
    riemannSec cov X Y Z x = riemannSec cov X Y' Z x := by
  classical
  have hY_at : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hY'_at : MDiffAt (T% Y') x := (hY' x).mdifferentiableAt (by simp)
  exact (tensorialAt_Y (cov := cov) (X := X) (Z := Z) hX hZ).pointwise hY_at hY'_at hYY'

/-! ## Locality of `riemannSec` in the Z-slot

For two smooth global sections `Z, Z'` of `V` agreeing on a neighbourhood of `x`, the values
`riemannSec cov X Y Z x` and `riemannSec cov X Y Z' x` coincide. The proof uses
`cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq` for the three terms of `riemannSec`. -/

private lemma covApply_eventuallyEq_of_Z_eq
    (cov : CovariantDerivative I F V)
    {Y : Π b : M, TangentSpace I b} {Z Z' : Π b : M, V b} {x : M}
    (_hY : MDiff (T% Y))
    (hZ : MDiff (T% Z)) (hZ' : MDiff (T% Z'))
    (hZZ' : ∀ᶠ b in 𝓝 x, Z b = Z' b) :
    ∀ᶠ b in 𝓝 x, covApply cov Y Z b = covApply cov Y Z' b := by
  classical
  -- Pick an open neighbourhood `V'` of `x` where `Z = Z'`.
  rw [eventually_iff_exists_mem] at hZZ'
  obtain ⟨U, hU, hZeqZ'⟩ := hZZ'
  obtain ⟨V', hV'U, hV'_open, hpV'⟩ := mem_nhds_iff.mp hU
  refine eventually_iff_exists_mem.mpr ⟨V', hV'_open.mem_nhds hpV', ?_⟩
  intro b hbV'
  -- For b ∈ V', Z =ᶠ[𝓝 b] Z' (since V' is open and contained in U).
  have hZeqZ'_b : ∀ᶠ b' in 𝓝 b, Z b' = Z' b' :=
    Filter.eventually_of_mem (hV'_open.mem_nhds hbV')
      (fun b' hb'V' => hZeqZ' b' (hV'U hb'V'))
  -- Apply cov.congr_of_eventuallyEq at b.
  have hcov_eq : cov.toFun Z b = cov.toFun Z' b :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq (hZ b) (hZ' b) Filter.univ_mem hZeqZ'_b
  change cov.toFun Z b (Y b) = cov.toFun Z' b (Y b)
  rw [hcov_eq]

lemma riemannSec_eq_of_Z_eventuallyEq
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y : Π b : M, TangentSpace I b} {Z Z' : Π b : M, V b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% Z))
    (hZ' : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% Z'))
    (hZZ' : ∀ᶠ b in 𝓝 x, Z b = Z' b) :
    riemannSec cov X Y Z x = riemannSec cov X Y Z' x := by
  classical
  have hY_mdiff : MDiff (T% Y) := hY.mdifferentiable (by simp)
  have hX_mdiff : MDiff (T% X) := hX.mdifferentiable (by simp)
  -- Smoothness of Z, Z' at every point (enough for the eventual equalities).
  have hZ_mdiff : MDiff (T% Z) := by
    have : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z) :=
      hZ.of_le (by exact_mod_cast le_self_add)
    exact this.mdifferentiable (by simp)
  have hZ'_mdiff : MDiff (T% Z') := by
    have : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z') :=
      hZ'.of_le (by exact_mod_cast le_self_add)
    exact this.mdifferentiable (by simp)
  have hX_at : MDiffAt (T% X) x := (hX x).mdifferentiableAt (by simp)
  have hY_at : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  unfold riemannSec
  -- Term 1: cov.toFun (covApply cov Y Z) x (X x) = cov.toFun (covApply cov Y Z') x (X x).
  have hcYZ_at : MDiffAt (T% (covApply cov Y Z)) x :=
    covApply_mdifferentiableAt_local (cov := cov) hY_at hZ
  have hcYZ'_at : MDiffAt (T% (covApply cov Y Z')) x :=
    covApply_mdifferentiableAt_local (cov := cov) hY_at hZ'
  have hcXZ_at : MDiffAt (T% (covApply cov X Z)) x :=
    covApply_mdifferentiableAt_local (cov := cov) hX_at hZ
  have hcXZ'_at : MDiffAt (T% (covApply cov X Z')) x :=
    covApply_mdifferentiableAt_local (cov := cov) hX_at hZ'
  have hev_cYZ : ∀ᶠ b in 𝓝 x, covApply cov Y Z b = covApply cov Y Z' b :=
    covApply_eventuallyEq_of_Z_eq cov hY_mdiff hZ_mdiff hZ'_mdiff hZZ'
  have hev_cXZ : ∀ᶠ b in 𝓝 x, covApply cov X Z b = covApply cov X Z' b :=
    covApply_eventuallyEq_of_Z_eq cov hX_mdiff hZ_mdiff hZ'_mdiff hZZ'
  have hT1 : cov.toFun (covApply cov Y Z) x = cov.toFun (covApply cov Y Z') x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hcYZ_at hcYZ'_at Filter.univ_mem hev_cYZ
  have hT2 : cov.toFun (covApply cov X Z) x = cov.toFun (covApply cov X Z') x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hcXZ_at hcXZ'_at Filter.univ_mem hev_cXZ
  -- Term 3: cov.toFun Z x (mlieBracket I X Y x) = cov.toFun Z' x (mlieBracket I X Y x).
  have hT3 : cov.toFun Z x = cov.toFun Z' x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (hZ_mdiff x) (hZ'_mdiff x) Filter.univ_mem hZZ'
  rw [hT1, hT2, hT3]

/-! ## Smoothness of `b ↦ extDerivFun f b (Y b) : M → ℝ`

For smooth `f : M → ℝ` and smooth tangent vector field `Y`, the function
`b ↦ extDerivFun f b (Y b) = mfderiv I 𝓘(ℝ, ℝ) f b (Y b)` is smooth. We realise this function
as the model-fibre coordinate of the second component of the bundled tangent map applied to
the smooth section `b ↦ ⟨b, Y b⟩` of `TM`. -/

private lemma extDerivFun_apply_contMDiff
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {Y : Π b : M, TangentSpace I b} (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b => extDerivFun f b (Y b)) := by
  classical
  -- The smoothness of `b ↦ mfderiv f b` as a section of `Hom(TM, ℝ)`.
  -- We express `b ↦ extDerivFun f b (Y b)` as `(tangentMap f ⟨b, Y b⟩).snd`, casting via
  -- `NormedSpace.fromTangentSpace` to see ℝ as the model fibre.
  -- The bundled tangent map of `f` is smooth.
  have htan : ContMDiff I.tangent (𝓘(ℝ, ℝ).tangent) ∞ (tangentMap I 𝓘(ℝ, ℝ) f) := by
    have h₁ : ContMDiff I 𝓘(ℝ, ℝ) ((∞ : WithTop ℕ∞) + 1) f := by
      simpa using hf
    exact h₁.contMDiff_tangentMap (le_refl _)
  -- The section `b ↦ ⟨b, Y b⟩` of `TM` is smooth (this is `hY` after unfolding `T%`).
  have hYsec : ContMDiff I I.tangent ∞
      (fun b => (TotalSpace.mk' E b (Y b) : TangentBundle I M)) := hY
  -- Composition: `b ↦ tangentMap f ⟨b, Y b⟩` is smooth.
  have hcomp : ContMDiff I (𝓘(ℝ, ℝ).tangent) ∞
      (fun b => tangentMap I 𝓘(ℝ, ℝ) f (TotalSpace.mk' E b (Y b))) :=
    htan.comp hYsec
  -- Project the smooth `b ↦ tangentMap f ⟨b, Y b⟩` to its `.snd` component (the tangent vector
  -- in ℝ, which IS ℝ via `TangentSpace 𝓘(ℝ, ℝ) y = ℝ`).
  have hsnd : ContMDiff (𝓘(ℝ, ℝ).tangent) 𝓘(ℝ, ℝ) ∞
      (fun p : TangentBundle 𝓘(ℝ, ℝ) ℝ => p.2) := contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)
  have hresult : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b => (tangentMap I 𝓘(ℝ, ℝ) f (TotalSpace.mk' E b (Y b))).2) :=
    hsnd.comp hcomp
  -- The result `(tangentMap f ⟨b, Y b⟩).2 = mfderiv f b (Y b)` (by `tangentMap_snd`),
  -- and `mfderiv f b (Y b) = extDerivFun f b (Y b)` definitionally.
  refine hresult.congr fun b => ?_
  simp [extDerivFun, tangentMap_snd, NormedSpace.fromTangentSpace]

/-! ## Smooth-section versions of the Z-slot tensoriality

For smooth global `f`, `Z`, `Z'`, and smooth global `X`, `Y`, the Z-slot additivity and
scalar-multiplication identities of `riemannSec` hold without the user supplying explicit
auxiliary `MDiffAt` hypotheses. -/

/-- Z-slot additivity for smooth global sections. -/
private lemma riemannSec_add_third_smooth
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y : Π b : M, TangentSpace I b} {Z Z' : Π b : M, V b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z))
    (hZ' : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z')) :
    riemannSec cov X Y (Z + Z') x = riemannSec cov X Y Z x + riemannSec cov X Y Z' x := by
  classical
  have hX_at : MDiffAt (T% X) x := (hX x).mdifferentiableAt (by simp)
  have hY_at : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hZ_le : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% Z) := by simpa using hZ
  have hZ'_le : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% Z') := by simpa using hZ'
  have hZsum_le : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% (Z + Z')) := by
    simpa using hZ.add_section hZ'
  have hZ_mdiff : MDiff (T% Z) := hZ.mdifferentiable (by simp)
  have hZ'_mdiff : MDiff (T% Z') := hZ'.mdifferentiable (by simp)
  refine riemannSec_add_third (cov := cov)
    (X := X) (Y := Y) (Z := Z) (Z' := Z') (x := x)
    (Filter.Eventually.of_forall hZ_mdiff)
    (Filter.Eventually.of_forall hZ'_mdiff)
    (covApply_mdifferentiableAt_local (cov := cov) hY_at hZ_le)
    (covApply_mdifferentiableAt_local (cov := cov) hY_at hZ'_le)
    (covApply_mdifferentiableAt_local (cov := cov) hY_at hZsum_le)
    (covApply_mdifferentiableAt_local (cov := cov) hX_at hZ_le)
    (covApply_mdifferentiableAt_local (cov := cov) hX_at hZ'_le)
    (covApply_mdifferentiableAt_local (cov := cov) hX_at hZsum_le)

/-- Z-slot scalar-multiplication identity for smooth global sections. -/
private lemma riemannSec_smul_third_smooth
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {f : M → ℝ} {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z)) :
    riemannSec cov X Y (f • Z) x = f x • riemannSec cov X Y Z x := by
  classical
  have hX_at : MDiffAt (T% X) x := (hX x).mdifferentiableAt (by simp)
  have hY_at : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hZ_le : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% Z) := by simpa using hZ
  have hfZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (f • Z)) := hf.smul_section hZ
  have hfZ_le : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% (f • Z)) := by
    simpa using hfZ
  have hf_at2 : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x := by
    have : (2 : WithTop ℕ∞) ≤ ∞ := by
      have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
      simpa using h1
    exact (hf x).of_le this
  have hf_mdiff : MDiff f := hf.mdifferentiable (by simp)
  have hZ_mdiff : MDiff (T% Z) := hZ.mdifferentiable (by simp)
  have hZ_at : MDiffAt (T% Z) x := hZ_mdiff x
  have hcXZ_at := covApply_mdifferentiableAt_local (cov := cov) hX_at hZ_le
  have hcYZ_at := covApply_mdifferentiableAt_local (cov := cov) hY_at hZ_le
  have hcXfZ_at := covApply_mdifferentiableAt_local (cov := cov) hX_at hfZ_le
  have hcYfZ_at := covApply_mdifferentiableAt_local (cov := cov) hY_at hfZ_le
  -- Smoothness of `b ↦ extDerivFun f b (X b)` and `b ↦ extDerivFun f b (Y b)`.
  have hYf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b => extDerivFun f b (Y b)) :=
    extDerivFun_apply_contMDiff hf hY
  have hXf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b => extDerivFun f b (X b)) :=
    extDerivFun_apply_contMDiff hf hX
  have hYf_at : MDiffAt (fun b => extDerivFun f b (Y b)) x :=
    (hYf x).mdifferentiableAt (by simp)
  have hXf_at : MDiffAt (fun b => extDerivFun f b (X b)) x :=
    (hXf x).mdifferentiableAt (by simp)
  -- Scalar-section product smoothness.
  have hcYZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (covApply cov Y Z)) := by
    -- Same proof as `covApply_contMDiffOn` but as `ContMDiff`.
    have hop : ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞ (T% (covApply cov Y Z)) Set.univ :=
      covApply_contMDiffOn (cov := cov) hY hZ_le
    intro b
    exact hop.contMDiffAt (Filter.univ_mem)
  have hcXZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (covApply cov X Z)) := by
    have hop : ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞ (T% (covApply cov X Z)) Set.univ :=
      covApply_contMDiffOn (cov := cov) hX hZ_le
    intro b
    exact hop.contMDiffAt (Filter.univ_mem)
  have hf_smul_cYZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (f • covApply cov Y Z)) :=
    hf.smul_section hcYZ
  have hf_smul_cXZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (f • covApply cov X Z)) :=
    hf.smul_section hcXZ
  have hYf_smul_Z : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (T% ((fun b => extDerivFun f b (Y b)) • Z)) := hYf.smul_section hZ
  have hXf_smul_Z : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (T% ((fun b => extDerivFun f b (X b)) • Z)) := hXf.smul_section hZ
  have hf_smul_cYZ_at : MDiffAt (T% (f • covApply cov Y Z)) x :=
    (hf_smul_cYZ x).mdifferentiableAt (by simp)
  have hf_smul_cXZ_at : MDiffAt (T% (f • covApply cov X Z)) x :=
    (hf_smul_cXZ x).mdifferentiableAt (by simp)
  have hYf_smul_Z_at : MDiffAt (T% ((fun b => extDerivFun f b (Y b)) • Z)) x :=
    (hYf_smul_Z x).mdifferentiableAt (by simp)
  have hXf_smul_Z_at : MDiffAt (T% ((fun b => extDerivFun f b (X b)) • Z)) x :=
    (hXf_smul_Z x).mdifferentiableAt (by simp)
  -- The chart-interior hypothesis is automatic from `BoundarylessManifold`.
  have hx_int : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    (I.isInteriorPoint_iff (x := x)).mp BoundarylessManifold.isInteriorPoint
  exact riemannSec_smul_third (cov := cov)
    (f := f) (X := X) (Y := Y) (Z := Z) (x := x)
    hX_at hY_at hf_at2
    (Filter.Eventually.of_forall hf_mdiff)
    (Filter.Eventually.of_forall hZ_mdiff)
    hZ_at hcXZ_at hcYZ_at hcXfZ_at hcYfZ_at hYf_at hXf_at
    hf_smul_cYZ_at hf_smul_cXZ_at hYf_smul_Z_at hXf_smul_Z_at hx_int

/-! ## Vanishing of `riemannSec` in the Z-slot when the section vanishes at `x`

For smooth global sections `X`, `Y`, `τ` with `τ x = 0`, we have
`riemannSec cov X Y τ x = 0`. The proof uses a smooth local frame near `x`, expresses `τ` near
`x` as a finite sum `∑ (ψ • g_i) • s'_i` of products of smooth scalar functions vanishing at
`x` with smooth global frame extensions, and applies Z-slot scalar multiplication
(`riemannSec_smul_third_smooth`) and additivity (`riemannSec_add_third_smooth`) to each
summand. -/

private lemma riemannSec_eq_zero_of_Z_eq_zero
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z))
    (hZx : Z x = 0) :
    riemannSec cov X Y Z x = 0 := by
  classical
  -- Trivialization at `x`, induced local frame `e.localFrame b`, basis of model fibre `b`.
  let e := trivializationAt F V x
  let basisF := Module.finBasis ℝ F
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
  have hframe := e.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) basisF
  obtain ⟨s', hs'⟩ := hframe.exists_contMDiffSection_eqOn_nhd e.open_baseSet he
  -- Smooth bump function `χ` at `x` with `tsupport χ ⊆ e.baseSet` and `χ = 1` near `x`.
  obtain ⟨χ, -, hχsupp⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
      (e.open_baseSet.mem_nhds he)
  -- The smooth coefficient functions `g_i := χ • localFrame_coeff i (·) (Z ·)`. These are
  -- smooth on `M` (zero outside `tsupport χ ⊆ e.baseSet`), and `g_i x = 0` since `Z x = 0`.
  have hZ_le : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% Z) := by simpa using hZ
  have hZ_at_global : ∀ b, MDiffAt (T% Z) b := hZ.mdifferentiable (by simp)
  have hcoeff_smooth : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b => χ b • hframe.coeff i b (Z b)) := by
    intro i
    have hsmooth_lfc : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun b => χ b • e.localFrame_coeff I basisF i b (Z b)) := by
      intro b
      by_cases hb : b ∈ tsupport (χ : M → ℝ)
      · exact (χ.contMDiff.of_le (by exact_mod_cast le_top)).contMDiffAt.smul
          (contMDiffAt_localFrame_coeff basisF (hχsupp hb) hZ.contMDiffAt i)
      · -- `χ = 0` near `b`, so the product is locally zero.
        have hχ_zero : ∀ᶠ y in nhds b, (χ : M → ℝ) y = 0 := by
          apply Filter.Eventually.mono
            ((isClosed_tsupport (χ : M → ℝ)).isOpen_compl.mem_nhds hb)
          intro y hy
          exact (notMem_tsupport_iff_eventuallyEq.mp hy).self_of_nhds
        exact (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
          (hχ_zero.mono fun y hy => by simp [hy])
    refine hsmooth_lfc.congr fun b => ?_
    by_cases hb : b ∈ e.baseSet
    · have hbasis : e.basisAt basisF hb = hframe.toBasisAt hb := by
        ext j
        simp [IsLocalFrameOn.toBasisAt, Trivialization.localFrame, Trivialization.basisAt, hb]
      simp only [hframe.coeff_apply_of_mem hb,
        e.localFrame_coeff_apply_of_mem_baseSet basisF hb, hbasis]
    · simp [hframe.coeff_apply_of_notMem hb,
        e.localFrame_coeff_apply_of_notMem_baseSet basisF hb]
  -- Define the smooth global scalar functions `g_i := χ • localFrame_coeff i ⋅ Z`.
  let g : Fin (Module.finrank ℝ F) → M → ℝ := fun i b => χ b • hframe.coeff i b (Z b)
  -- `g_i x = 0`.
  have hg_zero : ∀ i, g i x = 0 := by
    intro i
    change χ x • hframe.coeff i x (Z x) = 0
    rw [hZx, map_zero, smul_zero]
  -- `Z =ᶠ[𝓝 x] ∑ g_i • s'_i`.
  have hZ_eq_near : ∀ᶠ b in 𝓝 x, Z b = ∑ i, g i b • (s' i b) := by
    filter_upwards [hs', χ.eventuallyEq_one,
      e.open_baseSet.mem_nhds he] with b hs'b hχb hb
    change Z b = ∑ i, (χ b • hframe.coeff i b (Z b)) • (s' i b)
    simp only [show χ b = (1 : M → ℝ) b from hχb, Pi.one_apply, one_smul]
    conv_lhs => rw [hframe.coeff_sum_eq Z hb]
    congr 1
    ext i
    rw [hs'b i]
  -- Smoothness of the sum `∑ g i • s' i` as a global section.
  have hsum_smooth : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (T% (fun b => ∑ i, g i b • s' i b)) := by
    refine ContMDiff.sum_section (s := Finset.univ) (fun i _ => ?_)
    exact (hcoeff_smooth i).smul_section (s' i).contMDiff
  -- Replace `Z` by the sum near `x` (using Z-slot locality).
  have hZ_eq_riemannSec : riemannSec cov X Y Z x =
      riemannSec cov X Y (fun b => ∑ i, g i b • s' i b) x := by
    apply riemannSec_eq_of_Z_eventuallyEq (cov := cov) hX hY hZ_le
      (by simpa using hsum_smooth) hZ_eq_near
  rw [hZ_eq_riemannSec]
  -- Iteratively apply `riemannSec_add_third_smooth` to split the sum, then
  -- `riemannSec_smul_third_smooth` to each summand.
  -- Equivalent statement using `Finset.sum`: the sum equals `∑ i, riemannSec cov X Y (g i • s' i) x`,
  -- and each summand is `g i x • riemannSec cov X Y (s' i) x = 0` by `hg_zero`.
  -- We prove this by induction on the finset.
  suffices h : riemannSec cov X Y (fun b => ∑ i ∈ Finset.univ, g i b • s' i b) x =
      ∑ i ∈ Finset.univ, g i x • riemannSec cov X Y (fun b => s' i b) x by
    rw [show (fun b => ∑ i, g i b • s' i b) =
      (fun b => ∑ i ∈ Finset.univ, g i b • s' i b) from rfl, h]
    apply Finset.sum_eq_zero
    intro i _
    rw [hg_zero i, zero_smul]
  -- Induction on the finset.
  induction Finset.univ (α := Fin (Module.finrank ℝ F)) using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    -- riemannSec cov X Y 0 x = 0 (zero-section evaluation).
    change riemannSec cov X Y (fun _ : M => (0 : V _)) x = 0
    unfold riemannSec
    have h_cov_zero_at : ∀ Y' : Π b : M, TangentSpace I b,
        cov.toFun (covApply cov Y' (fun _ : M => (0 : V _))) x = 0 := by
      intro Y'
      have : covApply cov Y' (fun _ : M => (0 : V _)) = 0 := by
        funext b
        change cov.toFun (fun _ : M => (0 : V _)) b (Y' b) = 0
        rw [show (fun _ : M => (0 : V _)) = (0 : Π b : M, V b) from rfl,
            cov.isCovariantDerivativeOnUniv.zero (x := b)]
        rfl
      rw [this]
      have : cov.toFun (0 : Π b : M, V b) x = 0 :=
        cov.isCovariantDerivativeOnUniv.zero (x := x)
      exact this
    rw [h_cov_zero_at X, h_cov_zero_at Y]
    rw [show (fun _ : M => (0 : V _)) = (0 : Π b : M, V b) from rfl]
    have hcZero : cov.toFun (0 : Π b : M, V b) x = 0 :=
      cov.isCovariantDerivativeOnUniv.zero (x := x)
    rw [hcZero]
    simp
  | insert j s hjs IH =>
    -- Split the sum-over-(insert j s) into g j • s' j + (sum-over-s).
    have hsum_eq : (fun b => ∑ i ∈ insert j s, g i b • (s' i b)) =
        (fun b => g j b • (s' j) b + ∑ i ∈ s, g i b • (s' i) b) := by
      funext b
      rw [Finset.sum_insert hjs]
    rw [hsum_eq]
    -- Then rewrite as `g j • s' j + (fun b => ∑)`.
    have hsplit_eq : (fun b : M => g j b • (s' j) b + ∑ i ∈ s, g i b • (s' i) b) =
        ((g j • (s' j : Π b, V b)) + (fun b : M => ∑ i ∈ s, g i b • (s' i) b)) := by
      funext b; rfl
    rw [hsplit_eq]
    have hgj_smooth : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (g j • (s' j : Π b, V b))) :=
      (hcoeff_smooth j).smul_section (s' j).contMDiff
    have hrest_smooth : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
        (T% (fun b : M => ∑ i ∈ s, g i b • (s' i b))) := by
      refine ContMDiff.sum_section (s := s) (fun i _ => ?_)
      exact (hcoeff_smooth i).smul_section (s' i).contMDiff
    rw [riemannSec_add_third_smooth (cov := cov) hX hY hgj_smooth hrest_smooth]
    rw [riemannSec_smul_third_smooth (cov := cov) (f := g j) (Z := (s' j : Π b, V b))
      (hcoeff_smooth j) hX hY (s' j).contMDiff]
    rw [IH]
    rw [Finset.sum_insert hjs]

/-! ## Z-slot pointwise dependence -/

lemma riemannSec_eq_of_Z_eq_at
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y : Π b : M, TangentSpace I b} {Z Z' : Π b : M, V b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z))
    (hZ' : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z'))
    (hZZ' : Z x = Z' x) :
    riemannSec cov X Y Z x = riemannSec cov X Y Z' x := by
  classical
  -- τ := Z - Z' is smooth global with τ x = 0.
  set τ : Π b : M, V b := Z - Z' with hτ_def
  have hτ_smooth : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% τ) := hZ.sub_section hZ'
  have hτ_zero : τ x = 0 := by
    change Z x - Z' x = 0
    rw [hZZ']; abel
  have hτ_vanishes :
      riemannSec cov X Y τ x = 0 :=
    riemannSec_eq_zero_of_Z_eq_zero (cov := cov) hX hY hτ_smooth hτ_zero
  -- Express Z = Z' + τ.
  have hZ_eq : Z = Z' + τ := by
    funext b; change Z b = Z' b + (Z b - Z' b); abel
  -- Apply Z-slot additivity.
  rw [hZ_eq]
  rw [riemannSec_add_third_smooth (cov := cov) hX hY hZ' hτ_smooth]
  rw [hτ_vanishes, add_zero]

/-! ## Full well-definedness lemma -/

/-- **Well-definedness of `riemannSec` on smooth global sections, modulo pointwise agreement
at `x`.** Given two triples of smooth global sections `(X, Y, Z)` and `(X', Y', Z')` agreeing
pointwise at `x`, the values of `riemannSec` at `x` coincide. -/
theorem riemannSec_eq_of_pointwise_eq
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X X' Y Y' : Π b : M, TangentSpace I b} {Z Z' : Π b : M, V b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hX' : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X'))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hY' : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y'))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z))
    (hZ' : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z'))
    (hX_eq : X x = X' x) (hY_eq : Y x = Y' x) (hZ_eq : Z x = Z' x) :
    riemannSec cov X Y Z x = riemannSec cov X' Y' Z' x := by
  classical
  have hZ_le : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% Z) := by simpa using hZ
  -- Chain through X-slot, Y-slot, Z-slot.
  have h1 : riemannSec cov X Y Z x = riemannSec cov X' Y Z x :=
    riemannSec_eq_of_X_eq_at (cov := cov) hX hX' hY hZ_le hX_eq
  have h2 : riemannSec cov X' Y Z x = riemannSec cov X' Y' Z x :=
    riemannSec_eq_of_Y_eq_at (cov := cov) hX' hY hY' hZ_le hY_eq
  have h3 : riemannSec cov X' Y' Z x = riemannSec cov X' Y' Z' x :=
    riemannSec_eq_of_Z_eq_at (cov := cov) hX' hY' hZ hZ' hZ_eq
  rw [h1, h2, h3]

/-! ## Bundled trilinear continuous linear map

Using the well-definedness lemma `riemannSec_eq_of_pointwise_eq` together with the
slot-tensoriality of `riemannSec` on smooth global sections, we obtain a continuous trilinear
form `riemannOp cov x : T_x M →L[ℝ] T_x M →L[ℝ] V x →L[ℝ] V x` at each point. -/

/-- An evaluation form of `riemannOpFun` on smooth global sections. The proof uses
`riemannSec_eq_of_pointwise_eq` together with the smoothness of `smoothExtensionTangent`
and `smoothExtensionFiber`. -/
theorem riemannOpFun_eq_riemannSec
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z)) :
    riemannOpFun cov x (X x) (Y x) (Z x) = riemannSec cov X Y Z x := by
  classical
  unfold riemannOpFun
  refine riemannSec_eq_of_pointwise_eq (cov := cov)
    (smoothExtensionTangent_contMDiff x (X x))
    hX
    (smoothExtensionTangent_contMDiff x (Y x))
    hY
    (smoothExtensionFiber_contMDiff (V := V) x (Z x))
    hZ
    ?_ ?_ ?_
  · exact smoothExtensionTangent_eq x (X x)
  · exact smoothExtensionTangent_eq x (Y x)
  · exact smoothExtensionFiber_eq (V := V) x (Z x)

/-- `riemannOpFun cov x v w u` only depends on the fibre values `(v, w, u)`. The proof uses
two arbitrary smooth extensions and `riemannSec_eq_of_pointwise_eq`. -/
theorem riemannOpFun_well_defined
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M} {v w : TangentSpace I x}
    {u : V x}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z))
    (hX_eq : X x = v) (hY_eq : Y x = w) (hZ_eq : Z x = u) :
    riemannOpFun cov x v w u = riemannSec cov X Y Z x := by
  rw [← hX_eq, ← hY_eq, ← hZ_eq]
  exact riemannOpFun_eq_riemannSec (cov := cov) hX hY hZ

/-! ### Linearity in each slot -/

private lemma riemannOpFun_add_left
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (x : M) (v v' : TangentSpace I x) (w : TangentSpace I x) (u : V x) :
    riemannOpFun cov x (v + v') w u =
      riemannOpFun cov x v w u + riemannOpFun cov x v' w u := by
  classical
  -- Smooth extensions of v, v', v + v', w, u.
  set Xv := smoothExtensionTangent (I := I) x v
  set Xv' := smoothExtensionTangent (I := I) x v'
  set Xvv' : Π b : M, TangentSpace I b :=
    smoothExtensionTangent (I := I) x v + smoothExtensionTangent (I := I) x v'
  set Y := smoothExtensionTangent (I := I) x w
  set Z := smoothExtensionFiber (I := I) (F := F) (V := V) x u
  have hXv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xv) := smoothExtensionTangent_contMDiff x v
  have hXv' : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xv') := smoothExtensionTangent_contMDiff x v'
  have hXvv' : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xvv') := hXv.add_section hXv'
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) := smoothExtensionTangent_contMDiff x w
  have hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z) := smoothExtensionFiber_contMDiff x u
  have hXv_eq : Xv x = v := smoothExtensionTangent_eq x v
  have hXv'_eq : Xv' x = v' := smoothExtensionTangent_eq x v'
  have hY_eq : Y x = w := smoothExtensionTangent_eq x w
  have hZ_eq : Z x = u := smoothExtensionFiber_eq (V := V) x u
  have hXvv'_eq : Xvv' x = v + v' := by
    change Xv x + Xv' x = v + v'; rw [hXv_eq, hXv'_eq]
  -- LHS: riemannOpFun cov x (v + v') w u = riemannSec cov Xvv' Y Z x.
  rw [riemannOpFun_well_defined (cov := cov) hXvv' hY hZ hXvv'_eq hY_eq hZ_eq]
  -- RHS: each term unfolded.
  rw [riemannOpFun_well_defined (cov := cov) hXv hY hZ hXv_eq hY_eq hZ_eq,
      riemannOpFun_well_defined (cov := cov) hXv' hY hZ hXv'_eq hY_eq hZ_eq]
  -- Apply X-slot additivity.
  have hZ_le : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% Z) := by simpa using hZ
  exact riemannSec_add_left (cov := cov) (X := Xv) (X' := Xv') (Y := Y) (Z := Z) (x := x)
    ((hXv x).mdifferentiableAt (by simp))
    ((hXv' x).mdifferentiableAt (by simp))
    (covApply_mdifferentiableAt_local (cov := cov) ((hXv x).mdifferentiableAt (by simp)) hZ_le)
    (covApply_mdifferentiableAt_local (cov := cov) ((hXv' x).mdifferentiableAt (by simp)) hZ_le)

private lemma riemannOpFun_smul_left
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (x : M) (c : ℝ) (v w : TangentSpace I x) (u : V x) :
    riemannOpFun cov x (c • v) w u = c • riemannOpFun cov x v w u := by
  classical
  set Xv := smoothExtensionTangent (I := I) x v
  set Xcv : Π b : M, TangentSpace I b := c • smoothExtensionTangent (I := I) x v
  set Y := smoothExtensionTangent (I := I) x w
  set Z := smoothExtensionFiber (I := I) (F := F) (V := V) x u
  have hXv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xv) := smoothExtensionTangent_contMDiff x v
  have hXcv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xcv) := hXv.const_smul_section
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) := smoothExtensionTangent_contMDiff x w
  have hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z) := smoothExtensionFiber_contMDiff x u
  have hXv_eq : Xv x = v := smoothExtensionTangent_eq x v
  have hY_eq : Y x = w := smoothExtensionTangent_eq x w
  have hZ_eq : Z x = u := smoothExtensionFiber_eq (V := V) x u
  have hXcv_eq : Xcv x = c • v := by change c • Xv x = c • v; rw [hXv_eq]
  rw [riemannOpFun_well_defined (cov := cov) hXcv hY hZ hXcv_eq hY_eq hZ_eq,
      riemannOpFun_well_defined (cov := cov) hXv hY hZ hXv_eq hY_eq hZ_eq]
  -- Apply X-slot scalar mult (riemannSec_smul_left with f := constant c).
  have hZ_le : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% Z) := by simpa using hZ
  have h_const_smul : Xcv = (fun _ : M => c) • Xv := by funext b; rfl
  rw [h_const_smul]
  exact riemannSec_smul_left (cov := cov) (f := fun _ : M => c) (X := Xv) (Y := Y) (Z := Z) (x := x)
    mdifferentiableAt_const ((hXv x).mdifferentiableAt (by simp))
    (covApply_mdifferentiableAt_local (cov := cov) ((hXv x).mdifferentiableAt (by simp)) hZ_le)

private lemma riemannOpFun_add_right
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (x : M) (v : TangentSpace I x) (w w' : TangentSpace I x) (u : V x) :
    riemannOpFun cov x v (w + w') u =
      riemannOpFun cov x v w u + riemannOpFun cov x v w' u := by
  classical
  set X := smoothExtensionTangent (I := I) x v
  set Yw := smoothExtensionTangent (I := I) x w
  set Yw' := smoothExtensionTangent (I := I) x w'
  set Yww' : Π b : M, TangentSpace I b :=
    smoothExtensionTangent (I := I) x w + smoothExtensionTangent (I := I) x w'
  set Z := smoothExtensionFiber (I := I) (F := F) (V := V) x u
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X) := smoothExtensionTangent_contMDiff x v
  have hYw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Yw) := smoothExtensionTangent_contMDiff x w
  have hYw' : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Yw') := smoothExtensionTangent_contMDiff x w'
  have hYww' : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Yww') := hYw.add_section hYw'
  have hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z) := smoothExtensionFiber_contMDiff x u
  have hX_eq : X x = v := smoothExtensionTangent_eq x v
  have hYw_eq : Yw x = w := smoothExtensionTangent_eq x w
  have hYw'_eq : Yw' x = w' := smoothExtensionTangent_eq x w'
  have hZ_eq : Z x = u := smoothExtensionFiber_eq (V := V) x u
  have hYww'_eq : Yww' x = w + w' := by change Yw x + Yw' x = w + w'; rw [hYw_eq, hYw'_eq]
  rw [riemannOpFun_well_defined (cov := cov) hX hYww' hZ hX_eq hYww'_eq hZ_eq,
      riemannOpFun_well_defined (cov := cov) hX hYw hZ hX_eq hYw_eq hZ_eq,
      riemannOpFun_well_defined (cov := cov) hX hYw' hZ hX_eq hYw'_eq hZ_eq]
  have hZ_le : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% Z) := by simpa using hZ
  exact riemannSec_add_right (cov := cov) (X := X) (Y := Yw) (Y' := Yw') (Z := Z) (x := x)
    ((hYw x).mdifferentiableAt (by simp))
    ((hYw' x).mdifferentiableAt (by simp))
    (covApply_mdifferentiableAt_local (cov := cov) ((hYw x).mdifferentiableAt (by simp)) hZ_le)
    (covApply_mdifferentiableAt_local (cov := cov) ((hYw' x).mdifferentiableAt (by simp)) hZ_le)

private lemma riemannOpFun_smul_right
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (x : M) (v : TangentSpace I x) (c : ℝ) (w : TangentSpace I x) (u : V x) :
    riemannOpFun cov x v (c • w) u = c • riemannOpFun cov x v w u := by
  classical
  set X := smoothExtensionTangent (I := I) x v
  set Yw := smoothExtensionTangent (I := I) x w
  set Ycw : Π b : M, TangentSpace I b := c • smoothExtensionTangent (I := I) x w
  set Z := smoothExtensionFiber (I := I) (F := F) (V := V) x u
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X) := smoothExtensionTangent_contMDiff x v
  have hYw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Yw) := smoothExtensionTangent_contMDiff x w
  have hYcw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Ycw) := hYw.const_smul_section
  have hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z) := smoothExtensionFiber_contMDiff x u
  have hX_eq : X x = v := smoothExtensionTangent_eq x v
  have hYw_eq : Yw x = w := smoothExtensionTangent_eq x w
  have hZ_eq : Z x = u := smoothExtensionFiber_eq (V := V) x u
  have hYcw_eq : Ycw x = c • w := by change c • Yw x = c • w; rw [hYw_eq]
  rw [riemannOpFun_well_defined (cov := cov) hX hYcw hZ hX_eq hYcw_eq hZ_eq,
      riemannOpFun_well_defined (cov := cov) hX hYw hZ hX_eq hYw_eq hZ_eq]
  have hZ_le : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% Z) := by simpa using hZ
  have h_const_smul : Ycw = (fun _ : M => c) • Yw := by funext b; rfl
  rw [h_const_smul]
  exact riemannSec_smul_right (cov := cov) (f := fun _ : M => c) (X := X) (Y := Yw) (Z := Z) (x := x)
    mdifferentiableAt_const ((hYw x).mdifferentiableAt (by simp))
    (covApply_mdifferentiableAt_local (cov := cov) ((hYw x).mdifferentiableAt (by simp)) hZ_le)

private lemma riemannOpFun_add_third
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (x : M) (v : TangentSpace I x) (w : TangentSpace I x) (u u' : V x) :
    riemannOpFun cov x v w (u + u') = riemannOpFun cov x v w u + riemannOpFun cov x v w u' := by
  classical
  set X := smoothExtensionTangent (I := I) x v
  set Y := smoothExtensionTangent (I := I) x w
  set Zu := smoothExtensionFiber (I := I) (F := F) (V := V) x u
  set Zu' := smoothExtensionFiber (I := I) (F := F) (V := V) x u'
  set Zuu' : Π b : M, V b :=
    smoothExtensionFiber (I := I) (F := F) (V := V) x u +
    smoothExtensionFiber (I := I) (F := F) (V := V) x u'
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X) := smoothExtensionTangent_contMDiff x v
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) := smoothExtensionTangent_contMDiff x w
  have hZu : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Zu) := smoothExtensionFiber_contMDiff x u
  have hZu' : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Zu') := smoothExtensionFiber_contMDiff x u'
  have hZuu' : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Zuu') := hZu.add_section hZu'
  have hX_eq : X x = v := smoothExtensionTangent_eq x v
  have hY_eq : Y x = w := smoothExtensionTangent_eq x w
  have hZu_eq : Zu x = u := smoothExtensionFiber_eq (V := V) x u
  have hZu'_eq : Zu' x = u' := smoothExtensionFiber_eq (V := V) x u'
  have hZuu'_eq : Zuu' x = u + u' := by change Zu x + Zu' x = u + u'; rw [hZu_eq, hZu'_eq]
  rw [riemannOpFun_well_defined (cov := cov) hX hY hZuu' hX_eq hY_eq hZuu'_eq,
      riemannOpFun_well_defined (cov := cov) hX hY hZu hX_eq hY_eq hZu_eq,
      riemannOpFun_well_defined (cov := cov) hX hY hZu' hX_eq hY_eq hZu'_eq]
  exact riemannSec_add_third_smooth (cov := cov) hX hY hZu hZu'

private lemma riemannOpFun_smul_third
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (x : M) (v w : TangentSpace I x) (c : ℝ) (u : V x) :
    riemannOpFun cov x v w (c • u) = c • riemannOpFun cov x v w u := by
  classical
  set X := smoothExtensionTangent (I := I) x v
  set Y := smoothExtensionTangent (I := I) x w
  set Zu := smoothExtensionFiber (I := I) (F := F) (V := V) x u
  set Zcu : Π b : M, V b := (fun _ : M => c) • smoothExtensionFiber (I := I) (F := F) (V := V) x u
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X) := smoothExtensionTangent_contMDiff x v
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) := smoothExtensionTangent_contMDiff x w
  have hZu : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Zu) := smoothExtensionFiber_contMDiff x u
  have hcsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
  have hZcu : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Zcu) := hcsmooth.smul_section hZu
  have hX_eq : X x = v := smoothExtensionTangent_eq x v
  have hY_eq : Y x = w := smoothExtensionTangent_eq x w
  have hZu_eq : Zu x = u := smoothExtensionFiber_eq (V := V) x u
  have hZcu_eq : Zcu x = c • u := by change c • Zu x = c • u; rw [hZu_eq]
  rw [riemannOpFun_well_defined (cov := cov) hX hY hZcu hX_eq hY_eq hZcu_eq,
      riemannOpFun_well_defined (cov := cov) hX hY hZu hX_eq hY_eq hZu_eq]
  exact riemannSec_smul_third_smooth (cov := cov) hcsmooth hX hY hZu

/-! ## The bundled trilinear continuous linear map

Putting everything together: at each point `x`, `riemannOp cov x` is the continuous trilinear
form on `T_x M × T_x M × V x` valued in `V x`, given by `riemannOpFun cov x`. The proof packages
the linearity lemmas via `LinearMap.toContinuousLinearMap` (in finite dimensions). -/

/-- The Z-slot linear map for fixed `(v, w) ∈ T_x M × T_x M`. -/
private def riemannOp_Zslot
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (x : M) (v w : TangentSpace I x) : V x →ₗ[ℝ] V x where
  toFun u := riemannOpFun cov x v w u
  map_add' u u' := riemannOpFun_add_third (cov := cov) x v w u u'
  map_smul' c u := riemannOpFun_smul_third (cov := cov) x v w c u

/-- The Z-slot continuous linear map for fixed `(v, w) ∈ T_x M × T_x M`. -/
private noncomputable def riemannOp_Zslot_clm
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (x : M) (v w : TangentSpace I x) : V x →L[ℝ] V x :=
  haveI : T2Space (V x) := FiberBundle.t2Space F V x
  haveI : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  LinearMap.toContinuousLinearMap (riemannOp_Zslot (cov := cov) x v w)

/-- The Y-slot linear map for fixed `v ∈ T_x M`, valued in continuous linear maps. -/
private def riemannOp_Yslot
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (x : M) (v : TangentSpace I x) : TangentSpace I x →ₗ[ℝ] V x →L[ℝ] V x where
  toFun w := riemannOp_Zslot_clm (cov := cov) x v w
  map_add' w w' := by
    haveI : T2Space (V x) := FiberBundle.t2Space F V x
    haveI : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
    ext u
    change riemannOpFun cov x v (w + w') u =
      riemannOpFun cov x v w u + riemannOpFun cov x v w' u
    exact riemannOpFun_add_right (cov := cov) x v w w' u
  map_smul' c w := by
    haveI : T2Space (V x) := FiberBundle.t2Space F V x
    haveI : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
    ext u
    change riemannOpFun cov x v (c • w) u = c • riemannOpFun cov x v w u
    exact riemannOpFun_smul_right (cov := cov) x v c w u

/-- The Y-slot continuous linear map for fixed `v ∈ T_x M`. -/
private noncomputable def riemannOp_Yslot_clm
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (x : M) (v : TangentSpace I x) : TangentSpace I x →L[ℝ] V x →L[ℝ] V x :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (riemannOp_Yslot (cov := cov) x v)

/-- The X-slot linear map. -/
private def riemannOp_Xslot
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →L[ℝ] V x →L[ℝ] V x where
  toFun v := riemannOp_Yslot_clm (cov := cov) x v
  map_add' v v' := by
    haveI : T2Space (V x) := FiberBundle.t2Space F V x
    haveI : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
    haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
    haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
    ext w u
    change riemannOpFun cov x (v + v') w u =
      riemannOpFun cov x v w u + riemannOpFun cov x v' w u
    exact riemannOpFun_add_left (cov := cov) x v v' w u
  map_smul' c v := by
    haveI : T2Space (V x) := FiberBundle.t2Space F V x
    haveI : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
    haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
    haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
    ext w u
    change riemannOpFun cov x (c • v) w u = c • riemannOpFun cov x v w u
    exact riemannOpFun_smul_left (cov := cov) x c v w u

/-- **The bundled trilinear continuous linear form `riemannOp`.** At each point `x`, this is
the continuous trilinear form `T_x M × T_x M × V x → V x` given by the section-level Riemann
formula evaluated on smooth global extensions of the fibre vectors. -/
noncomputable def riemannOp
    (cov : CovariantDerivative I F V)
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞] (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x →L[ℝ] V x :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (riemannOp_Xslot (cov := cov) x)

/-- The defining identity: `riemannOp cov x (v) (w) (u) = riemannOpFun cov x v w u`. -/
theorem riemannOp_apply_fun
    (cov : CovariantDerivative I F V)
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (x : M) (v w : TangentSpace I x) (u : V x) :
    riemannOp cov x v w u = riemannOpFun cov x v w u := rfl

/-- **Application formula for `riemannOp` on smooth sections.** For smooth global sections
`X, Y` of `TM` and `Z` of `V`, we have `riemannOp cov x (X x) (Y x) (Z x) =
riemannSec cov X Y Z x`. -/
theorem riemannOp_apply_smooth
    (cov : CovariantDerivative I F V)
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z)) :
    riemannOp cov x (X x) (Y x) (Z x) = riemannSec cov X Y Z x := by
  rw [riemannOp_apply_fun]
  exact riemannOpFun_eq_riemannSec (cov := cov) hX hY hZ

/-- **Antisymmetry of `riemannOp` in the first two arguments.** At each point `x`, the bundled
trilinear form satisfies `R(v, w, u) = -R(w, v, u)`. -/
lemma riemannOp_swap
    (cov : CovariantDerivative I F V)
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (x : M) (v w : TangentSpace I x) (u : V x) :
    riemannOp cov x v w u = -riemannOp cov x w v u := by
  classical
  -- Use smooth extensions and the section-level antisymmetry `riemannSec_swap`.
  set X := smoothExtensionTangent (I := I) x v
  set Y := smoothExtensionTangent (I := I) x w
  set Z := smoothExtensionFiber (I := I) (F := F) (V := V) x u
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X) := smoothExtensionTangent_contMDiff x v
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) := smoothExtensionTangent_contMDiff x w
  have hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z) := smoothExtensionFiber_contMDiff x u
  have hX_eq : X x = v := smoothExtensionTangent_eq x v
  have hY_eq : Y x = w := smoothExtensionTangent_eq x w
  have hZ_eq : Z x = u := smoothExtensionFiber_eq (V := V) x u
  rw [show v = X x from hX_eq.symm, show w = Y x from hY_eq.symm, show u = Z x from hZ_eq.symm,
      riemannOp_apply_smooth (cov := cov) hX hY hZ,
      riemannOp_apply_smooth (cov := cov) hY hX hZ,
      riemannSec_swap]

end RiemannOpBundling

end Connection
end Integral
end DifferentialGeometry
