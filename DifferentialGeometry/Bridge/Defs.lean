import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Geometry.Manifold.BumpFunction
import DifferentialGeometry.Algebra.VectorField
import Mathlib.LinearAlgebra.Multilinear.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Bridge Definitions

## Main Definitions

* `VectorField` : A smooth vector field on a manifold `M`, defined as a `ContMDiffSection`
  of the tangent bundle.
* `ScalarField` : A smooth scalar field on `M`, defined as a bundled `C^∞` map `M → 𝕜`.
  Notation: `C^∞(M)`.
-/

namespace DifferentialGeometry.Bridge

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ⊤ M]

/-- A smooth vector field on `M`: a smooth section of the tangent bundle,
i.e. a bundled map `∀ x : M, TangentSpace I x` that is `C^∞`. -/
def VectorField :=
  ContMDiffSection I E (⊤ : ℕ∞) (TangentSpace I : M → Type _)

instance : DFunLike (VectorField (I := I) (M := M)) M (TangentSpace I) :=
  inferInstanceAs (DFunLike (ContMDiffSection I E (⊤ : ℕ∞) (TangentSpace I : M → Type _)) M _)

/-- A smooth scalar field on `M`: a bundled `C^∞` map from `M` to `𝕜`. -/
def ScalarField :=
  ContMDiffMap I (modelWithCornersSelf 𝕜 𝕜) M 𝕜 (⊤ : ℕ∞)

instance : FunLike (ScalarField (I := I) (M := M)) M 𝕜 :=
  inferInstanceAs (FunLike (ContMDiffMap I (modelWithCornersSelf 𝕜 𝕜) M 𝕜 (⊤ : ℕ∞)) M 𝕜)

scoped notation "C^∞(" M ")" => ScalarField (M := M)

/-- The action of a vector field `V` on a scalar field `f` by derivation:
`(V f)(x) = (mfderiv f x)(V x)`, i.e. the directional derivative of `f` along `V`. -/
noncomputable def VectorField.action
    (V : VectorField (I := I) (M := M)) (f : ScalarField (I := I) (M := M)) :
    ScalarField (I := I) (M := M) :=
  ⟨fun x => mfderiv I 𝓘(𝕜) f x (V x), by
    -- ContMDiff is ∀ x, ContMDiffAt, so introduce an arbitrary base point x₀.
    intro x₀
    set e₀ := trivializationAt E (TangentSpace I) x₀
    -- Step 1: x ↦ mfderiv I 𝓘(𝕜) f x expressed in tangent coordinates at x₀ is smooth.
    have hdf : ContMDiffAt I 𝓘(𝕜, E →L[𝕜] 𝕜) (⊤ : ℕ∞)
        (inTangentCoordinates I 𝓘(𝕜) id f (mfderiv I 𝓘(𝕜) f) x₀) x₀ :=
      f.contMDiff.contMDiffAt.mfderiv_const (WithTop.coe_le_coe.mpr le_top)
    -- Step 2: the section V read through the trivialization e₀ gives a smooth E-valued map.
    have hV : ContMDiffAt I 𝓘(𝕜, E) (⊤ : ℕ∞) (fun x => (e₀ ⟨x, V x⟩).2) x₀ :=
      (Bundle.contMDiffAt_section (n := (⊤ : ℕ∞)) x₀).mp V.contMDiff.contMDiffAt
    -- Step 3: applying the smooth CLM-valued map to the smooth E-valued map is smooth.
    -- The combined expression equals mfderiv I 𝓘(𝕜) f x (V x) on e₀.baseSet (a nhd of x₀),
    -- because the target-side coordinate change is trivial (𝓘(𝕜) model space) and
    -- the source-side trivialization and its inverse cancel on V x.
    refine (hdf.clm_apply hV).congr_of_eventuallyEq ?_
    filter_upwards
      [e₀.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (TangentSpace I) x₀)]
    intro x hx
    -- Unfold inTangentCoordinates and inCoordinates; the target-side coord change equals 1
    -- (by continuousLinearMapAt_model_space), so after comp_apply the goal has `(1 : 𝕜 →L[𝕜] 𝕜) v`.
    -- We use `change` (definitional equality) to strip the `1` application, then congr + inverse.
    simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates, Function.id_def,
      TangentBundle.continuousLinearMapAt_model_space, ContinuousLinearMap.comp_apply]
    -- After simp, the goal is `mfderiv f x (V x) = 1 (mfderiv f x (symmL e₀ x (...)))`.
    -- Use `change` (definitional equality, since `(1 : 𝕜 →L[𝕜] 𝕜) v = v`) to strip the `1`.
    change mfderiv I 𝓘(𝕜) f x (V x) = mfderiv I 𝓘(𝕜) f x (e₀.symmL 𝕜 x ((e₀ ⟨x, V x⟩).2))
    congr 1
    -- Goal: V x = e₀.symmL 𝕜 x ((e₀ ⟨x, V x⟩).2).
    -- Since symmL has toFun := e.symm, symm_apply_apply_mk gives e₀.symm x (...) = V x.
    exact (Bundle.Trivialization.symm_apply_apply_mk e₀ hx (V x)).symm⟩

/-- Smooth scalar fields form a commutative ring under pointwise addition and multiplication. -/
noncomputable instance : CommRing (ScalarField (I := I) (M := M)) :=
  inferInstanceAs (CommRing (ContMDiffMap I (modelWithCornersSelf 𝕜 𝕜) M 𝕜 (⊤ : ℕ∞)))

/-- Smooth vector fields form an additive commutative group under pointwise addition. -/
noncomputable instance : AddCommGroup (VectorField (I := I) (M := M)) :=
  inferInstanceAs (AddCommGroup (ContMDiffSection I E (⊤ : ℕ∞) (TangentSpace I : M → Type _)))

/-- Smooth vector fields form a module over smooth scalar fields by pointwise scaling. -/
noncomputable instance :
    Module (ScalarField (I := I) (M := M)) (VectorField (I := I) (M := M)) where
  smul f V := ⟨fun x => f x • V x, f.contMDiff.smul_section V.contMDiff⟩
  smul_add f V W := DFunLike.ext _ _ fun x => smul_add (f x) (V x) (W x)
  add_smul f g V := DFunLike.ext _ _ fun x => add_smul (f x) (g x) (V x)
  mul_smul f g V := DFunLike.ext _ _ fun x => mul_smul (f x) (g x) (V x)
  one_smul V     := DFunLike.ext _ _ fun x => one_smul 𝕜 (V x)
  zero_smul V    := DFunLike.ext _ _ fun x => zero_smul 𝕜 (V x)
  smul_zero f    := DFunLike.ext _ _ fun x => smul_zero (f x)



/-- The action of a vector field on a product of scalar fields obeys the Leibniz rule:
`V (f * g) = f * V g + g * V f`. -/
theorem VectorField.action_leibniz
    (V : VectorField (I := I) (M := M)) (f g : ScalarField (I := I) (M := M)) :
    V.action (f * g) = f * V.action g + g * V.action f := by
  apply DFunLike.ext; intro x
  -- Annotate with `𝕜` as the explicit target type so that `hf.mul hg` unifies
  -- (both mfderivslands in `TangentSpace I x →L[𝕜] 𝕜`, not at distinct base points).
  have hf : HasMFDerivAt I 𝓘(𝕜) ⇑f x (mfderiv I 𝓘(𝕜) ⇑f x : TangentSpace I x →L[𝕜] 𝕜) :=
    ((f.contMDiff x).mdifferentiableAt (mod_cast ENat.top_ne_zero)).hasMFDerivAt
  have hg : HasMFDerivAt I 𝓘(𝕜) ⇑g x (mfderiv I 𝓘(𝕜) ⇑g x : TangentSpace I x →L[𝕜] 𝕜) :=
    ((g.contMDiff x).mdifferentiableAt (mod_cast ENat.top_ne_zero)).hasMFDerivAt
  -- Product rule at V x: evaluate the CLM equality pointwise.
  have prod := congr_arg (· (V x)) (hf.mul hg).mfderiv
  exact prod

/-- Vector fields act on scalar fields by the directional derivative,
satisfying the abstract derivation interface. -/
noncomputable instance :
    AbstractDerivationAction (ScalarField (I := I) (M := M)) (VectorField (I := I) (M := M)) where
  action V f := V.action f

/-- The Lie bracket of two smooth vector fields, defined pointwise via Mathlib's
`VectorField.mlieBracket`. The result is again a smooth vector field. -/
noncomputable def VectorField.lieBracket [CompleteSpace E]
    (X Y : VectorField (I := I) (M := M)) :
    VectorField (I := I) (M := M) where
  toFun x := _root_.VectorField.mlieBracket I X Y x
  contMDiff_toFun := by
    intro x₀
    simp_rw [← _root_.VectorField.mlieBracketWithin_univ]
    exact (X.contMDiff x₀).contMDiffWithinAt.mlieBracketWithin_vectorField
      (Y.contMDiff x₀).contMDiffWithinAt uniqueMDiffOn_univ (Set.mem_univ x₀)
      (by simp [minSmoothness_of_isRCLikeNormedField])

/-- Smooth vector fields form a Lie algebra under the Lie bracket. -/
noncomputable instance [CompleteSpace E] :
    AbstractLieBracket (VectorField (I := I) (M := M)) where
  bracket := VectorField.lieBracket

/-- The Lie bracket product rule for function-scalar multiplication on the left:
`[c • X, Y](x₀) = c(x₀) • [X, Y](x₀) - (Y c)(x₀) • X(x₀)`.
This is the manifold-level analogue of `VectorField.mlieBracket_smul_left`. -/
private lemma mlieBracket_fun_smul_left [CompleteSpace E]
    (c : ScalarField (I := I) (M := M)) (X Y : VectorField (I := I) (M := M)) (x₀ : M) :
    _root_.VectorField.mlieBracket I (fun y ↦ c y • X y) (⇑Y) x₀ =
      c x₀ • _root_.VectorField.mlieBracket I (⇑X) (⇑Y) x₀ -
        NormedSpace.fromTangentSpace (c x₀) ((mfderiv I 𝓘(𝕜) (⇑c) x₀) (Y x₀)) • X x₀ := by
  have h := _root_.VectorField.mlieBracket_smul_left (I := I) (f := ⇑c) (V := ⇑X) (W := ⇑Y)
    (x := x₀)
    ((c.contMDiff x₀).mdifferentiableAt (mod_cast ENat.top_ne_zero))
    ((X.contMDiff x₀).mdifferentiableAt (mod_cast ENat.top_ne_zero))
  change _root_.VectorField.mlieBracket I (⇑c • ⇑X) (⇑Y) x₀ = _
  rw [h]; simp only [neg_smul]; abel

/-- The concrete directional derivative and Lie bracket on a manifold satisfy the abstract
derivation rules. -/
noncomputable instance [CompleteSpace E] :
    DerivationRules (ScalarField (I := I) (M := M)) (VectorField (I := I) (M := M)) where
  action_add_left X Y f := by
    apply DFunLike.ext; intro x
    exact map_add (mfderiv I 𝓘(𝕜) f x) (X x) (Y x)
  action_add_right X f g := by
    apply DFunLike.ext; intro x
    have hf : HasMFDerivAt I 𝓘(𝕜) ⇑f x (mfderiv I 𝓘(𝕜) ⇑f x : TangentSpace I x →L[𝕜] 𝕜) :=
      ((f.contMDiff x).mdifferentiableAt (mod_cast ENat.top_ne_zero)).hasMFDerivAt
    have hg : HasMFDerivAt I 𝓘(𝕜) ⇑g x (mfderiv I 𝓘(𝕜) ⇑g x : TangentSpace I x →L[𝕜] 𝕜) :=
      ((g.contMDiff x).mdifferentiableAt (mod_cast ENat.top_ne_zero)).hasMFDerivAt
    exact congr_arg (· (X x)) (hf.add hg).mfderiv
  action_smul_left c X f := by
    apply DFunLike.ext; intro x
    exact map_smul (mfderiv I 𝓘(𝕜) f x) (c x) (X x)
  action_smul_right X c f := by
    change X.action (c * f) = X.action c * f + c * X.action f
    rw [X.action_leibniz c f]; ring
  bracket_add_left X Y Z := by
    apply DFunLike.ext; intro x
    exact _root_.VectorField.mlieBracket_add_left
      ((X.contMDiff x).mdifferentiableAt (mod_cast ENat.top_ne_zero))
      ((Y.contMDiff x).mdifferentiableAt (mod_cast ENat.top_ne_zero))
  bracket_add_right X Y Z := by
    apply DFunLike.ext; intro x
    exact _root_.VectorField.mlieBracket_add_right
      ((Y.contMDiff x).mdifferentiableAt (mod_cast ENat.top_ne_zero))
      ((Z.contMDiff x).mdifferentiableAt (mod_cast ENat.top_ne_zero))
  bracket_smul_left c X Y := by
    apply DFunLike.ext; intro x₀
    exact mlieBracket_fun_smul_left c X Y x₀
  bracket_smul_right c X Y := by
    apply DFunLike.ext; intro x₀
    have h := _root_.VectorField.mlieBracket_smul_right (I := I) (f := ⇑c) (V := ⇑X) (W := ⇑Y)
      (x := x₀)
      ((c.contMDiff x₀).mdifferentiableAt (mod_cast ENat.top_ne_zero))
      ((Y.contMDiff x₀).mdifferentiableAt (mod_cast ENat.top_ne_zero))
    change _root_.VectorField.mlieBracket I (⇑X) (⇑c • ⇑Y) x₀ =
      c x₀ • _root_.VectorField.mlieBracket I (⇑X) (⇑Y) x₀ +
        NormedSpace.fromTangentSpace (c x₀) ((mfderiv I 𝓘(𝕜) (⇑c) x₀) (X x₀)) • Y x₀
    rw [h, add_comm]
  bracket_antisymm X Y := by
    apply DFunLike.ext; intro x
    exact _root_.VectorField.mlieBracket_swap_apply

/-- The action of smooth vector fields on smooth scalar fields is linear in the vector field. -/
noncomputable instance [CompleteSpace E] :
    ActionLinear (ScalarField (I := I) (M := M)) (VectorField (I := I) (M := M)) where
  action_add X Y f := by
    apply DFunLike.ext; intro x
    exact map_add (mfderiv I 𝓘(𝕜) f x) (X x) (Y x)

/-- Pointwise commutator identity: `[X,Y](f)(x₀) = X(Yf)(x₀) - Y(Xf)(x₀)`.

The proof reduces to the vector-space identity `VectorField.fderivWithin_apply_lieBracket` via the
chart `extChartAt I x₀`, following the same coordinate strategy as `mlieBracket_fun_smul_left`:
1. Express the LHS `mfderiv f x₀ (mlieBracket I X Y x₀)` in coordinates as
   `fderivWithin g (range I) y₀ (lieBracketWithin V' W' (range I) y₀)` where `g = f ∘ φ.symm`,
   using `mlieBracketWithin_apply` and the chain rule `hchain_f` with `D ∘ D⁻¹` cancellation.
2. Apply `fderivWithin_apply_lieBracket` to get the commutator in coordinates.
3. Show each RHS term `(X.action (Y.action f)) x₀` equals the corresponding fderivWithin
   expression via `hchain_at` (pointwise chain rule) and `EventuallyEq.fderivWithin_eq`. -/
private lemma lie_deriv_pointwise [CompleteSpace E]
    (X Y : VectorField (I := I) (M := M)) (f : ScalarField (I := I) (M := M)) (x₀ : M) :
    (VectorField.action (VectorField.lieBracket X Y) f) x₀ =
      (VectorField.action X (VectorField.action Y f)) x₀ -
        (VectorField.action Y (VectorField.action X f)) x₀ := by
  set φ := extChartAt I x₀; set y₀ := φ x₀
  set D := mfderiv I 𝓘(𝕜, E) (↑φ) x₀
  set Dψ := mfderivWithin 𝓘(𝕜, E) I (↑φ.symm) (Set.range I) y₀
  set V' := _root_.VectorField.mpullbackWithin 𝓘(𝕜, E) I (↑φ.symm) (⇑X) (Set.range I)
  set W' := _root_.VectorField.mpullbackWithin 𝓘(𝕜, E) I (↑φ.symm) (⇑Y) (Set.range I)
  set g := (⇑f) ∘ (↑φ.symm)
  have hx₀_src := mem_extChartAt_source (I := I) x₀
  have hy₀_tgt := φ.map_source hx₀_src
  have hy₀_range := extChartAt_target_subset_range x₀ hy₀_tgt
  have hud := I.uniqueDiffOn (𝕜 := 𝕜)
  have hD : ∀ v, D v = v := fun v ↦ by
    simp only [D, φ]; rw [(hasMFDerivAt_extChartAt (I := I) (mem_chart_source H x₀)).mfderiv,
      mfderiv_chartAt_eq_tangentCoordChange (I := I) (mem_chart_source H x₀)]
    exact tangentCoordChange_self (I := I) hx₀_src (v := v)
  have hDinv : ∀ v, D.inverse v = v := fun v ↦ (hD _).symm.trans
    (ContinuousLinearMap.ext_iff.mp (isInvertible_mfderiv_extChartAt hx₀_src).self_comp_inverse v)
  have hDψ : ∀ v, Dψ v = v := fun v ↦ by
    have h := ContinuousLinearMap.ext_iff.mp
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' (I := I) hx₀_src) v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
    rwa [hD] at h
  have hDψ_cancel (z) (hz : z ∈ φ.target) (v) :
      (mfderivWithin 𝓘(𝕜, E) I (↑φ.symm) (Set.range I) z)
        ((mfderivWithin 𝓘(𝕜, E) I (↑φ.symm) (Set.range I) z).inverse v) = v :=
    ContinuousLinearMap.ext_iff.mp
      (isInvertible_mfderivWithin_extChartAt_symm (I := I) hz).self_comp_inverse v
  have hpull (Z : VectorField (I := I) (M := M)) :
      (_root_.VectorField.mpullbackWithin 𝓘(𝕜, E) I (↑φ.symm) (⇑Z) (Set.range I)) y₀ = Z x₀ := by
    change Dψ.inverse (Z (φ.symm y₀)) = Z x₀
    rw [show ∀ v, Dψ.inverse v = v from fun v ↦
      (hDψ _).symm.trans (hDψ_cancel y₀ hy₀_tgt v), φ.left_inv hx₀_src]
  have hPd (Z : VectorField (I := I) (M := M)) : DifferentiableWithinAt 𝕜
      (_root_.VectorField.mpullbackWithin 𝓘(𝕜, E) I (↑φ.symm) (⇑Z) (Set.range I)) (Set.range I) y₀ := by
    have : MDifferentiableWithinAt I I.tangent
        (fun x ↦ (⟨x, Z x⟩ : TangentBundle I M)) Set.univ x₀ :=
      (Z.contMDiff x₀).mdifferentiableAt (mod_cast ENat.top_ne_zero)
    simpa [Set.preimage_univ] using this.differentiableWithinAt_mpullbackWithin_vectorField
  have hchain (z) (hz : z ∈ φ.target) : fderivWithin 𝕜 g (Set.range I) z =
      (mfderiv I 𝓘(𝕜) (⇑f) (φ.symm z)).comp
        (mfderivWithin 𝓘(𝕜, E) I (↑φ.symm) (Set.range I) z) := by
    rw [show g = (⇑f) ∘ (↑φ.symm) from rfl, ← mfderivWithin_eq_fderivWithin]
    exact mfderiv_comp_mfderivWithin_of_eq (I' := I)
      ((f.contMDiff (φ.symm z)).mdifferentiableAt (mod_cast ENat.top_ne_zero))
      (mdifferentiableWithinAt_extChartAt_symm hz)
      ((hud.uniqueDiffWithinAt (extChartAt_target_subset_range x₀ hz)).uniqueMDiffWithinAt) rfl
  have hmf_gen (h : ScalarField (I := I) (M := M)) (w) :
      mfderiv I 𝓘(𝕜) (⇑h) x₀ w = fderivWithin 𝕜 ((⇑h) ∘ ↑φ.symm) (Set.range I) y₀ w := by
    conv_rhs => rw [show fderivWithin 𝕜 ((⇑h) ∘ ↑φ.symm) (Set.range I) y₀ =
        (mfderiv I 𝓘(𝕜) (⇑h) x₀).comp Dψ from by
      rw [← mfderivWithin_eq_fderivWithin]; exact mfderiv_comp_mfderivWithin_of_eq (I' := I)
        ((h.contMDiff x₀).mdifferentiableAt (mod_cast ENat.top_ne_zero))
        (mdifferentiableWithinAt_extChartAt_symm hy₀_tgt)
        (hud.uniqueDiffWithinAt hy₀_range).uniqueMDiffWithinAt (φ.left_inv hx₀_src)]
    exact congr_arg _ (hDψ w).symm
  have hmf (w) : mfderiv I 𝓘(𝕜) (⇑f) x₀ w = fderivWithin 𝕜 g (Set.range I) y₀ w := hmf_gen f w
  have hcancel (Z : VectorField (I := I) (M := M)) (z) (hz : z ∈ φ.target) :
      fderivWithin 𝕜 g (Set.range I) z
        ((_root_.VectorField.mpullbackWithin 𝓘(𝕜, E) I (↑φ.symm) (⇑Z) (Set.range I)) z) =
        mfderiv I 𝓘(𝕜) (⇑f) (φ.symm z) (Z (φ.symm z)) := by
    conv_lhs => rw [hchain z hz]
    exact congr_arg _ (hDψ_cancel z hz _)
  have hcore := _root_.VectorField.fderivWithin_apply_lieBracket
    (((contMDiffAt_iff (I' := 𝓘(𝕜))).mp (f.contMDiff x₀)).2 : ContDiffWithinAt 𝕜 (⊤ : ℕ∞) g _ y₀)
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
    hud (I.range_subset_closure_interior hy₀_range) hy₀_range (hPd Y) (hPd X)
  have hLHS : ((X.lieBracket Y).action f) x₀ = fderivWithin 𝕜 g (Set.range I) y₀
      (_root_.VectorField.lieBracketWithin 𝕜 V' W' (Set.range I) y₀) := by
    change mfderiv I 𝓘(𝕜) (⇑f) x₀ (_root_.VectorField.mlieBracket I (⇑X) (⇑Y) x₀) = _
    rw [← _root_.VectorField.mlieBracketWithin_univ,
      _root_.VectorField.mlieBracketWithin_apply, Set.preimage_univ, Set.univ_inter, hmf, hDinv]
  have hRHS (Z U : VectorField (I := I) (M := M)) :
      (U.action (Z.action f)) x₀ = fderivWithin 𝕜
        (fun z ↦ fderivWithin 𝕜 g (Set.range I) z
          ((_root_.VectorField.mpullbackWithin 𝓘(𝕜, E) I (↑φ.symm) (⇑Z) (Set.range I)) z))
        (Set.range I) y₀
        ((_root_.VectorField.mpullbackWithin 𝓘(𝕜, E) I (↑φ.symm) (⇑U) (Set.range I)) y₀) := by
    change mfderiv I 𝓘(𝕜) (⇑(Z.action f)) x₀ (U x₀) = _
    rw [hmf_gen (Z.action f), ← hpull U]; congr 1
    exact Filter.EventuallyEq.fderivWithin_eq
      (by filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hy₀_tgt] with z hz
          exact (hcancel Z z hz).symm)
      (hcancel Z y₀ hy₀_tgt).symm
  rw [hLHS, hRHS Y X, hRHS X Y]; exact hcore

/-- The concrete Lie bracket on a manifold satisfies the commutator property:
`[X, Y](f) = X(Y(f)) − Y(X(f))`. -/
noncomputable instance [CompleteSpace E] :
    LieDerivation (ScalarField (I := I) (M := M)) (VectorField (I := I) (M := M)) where
  bracket_action X Y f := by
    apply DFunLike.ext; intro x₀
    exact lie_deriv_pointwise X Y f x₀

section NonDegeneracy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M] [T2Space M]

/-- On a real smooth manifold, vector fields are non-degenerate: if two vector fields have the
same action on every smooth scalar field, they are equal. The proof constructs, for each
continuous linear functional `L` on `TangentSpace I x = E`, a smooth scalar field `f = χ • (L ∘ φ)`
(using a smooth bump function `χ` and the chart `φ = extChartAt I x`) whose `mfderiv` at `x`
equals `L`. Hahn–Banach dual separation then gives `X x = Y x`. -/
noncomputable instance :
    VectorFieldNonDegenerate (ScalarField (I := I) (M := M))
      (VectorField (I := I) (M := M)) where
  eq_of_action_eq X Y h := by
    apply DFunLike.ext; intro x₀
    suffices ∀ L : E →L[ℝ] ℝ, L (X x₀) = L (Y x₀) from
      (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ) (V := E)).mpr this
    intro L
    -- Build f = χ • (L ∘ φ) where χ is a bump function, φ = extChartAt I x₀
    set φ := extChartAt I x₀
    obtain ⟨χ⟩ := (inferInstance : Nonempty (SmoothBumpFunction I x₀))
    have hLφ : ContMDiffOn I 𝓘(ℝ, ℝ) (⊤ : ℕ∞) (fun x => L (φ x)) (chartAt H x₀).source :=
      fun x hx => (L.contMDiffAt (𝕜 := ℝ)).comp_contMDiffWithinAt x
        (contMDiffOn_extChartAt (I := I) (x := x₀) x hx)
    -- Apply hypothesis to f
    have key := DFunLike.ext_iff.mp
      (h ⟨fun x => χ x • L (φ x), χ.contMDiff_smul hLφ⟩) x₀
    -- mfderiv f x₀ = mfderiv (L ∘ φ) x₀ since χ = 1 near x₀
    have hfnear : (fun x => χ x • L (φ x)) =ᶠ[nhds x₀] (fun x => L (φ x)) :=
      χ.eventuallyEq_one.mono fun x hx => by simp [show χ x = 1 from hx.symm ▸ rfl]
    change mfderiv I 𝓘(ℝ, ℝ) (fun x => χ x • L (φ x)) x₀ (X x₀) =
      mfderiv I 𝓘(ℝ, ℝ) (fun x => χ x • L (φ x)) x₀ (Y x₀) at key
    rw [hfnear.mfderiv_eq] at key
    -- mfderiv (L ∘ φ) x₀ = L via chain rule + mfderiv φ x₀ = id
    have hDid : ∀ v, mfderiv I 𝓘(ℝ, E) (⇑φ) x₀ v = v := fun v => by
      simp only [φ]
      rw [(hasMFDerivAt_extChartAt (I := I) (mem_chart_source H x₀)).mfderiv,
        mfderiv_chartAt_eq_tangentCoordChange (I := I) (mem_chart_source H x₀)]
      exact tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) x₀)
    -- Simplify mfderiv (L ∘ φ) x₀ v = L v via chain rule + mfderiv φ x₀ = id
    have hmfderiv_Lφ : ∀ v, mfderiv I 𝓘(ℝ, ℝ) (fun x => L (φ x)) x₀ v = L v := fun v => by
      change (mfderiv I 𝓘(ℝ, ℝ) (⇑L ∘ ⇑φ) x₀) v = L v
      rw [mfderiv_comp x₀ (L.mdifferentiableAt (𝕜 := ℝ))
        (mdifferentiableAt_extChartAt (I := I) (mem_chart_source H x₀))]
      erw [ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
      congr 1; exact hDid v
    exact (hmfderiv_Lφ (X x₀)).symm ▸ (hmfderiv_Lφ (Y x₀)).symm ▸ key

end NonDegeneracy

/-
  ## Tensor Calculus
-/

/-- Pure Tensor Algebra (Layer 1): Depends only on module structure, no geometry or calculus.
This is implemented by the analytic backend using multidimensional arrays. -/

abbrev TensorData (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] (r s : ℕ) :=
  MultilinearMap R (fun _ : Fin s => V) (MultilinearMap R (fun _ : Fin r => (V →ₗ[R] R)) R)

instance {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {r s : ℕ} : Zero (TensorData R V r s) := inferInstanceAs (Zero (MultilinearMap R (fun _ : Fin s => V) (MultilinearMap R (fun _ : Fin r => (V →ₗ[R] R)) R)))
instance {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {r s : ℕ} : Add (TensorData R V r s) := inferInstanceAs (Add (MultilinearMap R (fun _ : Fin s => V) (MultilinearMap R (fun _ : Fin r => (V →ₗ[R] R)) R)))
instance {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {r s : ℕ} : SMul R (TensorData R V r s) := inferInstanceAs (SMul R (MultilinearMap R (fun _ : Fin s => V) (MultilinearMap R (fun _ : Fin r => (V →ₗ[R] R)) R)))
def scalarToData {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (f : R) : TensorData R V 0 0 :=
  MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => V)
    (MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => (V →ₗ[R] R)) f)

def evalLinear {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (v : V) : (V →ₗ[R] R) →ₗ[R] R where
  toFun w := w v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def vectorToData {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (v : V) : TensorData R V 1 0 :=
  MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => V)
    (MultilinearMap.ofSubsingleton R (V →ₗ[R] R) R (0 : Fin 1) (evalLinear v))

class TensorAlgebra (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] where
  /-- Generic graded tensor type (r: contravariant, s: covariant) -/
  AbstractTensor : ℕ → ℕ → Type

  add {r s : ℕ} : AbstractTensor r s → AbstractTensor r s → AbstractTensor r s -- done
  smul {r s : ℕ} : R → AbstractTensor r s → AbstractTensor r s -- done
  tensor_prod {r1 s1 r2 s2 : ℕ} : AbstractTensor r1 s1 → AbstractTensor r2 s2 → AbstractTensor (r1 + r2) (s1 + s2) -- done

  -- Embedding & Extraction
  fromData {r s : ℕ} : TensorData R V r s → AbstractTensor r s
  toData {r s : ℕ} : AbstractTensor r s → TensorData R V r s

  -- Identity Operator (Kronecker Delta)
  delta_tensor : AbstractTensor 1 1

  -- Extraction
  toScalar : AbstractTensor 0 0 → R

  -- Permutations (Routing Mechanism)
  swap_contravariant {r s : ℕ} (i j : Fin r) : AbstractTensor r s → AbstractTensor r s
  swap_covariant {r s : ℕ} (i j : Fin s) : AbstractTensor r s → AbstractTensor r s

  /-- General contraction between one contravariant and one covariant slot -/
  contract {r s : ℕ} : AbstractTensor (r + 1) (s + 1) → AbstractTensor r s

  --  Axioms:
  -- 1. Linearity of Contraction:
  contract_add {r s : ℕ} : ∀ T1 T2 : AbstractTensor (r + 1) (s + 1), contract (add T1 T2) = add (contract T1) (contract T2)
  contract_smul {r s : ℕ} : ∀ (f : R) (T : AbstractTensor (r + 1) (s + 1)), contract (smul f T) = smul f (contract T)

  -- Evaluation Isomorphism Axioms
  fromData_toData {r s : ℕ} : ∀ (T : AbstractTensor r s), fromData (toData T) = T
  toData_fromData {r s : ℕ} : ∀ (D : TensorData R V r s), toData (fromData D) = D
  toData_add {r s : ℕ} : ∀ T1 T2 : AbstractTensor r s, toData (add T1 T2) = toData T1 + toData T2
  toData_smul {r s : ℕ} : ∀ (c : R) (T : AbstractTensor r s), toData (smul c T) = c • toData T
  toData_swap_covariant {r s : ℕ} : ∀ (i j : Fin s) (T : AbstractTensor r s) (m : Fin s → V) (n : Fin r → (V →ₗ[R] R)),
    toData (swap_covariant i j T) m n = toData T (m ∘ Equiv.swap i j) n

  -- For any tensor T of rank (r, s+2), swapping it's first two covariant slots then contracting with X ⊗ Y
  -- is equivalent to contracting the original tensor with Y ⊗ X.
  contract_swap_covariant_eval : ∀ {r s : ℕ} (X Y : V) (T : AbstractTensor r (s + 2)),
    contract (r:=r) (s:=s) (contract (r:=r+1) (s:=s+1) (tensor_prod (r1:=r) (s1:=s+2) (r2:=2) (s2:=0) (swap_covariant 0 1 T) (tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromData (vectorToData X)) (fromData (vectorToData Y))))) =
    contract (r:=r) (s:=s) (contract (r:=r+1) (s:=s+1) (tensor_prod (r1:=r) (s1:=s+2) (r2:=2) (s2:=0) T (tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromData (vectorToData Y)) (fromData (vectorToData X)))))

  -- Evaluation of double contraction of T ⊗ X ⊗ Y matches data evaluation
  eval02_axiom : ∀ (T : AbstractTensor 0 2) (X Y : V),
    (toData (contract (r:=0) (s:=0) (contract (r:=1) (s:=1) (tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) T (tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromData (vectorToData X)) (fromData (vectorToData Y))))))) ![] ![] =
    (toData T) ![X, Y] ![]

  -- 2. Scalar Definition:
  toScalar_add : ∀ T1 T2 : AbstractTensor 0 0, toScalar (add T1 T2) = toScalar T1 + toScalar T2
  toScalar_smul : ∀ (c : R) (T : AbstractTensor 0 0), toScalar (smul c T) = c * toScalar T

  tensor_prod_add_left : ∀ {r1 s1 r2 s2 : ℕ} (T1 T2 : AbstractTensor r1 s1) (T3 : AbstractTensor r2 s2),
    tensor_prod (add T1 T2) T3 = add (tensor_prod T1 T3) (tensor_prod T2 T3)
  tensor_prod_add_right : ∀ {r1 s1 r2 s2 : ℕ} (T1 : AbstractTensor r1 s1) (T2 T3 : AbstractTensor r2 s2),
    tensor_prod T1 (add T2 T3) = add (tensor_prod T1 T2) (tensor_prod T1 T3)
  tensor_prod_smul_left : ∀ {r1 s1 r2 s2 : ℕ} (c : R) (T1 : AbstractTensor r1 s1) (T2 : AbstractTensor r2 s2),
    tensor_prod (smul c T1) T2 = smul c (tensor_prod T1 T2)
  tensor_prod_smul_right : ∀ {r1 s1 r2 s2 : ℕ} (c : R) (T1 : AbstractTensor r1 s1) (T2 : AbstractTensor r2 s2),
    tensor_prod T1 (smul c T2) = smul c (tensor_prod T1 T2)

namespace TensorAlgebra

/-
Generalized Contraction.
-/
def contract_general {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  {r s : ℕ} (i : Fin (r + 1)) (j : Fin (s + 1)) (T : AbstractTensor R V (r + 1) (s + 1)) : AbstractTensor R V r s :=
  contract (swap_covariant 0 j (swap_contravariant 0 i T))

end TensorAlgebra


-- The following is used to protect previous structure from failing.

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]

def fromScalar (f : R) : TensorAlgebra.AbstractTensor R V 0 0 := TensorAlgebra.fromData (scalarToData f)
def fromVector (X : V) : TensorAlgebra.AbstractTensor R V 1 0 := TensorAlgebra.fromData (vectorToData X)

lemma vectorToData_add {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (X Y : V) :
  vectorToData (R:=R) (V:=V) (X + Y) = vectorToData (R:=R) X + vectorToData (R:=R) Y := by
  ext m n
  dsimp [vectorToData, evalLinear, MultilinearMap.constOfIsEmpty, MultilinearMap.ofSubsingleton]
  rw [LinearMap.map_add]

lemma vectorToData_smul {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (c : R) (X : V) :
  vectorToData (R:=R) (V:=V) (c • X) = c • vectorToData (R:=R) X := by
  ext m n
  dsimp [vectorToData, evalLinear, MultilinearMap.constOfIsEmpty, MultilinearMap.ofSubsingleton]
  rw [LinearMap.map_smul]
  rfl

lemma fromVector_add (X Y : V) : fromVector (R:=R) (X + Y) = TensorAlgebra.add (fromVector (R:=R) X) (fromVector (R:=R) Y) := by
  dsimp [fromVector]
  rw [vectorToData_add (R:=R) X Y]
  have h_add : TensorAlgebra.toData (TensorAlgebra.add (TensorAlgebra.fromData (vectorToData (R:=R) X)) (TensorAlgebra.fromData (vectorToData (R:=R) Y))) =
    vectorToData (R:=R) X + vectorToData (R:=R) Y := by
    rw [TensorAlgebra.toData_add, TensorAlgebra.toData_fromData, TensorAlgebra.toData_fromData]
  rw [← h_add, TensorAlgebra.fromData_toData]

lemma fromVector_smul (c : R) (X : V) : fromVector (R:=R) (c • X) = TensorAlgebra.smul c (fromVector (R:=R) X) := by
  dsimp [fromVector]
  rw [vectorToData_smul (R:=R) c X]
  have h_smul : TensorAlgebra.toData (TensorAlgebra.smul c (TensorAlgebra.fromData (vectorToData (R:=R) X))) = c • vectorToData (R:=R) X := by
    rw [TensorAlgebra.toData_smul, TensorAlgebra.toData_fromData]
  rw [← h_smul, TensorAlgebra.fromData_toData]



end DifferentialGeometry.Bridge
