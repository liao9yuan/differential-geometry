import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import DifferentialGeometry.Algebra.VectorField
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Geometry.Connection

set_option autoImplicit false
set_option linter.style.longLine false

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

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ⊤ M]

/-- A smooth vector field on `M`: a smooth section of the tangent bundle,
i.e. a bundled map `∀ x : M, TangentSpace I x` that is `C^∞`. -/
def VectorField :=
  ContMDiffSection I E ⊤ (TangentSpace I : M → Type _)

instance : DFunLike (VectorField (I := I) (M := M)) M (TangentSpace I) :=
  inferInstanceAs (DFunLike (ContMDiffSection I E ⊤ (TangentSpace I : M → Type _)) M _)

/-- A smooth scalar field on `M`: a bundled `C^∞` map from `M` to `𝕜`. -/
def ScalarField :=
  ContMDiffMap I (modelWithCornersSelf 𝕜 𝕜) M 𝕜 ⊤

instance : FunLike (ScalarField (I := I) (M := M)) M 𝕜 :=
  inferInstanceAs (FunLike (ContMDiffMap I (modelWithCornersSelf 𝕜 𝕜) M 𝕜 ⊤) M 𝕜)

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
    have hdf : ContMDiffAt I 𝓘(𝕜, E →L[𝕜] 𝕜) ⊤
        (inTangentCoordinates I 𝓘(𝕜) id f (mfderiv I 𝓘(𝕜) f) x₀) x₀ :=
      f.contMDiff.contMDiffAt.mfderiv_const le_top
    -- Step 2: the section V read through the trivialization e₀ gives a smooth E-valued map.
    have hV : ContMDiffAt I 𝓘(𝕜, E) ⊤ (fun x => (e₀ ⟨x, V x⟩).2) x₀ :=
      (Bundle.contMDiffAt_section x₀).mp V.contMDiff.contMDiffAt
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
    exact (Trivialization.symm_apply_apply_mk e₀ hx (V x)).symm⟩

/-- Smooth scalar fields form a commutative ring under pointwise addition and multiplication. -/
noncomputable instance : CommRing (ScalarField (I := I) (M := M)) :=
  inferInstanceAs (CommRing (ContMDiffMap I (modelWithCornersSelf 𝕜 𝕜) M 𝕜 ⊤))

/-- Smooth vector fields form an additive commutative group under pointwise addition. -/
noncomputable instance : AddCommGroup (VectorField (I := I) (M := M)) :=
  inferInstanceAs (AddCommGroup (ContMDiffSection I E ⊤ (TangentSpace I : M → Type _)))

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
    ((f.contMDiff x).mdifferentiableAt WithTop.top_ne_zero).hasMFDerivAt
  have hg : HasMFDerivAt I 𝓘(𝕜) ⇑g x (mfderiv I 𝓘(𝕜) ⇑g x : TangentSpace I x →L[𝕜] 𝕜) :=
    ((g.contMDiff x).mdifferentiableAt WithTop.top_ne_zero).hasMFDerivAt
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
      (Y.contMDiff x₀).contMDiffWithinAt uniqueMDiffOn_univ (Set.mem_univ x₀) le_top

/-- Smooth vector fields form a Lie algebra under the Lie bracket. -/
noncomputable instance [CompleteSpace E] :
    AbstractLieBracket (VectorField (I := I) (M := M)) where
  bracket := VectorField.lieBracket

/-- The Lie bracket product rule for function-scalar multiplication on the left:
`[c • X, Y](x₀) = c(x₀) • [X, Y](x₀) - (Y c)(x₀) • X(x₀)`.
This is the manifold-level analogue of `VectorField.lieBracketWithin_smul_left`. -/
private lemma mlieBracket_fun_smul_left [CompleteSpace E]
    (c : ScalarField (I := I) (M := M)) (X Y : VectorField (I := I) (M := M)) (x₀ : M) :
    _root_.VectorField.mlieBracket I (fun y ↦ c y • X y) (⇑Y) x₀ =
      c x₀ • _root_.VectorField.mlieBracket I (⇑X) (⇑Y) x₀ -
        (mfderiv I 𝓘(𝕜) (⇑c) x₀) (Y x₀) • X x₀ := by
  -- Unfold to mlieBracketWithin in coordinates
  simp only [← _root_.VectorField.mlieBracketWithin_univ,
    _root_.VectorField.mlieBracketWithin_apply, Set.preimage_univ, Set.univ_inter]
  -- Set up abbreviations for the coordinate representation
  set φ := extChartAt I x₀
  set y₀ := φ x₀
  set D := mfderiv I 𝓘(𝕜, E) φ x₀
  set Dψ := mfderivWithin 𝓘(𝕜, E) I φ.symm (Set.range I) y₀
  set V' := _root_.VectorField.mpullbackWithin 𝓘(𝕜, E) I φ.symm (⇑X) (Set.range I)
  set W' := _root_.VectorField.mpullbackWithin 𝓘(𝕜, E) I φ.symm (⇑Y) (Set.range I)
  set g := (⇑c) ∘ φ.symm with hg_def
  -- Step 1: Pullback of (c • X) equals g • V'
  have hpull : _root_.VectorField.mpullbackWithin 𝓘(𝕜, E) I φ.symm
      (fun x ↦ c x • X x) (Set.range I) = fun z ↦ g z • V' z := by
    ext z
    simp only [_root_.VectorField.mpullbackWithin_apply, V', g, Function.comp, map_smul]
  rw [hpull]
  -- Step 2: Differentiability hypotheses
  have hx₀_src : x₀ ∈ (extChartAt I x₀).source := mem_extChartAt_source x₀
  have hy₀_tgt : y₀ ∈ (extChartAt I x₀).target := (extChartAt I x₀).map_source hx₀_src
  have hc_mdiff : MDifferentiableAt I 𝓘(𝕜) (⇑c) x₀ :=
    (c.contMDiff x₀).mdifferentiableAt WithTop.top_ne_zero
  have hV_mdiff : MDifferentiableWithinAt I I.tangent
      (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) Set.univ x₀ :=
    (X.contMDiff x₀).mdifferentiableAt WithTop.top_ne_zero
  have hy₀_range : y₀ ∈ Set.range I := extChartAt_target_subset_range x₀ hy₀_tgt
  have hud : UniqueDiffWithinAt 𝕜 (Set.range I) y₀ :=
    I.uniqueDiffOn.uniqueDiffWithinAt hy₀_range
  have hg_diff : DifferentiableWithinAt 𝕜 g (Set.range I) y₀ := by
    rw [show g = (⇑c) ∘ φ.symm from rfl, ← mdifferentiableWithinAt_iff_differentiableWithinAt]
    have hc' : MDifferentiableAt I 𝓘(𝕜) (⇑c) (φ.symm y₀) := by
      rwa [φ.left_inv hx₀_src]
    exact hc'.comp_mdifferentiableWithinAt y₀
      (mdifferentiableWithinAt_extChartAt_symm hy₀_tgt)
  have hV'_diff : DifferentiableWithinAt 𝕜 V' (Set.range I) y₀ := by
    have := hV_mdiff.differentiableWithinAt_mpullbackWithin_vectorField
    simpa [Set.preimage_univ] using this
  -- Step 3: Apply the product rule (VectorField.lieBracketWithin_smul_left)
  rw [_root_.VectorField.lieBracketWithin_smul_left hg_diff hV'_diff hud]
  -- Step 4: Distribute D.inverse over the sum
  simp only [map_add, map_smul]
  -- Step 5: g y₀ = c x₀
  have hgy : g y₀ = c x₀ := congr_arg c (φ.left_inv hx₀_src)
  rw [hgy]
  -- Step 6: Key coordinate identities
  -- D and Dψ are mutual inverses (from the chart and its inverse)
  have hDφ_inv : D.IsInvertible := isInvertible_mfderiv_extChartAt hx₀_src
  have hDψ_inv : Dψ.IsInvertible := isInvertible_mfderivWithin_extChartAt_symm hy₀_tgt
  have hcomp' : Dψ.comp D = ContinuousLinearMap.id 𝕜 E :=
    mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (hy := hx₀_src)
  -- Helper: recover vector from double-inverse via mutual inverse cancellation
  -- D.inverse (Dψ.inverse v) = v, using: Dψ ∘ D = id, D ∘ D⁻¹ = id, Dψ ∘ Dψ⁻¹ = id
  have hcancel : ∀ v, D.inverse (Dψ.inverse v) = v := by
    intro v
    set w := D.inverse (Dψ.inverse v)
    have h1 : D w = Dψ.inverse v := by
      have := ContinuousLinearMap.ext_iff.mp hDφ_inv.self_comp_inverse (Dψ.inverse v)
      simpa [ContinuousLinearMap.comp_apply] using this
    have h2 : Dψ (D w) = w := by
      have := ContinuousLinearMap.ext_iff.mp hcomp' w
      simpa [ContinuousLinearMap.comp_apply] using this
    have h3 : Dψ (Dψ.inverse v) = v := by
      have := ContinuousLinearMap.ext_iff.mp hDψ_inv.self_comp_inverse v
      simpa [ContinuousLinearMap.comp_apply] using this
    calc w = Dψ (D w) := h2.symm
      _ = Dψ (Dψ.inverse v) := by rw [h1]
      _ = v := h3
  -- 6a: D.inverse (V' y₀) = X x₀
  have hDinv_V : D.inverse (V' y₀) = X x₀ := by
    change D.inverse (Dψ.inverse (X (φ.symm y₀))) = X x₀
    rw [hcancel, φ.left_inv hx₀_src]
  -- 6b: Dψ applied to W' y₀ cancels to Y (φ.symm y₀)
  have hDψ_W : Dψ (W' y₀) = Y (φ.symm y₀) := by
    change Dψ (Dψ.inverse (Y (φ.symm y₀))) = Y (φ.symm y₀)
    exact hDψ_inv.self_apply_inverse (Y (φ.symm y₀))
  -- 6c: (fderivWithin g ...)(W' y₀) = (mfderiv c x₀)(Y x₀)
  have hfg_W : (fderivWithin 𝕜 g (Set.range I) y₀) (W' y₀) =
      (mfderiv I 𝓘(𝕜) (⇑c) x₀) (Y x₀) := by
    -- Chain rule: fderivWithin g = (mfderiv c x₀) ∘L Dψ
    have hchain : fderivWithin 𝕜 g (Set.range I) y₀ =
        (mfderiv I 𝓘(𝕜) (⇑c) x₀).comp Dψ := by
      rw [show g = (⇑c) ∘ φ.symm from rfl, ← mfderivWithin_eq_fderivWithin]
      exact mfderiv_comp_mfderivWithin_of_eq (I' := I) hc_mdiff
        (mdifferentiableWithinAt_extChartAt_symm hy₀_tgt)
        hud.uniqueMDiffWithinAt (φ.left_inv hx₀_src)
    rw [hchain]
    change (mfderiv I 𝓘(𝕜) (⇑c) x₀) (Dψ (W' y₀)) = (mfderiv I 𝓘(𝕜) (⇑c) x₀) (Y x₀)
    rw [hDψ_W, φ.left_inv hx₀_src]
  -- Step 7: Substitute and close by algebra
  rw [hDinv_V, hfg_W, add_comm, neg_smul, ← sub_eq_add_neg]

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
      ((f.contMDiff x).mdifferentiableAt WithTop.top_ne_zero).hasMFDerivAt
    have hg : HasMFDerivAt I 𝓘(𝕜) ⇑g x (mfderiv I 𝓘(𝕜) ⇑g x : TangentSpace I x →L[𝕜] 𝕜) :=
      ((g.contMDiff x).mdifferentiableAt WithTop.top_ne_zero).hasMFDerivAt
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
      ((X.contMDiff x).mdifferentiableAt WithTop.top_ne_zero)
      ((Y.contMDiff x).mdifferentiableAt WithTop.top_ne_zero)
  bracket_add_right X Y Z := by
    apply DFunLike.ext; intro x
    exact _root_.VectorField.mlieBracket_add_right
      ((Y.contMDiff x).mdifferentiableAt WithTop.top_ne_zero)
      ((Z.contMDiff x).mdifferentiableAt WithTop.top_ne_zero)
  bracket_smul_left c X Y := by
    apply DFunLike.ext; intro x₀
    exact mlieBracket_fun_smul_left c X Y x₀
  bracket_smul_right c X Y := by
    apply DFunLike.ext; intro x₀
    -- Use the smul-left identity for (c, Y, X) combined with antisymmetry
    have hleft := mlieBracket_fun_smul_left c Y X x₀
    -- hleft : mlieBracket I (c•Y) X x₀ = c x₀ • mlieBracket I Y X x₀ - (mfderiv c x₀)(X x₀) • Y x₀
    have hswap1 := _root_.VectorField.mlieBracket_swap_apply
      (I := I) (V := ⇑X) (W := fun y ↦ c y • Y y) (x := x₀)
    -- hswap1 : mlieBracket I X (c•Y) x₀ = -mlieBracket I (c•Y) X x₀
    have hswap2 := _root_.VectorField.mlieBracket_swap_apply
      (I := I) (V := ⇑Y) (W := ⇑X) (x := x₀)
    -- hswap2 : mlieBracket I Y X x₀ = -mlieBracket I X Y x₀
    show _root_.VectorField.mlieBracket I (⇑X) (fun y ↦ c y • Y y) x₀ =
      c x₀ • _root_.VectorField.mlieBracket I (⇑X) (⇑Y) x₀ +
        (mfderiv I 𝓘(𝕜) (⇑c) x₀) (X x₀) • Y x₀
    rw [hswap1, hleft, hswap2]
    simp only [smul_neg, neg_sub]
    abel
  bracket_antisymm X Y := by
    apply DFunLike.ext; intro x
    exact _root_.VectorField.mlieBracket_swap_apply


/-
  ## Tensor Calculus
-/


open AbstractDerivationAction

variable [AbstractLieBracket (VectorField (I := I) (M := M))]

/--
General tensor calculus.
`r` is contravariant rank, `s` is covariant rank.
-/
class AbstractTensorCalculus (metric : AbstractMetricTensor (ScalarField (I := I) (M := M)) (VectorField (I := I) (M := M))) (conn : AbstractLeviCivitaConnection metric) where
  /-- Generic graded tensor type (r: contravariant, s: covariant) -/
  AbstractTensor : ℕ → ℕ → Type

  add {r s : ℕ} : AbstractTensor r s → AbstractTensor r s → AbstractTensor r s
  smul {r s : ℕ} : ScalarField (I := I) (M := M) → AbstractTensor r s → AbstractTensor r s
  tensor_prod {r1 s1 r2 s2 : ℕ} : AbstractTensor r1 s1 → AbstractTensor r2 s2 → AbstractTensor (r1 + r2) (s1 + s2)

  -- Embedding
  fromScalar : ScalarField (I := I) (M := M) → AbstractTensor 0 0
  fromVector : VectorField (I := I) (M := M) → AbstractTensor 1 0

  -- Covariant Derivative
  nabla_tensor {r s : ℕ} : VectorField (I := I) (M := M) → AbstractTensor r s → AbstractTensor r s

  /-- Interior product (contraction with a tangent vector) -/
  interior_product {s : ℕ} : AbstractTensor 0 (s + 1) → VectorField (I := I) (M := M) → AbstractTensor 0 s

  /-- Covariant contraction (feeding a vector into a mixed tensor) -/
  contract_covariant {r s : ℕ} : AbstractTensor r (s + 1) → VectorField (I := I) (M := M) → AbstractTensor r s

  /-- General contraction between one contravariant and one covariant slot -/
  contract {r s : ℕ} : AbstractTensor (r + 1) (s + 1) → AbstractTensor r s

  /-- Metric trace: contracting two covariant indices using the metric tensor -/
  metric_contract {r s : ℕ} : AbstractTensor r (s + 2) → AbstractTensor r s

  --  Axioms:
  -- 1. Linearity:
  contract_add {r s : ℕ} : ∀ T1 T2 : AbstractTensor (r + 1) (s + 1), contract (add T1 T2) = add (contract T1) (contract T2)
  contract_smul {r s : ℕ} : ∀ (f : ScalarField (I := I) (M := M)) (T : AbstractTensor (r + 1) (s + 1)), contract (smul f T) = smul f (contract T)

  nabla_tensor_add {r s : ℕ} : ∀ X (T1 T2 : AbstractTensor r s), nabla_tensor X (add T1 T2) = add (nabla_tensor X T1) (nabla_tensor X T2)

  nabla_tensor_add_left {r s : ℕ} : ∀ X Y (T : AbstractTensor r s), nabla_tensor (X + Y) T = add (nabla_tensor X T) (nabla_tensor Y T)
  nabla_tensor_smul_left {r s : ℕ} : ∀ (f : ScalarField (I := I) (M := M)) X (T : AbstractTensor r s), nabla_tensor (f • X) T = smul f (nabla_tensor X T)

  -- 2. Leibniz Rule: $\nabla_X(T_1 \otimes T_2) = (\nabla_X T_1) \otimes T_2 + T_1 \otimes (\nabla_X T_2)$
  leibniz_rule {r1 s1 r2 s2 : ℕ} : ∀ X (T1 : AbstractTensor r1 s1) (T2 : AbstractTensor r2 s2),
    nabla_tensor X (tensor_prod T1 T2) = add (tensor_prod (nabla_tensor X T1) T2) (tensor_prod T1 (nabla_tensor X T2))

  -- 3. Commutativity: $\text{contract}(\nabla_X T) = \nabla_X (\text{contract} T)$
  commutativity {r s : ℕ} : ∀ X (T : AbstractTensor (r + 1) (s + 1)), contract (nabla_tensor X T) = nabla_tensor X (contract T)

  -- 4. Base Cases: $\nabla_X (\text{fromScalar } f)$ = directional derivative; $\nabla_X (\text{fromVector } Y)$ = native connection
  base_scalar : ∀ X (f : ScalarField (I := I) (M := M)), nabla_tensor X (fromScalar f) = fromScalar (action X f)
  base_vector : ∀ X Y, nabla_tensor X (fromVector Y) = fromVector (conn.nabla X Y)

/-
  The proof to the previous class can be here.
-/

noncomputable instance mockTensorCalculus {metric : AbstractMetricTensor (ScalarField (I := I) (M := M)) (VectorField (I := I) (M := M))} {conn : AbstractLeviCivitaConnection metric} : AbstractTensorCalculus metric conn := sorry

end DifferentialGeometry.Bridge
