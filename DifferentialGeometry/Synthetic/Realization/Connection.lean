import DifferentialGeometry.Synthetic.Realization.Embedding
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# SmoothRicciFlow: Connection from CovariantDerivative

Given a Mathlib `CovariantDerivative I E (TangentSpace I)` on the tangent bundle of `M`,
this file constructs the Synthetic layer's `conn : V → V → V` and proves its four
linearity properties.

## Main definitions

* `concreteConn` : the connection `∇_X Y` as a smooth section, defined pointwise by
  `concreteConn cov X Y x := cov Y x (X x)`.

## Main results

* `concreteConn_add_right` : `∇_X (Y + Z) = ∇_X Y + ∇_X Z`
* `concreteConn_add_left` : `∇_{X+Y} Z = ∇_X Z + ∇_Y Z`
* `concreteConn_smul_left` : `∇_{fX} Z = f • ∇_X Z`
* `concreteConn_leibniz` : `∇_X (f • Y) = (embedDeriv X f) • Y + f • ∇_X Y`

## Convention

Mathlib's `CovariantDerivative` has the signature `cov σ x v` corresponding to `(∇_v σ)(x)`.
The Synthetic layer's `conn X Y` corresponds to `∇_X Y`. So `conn X Y x = cov Y x (X x)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Bundle CovariantDerivative

section Connection

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### Definition of concreteConn -/

/-- The connection `∇_X Y` as a smooth section of the tangent bundle.

Given a `CovariantDerivative` with `ContMDiffCovariantDerivative` regularity,
and smooth sections `X, Y`, the result `cov Y x (X x)` is smooth. This follows
because `cov Y` is a smooth section of `Hom(TM, TM)` (by the smoothness condition
of the covariant derivative), and `X` is a smooth section of `TM`, so their
pointwise pairing is smooth by `ContMDiff.clm_bundle_apply`. -/
noncomputable def concreteConn
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ where
  toFun x := cov Y x (X x)
  contMDiff_toFun := by
    -- ContMDiffCovariantDerivative gives us: for C^{∞+1} section Y,
    -- cov Y is a C^∞ section of Hom(TM, TM). Since ∞ + 1 = ∞, any C^∞ section suffices.
    have hY_plus : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ + 1) (T% fun x => Y x) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from by simp]
      exact Y.contMDiff
    have hcov_smooth := (‹ContMDiffCovariantDerivative cov ∞›).contMDiff.contMDiff
      (hY_plus.contMDiffOn)
    -- hcov_smooth : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
    --   (fun x => ⟨x, cov Y x⟩) Set.univ
    -- Convert to ContMDiff
    have hcov_global : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun x => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x) x (cov Y x)) := by
      rwa [← contMDiffOn_univ]
    -- X is a C^∞ section of TM
    have hX_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x => TotalSpace.mk' E (E := TangentSpace I) x (X x)) :=
      X.contMDiff
    -- Apply clm_bundle_apply: smooth Hom-section applied to smooth section is smooth
    exact ContMDiff.clm_bundle_apply (b := id) hcov_global hX_smooth

/-- The pointwise value of `concreteConn`: `concreteConn cov X Y x = cov Y x (X x)`. -/
theorem concreteConn_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    concreteConn I M cov X Y x = cov Y x (X x) := by
  rfl

/-! ### Linearity properties -/

/-- Right-additivity of the connection: `∇_X (Y + Z) = ∇_X Y + ∇_X Z`.

Follows from `IsCovariantDerivativeOn.add`: `cov (Y + Z) x = cov Y x + cov Z x`
for differentiable sections Y, Z. -/
theorem concreteConn_add_right
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    concreteConn I M cov X (Y + Z) = concreteConn I M cov X Y + concreteConn I M cov X Z := by
  apply ContMDiffSection.ext; intro x
  change cov (fun x => Y x + Z x) x (X x) =
    cov Y x (X x) + cov Z x (X x)
  have hY : MDiffAt (T% fun x => Y x) x := Y.mdifferentiableAt
  have hZ : MDiffAt (T% fun x => Z x) x := Z.mdifferentiableAt
  rw [show (fun x => Y x + Z x) = ((fun x => Y x) + fun x => Z x) from rfl,
    cov.isCovariantDerivativeOn.add hY hZ]
  simp [ContinuousLinearMap.add_apply]

/-- Left-additivity of the connection: `∇_{X+Y} Z = ∇_X Z + ∇_Y Z`.

Follows from the CLM linearity of `cov Z x` in the tangent vector argument:
`cov Z x (X x + Y x) = cov Z x (X x) + cov Z x (Y x)`. -/
theorem concreteConn_add_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    concreteConn I M cov (X + Y) Z = concreteConn I M cov X Z + concreteConn I M cov Y Z := by
  apply ContMDiffSection.ext; intro x
  change cov Z x (X x + Y x) = cov Z x (X x) + cov Z x (Y x)
  exact ContinuousLinearMap.map_add (cov Z x) (X x) (Y x)

/-- Left scalar multiplication: `∇_{f•X} Z = f • ∇_X Z` for `f : C^∞⟮I, M; ℝ⟯`.

Follows from the CLM linearity of `cov Z x` in the tangent vector argument:
`cov Z x (f x • X x) = f x • cov Z x (X x)`. -/
theorem concreteConn_smul_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (f : C^∞⟮I, M; ℝ⟯)
    (X Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    concreteConn I M cov (f • X) Z = f • concreteConn I M cov X Z := by
  apply ContMDiffSection.ext; intro x
  change cov Z x (f x • X x) = f x • cov Z x (X x)
  exact ContinuousLinearMap.map_smul (cov Z x) (f x) (X x)

/-- Leibniz rule: `∇_X (f • Y) = (embedDeriv I M X f) • Y + f • ∇_X Y`.

Follows from `IsCovariantDerivativeOn.leibniz`:
`cov (f • Y) x = f x • cov Y x + (extDerivFun f x).smulRight (Y x)`.

The key identification is that `(extDerivFun f x).smulRight (Y x)` applied to `X x`
gives `extDerivFun f x (X x) • Y x`, which is `vectorFieldAction I M X f x • Y x`
= `(embedDeriv I M X f) x • Y x`. -/
theorem concreteConn_leibniz
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f : C^∞⟮I, M; ℝ⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    concreteConn I M cov X (f • Y) =
      vectorFieldActionSmooth I M X f • Y + f • concreteConn I M cov X Y := by
  apply ContMDiffSection.ext; intro x
  -- LHS: cov (fun x => f x • Y x) x (X x)
  -- RHS: vectorFieldActionSmooth I M X f x • Y x + f x • cov Y x (X x)
  change cov (fun x => (f : M → ℝ) x • Y x) x (X x) =
    (vectorFieldActionSmooth I M X f) x • Y x + f x • cov Y x (X x)
  -- Apply IsCovariantDerivativeOn.leibniz
  have hY : MDiffAt (T% fun x => Y x) x := Y.mdifferentiableAt
  have hf : MDiffAt (f : M → ℝ) x :=
    f.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hfY_eq : (fun x => (f : M → ℝ) x • Y x) = ((f : M → ℝ) • fun x => Y x) := rfl
  rw [hfY_eq, cov.isCovariantDerivativeOn.leibniz hY hf]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  -- Goal: f x • cov Y x (X x) + extDerivFun f x (X x) • Y x =
  --        vectorFieldActionSmooth I M X f x • Y x + f x • cov Y x (X x)
  simp only [vectorFieldActionSmooth, ContMDiffMap.coeFn_mk, vectorFieldAction]
  abel

/-! ### DerivationEmbedding and torsion-free condition -/

/-- The concrete `DerivationEmbedding` assembling `embedLinearMap`, its injectivity,
and bracket closure into the Synthetic layer's core structure. -/
noncomputable def concreteDerivationEmbedding :
    DerivationEmbedding ℝ C^∞⟮I, M; ℝ⟯
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ where
  embed := embedLinearMap I M
  embed_injective := embedLinearMap_injective I M
  bracket_closed := embed_bracket_closed I M

/-- The Synthetic bracket from `concreteDerivationEmbedding` equals the Mathlib
Lie bracket section `mlieBracketSection`.

Both satisfy `embedLinearMap Z = ⁅embedLinearMap X, embedLinearMap Y⁆`:
- `bracket` is defined as `Classical.choose (embed_bracket_closed X Y)`.
- `mlieBracketSection` is the witness used in the proof of `embed_bracket_closed`.

By injectivity of `embedLinearMap`, they must be equal. -/
theorem bracket_eq_mlieBracketSection
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    bracket (concreteDerivationEmbedding I M) X Y = mlieBracketSection I M X Y := by
  apply (embedLinearMap_injective I M)
  -- bracket_spec: embed (bracket emb X Y) = ⁅embed X, embed Y⁆
  have h1 := bracket_spec (concreteDerivationEmbedding I M) X Y
  -- mlieBracketSection also maps to the same commutator
  have h2 : embedLinearMap I M (mlieBracketSection I M X Y) =
      ⁅embedLinearMap I M X, embedLinearMap I M Y⁆ := by
    apply Derivation.ext; intro f
    exact embedDeriv_mlieBracket I M X Y f
  -- Both h1 and h2 have the same RHS (up to definitional equality of embed vs embedLinearMap)
  -- so transitivity gives the result
  exact h1.trans h2.symm

/-- When the Mathlib covariant derivative has zero torsion, the Synthetic layer's
`IsTorsionFree` condition holds.

The proof uses `torsion_eq_zero_iff` from Mathlib:
  `cov.torsion = 0 ↔ ∀ X Y x, MDiffAt X x → MDiffAt Y x →
    cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x`

The LHS of `IsTorsionFree` is `concreteConn cov X Y - concreteConn cov Y X`,
which pointwise equals `cov Y x (X x) - cov X x (Y x)`.

The RHS is `bracket concreteDerivationEmbedding X Y`, which equals
`mlieBracketSection I M X Y` by `bracket_eq_mlieBracketSection`,
which pointwise equals `mlieBracket I X Y x`. -/
theorem concreteConn_torsion_free
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (h_tf : cov.torsion = 0) :
    IsTorsionFree (concreteDerivationEmbedding I M)
      (concreteConn I M cov) := by
  intro X Y
  apply ContMDiffSection.ext; intro x
  -- LHS: (concreteConn cov X Y - concreteConn cov Y X) x
  --     = cov Y x (X x) - cov X x (Y x)
  change concreteConn I M cov X Y x - concreteConn I M cov Y X x =
    bracket (concreteDerivationEmbedding I M) X Y x
  rw [concreteConn_apply, concreteConn_apply]
  -- Apply torsion_eq_zero_iff to get pointwise identity
  have h_eq := cov.torsion_eq_zero_iff.mp h_tf
    (X.mdifferentiableAt (x := x)) (Y.mdifferentiableAt (x := x))
  -- h_eq : cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x
  rw [h_eq]
  -- RHS: bracket concreteDerivationEmbedding X Y x = mlieBracketSection I M X Y x
  --     = mlieBracket I X Y x
  rw [bracket_eq_mlieBracketSection]
  rfl

end Connection

end
