import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Topology.FiberBundle.Basic
import DifferentialGeometry.Integral.Connection.LeviCivita

/-!
# The Riemann curvature operator of a covariant derivative

Given any covariant derivative `cov : CovariantDerivative I F V` on a vector bundle `V` over a
smooth manifold `M`, this file develops the section-level Riemann curvature formula
$$
  R^{\mathrm{cov}}(X, Y) Z := \nabla_X (\nabla_Y Z) - \nabla_Y (\nabla_X Z) - \nabla_{[X, Y]} Z,
$$
together with its pointwise tensoriality in the vector-field arguments `X` and `Y`,
antisymmetry, and the torsion-free reformulation of the Lie-bracket factor.

## Main definitions

* `covApply cov X Z` — the section `b ↦ cov.toFun Z b (X b)`, written `∇_X Z` on paper.
* `riemannSec cov X Y Z x` — the bare section-level Riemann formula.

## Main theorems

* `riemannSec_swap` — pointwise antisymmetry `R(X, Y) Z (x) = - R(Y, X) Z (x)`.
* `riemannSec_self_eq_zero` — `R(X, X) Z (x) = 0`.
* `riemannSec_add_left`, `riemannSec_add_right` — additivity in the vector-field arguments.
* `riemannSec_smul_left`, `riemannSec_smul_right` — `C^∞(M)`-scalar multiplication in the
  vector-field arguments. These two pairs of lemmas establish that, on smooth inputs (with the
  required differentiability of `covApply`), the section-level Riemann formula is bilinear in
  `(X, Y)` over the algebra of smooth real-valued functions on `M`.
* `covApply_sub_eq_mlieBracket` — the torsion-free identity
  `covApply cov X Y x - covApply cov Y X x = mlieBracket I X Y x` for differentiable `X, Y`.
* `riemannSec_torsionFree_form` — for a torsion-free covariant derivative on the tangent bundle,
  the third (Lie-bracket) term of `riemannSec` rewrites in terms of `cov` evaluated at fibre
  vectors via the torsion-free identity.
* `LeviCivita_riemannSec_torsionFree_form` — the previous identity specialised to the
  Levi-Civita covariant derivative.
* `covApply_contMDiffOn`, `covApply_mdifferentiableAt` — smoothness of `covApply cov X Z` from
  smoothness of `cov`, `X`, and `Z`.

## Argument convention

We follow Mathlib's convention `cov.toFun σ x v ≅ (∇_v σ)(x)`. Consequently, `∇_X Z` (the
covariant derivative of a section `Z` along a vector field `X`) is the section
`b ↦ cov.toFun Z b (X b)`, captured by `covApply cov X Z`.
-/

noncomputable section

open Bundle Manifold Set FiberBundle NormedSpace
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

/-! ## Section-level Riemann formula

The construction in this section is valid on **any** vector bundle `V` over a smooth manifold,
without metric, orientation, or boundary hypotheses. -/

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V]

/-- The section `cov_X Z := b ↦ cov.toFun Z b (X b)`. With Mathlib's argument convention
`cov.toFun σ x v ≅ (∇_v σ)(x)`, this is the section `∇_X Z` written on paper. -/
def covApply (cov : CovariantDerivative I F V)
    (X : Π b : M, TangentSpace I b) (Z : Π b : M, V b) : Π b : M, V b :=
  fun b => cov.toFun Z b (X b)

@[simp] lemma covApply_apply (cov : CovariantDerivative I F V)
    (X : Π b : M, TangentSpace I b) (Z : Π b : M, V b) (b : M) :
    covApply cov X Z b = cov.toFun Z b (X b) := rfl

/-- The section-level Riemann formula:
`R(X, Y) Z (x) = ∇_X (∇_Y Z) (x) - ∇_Y (∇_X Z) (x) - ∇_{[X, Y]} Z (x)`. -/
def riemannSec (cov : CovariantDerivative I F V)
    (X Y : Π b : M, TangentSpace I b) (Z : Π b : M, V b) (x : M) : V x :=
  cov.toFun (covApply cov Y Z) x (X x) - cov.toFun (covApply cov X Z) x (Y x)
    - cov.toFun Z x (VectorField.mlieBracket I X Y x)

/-- Definitional unfolding of `riemannSec`. -/
lemma riemannSec_def (cov : CovariantDerivative I F V)
    (X Y : Π b : M, TangentSpace I b) (Z : Π b : M, V b) (x : M) :
    riemannSec cov X Y Z x =
      cov.toFun (covApply cov Y Z) x (X x) - cov.toFun (covApply cov X Z) x (Y x)
        - cov.toFun Z x (VectorField.mlieBracket I X Y x) := rfl

/-! ### Antisymmetry of `riemannSec` in the (X, Y) arguments -/

/-- Antisymmetry of `riemannSec` in `(X, Y)`, pointwise. -/
lemma riemannSec_swap (cov : CovariantDerivative I F V)
    (X Y : Π b : M, TangentSpace I b) (Z : Π b : M, V b) (x : M) :
    riemannSec cov X Y Z x = - riemannSec cov Y X Z x := by
  unfold riemannSec
  rw [VectorField.mlieBracket_swap_apply (V := X) (W := Y)]
  simp
  abel

/-- Vanishing of `riemannSec` on the diagonal `(X, X)`, pointwise. -/
@[simp] lemma riemannSec_self_eq_zero (cov : CovariantDerivative I F V)
    (X : Π b : M, TangentSpace I b) (Z : Π b : M, V b) (x : M) :
    riemannSec cov X X Z x = 0 := by
  unfold riemannSec
  rw [show VectorField.mlieBracket I X X = 0 from VectorField.mlieBracket_self]
  simp

end General

/-! ## Tensoriality in the vector-field arguments

For smooth vector fields `X, Y` and a smooth section `Z`, the formula `riemannSec cov X Y Z x`
is `C^∞(M)`-linear in each of `X` and `Y`. The proofs use the Lie-bracket Leibniz identities
`VectorField.mlieBracket_smul_left/right` together with the covariant-derivative Leibniz
`IsCovariantDerivativeOn.leibniz` to make the cross terms cancel.

These lemmas require `[IsManifold I 2 M]` and `[CompleteSpace E]` (the standing hypotheses for
the manifold Lie-bracket Leibniz identities). They additionally ask for differentiability of
`covApply cov X Z` at `x`, which is supplied externally; in practice it follows from `cov` being
of class `C^∞` and `X, Z` being smooth, but stating the lemmas with `MDiffAt`-hypotheses on
`covApply` keeps them maximally general. -/

section TensorVectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

variable {cov : CovariantDerivative I F V}

/-! ### Additivity of `riemannSec` in the X argument -/

/-- Additivity of `riemannSec` in the X argument, at a single point.

The hypotheses on `covApply` are needed to invoke `IsCovariantDerivativeOn.add` for the second
piece of the formula. -/
lemma riemannSec_add_left
    {X X' Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hcXZ : MDiffAt (T% (covApply cov X Z)) x)
    (hcX'Z : MDiffAt (T% (covApply cov X' Z)) x) :
    riemannSec cov (X + X') Y Z x = riemannSec cov X Y Z x + riemannSec cov X' Y Z x := by
  classical
  unfold riemannSec
  -- Term 1 distributes by CLM linearity in the third argument.
  have h1 : cov.toFun (covApply cov Y Z) x ((X + X') x) =
      cov.toFun (covApply cov Y Z) x (X x) + cov.toFun (covApply cov Y Z) x (X' x) := by
    simp [Pi.add_apply]
  -- Term 2: rewrite `covApply cov (X + X') Z = covApply cov X Z + covApply cov X' Z` and
  -- use `cov`-additivity on the right.
  have hcov_add : covApply cov (X + X') Z = covApply cov X Z + covApply cov X' Z := by
    funext b
    simp [covApply, Pi.add_apply]
  have h2 : cov.toFun (covApply cov (X + X') Z) x (Y x) =
      cov.toFun (covApply cov X Z) x (Y x) + cov.toFun (covApply cov X' Z) x (Y x) := by
    rw [hcov_add]
    rw [cov.isCovariantDerivativeOnUniv.add hcXZ hcX'Z]
    rfl
  -- Term 3: distribute `mlieBracket` by `mlieBracket_add_left` then by CLM linearity.
  have hbr : VectorField.mlieBracket I (X + X') Y x =
      VectorField.mlieBracket I X Y x + VectorField.mlieBracket I X' Y x :=
    VectorField.mlieBracket_add_left hX hX'
  have h3 : cov.toFun Z x (VectorField.mlieBracket I (X + X') Y x) =
      cov.toFun Z x (VectorField.mlieBracket I X Y x)
        + cov.toFun Z x (VectorField.mlieBracket I X' Y x) := by
    rw [hbr]
    simp
  rw [h1, h2, h3]
  abel

/-- Additivity of `riemannSec` in the Y argument, at a single point. -/
lemma riemannSec_add_right
    {X Y Y' : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x)
    (hcYZ : MDiffAt (T% (covApply cov Y Z)) x)
    (hcY'Z : MDiffAt (T% (covApply cov Y' Z)) x) :
    riemannSec cov X (Y + Y') Z x = riemannSec cov X Y Z x + riemannSec cov X Y' Z x := by
  -- Use antisymmetry to reduce to `riemannSec_add_left`.
  rw [riemannSec_swap, riemannSec_add_left hY hY' hcYZ hcY'Z,
      riemannSec_swap (cov := cov) (X := Y) (Y := X) (Z := Z),
      riemannSec_swap (cov := cov) (X := Y') (Y := X) (Z := Z)]
  abel

/-! ### Scalar-function multiplication: `f • X` and `f • Y` -/

/-- `C^∞(M)`-linearity of `riemannSec` in the X argument: scalar-multiplication by a smooth
real-valued function `f`. -/
lemma riemannSec_smul_left
    {f : M → ℝ} {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x)
    (hcXZ : MDiffAt (T% (covApply cov X Z)) x) :
    riemannSec cov (f • X) Y Z x = f x • riemannSec cov X Y Z x := by
  classical
  unfold riemannSec
  -- Term 1: CLM-linearity in the third argument.
  have h1 : cov.toFun (covApply cov Y Z) x ((f • X) x) =
      f x • cov.toFun (covApply cov Y Z) x (X x) := by
    simp
  -- Term 2: rewrite `covApply cov (f • X) Z = f • covApply cov X Z` and apply Leibniz.
  have hcov_smul : covApply cov (f • X) Z = f • covApply cov X Z := by
    funext b
    simp [covApply]
  have h2 : cov.toFun (covApply cov (f • X) Z) x (Y x) =
      f x • cov.toFun (covApply cov X Z) x (Y x)
        + extDerivFun f x (Y x) • cov.toFun Z x (X x) := by
    rw [hcov_smul]
    rw [cov.isCovariantDerivativeOnUniv.leibniz hcXZ hf]
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.smulRight_apply]
  -- Term 3: use `mlieBracket_smul_left`.
  have hbr : VectorField.mlieBracket I (f • X) Y x =
      - (extDerivFun f x (Y x)) • X x
        + f x • VectorField.mlieBracket I X Y x := by
    have := VectorField.mlieBracket_smul_left (V := X) (W := Y) (x := x) hf hX
    -- The lemma reads:
    --   mlieBracket I (f • X) Y x =
    --     - (fromTangentSpace (f x) (mfderiv% f x (Y x))) • X x + f x • mlieBracket I X Y x
    -- and `extDerivFun f x v = fromTangentSpace _ (mfderiv f x v)` definitionally.
    convert this using 2
  have h3 : cov.toFun Z x (VectorField.mlieBracket I (f • X) Y x) =
      - extDerivFun f x (Y x) • cov.toFun Z x (X x)
        + f x • cov.toFun Z x (VectorField.mlieBracket I X Y x) := by
    rw [hbr]
    simp [neg_smul]
  rw [h1, h2, h3]
  -- Now everything is a linear combination of three "core" terms; the cross terms cancel.
  rw [smul_sub, smul_sub]
  module

/-- `C^∞(M)`-linearity of `riemannSec` in the Y argument: scalar-multiplication by a smooth
real-valued function `f`. -/
lemma riemannSec_smul_right
    {f : M → ℝ} {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x)
    (hcYZ : MDiffAt (T% (covApply cov Y Z)) x) :
    riemannSec cov X (f • Y) Z x = f x • riemannSec cov X Y Z x := by
  -- Reduce to `riemannSec_smul_left` via antisymmetry.
  rw [riemannSec_swap, riemannSec_smul_left hf hY hcYZ,
      riemannSec_swap (cov := cov) (X := Y) (Y := X) (Z := Z),
      smul_neg, neg_neg]

end TensorVectorField

/-! ## Smoothness of `covApply`

Given a `C^∞`-class covariant derivative `cov`, a smooth tangent vector field `X`, and a section
`Z` of class `C^{∞+1}` (i.e. `C^∞` at one degree higher than the surrounding manifold-smoothness
threshold), the section `b ↦ cov.toFun Z b (X b)` is smooth. -/

section CovApplySmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

variable {cov : CovariantDerivative I F V}

/-- Smoothness of `covApply cov X Z` from smoothness of `cov`, `X`, and `Z`. The hypothesis on
`Z` is one degree higher than the hypothesis on the result (Mathlib's
`ContMDiffCovariantDerivative` convention: `cov` of class `C^k` takes `C^{k+1}`-sections to
`C^k`-sections). -/
lemma covApply_contMDiffOn
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X : Π b : M, TangentSpace I b} {Z : Π b : M, V b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% Z)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞ (T% (covApply cov X Z)) Set.univ := by
  classical
  -- Smoothness of `b ↦ cov.toFun Z b` as a section of `Hom(TM, V)`.
  have hop : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun b : M => (⟨b, cov.toFun Z b⟩ :
        TotalSpace (E →L[ℝ] F) fun b : M => TangentSpace I b →L[ℝ] V b)) Set.univ :=
    hcov.contMDiff.contMDiff (σ := Z) (hZ.contMDiffOn)
  -- Apply `clm_bundle_apply` pointwise to get smoothness of `b ↦ cov.toFun Z b (X b)`.
  intro x _hx
  exact (hop.contMDiffAt (Filter.univ_mem)).clm_bundle_apply (v := X) (hX x) |>.contMDiffWithinAt

/-- `MDiffAt`-form of `covApply` smoothness at a single point, useful for invoking the
tensoriality lemmas. -/
lemma covApply_mdifferentiableAt
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% Z)) :
    MDiffAt (T% (covApply cov X Z)) x := by
  have hAt : ContMDiffAt I (I.prod 𝓘(ℝ, F)) ∞ (T% (covApply cov X Z)) x :=
    (covApply_contMDiffOn hX hZ).contMDiffAt (Filter.univ_mem)
  exact hAt.mdifferentiableAt (by simp)

end CovApplySmooth

/-! ## Torsion-free formulae

For a torsion-free covariant derivative on the tangent bundle, the Lie-bracket factor in the
Riemann formula simplifies to `[X, Y] = ∇_X Y - ∇_Y X`, allowing the section-level Riemann
formula to be rewritten with the Lie-bracket replaced by the antisymmetric pairing of `cov`
evaluated at fibre vectors. -/

section TorsionFreeAbstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
variable (htor : cov.torsion = 0)

include htor in
/-- Torsion-free identity: `cov_X Y - cov_Y X = [X, Y]` at points where `X, Y` are
differentiable. With Mathlib's argument convention, this reads
`covApply cov X Y x - covApply cov Y X x = mlieBracket I X Y x`. -/
lemma covApply_sub_eq_mlieBracket
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    covApply cov X Y x - covApply cov Y X x = VectorField.mlieBracket I X Y x :=
  -- `torsion_eq_zero_iff.mp` returns
  --   cov.toFun Y x (X x) - cov.toFun X x (Y x) = mlieBracket I X Y x.
  -- And `covApply cov X Y x = cov.toFun Y x (X x)` by definition.
  (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp htor hX hY

end TorsionFreeAbstract

/-! ### Torsion-free reformulation of the Lie-bracket factor -/

section TorsionFree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}

/-- For a torsion-free covariant derivative on the tangent bundle, the third (Lie-bracket)
term of `riemannSec` at a differentiable point can be rewritten via the torsion-free identity
`mlieBracket I X Y x = cov.toFun Y x (X x) - cov.toFun X x (Y x)`. -/
lemma riemannSec_torsionFree_form
    (htor : cov.torsion = 0)
    {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, TangentSpace I b} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    riemannSec cov X Y Z x =
      cov.toFun (covApply cov Y Z) x (X x) - cov.toFun (covApply cov X Z) x (Y x)
        - (cov.toFun Z x (cov.toFun Y x (X x)) - cov.toFun Z x (cov.toFun X x (Y x))) := by
  classical
  have hXY : VectorField.mlieBracket I X Y x =
      cov.toFun Y x (X x) - cov.toFun X x (Y x) :=
    ((CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp htor hX hY).symm
  unfold riemannSec
  rw [hXY, map_sub]

end TorsionFree

section LeviCivitaTorsionFree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- For the Levi-Civita covariant derivative, the third term of `riemannSec` admits the
torsion-free form. -/
theorem LeviCivita_riemannSec_torsionFree_form
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, TangentSpace I b} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    riemannSec (LeviCivita (I := I) g) X Y Z x =
      (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) Y Z) x (X x)
        - (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) X Z) x (Y x)
        - ((LeviCivita (I := I) g).toFun Z x
              ((LeviCivita (I := I) g).toFun Y x (X x))
            - (LeviCivita (I := I) g).toFun Z x
              ((LeviCivita (I := I) g).toFun X x (Y x))) :=
  riemannSec_torsionFree_form (cov := LeviCivita (I := I) g)
    (LeviCivita_torsion_eq_zero (I := I) g) hX hY

end LeviCivitaTorsionFree

/-! ## Tensoriality in the section argument

The section-level Riemann formula is `C^∞(M)`-linear in the third (section) argument too:
$$
  R(X, Y)(f Z) = f \cdot R(X, Y) Z, \qquad R(X, Y)(Z + Z') = R(X, Y) Z + R(X, Y) Z'.
$$
The proof of the smul case relies on the foundation identity
`[X, Y](f) = X(Y f) - Y(X f)` for the cross-term cancellation, which is provided by
`extDerivFun_apply_mlieBracket` from `ChartLieBracket.lean`.

For Z-slot additivity at a point, the key technical issue is that
`covApply cov Y (Z + Z')` and `covApply cov Y Z + covApply cov Y Z'` are equal at points
where `Z, Z'` are differentiable, but may differ as sections off this locus. We therefore
hypothesise the *eventual equality* on a neighbourhood of `x`, which is automatic when
`Z, Z'` are differentiable on a neighbourhood (e.g. when both are `C^k` for `k ≥ 1`).
The hypotheses are exposed in two flavours: a fully general "eventual equality" form,
and a `ContMDiffAt`-based form that is convenient for downstream consumption. -/

section TensorSection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

variable {cov : CovariantDerivative I F V}

/-! ### Z-slot additivity -/

/-- Additivity of `riemannSec` in the Z (section) argument, at a single point.

The key auxiliary section identity `covApply cov Y (Z + Z') =ᶠ[𝓝 x] covApply cov Y Z +
covApply cov Y Z'` follows from `cov`-additivity at *all* points of a neighbourhood,
whence the assumption that `Z, Z'` be `MDifferentiable` eventually at `x`. The two
auxiliary `MDiffAt`-hypotheses on `covApply cov Y Z, covApply cov Y Z'` (and likewise
for `X`) are needed to invoke `IsCovariantDerivativeOn.congr_of_eventuallyEq`. -/
lemma riemannSec_add_third
    {X Y : Π b : M, TangentSpace I b} {Z Z' : Π b : M, V b} {x : M}
    (hZnhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% Z) b)
    (hZ'nhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% Z') b)
    (hcYZ : MDiffAt (T% (covApply cov Y Z)) x)
    (hcYZ' : MDiffAt (T% (covApply cov Y Z')) x)
    (hcYZZ' : MDiffAt (T% (covApply cov Y (Z + Z'))) x)
    (hcXZ : MDiffAt (T% (covApply cov X Z)) x)
    (hcXZ' : MDiffAt (T% (covApply cov X Z')) x)
    (hcXZZ' : MDiffAt (T% (covApply cov X (Z + Z'))) x) :
    riemannSec cov X Y (Z + Z') x = riemannSec cov X Y Z x + riemannSec cov X Y Z' x := by
  classical
  unfold riemannSec
  -- Eventual pointwise equality of the auxiliary sections.
  have hYZZ'_ev : ∀ᶠ b in 𝓝 x,
      covApply cov Y (Z + Z') b = (covApply cov Y Z + covApply cov Y Z') b := by
    filter_upwards [hZnhd, hZ'nhd] with b hZb hZ'b
    change cov.toFun (Z + Z') b (Y b) = (cov.toFun Z b (Y b) + cov.toFun Z' b (Y b))
    rw [cov.isCovariantDerivativeOnUniv.add hZb hZ'b]
    rfl
  have hXZZ'_ev : ∀ᶠ b in 𝓝 x,
      covApply cov X (Z + Z') b = (covApply cov X Z + covApply cov X Z') b := by
    filter_upwards [hZnhd, hZ'nhd] with b hZb hZ'b
    change cov.toFun (Z + Z') b (X b) = (cov.toFun Z b (X b) + cov.toFun Z' b (X b))
    rw [cov.isCovariantDerivativeOnUniv.add hZb hZ'b]
    rfl
  -- The two `cov.toFun (covApply cov · (Z+Z')) x` terms agree with their split via
  -- `congr_of_eventuallyEq`.
  have hcYZZ'_split : MDiffAt (T% (covApply cov Y Z + covApply cov Y Z')) x :=
    mdifferentiableAt_add_section hcYZ hcYZ'
  have hcXZZ'_split : MDiffAt (T% (covApply cov X Z + covApply cov X Z')) x :=
    mdifferentiableAt_add_section hcXZ hcXZ'
  have hY_term :
      cov.toFun (covApply cov Y (Z + Z')) x =
        cov.toFun (covApply cov Y Z + covApply cov Y Z') x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hcYZZ' hcYZZ'_split (Filter.univ_mem) hYZZ'_ev
  have hX_term :
      cov.toFun (covApply cov X (Z + Z')) x =
        cov.toFun (covApply cov X Z + covApply cov X Z') x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hcXZZ' hcXZZ'_split (Filter.univ_mem) hXZZ'_ev
  -- Now apply additivity in section argument for the split sums.
  rw [hY_term, hX_term]
  rw [cov.isCovariantDerivativeOnUniv.add hcYZ hcYZ',
      cov.isCovariantDerivativeOnUniv.add hcXZ hcXZ']
  -- Term 3: cov.toFun (Z + Z') x ([X,Y] x) splits via Mathlib additivity.
  have hZZ'_at : cov.toFun (Z + Z') x =
      cov.toFun Z x + cov.toFun Z' x :=
    cov.isCovariantDerivativeOnUniv.add (hZnhd.self_of_nhds) (hZ'nhd.self_of_nhds)
  rw [hZZ'_at]
  -- Final cleanup using CLM application linearity.
  simp only [ContinuousLinearMap.add_apply]
  abel

/-! ### Z-slot scalar-function multiplication -/

set_option linter.style.show false in
/-- `C^∞(M)`-linearity of `riemannSec` in the Z (section) argument: scalar-multiplication by a
smooth real-valued function `f`.

The proof uses the foundation identity `[X, Y] f = X(Y f) - Y(X f)` (provided by
`extDerivFun_apply_mlieBracket` from `ChartLieBracket.lean`) to cancel the cross terms that
arise from applying Leibniz twice. This identity is the only place where the chart-interior
hypothesis `extChartAt I x x ∈ interior ((extChartAt I x).target : Set E)` enters, and is
automatic under `[BoundarylessManifold I M]` via `BoundarylessManifold.isInteriorPoint`.

The hypotheses are exposed in their max-general `MDiff`/`ContMDiff`-at-a-point form. The
neighbourhood-MDifferentiability hypotheses on `f, Z` are needed for the eventual section
equality of `covApply cov · (f • Z)` with `f • (covApply cov · Z) + ((·) f) • Z`. -/
lemma riemannSec_smul_third
    {f : M → ℝ} {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hfnhd : ∀ᶠ b in 𝓝 x, MDiffAt f b)
    (hZnhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% Z) b)
    (hZx : MDiffAt (T% Z) x)
    (hcXZ : MDiffAt (T% (covApply cov X Z)) x)
    (hcYZ : MDiffAt (T% (covApply cov Y Z)) x)
    (hcXfZ : MDiffAt (T% (covApply cov X (f • Z))) x)
    (hcYfZ : MDiffAt (T% (covApply cov Y (f • Z))) x)
    (hYf : MDiffAt (fun b => extDerivFun f b (Y b)) x)
    (hXf : MDiffAt (fun b => extDerivFun f b (X b)) x)
    (hf_smul_cYZ : MDiffAt (T% (f • covApply cov Y Z)) x)
    (hf_smul_cXZ : MDiffAt (T% (f • covApply cov X Z)) x)
    (hYf_smul_Z : MDiffAt (T% ((fun b => extDerivFun f b (Y b)) • Z)) x)
    (hXf_smul_Z : MDiffAt (T% ((fun b => extDerivFun f b (X b)) • Z)) x)
    (hx_int : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E)) :
    riemannSec cov X Y (f • Z) x = f x • riemannSec cov X Y Z x := by
  classical
  -- Set up directional-derivative shorthands.
  set Yf : M → ℝ := fun b => extDerivFun f b (Y b) with hYf_def
  set Xf : M → ℝ := fun b => extDerivFun f b (X b) with hXf_def
  -- Key eventual equalities for `covApply cov V (f • Z)` (V = X or Y).
  -- At any point `b` where `f` and `Z` are MDiff, Leibniz applied to the section sum
  -- gives `cov.toFun (f • Z) b = f b • cov.toFun Z b + (extDerivFun f b).smulRight (Z b)`.
  -- Applied to `V b`, this equals `f b • cov.toFun Z b (V b) + extDerivFun f b (V b) • Z b`.
  have heventY :
      ∀ᶠ b in 𝓝 x, covApply cov Y (f • Z) b =
        ((f • covApply cov Y Z) + (Yf • Z)) b := by
    filter_upwards [hfnhd, hZnhd] with b hfb hZb
    change cov.toFun (f • Z) b (Y b) =
      f b • cov.toFun Z b (Y b) + extDerivFun f b (Y b) • Z b
    rw [cov.isCovariantDerivativeOnUniv.leibniz hZb hfb]
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.smulRight_apply]
  have heventX :
      ∀ᶠ b in 𝓝 x, covApply cov X (f • Z) b =
        ((f • covApply cov X Z) + (Xf • Z)) b := by
    filter_upwards [hfnhd, hZnhd] with b hfb hZb
    change cov.toFun (f • Z) b (X b) =
      f b • cov.toFun Z b (X b) + extDerivFun f b (X b) • Z b
    rw [cov.isCovariantDerivativeOnUniv.leibniz hZb hfb]
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.smulRight_apply]
  -- Smoothness of the split section at x.
  have hsplitY : MDiffAt (T% ((f • covApply cov Y Z) + (Yf • Z))) x :=
    mdifferentiableAt_add_section hf_smul_cYZ hYf_smul_Z
  have hsplitX : MDiffAt (T% ((f • covApply cov X Z) + (Xf • Z))) x :=
    mdifferentiableAt_add_section hf_smul_cXZ hXf_smul_Z
  -- Apply `congr_of_eventuallyEq` to replace the LHS with the split version.
  have hY_replace :
      cov.toFun (covApply cov Y (f • Z)) x =
        cov.toFun ((f • covApply cov Y Z) + (Yf • Z)) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hcYfZ hsplitY (Filter.univ_mem) heventY
  have hX_replace :
      cov.toFun (covApply cov X (f • Z)) x =
        cov.toFun ((f • covApply cov X Z) + (Xf • Z)) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hcXfZ hsplitX (Filter.univ_mem) heventX
  -- Compute riemannSec cov X Y (f • Z) x.
  unfold riemannSec
  rw [hY_replace, hX_replace]
  -- Split via cov-additivity:
  rw [cov.isCovariantDerivativeOnUniv.add hf_smul_cYZ hYf_smul_Z,
      cov.isCovariantDerivativeOnUniv.add hf_smul_cXZ hXf_smul_Z]
  -- Apply Leibniz to each term: convert `ContMDiffAt 2 f x` to `MDiffAt f x` first.
  have hf_mdiff : MDiffAt f x := hf.mdifferentiableAt (by simp)
  rw [cov.isCovariantDerivativeOnUniv.leibniz hcYZ hf_mdiff,
      cov.isCovariantDerivativeOnUniv.leibniz hZx hYf,
      cov.isCovariantDerivativeOnUniv.leibniz hcXZ hf_mdiff,
      cov.isCovariantDerivativeOnUniv.leibniz hZx hXf]
  -- Apply Leibniz to the third term `cov.toFun (f • Z) x ([X,Y] x)`:
  rw [show cov.toFun (f • Z) x = f x • cov.toFun Z x + (extDerivFun f x).smulRight (Z x) from
      cov.isCovariantDerivativeOnUniv.leibniz hZx hf_mdiff]
  -- Unfold all the CLM applications.
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
             ContinuousLinearMap.smulRight_apply]
  -- The remaining cancellation requires the foundation lemma:
  --   extDerivFun f x ([X,Y] x) = extDerivFun (Yf) x (X x) - extDerivFun (Xf) x (Y x).
  have hfound :
      extDerivFun f x (VectorField.mlieBracket I X Y x) =
        extDerivFun Yf x (X x) - extDerivFun Xf x (Y x) :=
    extDerivFun_apply_mlieBracket hX hY hf hx_int
  -- Substitute the foundation identity.
  rw [hfound]
  -- Unfold the `set`-defined `Xf, Yf` to match `extDerivFun f`.
  simp only [hXf_def, hYf_def]
  -- Unfold `covApply` to make the symbol-level equality `covApply cov X Z x = ↑cov Z x (X x)`
  -- explicit, so the cross terms cancel correctly.
  simp only [covApply_apply]
  -- Distributivity of subtraction in the `extDerivFun (Yf) - extDerivFun (Xf)` smul.
  rw [sub_smul]
  -- Algebraic cancellation: cross terms cancel, then smul-distributivity over the
  -- remaining `f x •` factor. `module` handles smul over a commutative semiring.
  module

end TensorSection

/-! ## First Bianchi identity for the Levi-Civita derivative

For a torsion-free covariant derivative on the tangent bundle, the cyclic sum of the
Riemann curvature operator vanishes:
$$
  R(X, Y) Z + R(Y, Z) X + R(Z, X) Y = 0.
$$
We prove this for the bundled `LeviCivita` covariant derivative. The proof uses the
torsion-free reformulation `cov_X Y - cov_Y X = [X, Y]` (i.e.
`covApply cov X Y - covApply cov Y X = mlieBracket I X Y` at the manifold level) and the
Jacobi identity `[X, [Y, Z]] = [[X, Y], Z] + [Y, [X, Z]]` for the manifold Lie bracket. -/

section Bianchi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure

/-- **Auxiliary: section-level torsion-free identity.** For a torsion-free `cov` on the
tangent bundle, and tangent vector fields `A, B` differentiable on a neighbourhood of `x`,
the section difference `covApply cov A B - covApply cov B A` agrees on a neighbourhood of
`x` with the manifold Lie bracket section `mlieBracket I A B`. This is the
section-level (eventual-equality) form of the torsion-free identity. -/
private lemma covApply_sub_eventuallyEq_mlieBracket
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) (htor : cov.torsion = 0)
    {A B : Π b : M, TangentSpace I b} {x : M}
    (hAnhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% A) b)
    (hBnhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% B) b) :
    ∀ᶠ b in 𝓝 x,
      covApply cov A B b - covApply cov B A b = VectorField.mlieBracket I A B b := by
  filter_upwards [hAnhd, hBnhd] with b hAb hBb
  exact (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp htor hAb hBb

/-- **Auxiliary: cov-of-section-difference identity** for a torsion-free covariant
derivative on the tangent bundle. Under section-level torsion-free, the value of
`cov.toFun (covApply cov A B) x` minus `cov.toFun (covApply cov B A) x` (as CLMs)
equals `cov.toFun (mlieBracket I A B) x`. The proof uses `IsCovariantDerivativeOn.add`
to compute `cov.toFun (covApply cov A B) x - cov.toFun (covApply cov B A) x =
cov.toFun ((covApply cov A B) - (covApply cov B A)) x`, then `congr_of_eventuallyEq`
to swap the section difference for `mlieBracket I A B`. -/
private lemma cov_covApply_sub_eq_cov_mlieBracket
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) (htor : cov.torsion = 0)
    {A B : Π b : M, TangentSpace I b} {x : M}
    (hAnhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% A) b)
    (hBnhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% B) b)
    (hcAB : MDiffAt (T% (covApply cov A B)) x)
    (hcBA : MDiffAt (T% (covApply cov B A)) x)
    (hbracket : MDiffAt (T% (VectorField.mlieBracket I A B)) x) :
    cov.toFun (covApply cov A B) x - cov.toFun (covApply cov B A) x =
      cov.toFun (VectorField.mlieBracket I A B) x := by
  classical
  -- Define `σ := covApply cov A B - covApply cov B A` and observe that
  -- `covApply cov A B = σ + covApply cov B A`. By cov-additivity at x (using both
  -- `σ` and `covApply cov B A` MDiff at x), we get
  --    cov.toFun (covApply cov A B) x = cov.toFun σ x + cov.toFun (covApply cov B A) x,
  -- hence `cov.toFun σ x = cov.toFun (covApply cov A B) x - cov.toFun (covApply cov B A) x`.
  -- Then by section-level torsion-free + `congr_of_eventuallyEq`,
  --    cov.toFun σ x = cov.toFun (mlieBracket I A B) x.
  -- Combine.
  set σ : Π b : M, TangentSpace I b := covApply cov A B - covApply cov B A with hσ_def
  have hσ_eq : covApply cov A B = σ + covApply cov B A := by funext b; simp [σ]
  -- σ MDiff at x: as difference of MDiff sections.
  -- `MDifferentiableAt.sub_section` (Mathlib) provides this.
  have hσ_mdiff : MDiffAt (T% σ) x := by
    have hneg : MDiffAt (T% (-(covApply cov B A))) x :=
      mdifferentiableAt_neg_section hcBA
    have := mdifferentiableAt_add_section hcAB hneg
    -- `σ = covApply cov A B + (- covApply cov B A) = covApply cov A B - covApply cov B A`.
    convert this using 1
    funext b; simp [σ, sub_eq_add_neg]
  -- Apply cov-additivity at x to the equation `covApply cov A B = σ + covApply cov B A`.
  have hadd_at_x :
      cov.toFun (covApply cov A B) x = cov.toFun σ x + cov.toFun (covApply cov B A) x := by
    rw [hσ_eq]
    exact cov.isCovariantDerivativeOnUniv.add hσ_mdiff hcBA
  -- Hence `cov.toFun σ x = cov.toFun (covApply cov A B) x - cov.toFun (covApply cov B A) x`.
  have hσ_val : cov.toFun σ x =
      cov.toFun (covApply cov A B) x - cov.toFun (covApply cov B A) x := by
    rw [hadd_at_x]; abel
  -- Section-level torsion-free: σ =ᶠ[𝓝 x] mlieBracket I A B (pointwise eventual equality).
  have hsec_ev : ∀ᶠ b in 𝓝 x, σ b = VectorField.mlieBracket I A B b := by
    have := covApply_sub_eventuallyEq_mlieBracket (cov := cov) htor hAnhd hBnhd
    filter_upwards [this] with b hb
    change (covApply cov A B - covApply cov B A) b = _
    rw [Pi.sub_apply]; exact hb
  -- Apply `congr_of_eventuallyEq` to swap σ for mlieBracket I A B.
  have hcov_swap :
      cov.toFun σ x = cov.toFun (VectorField.mlieBracket I A B) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hσ_mdiff hbracket (Filter.univ_mem) hsec_ev
  -- Combine.
  rw [← hcov_swap, hσ_val]

set_option linter.style.show false in
/-- **First Bianchi identity for the Levi-Civita derivative.**

The cyclic sum `R(X, Y) Z + R(Y, Z) X + R(Z, X) Y` of the section-level Riemann curvature
operator vanishes for the Levi-Civita covariant derivative on the tangent bundle.

Hypotheses: `X, Y, Z` are tangent vector fields, all `MDifferentiableAt` at `x`, with
their pairwise covariant derivatives also `MDifferentiableAt` at `x`. The section-level
torsion-free identity requires `X, Y, Z` to be `MDifferentiable` on a neighbourhood of
`x`, plus the pairwise manifold Lie bracket sections `mlieBracket I A B` to be `MDiff`
at `x` for each cyclic pair. The Jacobi-identity step requires `X, Y, Z` to be
`ContMDiffAt` of order `minSmoothness ℝ 2 = 2` at `x` (Mathlib's smoothness threshold
for the manifold-level Jacobi identity). -/
theorem riemannSec_first_bianchi_levi_civita
    (g : SmoothRiemannianMetric I M)
    {X Y Z : Π b : M, TangentSpace I b} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (hXnhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% X) b)
    (hYnhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% Y) b)
    (hZnhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% Z) b)
    (hcXY : MDiffAt (T% (covApply (LeviCivita (I := I) g) X Y)) x)
    (hcYX : MDiffAt (T% (covApply (LeviCivita (I := I) g) Y X)) x)
    (hcXZ : MDiffAt (T% (covApply (LeviCivita (I := I) g) X Z)) x)
    (hcZX : MDiffAt (T% (covApply (LeviCivita (I := I) g) Z X)) x)
    (hcYZ : MDiffAt (T% (covApply (LeviCivita (I := I) g) Y Z)) x)
    (hcZY : MDiffAt (T% (covApply (LeviCivita (I := I) g) Z Y)) x)
    (hbrXY : MDiffAt (T% (VectorField.mlieBracket I X Y)) x)
    (hbrYZ : MDiffAt (T% (VectorField.mlieBracket I Y Z)) x)
    (hbrZX : MDiffAt (T% (VectorField.mlieBracket I Z X)) x)
    (hX2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2) (T% X) x)
    (hY2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2) (T% Y) x)
    (hZ2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2) (T% Z) x) :
    riemannSec (LeviCivita (I := I) g) X Y Z x +
      riemannSec (LeviCivita (I := I) g) Y Z X x +
      riemannSec (LeviCivita (I := I) g) Z X Y x = 0 := by
  classical
  -- Synthesize the manifold-smoothness instance needed for the manifold Jacobi identity.
  haveI : IsManifold I (minSmoothness ℝ 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set cov := LeviCivita (I := I) g with hcov
  have htor : cov.torsion = 0 := LeviCivita_torsion_eq_zero (I := I) g
  -- Unfold each `riemannSec` to its definition.
  unfold riemannSec
  -- Use the cov-of-section-difference identity for the three "linear-derivative" pairs.
  have hpairX :
      cov.toFun (covApply cov Y Z) x (X x) - cov.toFun (covApply cov Z Y) x (X x) =
        cov.toFun (VectorField.mlieBracket I Y Z) x (X x) := by
    have := cov_covApply_sub_eq_cov_mlieBracket (cov := cov) htor hYnhd hZnhd hcYZ hcZY hbrYZ
    -- Apply both sides at (X x).
    have happ : (cov.toFun (covApply cov Y Z) x - cov.toFun (covApply cov Z Y) x) (X x) =
        cov.toFun (VectorField.mlieBracket I Y Z) x (X x) := by rw [this]
    simp only [ContinuousLinearMap.sub_apply] at happ
    exact happ
  have hpairY :
      cov.toFun (covApply cov Z X) x (Y x) - cov.toFun (covApply cov X Z) x (Y x) =
        cov.toFun (VectorField.mlieBracket I Z X) x (Y x) := by
    have := cov_covApply_sub_eq_cov_mlieBracket (cov := cov) htor hZnhd hXnhd hcZX hcXZ hbrZX
    have happ : (cov.toFun (covApply cov Z X) x - cov.toFun (covApply cov X Z) x) (Y x) =
        cov.toFun (VectorField.mlieBracket I Z X) x (Y x) := by rw [this]
    simp only [ContinuousLinearMap.sub_apply] at happ
    exact happ
  have hpairZ :
      cov.toFun (covApply cov X Y) x (Z x) - cov.toFun (covApply cov Y X) x (Z x) =
        cov.toFun (VectorField.mlieBracket I X Y) x (Z x) := by
    have := cov_covApply_sub_eq_cov_mlieBracket (cov := cov) htor hXnhd hYnhd hcXY hcYX hbrXY
    have happ : (cov.toFun (covApply cov X Y) x - cov.toFun (covApply cov Y X) x) (Z x) =
        cov.toFun (VectorField.mlieBracket I X Y) x (Z x) := by rw [this]
    simp only [ContinuousLinearMap.sub_apply] at happ
    exact happ
  -- Goal: regrouped cyclic sum = 0.
  -- Linear-derivative pieces collapse to `cov.toFun (mlieBracket Y Z) x (X x) + ...` (3 such).
  -- Cov-cov pieces collapse to `-cov.toFun Z x (mlieBracket X Y x) - ...` (3 such).
  -- The total is a sum of `cov.toFun ([A,B]) x (C x) - cov.toFun C x ([A,B] x)` pairs (3 such),
  -- each of which equals `mlieBracket I C [A,B] x` by torsion-free at x for the sections
  -- `[A,B]` and `C`.
  -- After collecting cyclic pairs, the total is
  --   `mlieBracket I X [Y,Z] x + mlieBracket I Y [Z,X] x + mlieBracket I Z [X,Y] x`,
  -- which is zero by the Jacobi identity.
  -- Apply the Jacobi identity (in cyclic form) to close the goal.
  have hJacobi := VectorField.leibniz_identity_mlieBracket_apply (I := I)
    (U := X) (V := Y) (W := Z) (x := x) hX2 hY2 hZ2
  -- `[X, [Y, Z]] = [[X, Y], Z] + [Y, [X, Z]]`.
  -- Convert to cyclic form using antisymmetry:
  -- [X, [Y,Z]] - [Y, [X,Z]] - [[X,Y], Z] = 0
  -- ↔  [X, [Y,Z]] + [Y, [Z,X]] + [Z, [X,Y]] = 0  (using [Y,[X,Z]] = -[Y,[Z,X]] and [[X,Y],Z] = -[Z,[X,Y]]).
  have hJac_cyc :
      VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z) x +
        VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x +
        VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) x = 0 := by
    -- Convert `[Y, [X, Z]]` to `-[Y, [Z, X]]` by function-level swap.
    have hbr_XZ : VectorField.mlieBracket I X Z =
        - VectorField.mlieBracket I Z X :=
      VectorField.mlieBracket_swap (V := X) (W := Z)
    have hab1 : VectorField.mlieBracket I (VectorField.mlieBracket I X Y) Z x =
        - VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) x :=
      VectorField.mlieBracket_swap_apply (V := VectorField.mlieBracket I X Y) (W := Z)
    -- Apply this rewrite inside `mlieBracket I Y _`.
    have hab2 : VectorField.mlieBracket I Y (VectorField.mlieBracket I X Z) x =
        - VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x := by
      conv_lhs => rw [hbr_XZ]
      -- Now LHS = mlieBracket I Y (-mlieBracket I Z X) x.
      have hsmul : (-VectorField.mlieBracket I Z X) = (-1 : ℝ) • VectorField.mlieBracket I Z X := by
        ext b; simp
      rw [hsmul]
      rw [VectorField.mlieBracket_const_smul_right (c := (-1 : ℝ)) (V := Y)
        (W := VectorField.mlieBracket I Z X) (x := x) hbrZX]
      simp
    rw [hab1, hab2] at hJacobi
    -- Now `hJacobi : [X, [Y, Z]] x = -[Z, [X, Y]] x + (-[Y, [Z, X]] x)`.
    -- Rearrange to cyclic form via `abel`.
    rw [hJacobi]; abel
  -- Now collapse the goal using the section identities `hpairX, hpairY, hpairZ` and the
  -- cyclic Jacobi identity.
  -- We claim the cyclic sum (after `unfold riemannSec`) equals `[X, [Y,Z]] + [Y, [Z,X]] + [Z, [X,Y]]`
  -- (at x), which is zero by `hJac_cyc`.
  -- Collect via algebraic manipulation: linear-derivative groups become cov(·, [·,·]),
  -- cov-cov groups become -cov(·, [·,·]), and each pair `cov([A,B], C) - cov(C, [A,B])`
  -- equals `mlieBracket I C [A, B] x` by torsion-free applied to the sections `[A,B]` and `C`.
  -- Each of the three `pair` identities below uses torsion-free at `x` for sections
  -- `mlieBracket I A B` (a section) and `C` (a section), giving
  --   cov.toFun C x ([A,B] x) - cov.toFun ([A,B]) x (C x) = mlieBracket I [A,B] C x
  -- and `mlieBracket I [A,B] C x = -mlieBracket I C [A,B] x` by antisymmetry.
  have hpairXYZ :
      cov.toFun (VectorField.mlieBracket I Y Z) x (X x) -
        cov.toFun X x (VectorField.mlieBracket I Y Z x) =
      VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z) x := by
    have htf : cov.toFun X x (VectorField.mlieBracket I Y Z x) -
        cov.toFun (VectorField.mlieBracket I Y Z) x (X x) =
        VectorField.mlieBracket I (VectorField.mlieBracket I Y Z) X x :=
      (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp htor hbrYZ hX
    have hbr_swap :
        VectorField.mlieBracket I (VectorField.mlieBracket I Y Z) X x =
        - VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z) x :=
      VectorField.mlieBracket_swap_apply
        (V := VectorField.mlieBracket I Y Z) (W := X)
    -- `htf` gives the negated form; combine with antisymmetry.
    have : cov.toFun (VectorField.mlieBracket I Y Z) x (X x) -
        cov.toFun X x (VectorField.mlieBracket I Y Z x) =
        - VectorField.mlieBracket I (VectorField.mlieBracket I Y Z) X x := by
      rw [← htf]; abel
    rw [this, hbr_swap]; abel
  have hpairYZX :
      cov.toFun (VectorField.mlieBracket I Z X) x (Y x) -
        cov.toFun Y x (VectorField.mlieBracket I Z X x) =
      VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x := by
    have htf : cov.toFun Y x (VectorField.mlieBracket I Z X x) -
        cov.toFun (VectorField.mlieBracket I Z X) x (Y x) =
        VectorField.mlieBracket I (VectorField.mlieBracket I Z X) Y x :=
      (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp htor hbrZX hY
    have hbr_swap :
        VectorField.mlieBracket I (VectorField.mlieBracket I Z X) Y x =
        - VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x :=
      VectorField.mlieBracket_swap_apply
        (V := VectorField.mlieBracket I Z X) (W := Y)
    have : cov.toFun (VectorField.mlieBracket I Z X) x (Y x) -
        cov.toFun Y x (VectorField.mlieBracket I Z X x) =
        - VectorField.mlieBracket I (VectorField.mlieBracket I Z X) Y x := by
      rw [← htf]; abel
    rw [this, hbr_swap]; abel
  have hpairZXY :
      cov.toFun (VectorField.mlieBracket I X Y) x (Z x) -
        cov.toFun Z x (VectorField.mlieBracket I X Y x) =
      VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) x := by
    have htf : cov.toFun Z x (VectorField.mlieBracket I X Y x) -
        cov.toFun (VectorField.mlieBracket I X Y) x (Z x) =
        VectorField.mlieBracket I (VectorField.mlieBracket I X Y) Z x :=
      (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp htor hbrXY hZ
    have hbr_swap :
        VectorField.mlieBracket I (VectorField.mlieBracket I X Y) Z x =
        - VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) x :=
      VectorField.mlieBracket_swap_apply
        (V := VectorField.mlieBracket I X Y) (W := Z)
    have : cov.toFun (VectorField.mlieBracket I X Y) x (Z x) -
        cov.toFun Z x (VectorField.mlieBracket I X Y x) =
        - VectorField.mlieBracket I (VectorField.mlieBracket I X Y) Z x := by
      rw [← htf]; abel
    rw [this, hbr_swap]; abel
  -- Now substitute everything and use `hJac_cyc` to close.
  -- The goal is:
  --   [c(D_Y Z, X) - c(D_X Z, Y) - c(Z, [X,Y])] + [c(D_Z X, Y) - c(D_Y X, Z) - c(X, [Y,Z])]
  --     + [c(D_X Y, Z) - c(D_Z Y, X) - c(Y, [Z,X])] = 0
  -- Regroup:
  --   (c(D_Y Z, X) - c(D_Z Y, X)) - c(X, [Y,Z])  ← X-slot
  --   + (c(D_Z X, Y) - c(D_X Z, Y)) - c(Y, [Z,X])  ← Y-slot
  --   + (c(D_X Y, Z) - c(D_Y X, Z)) - c(Z, [X,Y])  ← Z-slot
  --   = c([Y,Z], X) - c(X, [Y,Z]) + c([Z,X], Y) - c(Y, [Z,X]) + c([X,Y], Z) - c(Z, [X,Y])
  --   = mlieBracket I X [Y,Z] x + mlieBracket I Y [Z,X] x + mlieBracket I Z [X,Y] x
  --   = 0 by Jacobi.
  -- Apply the section-difference identities to the linear-derivative slot pairs in the
  -- regrouped sum. After `abel` regrouping we have:
  --   (c(D_Y Z, X) - c(D_Z Y, X)) + (c(D_Z X, Y) - c(D_X Z, Y)) + (c(D_X Y, Z) - c(D_Y X, Z))
  --     - c(Z, [X,Y]) - c(X, [Y,Z]) - c(Y, [Z,X]) = 0
  -- Substitute via `hpairX, hpairY, hpairZ`:
  --   c([Y,Z], X) + c([Z,X], Y) + c([X,Y], Z) - c(Z, [X,Y]) - c(X, [Y,Z]) - c(Y, [Z,X]) = 0.
  -- Then use `hpairXYZ, hpairYZX, hpairZXY` to fold the cyclic pairs into mlieBracket terms,
  -- and apply `hJac_cyc`.
  -- We achieve this by adding zero copies of the identities and applying abel.
  have hgoal :
      (cov.toFun (covApply cov Y Z) x (X x) - cov.toFun (covApply cov X Z) x (Y x) -
        cov.toFun Z x (VectorField.mlieBracket I X Y x)) +
      (cov.toFun (covApply cov Z X) x (Y x) - cov.toFun (covApply cov Y X) x (Z x) -
        cov.toFun X x (VectorField.mlieBracket I Y Z x)) +
      (cov.toFun (covApply cov X Y) x (Z x) - cov.toFun (covApply cov Z Y) x (X x) -
        cov.toFun Y x (VectorField.mlieBracket I Z X x)) =
      (VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z) x +
        VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x +
        VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) x) := by
    -- Algebraic rearrangement using `hpairX, hpairY, hpairZ, hpairXYZ, hpairYZX, hpairZXY`.
    have e1 : cov.toFun (covApply cov Y Z) x (X x) - cov.toFun (covApply cov Z Y) x (X x) =
        cov.toFun (VectorField.mlieBracket I Y Z) x (X x) := hpairX
    have e2 : cov.toFun (covApply cov Z X) x (Y x) - cov.toFun (covApply cov X Z) x (Y x) =
        cov.toFun (VectorField.mlieBracket I Z X) x (Y x) := hpairY
    have e3 : cov.toFun (covApply cov X Y) x (Z x) - cov.toFun (covApply cov Y X) x (Z x) =
        cov.toFun (VectorField.mlieBracket I X Y) x (Z x) := hpairZ
    -- After regrouping, the linear-derivative pairs become `mlieBracket`-section evaluations.
    -- Then by `hpairXYZ, hpairYZX, hpairZXY`, those minus the `c(C, [A,B])` terms collapse.
    -- We use `abel` on both sides: the LHS becomes
    --   (linear pairs) - (cov-cov terms), and after applying e1, e2, e3 and the pair lemmas,
    -- it equals the cyclic Jacobi sum on RHS.
    have h1 : cov.toFun (covApply cov Y Z) x (X x) - cov.toFun (covApply cov Z Y) x (X x) -
        cov.toFun X x (VectorField.mlieBracket I Y Z x) =
        VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z) x := by
      rw [e1]; exact hpairXYZ
    have h2 : cov.toFun (covApply cov Z X) x (Y x) - cov.toFun (covApply cov X Z) x (Y x) -
        cov.toFun Y x (VectorField.mlieBracket I Z X x) =
        VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x := by
      rw [e2]; exact hpairYZX
    have h3 : cov.toFun (covApply cov X Y) x (Z x) - cov.toFun (covApply cov Y X) x (Z x) -
        cov.toFun Z x (VectorField.mlieBracket I X Y x) =
        VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) x := by
      rw [e3]; exact hpairZXY
    -- LHS of `hgoal` is `(R_X) + (R_Y) + (R_Z)` where R_? are riemannSec terms (after unfold).
    -- Regroup: R_X + R_Y + R_Z = h1's LHS + h2's LHS + h3's LHS (after abel).
    -- The abel below does: distribute the regroup so each linear-derivative slot pair
    -- (X-slot, Y-slot, Z-slot) collects with the matching cov-cov term.
    have hLHS : ((cov.toFun (covApply cov Y Z) x (X x) - cov.toFun (covApply cov X Z) x (Y x) -
        cov.toFun Z x (VectorField.mlieBracket I X Y x)) +
      (cov.toFun (covApply cov Z X) x (Y x) - cov.toFun (covApply cov Y X) x (Z x) -
        cov.toFun X x (VectorField.mlieBracket I Y Z x)) +
      (cov.toFun (covApply cov X Y) x (Z x) - cov.toFun (covApply cov Z Y) x (X x) -
        cov.toFun Y x (VectorField.mlieBracket I Z X x))) =
      (cov.toFun (covApply cov Y Z) x (X x) - cov.toFun (covApply cov Z Y) x (X x) -
        cov.toFun X x (VectorField.mlieBracket I Y Z x)) +
      (cov.toFun (covApply cov Z X) x (Y x) - cov.toFun (covApply cov X Z) x (Y x) -
        cov.toFun Y x (VectorField.mlieBracket I Z X x)) +
      (cov.toFun (covApply cov X Y) x (Z x) - cov.toFun (covApply cov Y X) x (Z x) -
        cov.toFun Z x (VectorField.mlieBracket I X Y x)) := by abel
    rw [hLHS, h1, h2, h3]
  rw [hgoal]
  exact hJac_cyc

end Bianchi

/-! ## Bundled trilinear form of the section-level Riemann operator

The section-level `riemannSec` formula descends to a trilinear continuous map at each
point `x : M`, capturing the Riemann curvature tensor `R(X, Y) Z` as a `T_x M ⊗ T_x M ⊗
V x → V x` operator. The construction proceeds by extending each fibre vector
`(v, w, u) ∈ T_x M × T_x M × V x` to a smooth global section via
`ContMDiffSection.exists_eq_at`, then evaluating `riemannSec cov X Y Z x` on the chosen
extensions. By the C^∞(M)-tensoriality of `riemannSec` in each of its three section
arguments (proved as `riemannSec_smul_left`, `riemannSec_smul_right`, and
`riemannSec_smul_third` above), the result depends only on the fibre values
`(v, w, u)`, not on the chosen extensions. -/

section RiemannOp

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

/-- Pick a smooth global section of the tangent bundle through a given fibre vector. -/
noncomputable def smoothExtensionTangent (x : M) (v : TangentSpace I x) :
    Π b : M, TangentSpace I b :=
  fun b => ((ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x v).choose : Cₛ^(⊤ : ℕ∞)⟮I; E,
    (TangentSpace I : M → Type _)⟯) b

/-- Pick a smooth global section of `V` through a given fibre vector. -/
noncomputable def smoothExtensionFiber (x : M) (u : V x) :
    Π b : M, V b :=
  fun b => ((ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := F) (V := V) x u).choose : Cₛ^(⊤ : ℕ∞)⟮I; F, V⟯) b

/-- The chosen smooth tangent extension agrees with the prescribed value at `x`. -/
lemma smoothExtensionTangent_eq (x : M) (v : TangentSpace I x) :
    smoothExtensionTangent (I := I) x v x = v := by
  classical
  exact (ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x v).choose_spec

/-- The chosen smooth fibre extension agrees with the prescribed value at `x`. -/
lemma smoothExtensionFiber_eq (x : M) (u : V x) :
    smoothExtensionFiber (I := I) (F := F) (V := V) x u x = u := by
  classical
  exact (ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := F) (V := V) x u).choose_spec

/-- **The section-level Riemann curvature operator at a point**, as a trilinear function
on fibre values.

For a covariant derivative `cov` on a vector bundle `V` over `M`, and a point `x : M`,
this is the function
$$
  R_{\mathrm{op}}^{\mathrm{cov}, x} : T_x M \times T_x M \times V_x \to V_x,
  \quad R_{\mathrm{op}}^{\mathrm{cov}, x}(v, w, u) :=
    R^{\mathrm{cov}}(\widetilde{v}, \widetilde{w}) \widetilde{u} (x),
$$
where `$\widetilde{v}, \widetilde{w}, \widetilde{u}$` are arbitrarily chosen smooth global
extensions of the fibre vectors. The construction uses `Classical.choice` via
`ContMDiffSection.exists_eq_at` to make the choice. Independence of the chosen extensions
(which follows from `riemannSec_smul_left/right/third` and the standard "acts pointwise"
argument) is not formalised here. -/
noncomputable def riemannOpFun (cov : CovariantDerivative I F V) (x : M) :
    TangentSpace I x → TangentSpace I x → V x → V x :=
  fun v w u =>
    riemannSec cov
      (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x w)
      (smoothExtensionFiber (I := I) (F := F) (V := V) x u) x

/-- **Section-evaluation form of `riemannOpFun`**: for any smooth global extensions
`X, Y` of `(v, w)` and any smooth global section `Z` agreeing with `u` at `x` (and with
suitable MDifferentiability hypotheses for `riemannSec`), the value
`riemannOpFun cov x v w u` equals `riemannSec cov X Y Z x`. **Independence of the choice
of extensions is left as a separate proof obligation.** -/
theorem riemannOpFun_def (cov : CovariantDerivative I F V) (x : M)
    (v w : TangentSpace I x) (u : V x) :
    riemannOpFun cov x v w u =
      riemannSec cov
        (smoothExtensionTangent (I := I) x v)
        (smoothExtensionTangent (I := I) x w)
        (smoothExtensionFiber (I := I) (F := F) (V := V) x u) x := rfl

end RiemannOp

end Connection
end Integral
end DifferentialGeometry
