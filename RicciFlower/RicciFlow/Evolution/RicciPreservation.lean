import RicciFlower.DimensionThree.RicciControlsRm
import RicciFlower.MaximumPrinciple.TensorWeak
import RicciFlower.Realized.CurvatureProducers
import RicciFlower.RicciFlow.Basic
import RicciFlower.LeviCivita.Koszul
import RicciFlower.Tensor.RSTensor.QuadraticBounds

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# Ricci positivity and pinching preservation

This file contains the Ricci-flow-specific consumer layer for LaTeX Lemma 9.1
and Lemma 9.2.  The results here are conditional on the current tensor weak
maximum principle regularity package.  They do not reopen the analytic proof of
Hamilton's tensor maximum principle.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open Realized
open Bundle
open Tensor0SBundle
open scoped BigOperators Manifold ContDiff

/-! ## Pure three-dimensional reaction algebra -/

/-- Matrix square of Ricci components in an orthonormal `Fin 3` basis. -/
def ricciSq3 (Ric : Fin 3 -> Fin 3 -> Real) (i j : Fin 3) : Real :=
  ∑ k : Fin 3, Ric i k * Ric k j

/-- Ricci component trace in an orthonormal `Fin 3` basis. -/
def ricciScal3 (Ric : Fin 3 -> Fin 3 -> Real) : Real :=
  ∑ i : Fin 3, Ric i i

/-- Ricci component norm square in an orthonormal `Fin 3` basis. -/
def ricciNorm3 (Ric : Fin 3 -> Fin 3 -> Real) : Real :=
  ∑ i : Fin 3, ∑ j : Fin 3, Ric i j * Ric i j

/-- The Ricci reaction tensor components
`2 R_ikjl Ric_kl - 2 Ric_i^k Ric_kj` in an orthonormal `Fin 3` basis. -/
def ricciPresReact
    (Rm : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (Ric : Fin 3 -> Fin 3 -> Real) (i j : Fin 3) : Real :=
  2 * (∑ k : Fin 3, ∑ l : Fin 3, Rm i k j l * Ric k l) -
    2 * ricciSq3 Ric i j

/-- The shifted pinching reaction for `S = Ric - delta R g`, in an
orthonormal `Fin 3` basis. -/
def pinchReact
    (delta : Real)
    (Rm : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (Ric : Fin 3 -> Fin 3 -> Real) (i j : Fin 3) : Real :=
  ricciPresReact Rm Ric i j -
    2 * delta * (ricciNorm3 Ric * RicciFlower.DimensionThree.delta3 i j -
      ricciScal3 Ric * Ric i j)

/-- Standard three-dimensional Riemann-from-Ricci component model for an
arbitrary Ricci matrix in an orthonormal `Fin 3` basis. -/
def stdRmOfRic3
    (Ric : Fin 3 -> Fin 3 -> Real)
    (i j k l : Fin 3) : Real :=
  RicciFlower.DimensionThree.delta3 i k * Ric j l
    - RicciFlower.DimensionThree.delta3 i l * Ric j k
    - RicciFlower.DimensionThree.delta3 j k * Ric i l
    + RicciFlower.DimensionThree.delta3 j l * Ric i k
    - (1 / 2 : Real) * ricciScal3 Ric *
        (RicciFlower.DimensionThree.delta3 i k *
            RicciFlower.DimensionThree.delta3 j l -
          RicciFlower.DimensionThree.delta3 i l *
            RicciFlower.DimensionThree.delta3 j k)

/-- Lemma 9.1 reaction algebra at a Ricci-null eigenvector. -/
theorem ricciReactNull
    (l1 l2 l3 : Real) (hnull : l1 = 0) :
    ricciPresReact (RicciFlower.DimensionThree.stdRmDiag3 l1 l2 l3)
      (RicciFlower.DimensionThree.ricciDiag3 l1 l2 l3) 0 0 =
      (l2 - l3) ^ 2 := by
  subst l1
  unfold ricciPresReact ricciSq3 RicciFlower.DimensionThree.stdRmDiag3
    RicciFlower.DimensionThree.ricciDiag3 RicciFlower.DimensionThree.ricciEigenScalar3
    RicciFlower.DimensionThree.delta3
  simp [Fin.sum_univ_three]
  ring

/-- Nonnegativity form of `ricciReactNull`. -/
theorem ricciReact_ge
    (l1 l2 l3 : Real) (hnull : l1 = 0) :
    0 <= ricciPresReact (RicciFlower.DimensionThree.stdRmDiag3 l1 l2 l3)
      (RicciFlower.DimensionThree.ricciDiag3 l1 l2 l3) 0 0 := by
  rw [ricciReactNull l1 l2 l3 hnull]
  positivity

/-- Lemma 9.2 shifted reaction algebra at a pinching-null eigenvector. -/
theorem pinchReactNull
    (delta l1 l2 l3 : Real)
    (hnull : l1 = delta * RicciFlower.DimensionThree.ricciEigenScalar3 l1 l2 l3) :
    pinchReact delta (RicciFlower.DimensionThree.stdRmDiag3 l1 l2 l3)
      (RicciFlower.DimensionThree.ricciDiag3 l1 l2 l3) 0 0 =
      delta ^ 2 * (1 - 3 * delta) *
          RicciFlower.DimensionThree.ricciEigenScalar3 l1 l2 l3 ^ 2 +
        (1 - delta) * (l2 - l3) ^ 2 := by
  let lhs :=
    pinchReact delta (RicciFlower.DimensionThree.stdRmDiag3 l1 l2 l3)
      (RicciFlower.DimensionThree.ricciDiag3 l1 l2 l3) 0 0
  let rhs :=
    delta ^ 2 * (1 - 3 * delta) *
        RicciFlower.DimensionThree.ricciEigenScalar3 l1 l2 l3 ^ 2 +
      (1 - delta) * (l2 - l3) ^ 2
  change lhs = rhs
  have hrel : delta * (l1 + l2 + l3) - l1 = 0 := by
    unfold RicciFlower.DimensionThree.ricciEigenScalar3 at hnull
    nlinarith
  have hfactor :
      lhs - rhs =
        (delta * (l1 + l2 + l3) - l1) *
          (3 * delta ^ 2 * l1 + 3 * delta ^ 2 * l2 + 3 * delta ^ 2 * l3 +
            2 * delta * l1 - delta * l2 - delta * l3 + 2 * l1 - l2 - l3) := by
    dsimp [lhs, rhs]
    unfold pinchReact ricciPresReact ricciSq3 ricciNorm3 ricciScal3
      RicciFlower.DimensionThree.stdRmDiag3 RicciFlower.DimensionThree.ricciDiag3
      RicciFlower.DimensionThree.ricciEigenScalar3 RicciFlower.DimensionThree.delta3
    simp [Fin.sum_univ_three]
    ring
  have hzero : lhs - rhs = 0 := by
    rw [hfactor, hrel]
    ring
  nlinarith

/-- Nonnegativity form of `pinchReactNull` for `0 <= delta <= 1/3`. -/
theorem pinchReact_ge
    (delta l1 l2 l3 : Real)
    (hdelta0 : 0 <= delta) (hdelta13 : delta <= (1 : Real) / 3)
    (hnull : l1 = delta * RicciFlower.DimensionThree.ricciEigenScalar3 l1 l2 l3) :
    0 <= pinchReact delta (RicciFlower.DimensionThree.stdRmDiag3 l1 l2 l3)
      (RicciFlower.DimensionThree.ricciDiag3 l1 l2 l3) 0 0 := by
  rw [pinchReactNull delta l1 l2 l3 hnull]
  have h1 : 0 <= delta ^ 2 * (1 - 3 * delta) *
      RicciFlower.DimensionThree.ricciEigenScalar3 l1 l2 l3 ^ 2 := by
    have hdelta_sq : 0 <= delta ^ 2 := sq_nonneg delta
    have hcoeff : 0 <= 1 - 3 * delta := by nlinarith
    have hscalar_sq : 0 <= RicciFlower.DimensionThree.ricciEigenScalar3 l1 l2 l3 ^ 2 :=
      sq_nonneg _
    positivity
  have h2 : 0 <= (1 - delta) * (l2 - l3) ^ 2 := by
    have hcoeff : 0 <= 1 - delta := by nlinarith
    have hsquare : 0 <= (l2 - l3) ^ 2 := sq_nonneg _
    positivity
  exact add_nonneg h1 h2

/-- Scalar curvature reconstructed from a shifted pinching-null diagonal tensor
`diag(0,a,b) = Ric - delta R g` when `delta < 1/3`. -/
def shiftScal3 (delta a b : Real) : Real :=
  (a + b) / (1 - 3 * delta)

/-- First Ricci eigenvalue reconstructed from a shifted pinching-null diagonal
tensor. -/
def shiftRic1 (delta a b : Real) : Real :=
  delta * shiftScal3 delta a b

/-- Second Ricci eigenvalue reconstructed from a shifted pinching-null diagonal
tensor. -/
def shiftRic2 (delta a b : Real) : Real :=
  a + delta * shiftScal3 delta a b

/-- Third Ricci eigenvalue reconstructed from a shifted pinching-null diagonal
tensor. -/
def shiftRic3 (delta a b : Real) : Real :=
  b + delta * shiftScal3 delta a b

/-- The reconstructed Ricci eigenvalues have scalar trace `shiftScal3`. -/
theorem shiftScal3_eq
    (delta a b : Real) (hdelta13 : delta < (1 : Real) / 3) :
    RicciFlower.DimensionThree.ricciEigenScalar3
      (shiftRic1 delta a b) (shiftRic2 delta a b) (shiftRic3 delta a b) =
      shiftScal3 delta a b := by
  have hden : 1 - 3 * delta ≠ 0 := by
    nlinarith
  have hden' : 1 - delta * 3 ≠ 0 := by
    nlinarith
  unfold RicciFlower.DimensionThree.ricciEigenScalar3
    shiftRic1 shiftRic2 shiftRic3 shiftScal3
  field_simp [hden, hden']
  ring

/-- The first reconstructed Ricci eigenvalue is pinching-null. -/
theorem shiftNull3
    (delta a b : Real) (hdelta13 : delta < (1 : Real) / 3) :
    shiftRic1 delta a b =
      delta * RicciFlower.DimensionThree.ricciEigenScalar3
        (shiftRic1 delta a b) (shiftRic2 delta a b) (shiftRic3 delta a b) := by
  rw [shiftScal3_eq delta a b hdelta13]
  rfl

/-- Shifted pinching reaction nonnegativity at a reconstructed null direction.

This is the algebraic core for the strict `0 < delta < 1/3` Section 9 null
condition after diagonalizing a nonnegative tensor
`Ric - delta R g = diag(0,a,b)`.  The nonnegativity of `a,b` belongs to the
diagonalization/reconstruction bridge; the reaction value itself only needs the
pinching-null relation and `0 <= delta < 1/3`. -/
theorem pinchShiftNull_ge
    (delta a b : Real)
    (hdelta0 : 0 <= delta) (hdelta13 : delta < (1 : Real) / 3) :
    0 <= pinchReact delta
      (RicciFlower.DimensionThree.stdRmDiag3
        (shiftRic1 delta a b) (shiftRic2 delta a b) (shiftRic3 delta a b))
      (RicciFlower.DimensionThree.ricciDiag3
        (shiftRic1 delta a b) (shiftRic2 delta a b) (shiftRic3 delta a b))
      0 0 := by
  exact pinchReact_ge delta
    (shiftRic1 delta a b) (shiftRic2 delta a b) (shiftRic3 delta a b)
    hdelta0 (le_of_lt hdelta13) (shiftNull3 delta a b hdelta13)

/-- Scalar target for the shifted pinching reaction at a reconstructed
first-null diagonal tensor.  This is the compact form future component
producers should identify with the canonical reaction evaluation. -/
def shiftReact3 (delta a b : Real) : Real :=
  pinchReact delta
    (RicciFlower.DimensionThree.stdRmDiag3
      (shiftRic1 delta a b) (shiftRic2 delta a b) (shiftRic3 delta a b))
    (RicciFlower.DimensionThree.ricciDiag3
      (shiftRic1 delta a b) (shiftRic2 delta a b) (shiftRic3 delta a b))
    0 0

/-- Strict-delta nonnegativity of the compact shifted reaction target. -/
theorem shiftReact3_nonneg
    (delta a b : Real)
    (hdelta0 : 0 < delta) (hdelta13 : delta < (1 : Real) / 3) :
    0 <= shiftReact3 delta a b := by
  exact pinchShiftNull_ge delta a b (le_of_lt hdelta0) hdelta13

/-- Components of a shifted first-null block
`S = Ric - delta * R * g` in an orthonormal basis whose first vector is null:
`[[0,0,0],[0,a,c],[0,c,b]]`. -/
def shiftBlockS3 (a b c : Real) (i j : Fin 3) : Real :=
  if i = 0 then 0
  else if j = 0 then 0
  else if i = 1 then
    if j = 1 then a else c
  else
    if j = 1 then c else b

/-- Ricci components reconstructed from a shifted first-null block. -/
def shiftRicBlock3 (delta a b c : Real) (i j : Fin 3) : Real :=
  shiftBlockS3 a b c i j +
    delta * shiftScal3 delta a b * RicciFlower.DimensionThree.delta3 i j

/-- Shifted pinching reaction at a first-null block, using the full
three-dimensional Riemann-from-Ricci model rather than a diagonal model. -/
def shiftReactBlock3 (delta a b c : Real) : Real :=
  pinchReact delta
    (stdRmOfRic3 (shiftRicBlock3 delta a b c))
    (shiftRicBlock3 delta a b c) 0 0

/-- Explicit block expansion of the shifted first-null reaction. -/
theorem shiftReactBlock3_eq
    (delta a b c : Real) (hdelta13 : delta < (1 : Real) / 3) :
    shiftReactBlock3 delta a b c =
      delta ^ 2 * (1 - 3 * delta) * shiftScal3 delta a b ^ 2 +
        (1 - delta) * ((a - b) ^ 2 + 4 * c ^ 2) := by
  have hden : 1 - 3 * delta ≠ 0 := by nlinarith
  have hden' : 1 - delta * 3 ≠ 0 := by nlinarith
  have hden2 : 1 - delta * 6 + delta ^ 2 * 9 ≠ 0 := by
    have hsq : (1 - delta * 3) ^ 2 ≠ 0 := pow_ne_zero 2 hden'
    convert hsq using 1
    ring
  unfold shiftReactBlock3 pinchReact ricciPresReact ricciSq3 ricciNorm3
    stdRmOfRic3 shiftRicBlock3 shiftBlockS3 shiftScal3
    RicciFlower.DimensionThree.delta3
  simp [Fin.sum_univ_three, ricciScal3]
  field_simp [hden, hden', hden2]
  ring_nf

/-- Strict-delta nonnegativity of the shifted first-null block reaction. -/
theorem shiftReactBlock3_nonneg
    (delta a b c : Real)
    (hdelta0 : 0 < delta) (hdelta13 : delta < (1 : Real) / 3) :
    0 <= shiftReactBlock3 delta a b c := by
  rw [shiftReactBlock3_eq delta a b c hdelta13]
  have hdelta0' : 0 <= delta := le_of_lt hdelta0
  have hcoeff1 : 0 <= 1 - 3 * delta := by nlinarith
  have hcoeff2 : 0 <= 1 - delta := by nlinarith
  have hR2 : 0 <= shiftScal3 delta a b ^ 2 := sq_nonneg _
  have hsq : 0 <= (a - b) ^ 2 + 4 * c ^ 2 := by
    have h1 : 0 <= (a - b) ^ 2 := sq_nonneg _
    have h2 : 0 <= 4 * c ^ 2 := by positivity
    exact add_nonneg h1 h2
  have hterm1 :
      0 <= delta ^ 2 * (1 - 3 * delta) * shiftScal3 delta a b ^ 2 := by
    have hdelta_sq : 0 <= delta ^ 2 := sq_nonneg delta
    positivity
  have hterm2 :
      0 <= (1 - delta) * ((a - b) ^ 2 + 4 * c ^ 2) := by
    positivity
  exact add_nonneg hterm1 hterm2

/-! ## Conditional tensor-WMP consumers -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- A pointwise shifted first-null block in an orthonormal `Fin 3` basis.

This only records the geometric block shape of the raw tensor.  It does not
assert any reaction formula, and it does not choose the orthonormal basis. -/
structure ShiftBlockAt
    (g : SmoothRiemannianMetric I M)
    (A : RawTwoTensorField (I := I) (M := M)) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (a b c : Real) : Prop where
  orthonormal : DimensionThree.OrthonormalBasisAt (I := I) g x basis
  components :
    ∀ i j : Fin 3,
      A x (basis i) (basis j) = shiftBlockS3 a b c i j

/-- A nonzero scalar multiple of a raw bilinear null vector is null in the
reverse direction.  This is the normalization step used before feeding a
first-null vector into an orthonormal basis. -/
theorem raw_null_of_smul
    {A : RawTwoTensorField (I := I) (M := M)} {x : M}
    {v e : TangentSpace I x} {r : Real}
    (hbilin : TwoTensorBilinearAt (I := I) (M := M) A x)
    (hnull : A x v v = 0) (hscale : v = r • e) (hr : r ≠ 0) :
    A x e e = 0 := by
  have hscale_eval : A x v v = (r * r) * A x e e := by
    rw [hscale, hbilin.smul_left r e (r • e),
      hbilin.smul_right r e e]
    ring
  have hmul : (r * r) * A x e e = 0 := by
    simpa [hscale_eval] using hnull
  have hr2 : r * r ≠ 0 := mul_ne_zero hr hr
  exact (mul_eq_zero.mp hmul).resolve_left hr2

/-- A PSD symmetric bilinear first-null tensor has shifted block components in
any supplied orthonormal basis whose first vector is a normalization of the
null direction.  The theorem consumes the basis; the separate basis-completion
producer is still a frontier. -/
theorem shiftBlockOfNull
    {g : SmoothRiemannianMetric I M}
    {A : RawTwoTensorField (I := I) (M := M)} {x : M}
    {v : TangentSpace I x} {r : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DimensionThree.OrthonormalBasisAt (I := I) g x basis)
    (hsym : TwoTensorSymmetricAt (I := I) (M := M) A x)
    (hbilin : TwoTensorBilinearAt (I := I) (M := M) A x)
    (hpsd : TwoTensorNonnegativeAt (I := I) (M := M) A x)
    (hnull : A x v v = 0) (hscale : v = r • basis 0) (hr : r ≠ 0) :
    ShiftBlockAt (I := I) (M := M) g A x basis
      (A x (basis 1) (basis 1))
      (A x (basis 2) (basis 2))
      (A x (basis 1) (basis 2)) := by
  refine ⟨horth, ?_⟩
  have hnull0 : A x (basis 0) (basis 0) = 0 :=
    raw_null_of_smul (I := I) (M := M) hbilin hnull hscale hr
  have hleft :
      ∀ w : TangentSpace I x, A x (basis 0) w = 0 :=
    psd_null_left_raw (I := I) (M := M) hsym hbilin hpsd hnull0
  have hright :
      ∀ w : TangentSpace I x, A x w (basis 0) = 0 :=
    psd_null_right_raw (I := I) (M := M) hsym hbilin hpsd hnull0
  intro i j
  fin_cases i <;> fin_cases j
  · simp [shiftBlockS3, hnull0]
  · simp [shiftBlockS3, hleft]
  · simp [shiftBlockS3, hleft]
  · simp [shiftBlockS3, hright]
  · simp [shiftBlockS3]
  · simp [shiftBlockS3]
  · simp [shiftBlockS3, hright]
  · simpa [shiftBlockS3] using hsym (basis 2) (basis 1)
  · simp [shiftBlockS3]

/-- Component-realization predicate for the shifted first-null block reaction.

This is deliberately only an equality to the finite-dimensional block target.
It does not assert that a raw tensor input has already been put into block
form, nor that the supplied reaction is the canonical Ricci-flow reaction. -/
def ShiftBlockReactRealizes
    (G : Real -> SmoothRiemannianMetric I M)
    (N : TwoTensorReaction (I := I) (M := M))
    (delta t : Real)
    (A : RawTwoTensorField (I := I) (M := M)) {x : M}
    (v : TangentSpace I x) (a b c : Real) : Prop :=
  (N t (G t) A) x v v = shiftReactBlock3 delta a b c

/-- A symmetric-input null condition follows from a shifted first-null block
realization plus the strict block algebra.  The geometric producer still has to
show the reaction component equals `shiftReactBlock3`; this theorem only
packages the algebraic nonnegativity once that component realization is known. -/
theorem shiftNullSymm_of_block
    {G : Real -> SmoothRiemannianMetric I M}
    {N : TwoTensorReaction (I := I) (M := M)}
    {U : Set Real} {delta : Real}
    (hdelta0 : 0 < delta) (hdelta13 : delta < (1 : Real) / 3)
    (hreal :
      ∀ t, t ∈ U -> ∀ A : RawTwoTensorField (I := I) (M := M), ∀ x,
        TwoTensorSymmetricAt (I := I) (M := M) A x ->
        TwoTensorBilinearAt (I := I) (M := M) A x ->
        TwoTensorNonnegativeAt (I := I) (M := M) A x ->
        ∀ v : TangentSpace I x,
          A x v v = 0 ->
          ∃ a b c : Real,
            ShiftBlockReactRealizes (I := I) (M := M) G N delta t A v a b c) :
    TensorNullEigenvectorConditionSymm (I := I) (M := M) G N U := by
  intro t ht A x hsym hbilin hA v hv
  rcases hreal t ht A x hsym hbilin hA v hv with ⟨a, b, c, hreact⟩
  rw [hreact]
  exact shiftReactBlock3_nonneg delta a b c hdelta0 hdelta13

/-- The pinching tensor `Ric - delta R g`. -/
def pinchTensor
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) (delta : Real) :
    TwoTensorFamily (I := I) (M := M) :=
  fun t x v w => Ric t x v w - delta * scalar t x * (G t).inner x v w

/-- Initial strict positivity of the Ricci tensor as a quadratic form. -/
def RicciPosInit
    (Ric : TwoTensorFamily (I := I) (M := M)) : Prop :=
  ∀ x, TwoTensorPositiveDefiniteAt (I := I) (M := M) (Ric 0) x

/-- The compactness/eigenvalue-minimum input of Corollary 9.3: an initial
pinching constant has been selected. -/
def PinchInit
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) : Prop :=
  ∃ delta : Real,
    0 < delta ∧ delta <= (1 : Real) / 3 ∧
      TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
        (pinchTensor (I := I) (M := M) G Ric scalar delta) 0

/-- Strict version of the initial pinching selector, used by the shifted
pinching null-condition route where `delta = 1/3` is intentionally excluded. -/
def PinchInitLt
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) : Prop :=
  ∃ delta : Real,
    0 < delta ∧ delta < (1 : Real) / 3 ∧
      TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
        (pinchTensor (I := I) (M := M) G Ric scalar delta) 0

/-- Forget the strict upper bound in the compatibility initial pinching
selector. -/
theorem pinchInit_of_lt
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (hinit : PinchInitLt (I := I) (M := M) G Ric scalar) :
    PinchInit (I := I) (M := M) G Ric scalar := by
  rcases hinit with ⟨delta, hdelta0, hdelta13, hpinch⟩
  exact ⟨delta, hdelta0, le_of_lt hdelta13, hpinch⟩

/-- Uniform initial bounds which imply a selected pinching constant.  The
compactness/eigenvalue selector for Corollary 9.3 should produce this package
from strict initial Ricci positivity and scalar trace compatibility. -/
def InitBounds
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) : Prop :=
  ∃ c C : Real,
    0 < c ∧ 0 < C ∧
      (∀ x v, c * (G 0).inner x v v <= Ric 0 x v v) ∧
      (∀ x, scalar 0 x <= C)

/-- A base-function realization of the least initial Ricci lower bound.
The remaining geometric selector frontier is to construct such a continuous
positive function from strict initial Ricci positivity. -/
def RicMinData
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (ricMin : M -> Real) : Prop :=
  Continuous ricMin ∧
    (∀ x, 0 < ricMin x) ∧
    (∀ x v, ricMin x * (G 0).inner x v v <= Ric 0 x v v)

/-- Initial Ricci tensor data realized as the Ricci tensor of the initial
metric.  This is the canonical 9.3 entrypoint; `RicMinData` below is only the
compactness adapter once a lower-bound function has been produced. -/
structure MetricRicciData
    [SigmaCompactSpace M] [T2Space M]
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M)) where
  K : CurvatureSectionProducerData
    (I := I) (M := M)
    (LeviCivita.leviCivitaConnectionOfMetric (I := I) (G 0)) (G 0)
  ricci_eq :
    ∀ x v w, Ric 0 x v w = K.ricci x (Curvature.vec2 (I := I) v w)

/-- Strict positivity of the canonical initial Ricci tensor. -/
def MetricRicciPos
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric) : Prop :=
  ∀ x v, v ≠ 0 -> 0 < D.K.ricci x (Curvature.vec2 (I := I) v v)

/-- A base lower-bound function for the canonical initial Ricci tensor. -/
def MetricRicciMin
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (ricMin : M -> Real) : Prop :=
  Continuous ricMin ∧
    (∀ x, 0 < ricMin x) ∧
    (∀ x v,
      ricMin x * (G 0).inner x v v <=
        D.K.ricci x (Curvature.vec2 (I := I) v v))

/-- The unit tangent bundle of one metric as a subtype of the actual tangent
bundle.  This is the compactness-facing interface for the 9.3 selector. -/
abbrev UnitTangent (g : SmoothRiemannianMetric I M) : Type _ :=
  MetricUnitTangent (I := I) (M := M) g

namespace UnitTangent

/-- Base point of a unit tangent vector. -/
def base {g : SmoothRiemannianMetric I M}
    (p : UnitTangent (I := I) (M := M) g) : M :=
  p.1.1

/-- Fiber vector of a unit tangent vector. -/
def vec {g : SmoothRiemannianMetric I M}
    (p : UnitTangent (I := I) (M := M) g) :
    TangentSpace I (base (I := I) (M := M) p) :=
  p.1.2

@[simp]
theorem unit {g : SmoothRiemannianMetric I M}
    (p : UnitTangent (I := I) (M := M) g) :
    g.inner (base (I := I) (M := M) p)
      (vec (I := I) (M := M) p) (vec (I := I) (M := M) p) = 1 :=
  p.2

@[simp]
theorem base_mk {g : SmoothRiemannianMetric I M} {x : M}
    {v : TangentSpace I x} {hunit : g.inner x v v = 1} :
    base (I := I) (M := M)
      (⟨(⟨x, v⟩ : TangentBundle I M), hunit⟩ :
        UnitTangent (I := I) (M := M) g) = x :=
  rfl

@[simp]
theorem vec_mk {g : SmoothRiemannianMetric I M} {x : M}
    {v : TangentSpace I x} {hunit : g.inner x v v = 1} :
    vec (I := I) (M := M)
      (⟨(⟨x, v⟩ : TangentBundle I M), hunit⟩ :
        UnitTangent (I := I) (M := M) g) = v :=
  rfl

end UnitTangent

/-- Uniform initial Ricci lower bound on `g_0`-unit vectors. -/
def UnitRicciLower
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric) (c : Real) : Prop :=
  0 < c ∧
    ∀ x (v : TangentSpace I x), (G 0).inner x v v = 1 ->
      c <= D.K.ricci x (Curvature.vec2 (I := I) v v)

/-- Ricci quadratic evaluation on the initial unit tangent bundle. -/
def unitRicEval
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (p : UnitTangent (I := I) (M := M) (G 0)) : Real :=
  D.K.ricci (UnitTangent.base (I := I) (M := M) p)
    (Curvature.vec2 (I := I)
      (UnitTangent.vec (I := I) (M := M) p)
      (UnitTangent.vec (I := I) (M := M) p))

/-- A unit-vector Ricci lower bound gives a constant base lower-bound
function. -/
theorem metricMin_unit
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {c : Real}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hlower : UnitRicciLower (I := I) (M := M) D c) :
    MetricRicciMin (I := I) (M := M) D (fun _ : M => c) := by
  rcases hlower with ⟨hc, hlower⟩
  refine ⟨continuous_const, fun _ => hc, ?_⟩
  intro x v
  by_cases hv : v = 0
  · subst v
    have hzero :
        D.K.ricci x (Curvature.vec2 (I := I)
          (0 : TangentSpace I x) (0 : TangentSpace I x)) = 0 := by
      have hzero' :
          D.K.ricci x (fun _ : Fin 2 => (0 : TangentSpace I x)) = 0 := by
        simpa [quad02] using
          RicciFlower.tensor02_smul2 (I := I) (M := M) (D.K.ricci x)
            0 (0 : TangentSpace I x)
      have hvec :
          Curvature.vec2 (I := I) (0 : TangentSpace I x) (0 : TangentSpace I x) =
            (fun _ : Fin 2 => (0 : TangentSpace I x)) := by
        funext i
        simp [Curvature.vec2]
      simpa [hvec] using hzero'
    simp [hzero]
  let r : Real := (G 0).inner x v v
  have hrpos : 0 < r := by
    exact (G 0).pos x v hv
  let s : Real := Real.sqrt r
  have hspos : 0 < s := Real.sqrt_pos.mpr hrpos
  have hsne : s ≠ 0 := ne_of_gt hspos
  let a : Real := s⁻¹
  let u : TangentSpace I x := a • v
  have hss : s * s = r := by
    simpa [sq] using (Real.sq_sqrt (le_of_lt hrpos))
  have haa : a * a * r = 1 := by
    have hmul : (s * s) * (s⁻¹ * s⁻¹) = 1 := by
      field_simp [hsne]
    calc
      a * a * r = (s⁻¹ * s⁻¹) * (s * s) := by
        rw [hss]
      _ = (s * s) * (s⁻¹ * s⁻¹) := by ring
      _ = 1 := hmul
  have hunit : (G 0).inner x u u = 1 := by
    calc
      (G 0).inner x u u = a * a * r := by
        simpa [u, r] using RicciFlower.metric_smul2 (I := I) (M := M) (G 0) a v
      _ = 1 := haa
  have hRic_unit := hlower x u hunit
  have hRic_scale :
      D.K.ricci x (Curvature.vec2 (I := I) u u) =
        a * a * D.K.ricci x (Curvature.vec2 (I := I) v v) := by
    have hscale' :
        D.K.ricci x (fun _ : Fin 2 => a • v) =
          a * a * D.K.ricci x (fun _ : Fin 2 => v) := by
      simpa [quad02] using
        RicciFlower.tensor02_smul2 (I := I) (M := M)
          (D.K.ricci x) a v
    have hvecu :
        Curvature.vec2 (I := I) u u = (fun _ : Fin 2 => u) := by
      funext i
      simp [Curvature.vec2]
    have hvecv :
        Curvature.vec2 (I := I) v v = (fun _ : Fin 2 => v) := by
      funext i
      simp [Curvature.vec2]
    simpa [hvecu, hvecv, u] using hscale'
  have hineq :
      c <= a * a * D.K.ricci x (Curvature.vec2 (I := I) v v) := by
    simpa [hRic_scale] using hRic_unit
  have hs2_nonneg : 0 <= s * s := mul_nonneg (le_of_lt hspos) (le_of_lt hspos)
  have hmul := mul_le_mul_of_nonneg_left hineq hs2_nonneg
  have hcancel : (s * s) * (a * a *
        D.K.ricci x (Curvature.vec2 (I := I) v v)) =
      D.K.ricci x (Curvature.vec2 (I := I) v v) := by
    have hmul : (s * s) * (a * a) = 1 := by
      have hsa : s * a = 1 := by
        simp [a, hsne]
      calc
        (s * s) * (a * a) = (s * a) * (s * a) := by ring
        _ = 1 := by rw [hsa]; ring
    calc
      (s * s) * (a * a *
          D.K.ricci x (Curvature.vec2 (I := I) v v)) =
          ((s * s) * (a * a)) *
            D.K.ricci x (Curvature.vec2 (I := I) v v) := by ring
      _ = D.K.ricci x (Curvature.vec2 (I := I) v v) := by
        rw [hmul]
        ring
  have hleft : (s * s) * c = c * (G 0).inner x v v := by
    rw [hss]
    ring
  rwa [hcancel, hleft] at hmul

/-- Compactness of the initial unit tangent bundle gives a uniform positive
Ricci lower bound on unit vectors.  The remaining geometry outside this file is
to supply the compactness and continuity inputs for the canonical unit tangent
bundle. -/
theorem unitLower_raw
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D)
    (hcompact : IsCompact (Set.univ : Set (UnitTangent (I := I) (M := M) (G 0))))
    (hcont : Continuous (unitRicEval (I := I) (M := M) D)) :
    ∃ c : Real, UnitRicciLower (I := I) (M := M) D c := by
  classical
  by_cases hne : (Set.univ : Set (UnitTangent (I := I) (M := M) (G 0))).Nonempty
  · obtain ⟨p0, _hp0, hmin⟩ :=
      hcompact.exists_isMinOn hne hcont.continuousOn
    let c : Real :=
      unitRicEval (I := I) (M := M) D p0
    have hc : 0 < c := by
      let x0 := UnitTangent.base (I := I) (M := M) p0
      let v0 := UnitTangent.vec (I := I) (M := M) p0
      have hunit0 : (G 0).inner x0 v0 v0 = 1 := by
        simp [x0, v0, UnitTangent.unit]
      have hv0 : v0 ≠ 0 := by
        intro hz
        have hbad : (0 : Real) = 1 := by
          simp [hz] at hunit0
        norm_num at hbad
      exact hpos x0 v0 hv0
    refine ⟨c, hc, ?_⟩
    intro x v hunit
    let p : UnitTangent (I := I) (M := M) (G 0) :=
      ⟨(⟨x, v⟩ : TangentBundle I M), hunit⟩
    exact (isMinOn_iff.mp hmin) p (Set.mem_univ p)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x v hunit
    exfalso
    exact hne ⟨⟨(⟨x, v⟩ : TangentBundle I M), hunit⟩, Set.mem_univ _⟩

/-- Compactness of the unit tangent bundle of a compact base.  This is the
remaining vector-bundle topology producer: prove it by local trivializations,
compact model spheres, and a finite subcover of the base. -/
theorem unitTan_compact
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    IsCompact (Set.univ : Set (UnitTangent (I := I) (M := M) g)) := by
  exact metricUnit_compact (I := I) (M := M) g

/-- Continuity of the Ricci quadratic form on the initial unit tangent bundle. -/
theorem unitRic_cont
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric) :
    Continuous (unitRicEval (I := I) (M := M) D) := by
  refine (metricUnit_quadCont (I := I) (M := M) (G 0) D.K.ricci).congr ?_
  intro p
  dsimp [unitRicEval, quad02, UnitTangent.base, UnitTangent.vec,
    MetricUnitTangent.base, MetricUnitTangent.vec]
  congr 1
  funext i
  fin_cases i <;> simp [Curvature.vec2]

/-- Unit tangent compactness and unit Ricci positivity produce a uniform
positive Ricci lower bound on unit vectors. -/
theorem unitLower_pos
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D) :
    ∃ c : Real, UnitRicciLower (I := I) (M := M) D c := by
  exact unitLower_raw (I := I) (M := M) D hpos
    (unitTan_compact (I := I) (M := M) (G 0))
    (unitRic_cont (I := I) (M := M) D)

/-- Unit tangent compactness and unit Ricci positivity produce a constant
metric/Ricci lower-bound function. -/
theorem metricMin_pos
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D) :
    ∃ ricMin : M -> Real,
      MetricRicciMin (I := I) (M := M) D ricMin := by
  rcases unitLower_pos (I := I) (M := M) D hpos with ⟨c, hc⟩
  exact ⟨fun _ : M => c, metricMin_unit (I := I) (M := M) D hc⟩

/-- Canonical Ricci positivity implies the legacy pointwise positivity
predicate for the supplied Ricci family. -/
theorem ricciPos_metric
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D) :
    RicciPosInit (I := I) (M := M) Ric := by
  intro x v hv
  rw [D.ricci_eq x v v]
  exact hpos x v hv

/-- A canonical initial Ricci lower-bound function is the older `RicMinData`
adapter for the supplied Ricci family. -/
theorem ricMin_of_metric
    [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {ricMin : M -> Real}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hmin : MetricRicciMin (I := I) (M := M) D ricMin) :
    RicMinData (I := I) (M := M) G Ric ricMin := by
  rcases hmin with ⟨hcont, hpos, hlower⟩
  refine ⟨hcont, hpos, ?_⟩
  intro x v
  rw [D.ricci_eq x v v]
  exact hlower x v

/-- Compactness-facing selector predicate: strict initial Ricci positivity
supplies the uniform bounds used to select the pinching constant. -/
def BoundsOfPosRic
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) : Prop :=
  RicciPosInit (I := I) (M := M) Ric ->
    InitBounds (I := I) (M := M) G Ric scalar

/-- A realized Ricci-minimum lower bound implies strict initial Ricci
positivity. -/
theorem ricPos_ricMin
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {ricMin : M -> Real}
    (hmin : RicMinData (I := I) (M := M) G Ric ricMin) :
    RicciPosInit (I := I) (M := M) Ric := by
  rcases hmin with ⟨_hcont, hpos, hlower⟩
  intro x v hv
  have hgpos : 0 < (G 0).inner x v v := (G 0).pos x v hv
  exact lt_of_lt_of_le (mul_pos (hpos x) hgpos) (hlower x v)

/-- A continuous scalar curvature has a positive upper bound on compact
initial space. -/
theorem scalarUpper_cont
    [CompactSpace M] [Nonempty M]
    {scalar : Real -> M -> Real}
    (hcont : Continuous (fun x : M => scalar 0 x)) :
    ∃ C : Real, 0 < C ∧ ∀ x, scalar 0 x <= C := by
  have hcompact : IsCompact (Set.univ : Set M) := isCompact_univ
  have hnonempty : (Set.univ : Set M).Nonempty := Set.univ_nonempty
  obtain ⟨x0, _hx0, hmax⟩ :=
    hcompact.exists_isMaxOn hnonempty hcont.continuousOn
  refine ⟨max 1 (scalar 0 x0), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left 1 (scalar 0 x0))
  · intro x
    exact le_trans (hmax (by simp : x ∈ (Set.univ : Set M)))
      (le_max_right 1 (scalar 0 x0))

/-- A continuous positive realized Ricci-minimum function supplies the uniform
initial lower Ricci bound once the scalar upper bound is known. -/
theorem bounds_ricMin
    [CompactSpace M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    (hmin : RicMinData (I := I) (M := M) G Ric ricMin)
    (hscalar : ∃ C : Real, 0 < C ∧ ∀ x, scalar 0 x <= C) :
    InitBounds (I := I) (M := M) G Ric scalar := by
  rcases hmin with ⟨hcont, hpos, hRicLower⟩
  rcases hscalar with ⟨C, hC, hScalarUpper⟩
  have hcompact : IsCompact (Set.univ : Set M) := isCompact_univ
  have hnonempty : (Set.univ : Set M).Nonempty := Set.univ_nonempty
  obtain ⟨x0, _hx0, hminOn⟩ :=
    hcompact.exists_isMinOn hnonempty hcont.continuousOn
  let c : Real := ricMin x0
  have hc : 0 < c := by
    dsimp [c]
    exact hpos x0
  have hc_le : ∀ x : M, c <= ricMin x := by
    intro x
    exact hminOn (by simp : x ∈ (Set.univ : Set M))
  refine ⟨c, C, hc, hC, ?_, hScalarUpper⟩
  intro x v
  have hg_nonneg : 0 <= (G 0).inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact le_of_lt ((G 0).pos x v hv)
  exact le_trans (mul_le_mul_of_nonneg_right (hc_le x) hg_nonneg)
    (hRicLower x v)

/-- The base-function selector also supplies the older compactness-facing
selector predicate. -/
theorem boundsPos_ricMin
    [CompactSpace M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    (hmin : RicMinData (I := I) (M := M) G Ric ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x)) :
    BoundsOfPosRic (I := I) (M := M) G Ric scalar := by
  intro _hpos
  exact bounds_ricMin (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (ricMin := ricMin) hmin
    (scalarUpper_cont (M := M) hscalar)

/-- Uniform initial lower Ricci and upper scalar bounds select a strict
initial pinching constant `0 < delta < 1/3`. -/
theorem pinchInitLt_bounds
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (hbounds : InitBounds (I := I) (M := M) G Ric scalar) :
    PinchInitLt (I := I) (M := M) G Ric scalar := by
  rcases hbounds with ⟨c, C, hc, hC, hRicLower, hScalarUpper⟩
  let delta : Real := min ((1 : Real) / 6) (c / C)
  have hsix_pos : 0 < (1 : Real) / 6 := by norm_num
  have hdiv_pos : 0 < c / C := div_pos hc hC
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    exact lt_min hsix_pos hdiv_pos
  have hdelta_le_six : delta <= (1 : Real) / 6 := by
    dsimp [delta]
    exact min_le_left _ _
  have hdelta_lt_third : delta < (1 : Real) / 3 := by
    nlinarith
  have hdelta_nonneg : 0 <= delta := le_of_lt hdelta_pos
  have hdelta_le_div : delta <= c / C := by
    dsimp [delta]
    exact min_le_right _ _
  have hdeltaC_le_c : delta * C <= c := by
    have hmul := mul_le_mul_of_nonneg_right hdelta_le_div (le_of_lt hC)
    have hcancel : c / C * C = c := div_mul_cancel₀ c (ne_of_gt hC)
    nlinarith
  refine ⟨delta, hdelta_pos, hdelta_lt_third, ?_⟩
  intro x v
  have hg_nonneg : 0 <= (G 0).inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact le_of_lt ((G 0).pos x v hv)
  have hscalar_le : delta * scalar 0 x <= delta * C :=
    mul_le_mul_of_nonneg_left (hScalarUpper x) hdelta_nonneg
  have hscaled_le :
      delta * scalar 0 x * (G 0).inner x v v <= c * (G 0).inner x v v := by
    calc
      delta * scalar 0 x * (G 0).inner x v v
          = (delta * scalar 0 x) * (G 0).inner x v v := by ring
      _ <= (delta * C) * (G 0).inner x v v :=
          mul_le_mul_of_nonneg_right hscalar_le hg_nonneg
      _ <= c * (G 0).inner x v v :=
          mul_le_mul_of_nonneg_right hdeltaC_le_c hg_nonneg
  have hpinch_le : delta * scalar 0 x * (G 0).inner x v v <= Ric 0 x v v :=
    le_trans hscaled_le (hRicLower x v)
  simpa [pinchTensor, sub_nonneg] using hpinch_le

/-- Uniform initial lower Ricci and upper scalar bounds select an initial
pinching constant. -/
theorem pinchInit_of_bounds
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (hbounds : InitBounds (I := I) (M := M) G Ric scalar) :
    PinchInit (I := I) (M := M) G Ric scalar := by
  exact pinchInit_of_lt (I := I) (M := M)
    (pinchInitLt_bounds (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) hbounds)

/-- Strict initial Ricci positivity gives strict initial pinching once the
compactness selector has produced the uniform initial bounds. -/
theorem pinchInitLt_of_pos
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (hpos : RicciPosInit (I := I) (M := M) Ric)
    (hbounds : BoundsOfPosRic (I := I) (M := M) G Ric scalar) :
    PinchInitLt (I := I) (M := M) G Ric scalar := by
  exact pinchInitLt_bounds (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (hbounds hpos)

/-- Strict initial Ricci positivity gives initial pinching once the compactness
selector has produced the uniform initial bounds. -/
theorem pinchInit_of_pos
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (hpos : RicciPosInit (I := I) (M := M) Ric)
    (hbounds : BoundsOfPosRic (I := I) (M := M) G Ric scalar) :
    PinchInit (I := I) (M := M) G Ric scalar := by
  exact pinchInit_of_lt (I := I) (M := M)
    (pinchInitLt_of_pos (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) hpos hbounds)

/-- A realized Ricci-minimum lower bound and scalar continuity select a strict
initial pinching constant. -/
theorem pinchInitLt_ricMin
    [CompactSpace M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    (hmin : RicMinData (I := I) (M := M) G Ric ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x)) :
    PinchInitLt (I := I) (M := M) G Ric scalar :=
  pinchInitLt_bounds (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar)
    (bounds_ricMin (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) (ricMin := ricMin) hmin
      (scalarUpper_cont (M := M) hscalar))

/-- A realized Ricci-minimum lower bound and scalar continuity select the
initial pinching constant. -/
theorem pinchInit_ricMin
    [CompactSpace M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    (hmin : RicMinData (I := I) (M := M) G Ric ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x)) :
    PinchInit (I := I) (M := M) G Ric scalar :=
  pinchInit_of_lt (I := I) (M := M)
    (pinchInitLt_ricMin (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) (ricMin := ricMin) hmin hscalar)

/-- Metric/Ricci-native initial pinching selector.  The remaining geometric
producer is now the canonical lower-bound function for the initial Ricci tensor,
not a lower-bound function for an arbitrary supplied tensor family. -/
theorem pinchInitLt_metric
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hmin : MetricRicciMin (I := I) (M := M) D ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x)) :
    PinchInitLt (I := I) (M := M) G Ric scalar :=
  pinchInitLt_ricMin (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (ricMin := ricMin)
    (ricMin_of_metric (I := I) (M := M) D hmin) hscalar

/-- Metric/Ricci-native initial pinching selector.  The remaining geometric
producer is now the canonical lower-bound function for the initial Ricci tensor,
not a lower-bound function for an arbitrary supplied tensor family. -/
theorem pinchInit_metric
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hmin : MetricRicciMin (I := I) (M := M) D ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x)) :
    PinchInit (I := I) (M := M) G Ric scalar :=
  pinchInit_of_lt (I := I) (M := M)
    (pinchInitLt_metric (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) (ricMin := ricMin) D hmin hscalar)

/-- Metric/Ricci-native initial pinching selector from the unit tangent compact
minimum route. -/
theorem pinchInitLt_pos
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D)
    (hscalar : Continuous (fun x : M => scalar 0 x)) :
    PinchInitLt (I := I) (M := M) G Ric scalar := by
  rcases metricMin_pos (I := I) (M := M) D hpos with ⟨ricMin, hmin⟩
  exact pinchInitLt_metric (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (ricMin := ricMin) D hmin hscalar

/-- Metric/Ricci-native initial pinching selector from the unit tangent compact
minimum route. -/
theorem pinchInit_pos
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D)
    (hscalar : Continuous (fun x : M => scalar 0 x)) :
    PinchInit (I := I) (M := M) G Ric scalar := by
  exact pinchInit_of_lt (I := I) (M := M)
    (pinchInitLt_pos (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) D hpos hscalar)

/-- Preserved pinching conclusion for a fixed `delta`. -/
def PinchPres
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) (T delta : Real) : Prop :=
  TwoTensorFamilyNonnegativeOn (I := I) (M := M)
    (pinchTensor (I := I) (M := M) G Ric scalar delta) (Set.Icc 0 T)

/-! ### Ricci-flow producers for theorem 7.5 input packages -/

/-- The all-time `C^1` regularity of the Levi-Civita connection in a
Ricci-flow solution candidate. -/
theorem ricciCov1
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M) (S.base.connection t)
      (1 : WithTop ℕ∞) := by
  simpa [SolutionFamily.connection] using
    (LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) (S.base.metric t))

/-- The all-time smoothness of the Levi-Civita connection in a Ricci-flow
solution candidate. -/
theorem ricciCovInf
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M) (S.base.connection t)
      (∞ : WithTop ℕ∞) := by
  simpa [SolutionFamily.connection, metricCov] using
    metricCov_smooth (I := I) (M := M) (S.base.metric t)

/-- Metric compatibility of the canonical Levi-Civita connection in a
Ricci-flow solution candidate. -/
theorem ricciMetricComp
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    RicciFlower.Connection.IsMetricCompatible
      (I := I) (S.base.connection t) (S.base.metric t) := by
  simpa [SolutionFamily.connection] using
    (LeviCivita.leviCivitaConnectionOfMetric_isMetricCompatible
      (I := I) (S.base.metric t))

/-- Canonical first and second spatial Ricci derivatives for a solution
candidate at one time. -/
noncomputable def ricciDerivsWMP
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    CanonicalSpatialDerivs0S (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) (S.base.connection t) (S.ricci t) :=
  CanonicalSpatialDerivs0S.of_smooth_connection
    (E := E) (H := H) (I := I) (M := M)
    (S.base.connection t) (ricciCovInf (I := I) S t) (S.ricci t)

/-- Canonical smooth section representing `∇ Ric` for theorem 7.5 inputs. -/
noncomputable def ricciNablaWMP
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    TensorNabla1SecFamily (I := I) (M := M) :=
  fun t => (ricciDerivsWMP (I := I) S t).nablaA

/-- Canonical smooth section representing `∇² Ric` for theorem 7.5 inputs. -/
noncomputable def ricciNabla2WMP
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    TensorNabla2SecFamily (I := I) (M := M) :=
  fun t => (ricciDerivsWMP (I := I) S t).nabla2A

/-- The canonical Ricci derivative sections realize the first and second total
covariant derivatives required by theorem 7.5. -/
theorem ricciSpatialWMP
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    TensorSpatialDerivs (I := I) (M := M)
      (fun t : Real => S.base.connection t) S.ricci
      (ricciNablaWMP (I := I) S) (ricciNabla2WMP (I := I) S) := by
  constructor
  · intro t
    simpa [ricciNablaWMP, ricciDerivsWMP] using
      (ricciDerivsWMP (I := I) S t).first
  · intro t
    simpa [ricciNablaWMP, ricciNabla2WMP, ricciDerivsWMP] using
      (ricciDerivsWMP (I := I) S t).second

/-- The canonical smooth section for the shifted pinching tensor
`Ric - delta R g`. -/
noncomputable def pinchSec
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta : Real) :
    TwoTensorSecFamily (I := I) (M := M) :=
  fun t =>
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2
    let hscalar :
        ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (fun x : M => delta * S.scalar t x) := by
      have hR :
          ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
            (fun x : M => S.scalar t x) := by
        simpa [SolutionOn.scalar, SolutionFamily.scalar] using
          metricScalar_smooth (I := I) (M := M) (S.base.metric t)
      simpa only [Pi.mul_apply] using (contMDiff_const.mul hR)
    let Ric : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2 := S.ricci t
    Ric + (-1 : Real) •
      tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
        (fun x : M => delta * S.scalar t x) hscalar
        (metricTensorField (I := I) (S.base.metric t))

@[simp]
theorem pinchSec_eq
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta : Real) :
    twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta) =
      pinchTensor (I := I) (M := M) (fun t : Real => S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar delta := by
  funext t x v w
  simp only [pinchSec, pinchTensor, twoTensorSecToFamily,
    ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.coe_smul,
    Pi.smul_apply, tensor0SField_smulByFun_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul]
  change
    ((S.ricci t) x) (vec2 (I := I) v w) +
        (-1 : Real) * (delta * S.scalar t x *
          (metricTensorField (I := I) (S.base.metric t) x)
            (vec2 (I := I) v w)) =
      ((S.ricci t) x) (vec2 (I := I) v w) -
        delta * S.scalar t x * (S.base.metric t).inner x v w
  rw [metricTensorField_apply]
  have h0 : vec2 (I := I) v w 0 = v := by
    unfold vec2 Curvature.vec2
    simp
  have h1 : vec2 (I := I) v w 1 = w := by
    unfold vec2 Curvature.vec2
    norm_num
  rw [h0, h1]
  ring

/-- Pointwise symmetry of the canonical metric Ricci tensor. -/
theorem ricciAt_symm
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) :
    RicciFlower.DimensionThree.RicciSymAt (I := I) (S.ricciAt t x) := by
  classical
  let basis : Module.Basis (Coordinates.CoordinateIdx (𝕜 := Real) E)
      Real (TangentSpace I x) :=
    Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv :
      Coordinates.CoordinateIdx (𝕜 := Real) E ->
        Coordinates.CoordinateIdx (𝕜 := Real) E -> Real := fun k l =>
    Coordinates.inverseMetricFlatModelInChart_component
      (I := I) (S.base.metric t) x k l (extChartAt I x x)
  have hinv :
      MetricInverseInBasis (I := I) (S.base.metric t) x basis gInv := by
    simpa [basis, gInv] using
      Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) (S.base.metric t) x
  exact RicciFlower.DimensionThree.ricciSym_of_basis
    (I := I) basis (S.ricciAt t x)
    (fun i j => by
      simpa [SolutionOn.ricciAt, SolutionFamily.ricciAt, basis, gInv] using
        Curvature.metricRicciSymm (I := I) (M := M) (S.base.metric t)
          basis gInv hinv i j)

/-- Symmetry of the canonical Ricci section family. -/
theorem ricciSec_symm
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (U : Set Real) :
    TwoTensorFamilySymmetricOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) U := by
  intro t _ht x v w
  simpa [twoTensorSecToFamily, SolutionOn.ricci, SolutionFamily.ricci,
    SolutionOn.ricciAt, SolutionFamily.ricciAt] using
    ricciAt_symm (I := I) S t x v w

/-- Symmetry of the shifted pinching section `Ric - delta R g`. -/
theorem pinchSec_symm
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta : Real) (U : Set Real) :
    TwoTensorFamilySymmetricOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta)) U := by
  intro t _ht x v w
  rw [pinchSec_eq (I := I) S delta]
  simp only [pinchTensor]
  have hRic := ricciAt_symm (I := I) S t x v w
  have hg := (S.base.metric t).symm x v w
  simpa [twoTensorSecToFamily, SolutionOn.ricci, SolutionFamily.ricci,
    SolutionOn.ricciAt, SolutionFamily.ricciAt, hg] using congrArg
      (fun z => z - delta * S.scalar t x * (S.base.metric t).inner x w v)
      hRic

/-- Canonical first and second spatial derivatives of the shifted pinching
section for a solution candidate at one time. -/
noncomputable def pinchDerivsWMP
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta : Real) (t : Real) :
    CanonicalSpatialDerivs0S (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) (S.base.connection t) ((pinchSec (I := I) S delta) t) :=
  CanonicalSpatialDerivs0S.of_smooth_connection
    (E := E) (H := H) (I := I) (M := M)
    (S.base.connection t) (ricciCovInf (I := I) S t)
    ((pinchSec (I := I) S delta) t)

/-- Canonical smooth section representing `∇ (Ric - delta R g)` for theorem
7.5 inputs. -/
noncomputable def pinchNablaWMP
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta : Real) :
    TensorNabla1SecFamily (I := I) (M := M) :=
  fun t => (pinchDerivsWMP (I := I) S delta t).nablaA

/-- Canonical smooth section representing `∇² (Ric - delta R g)` for theorem
7.5 inputs. -/
noncomputable def pinchNabla2WMP
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta : Real) :
    TensorNabla2SecFamily (I := I) (M := M) :=
  fun t => (pinchDerivsWMP (I := I) S delta t).nabla2A

/-- The canonical shifted-pinching derivative sections realize the first and
second total covariant derivatives required by theorem 7.5. -/
theorem pinchSpatialWMP
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (delta : Real) :
    TensorSpatialDerivs (I := I) (M := M)
      (fun t : Real => S.base.connection t) (pinchSec (I := I) S delta)
      (pinchNablaWMP (I := I) S delta) (pinchNabla2WMP (I := I) S delta) := by
  constructor
  · intro t
    simpa [pinchNablaWMP, pinchDerivsWMP] using
      (pinchDerivsWMP (I := I) S delta t).first
  · intro t
    simpa [pinchNablaWMP, pinchNabla2WMP, pinchDerivsWMP] using
      (pinchDerivsWMP (I := I) S delta t).second

/-- The shifted pinching section is jointly continuous over the solution
interval when the Ricci-flow solution package supplies scalar, Ricci, and
metric total-space continuity. -/
theorem pinchSecFamilyContinuousOnSet
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (delta : Real) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
      (fun t x => (pinchSec (I := I) S delta) t x) := by
  have hmap :
      Continuous (fun q : {t : Real // t ∈ D.carrier} × M =>
        ((q.1.1 : Real), q.2)) := by
    exact (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hcoef :
      Continuous (fun q : {t : Real // t ∈ D.carrier} × M =>
        delta * S.scalar q.1.1 q.2) := by
    have hscalarSub :
        Continuous (fun q : {t : Real // t ∈ D.carrier} × M =>
          S.scalar q.1.1 q.2) := by
      rw [continuous_iff_continuousAt]
      intro q
      exact ContinuousAt.comp
        (x := q)
        (f := fun q : {t : Real // t ∈ D.carrier} × M =>
          ((q.1.1 : Real), q.2))
        (g := fun p : Real × M => S.scalar p.1 p.2)
        (hS.scalarCont (q.1.1, q.2)) hmap.continuousAt
    exact continuous_const.mul hscalarSub
  have hmetric :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x => metricTensorField (I := I) (S.base.metric t) x) := by
    simpa [SolutionOn.family] using hS.smoothMetric.metricTensor_cont
  have hscaled :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x =>
          (delta * S.scalar t x) •
            metricTensorField (I := I) (S.base.metric t) x) :=
    Tensor0SFamilyContinuousOnSet.smul (I := I) (M := M)
      (s := 2) (K := D.carrier)
      (f := fun t x => delta * S.scalar t x)
      (A := fun t x => metricTensorField (I := I) (S.base.metric t) x)
      hcoef hmetric
  have hneg :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x =>
          (-1 : Real) •
            ((delta * S.scalar t x) •
              metricTensorField (I := I) (S.base.metric t) x)) :=
    Tensor0SFamilyContinuousOnSet.const_smul (I := I) (M := M)
      (s := 2) (K := D.carrier)
      (A := fun t x =>
        (delta * S.scalar t x) •
          metricTensorField (I := I) (S.base.metric t) x)
      (-1 : Real) hscaled
  have hsum :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
        (fun t x =>
          S.ricci t x +
            (-1 : Real) •
              ((delta * S.scalar t x) •
                metricTensorField (I := I) (S.base.metric t) x)) :=
    Tensor0SFamilyContinuousOnSet.add (I := I) (M := M)
      (s := 2) (K := D.carrier)
      (A := fun t x => S.ricci t x)
      (B := fun t x =>
        (-1 : Real) •
          ((delta * S.scalar t x) •
            metricTensorField (I := I) (S.base.metric t) x))
      hS.ricciCont hneg
  simpa [pinchSec, tensor0SField_smulByFun_apply] using hsum

/-- Tangent-bundle form of shifted pinching section continuity on any time set
inside the solution interval. -/
theorem pinchSec_tangentBundle_cont
    {D : Realized.RealTimeInterval} {K : Set Real}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (delta : Real)
    (hK : K ⊆ D.carrier) :
    Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
        ((pinchSec (I := I) S delta) q.1.1 q.2.proj)) := by
  exact Tensor0SFamilyContinuousOnSet.tangentBundle (I := I) (M := M)
    (Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
      (pinchSecFamilyContinuousOnSet (I := I) S hS delta) hK)

/-- Quadratic-evaluation continuity for the shifted pinching section on any
time set inside the solution interval. -/
theorem pinchSec_tensorQuadCont
    {D : Realized.RealTimeInterval} {K : Set Real}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (delta : Real)
    (hK : K ⊆ D.carrier) :
    Continuous
      (tensorSecBundleQuad (I := I) (M := M)
        (pinchSec (I := I) S delta) K) :=
  tensorQuadCont (I := I) (M := M) (pinchSec (I := I) S delta) K
    (pinchSec_tangentBundle_cont (I := I) S hS delta hK)

/-- Core theorem-7.5 section regularity for the shifted pinching section from
smooth Ricci-flow data, once the analytic barrier regularity field is supplied.

This proves the compactness, metric/tensor total-space continuity, fixed-vector
barrier continuity, and symmetry parts of the core package.  It intentionally
does not prove `TensorBarrierRegularityOn.smallBarrierLip`; that remains the
separate analytic reaction-control frontier. -/
theorem pinchSecCore
    {D : Realized.RealTimeInterval}
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T delta : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    (hbar : TensorBarrierRegularityOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      X N T) :
    TensorWMPSectionCore (I := I) (M := M)
      (fun t : Real => S.base.metric t) (pinchSec (I := I) S delta) X N T := by
  exact TensorWMPSectionCore.ofSmoothMetric (I := I) (M := M)
    (G := S.family) (S := pinchSec (I := I) S delta)
    (X := X) (N := N) (T := T)
    hTsub hS.smoothMetric
    (pinchSec_symm (I := I) S delta (Set.Icc 0 T))
    (by simpa [SolutionOn.family] using hbar)
    (fun d t0 _hd hsub =>
      pinchSec_tangentBundle_cont (I := I) S hS delta
        (fun t ht => hTsub (hsub ht)))
    (fun epsilon d t0 _hepsilon _hd hsub x v =>
      hbar.barrier_eval_continuous epsilon d t0 hsub x v v)

/-- Section 9 Ricci-flow data needed to feed theorem 7.5 for the canonical
Ricci tensor.  The connection, metric compatibility, and spatial derivative
realization are produced canonically from the solution candidate; the remaining
fields are the genuine WMP application inputs. -/
structure RicciWMPData
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (T : Real) : Type _ where
  X : TimeDependentVectorField (I := I) (M := M)
  N : TwoTensorReaction (I := I) (M := M)
  reg :
    TensorWMPSectionCore (I := I) (M := M)
      (fun t : Real => S.base.metric t) S.ricci X N T
  parabolic :
    TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) X N
      (fun t x => ricciNabla2WMP (I := I) S t x)
      (fun t x => ricciNablaWMP (I := I) S t x) T
  null :
    TensorNullEigenvectorCondition (I := I) (M := M)
      (fun t : Real => S.base.metric t) N (Set.Icc 0 T)
  initial :
    TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) 0

namespace RicciWMPData

/-- Build the theorem-7.5 input package for the canonical Ricci section of a
Ricci-flow solution candidate. -/
def toInput
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    {S : SolutionOn (I := I) (M := M) D} {T : Real}
    (data : RicciWMPData (I := I) (M := M) S T) (hT : 0 <= T) :
    TensorWMPInput (I := I) (M := M)
      (fun t : Real => S.base.metric t) S.ricci data.X data.N
      (fun t : Real => S.base.connection t)
      (ricciNablaWMP (I := I) S) (ricciNabla2WMP (I := I) S) T where
  hT := hT
  reg := data.reg
  parabolic := data.parabolic
  null := data.null
  initial := data.initial
  hcov1 := fun t => ricciCov1 (I := I) S t
  hcovInf := fun t => ricciCovInf (I := I) S t
  hmc := fun t => ricciMetricComp (I := I) S t
  spatial := ricciSpatialWMP (I := I) S

end RicciWMPData

/-- Tensor-WMP data for the shifted tensor `Ric - delta R g`. -/
structure PinchWMPData
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : TwoTensorFamily (I := I) (M := M))
    (scalar : Real -> M -> Real) (T delta : Real) : Type _ where
  S : TwoTensorSecFamily (I := I) (M := M)
  X : TimeDependentVectorField (I := I) (M := M)
  N : TwoTensorReaction (I := I) (M := M)
  cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)
  nablaS : TensorNabla1SecFamily (I := I) (M := M)
  nabla2S : TensorNabla2SecFamily (I := I) (M := M)
  section_eq :
    twoTensorSecToFamily (I := I) (M := M) S =
      pinchTensor (I := I) (M := M) G Ric scalar delta
  reg :
    TensorWMPSectionCore (I := I) (M := M) G S X N T
  parabolic :
    TensorParabolicSupersolutionWithDriftOn (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) X N
      (fun t x => nabla2S t x) (fun t x => nablaS t x) T
  null :
    TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T)
  hcov1 :
    forall t : Real,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (cov t) (1 : WithTop ℕ∞)
  hcovInf :
    forall t : Real,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (cov t) (∞ : WithTop ℕ∞)
  hmc :
    forall t : Real,
      RicciFlower.Connection.IsMetricCompatible (I := I) (cov t) (G t)
  spatial : TensorSpatialDerivs (I := I) (M := M) cov S nablaS nabla2S

namespace PinchWMPData

/-- Build the theorem-7.5 input package from the Section 9 pinching data. -/
def toInput
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T delta : Real}
    (data : PinchWMPData (I := I) (M := M) G Ric scalar T delta)
    (hT : 0 <= T)
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (pinchTensor (I := I) (M := M) G Ric scalar delta) 0) :
    TensorWMPInput (I := I) (M := M)
      G data.S data.X data.N data.cov data.nablaS data.nabla2S T where
  hT := hT
  reg := data.reg
  parabolic := data.parabolic
  null := data.null
  initial := by
    simpa [data.section_eq] using hinit
  hcov1 := data.hcov1
  hcovInf := data.hcovInf
  hmc := data.hmc
  spatial := data.spatial

end PinchWMPData

/-- Canonical Ricci-flow pinching WMP data with the section, connection, and
spatial derivative fields produced from the solution candidate.  The remaining
fields are exactly the still-genuine WMP application frontiers:
section/barrier regularity, the parabolic inequality, and the reaction-wide
null-eigenvector condition. -/
structure PinchFlowWMPData
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (T delta : Real) : Type _ where
  X : TimeDependentVectorField (I := I) (M := M)
  N : TwoTensorReaction (I := I) (M := M)
  reg :
    TensorWMPSectionCore (I := I) (M := M)
      (fun t : Real => S.base.metric t) (pinchSec (I := I) S delta) X N T
  parabolic :
    TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      X N
      (fun t x => pinchNabla2WMP (I := I) S delta t x)
      (fun t x => pinchNablaWMP (I := I) S delta t x) T
  null :
    TensorNullEigenvectorCondition (I := I) (M := M)
      (fun t : Real => S.base.metric t) N (Set.Icc 0 T)

namespace PinchFlowWMPData

/-- Build the canonical shifted-pinching WMP data package once the genuine
application inputs have been supplied.  The core section regularity is produced
from smooth solution data by `pinchSecCore`; callers no longer need to assemble
the compactness and continuity fields manually. -/
def ofBarrier
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn (I := I) S)
    {T delta : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (hbar : TensorBarrierRegularityOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      X N T)
    (hparabolic :
      TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
        (fun t : Real => S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
        X N
        (fun t x => pinchNabla2WMP (I := I) S delta t x)
        (fun t x => pinchNablaWMP (I := I) S delta t x) T)
    (hnull :
      TensorNullEigenvectorCondition (I := I) (M := M)
        (fun t : Real => S.base.metric t) N (Set.Icc 0 T)) :
    PinchFlowWMPData (I := I) (M := M) S T delta where
  X := X
  N := N
  reg := pinchSecCore (I := I) S hS hTsub hbar
  parabolic := hparabolic
  null := hnull

/-- Build the canonical shifted-pinching WMP data using the natural symmetric
null-condition interface.  The legacy raw null condition is recovered by
symmetrizing the reaction input, so future reaction producers can work only on
symmetric first-null tensors. -/
def ofSymmNull
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn (I := I) S)
    {T delta : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (hbar : TensorBarrierRegularityOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
      X N T)
    (hparabolic :
      TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
        (fun t : Real => S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S delta))
        X N
        (fun t x => pinchNabla2WMP (I := I) S delta t x)
        (fun t x => pinchNablaWMP (I := I) S delta t x) T)
    (hdep :
      TensorReactionSymmInputOn (I := I) (M := M)
        (fun t : Real => S.base.metric t) N (Set.Icc 0 T))
    (hnull :
      TensorNullEigenvectorConditionSymm (I := I) (M := M)
        (fun t : Real => S.base.metric t) N (Set.Icc 0 T)) :
    PinchFlowWMPData (I := I) (M := M) S T delta :=
  ofBarrier (I := I) (M := M) hS hTsub X N hbar hparabolic
    (null_of_symm (I := I) (M := M) hdep hnull)

/-- Fill the old Section 9 pinching package from the canonical solution-level
pinching section and derivative producers. -/
def toPinchWMPData
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    {S : SolutionOn (I := I) (M := M) D} {T delta : Real}
    (data : PinchFlowWMPData (I := I) (M := M) S T delta) :
    PinchWMPData (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci)
      S.scalar T delta where
  S := pinchSec (I := I) S delta
  X := data.X
  N := data.N
  cov := fun t : Real => S.base.connection t
  nablaS := pinchNablaWMP (I := I) S delta
  nabla2S := pinchNabla2WMP (I := I) S delta
  section_eq := pinchSec_eq (I := I) S delta
  reg := data.reg
  parabolic := data.parabolic
  null := data.null
  hcov1 := fun t => ricciCov1 (I := I) S t
  hcovInf := fun t => ricciCovInf (I := I) S t
  hmc := fun t => ricciMetricComp (I := I) S t
  spatial := pinchSpatialWMP (I := I) S delta

end PinchFlowWMPData

/-- Lemma 9.1 as a raw compatibility consumer of Hamilton's tensor WMP. -/
theorem ricci_nonneg_wmp_raw
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Ric : TensorNabla2Family (I := I) (M := M)}
    {nablaRic : TensorNabla1Family (I := I) (M := M)}
    {T : Real}
    (hT : 0 <= T)
    (hreg : TensorWMPRegularityOn (I := I) (M := M) G Ric X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G Ric X N nabla2Ric nablaRic T)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T))
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) Ric 0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M) Ric (Set.Icc 0 T) := by
  exact hamilton_tensor_wmp (I := I) (M := M) (G := G) (S := Ric)
    (X := X) (N := N) (nabla2S := nabla2Ric) (nablaS := nablaRic)
    hT hreg hparabolic hnull hinit

/-- Lemma 9.1 as a section-backed consumer of theorem 7.5. -/
theorem ricci_nonneg_wmp
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {RicSec : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {nablaRic : TensorNabla1SecFamily (I := I) (M := M)}
    {nabla2Ric : TensorNabla2SecFamily (I := I) (M := M)}
    {T : Real}
    (hRic :
      twoTensorSecToFamily (I := I) (M := M) RicSec = Ric)
    (data : TensorWMPInput (I := I) (M := M)
      G RicSec X N cov nablaRic nabla2Ric T) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M) Ric (Set.Icc 0 T) := by
  have hsec :
      TwoTensorFamilyNonnegativeOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) RicSec) (Set.Icc 0 T) :=
    tensor_wmp (I := I) (M := M) data
  simpa [hRic] using hsec

/-- Lemma 9.1 for the canonical Ricci section of a Ricci-flow solution
candidate, with theorem-7.5 connection and spatial-derivative inputs produced
from the solution candidate. -/
theorem ricci_nonneg_sol
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    {T : Real}
    (hT : 0 <= T)
    (data : RicciWMPData (I := I) (M := M) S T) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) (Set.Icc 0 T) := by
  exact tensor_wmp (I := I) (M := M) (RicciWMPData.toInput
    (I := I) (M := M) data hT)

/-- Lemma 9.2 as a raw compatibility consumer of Hamilton's tensor WMP. -/
theorem ricci_pinch_wmp_raw
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {delta : Real}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {T : Real}
    (hT : 0 <= T)
    (_hdelta0 : 0 <= delta) (_hdelta13 : delta <= (1 : Real) / 3)
    (hreg : TensorWMPRegularityOn (I := I) (M := M) G
      (pinchTensor (I := I) (M := M) G Ric scalar delta) X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G
      (pinchTensor (I := I) (M := M) G Ric scalar delta) X N
      nabla2S nablaS T)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T))
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (pinchTensor (I := I) (M := M) G Ric scalar delta) 0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (pinchTensor (I := I) (M := M) G Ric scalar delta) (Set.Icc 0 T) := by
  exact hamilton_tensor_wmp (I := I) (M := M) (G := G)
    (S := pinchTensor (I := I) (M := M) G Ric scalar delta)
    (X := X) (N := N) (nabla2S := nabla2S) (nablaS := nablaS)
    hT hreg hparabolic hnull hinit

/-- Lemma 9.2 as a section-backed consumer of theorem 7.5. -/
theorem ricci_pinch_wmp
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {delta : Real}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {nablaS : TensorNabla1SecFamily (I := I) (M := M)}
    {nabla2S : TensorNabla2SecFamily (I := I) (M := M)}
    {T : Real}
    (_hdelta0 : 0 <= delta) (_hdelta13 : delta <= (1 : Real) / 3)
    (hS :
      twoTensorSecToFamily (I := I) (M := M) S =
        pinchTensor (I := I) (M := M) G Ric scalar delta)
    (data : TensorWMPInput (I := I) (M := M)
      G S X N cov nablaS nabla2S T) :
    PinchPres (I := I) (M := M) G Ric scalar T delta := by
  have hsec :
      TwoTensorFamilyNonnegativeOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T) :=
    tensor_wmp (I := I) (M := M) data
  simpa [PinchPres, hS] using hsec

namespace PinchWMPData

/-- Preserve a supplied Section 9 pinching package through theorem 7.5. -/
theorem preserve
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T delta : Real}
    (data : PinchWMPData (I := I) (M := M) G Ric scalar T delta)
    (hT : 0 <= T)
    (hdelta0 : 0 <= delta) (hdelta13 : delta <= (1 : Real) / 3)
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (pinchTensor (I := I) (M := M) G Ric scalar delta) 0) :
    PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact ricci_pinch_wmp (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (delta := delta) (S := data.S) (X := data.X)
    (N := data.N) (cov := data.cov) (nablaS := data.nablaS)
    (nabla2S := data.nabla2S) (T := T)
    hdelta0 hdelta13 data.section_eq (data.toInput hT hinit)

end PinchWMPData

namespace PinchFlowWMPData

/-- Preserve the canonical shifted pinching section through theorem 7.5 once
the remaining WMP application data have been proved for that canonical
section. -/
theorem preserve
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    {T delta : Real}
    (data : PinchFlowWMPData (I := I) (M := M) S T delta)
    (hT : 0 <= T)
    (hdelta0 : 0 <= delta) (hdelta13 : delta <= (1 : Real) / 3)
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (pinchTensor (I := I) (M := M) (fun t : Real => S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar delta) 0) :
    PinchPres (I := I) (M := M) (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) S.ricci) S.scalar T delta := by
  exact (data.toPinchWMPData (I := I) (M := M)).preserve
    (I := I) (M := M) hT hdelta0 hdelta13 hinit

end PinchFlowWMPData

/-- Corollary 9.3 setup from an already selected initial pinching constant. -/
theorem pinch_init_wmp
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (hinit : PinchInit (I := I) (M := M) G Ric scalar)
    (hdata :
      ∀ delta : Real, 0 < delta -> delta <= (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta <= (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  rcases hinit with ⟨delta, hdelta0, hdelta13, hpinch0⟩
  let data := hdata delta hdelta0 hdelta13
  refine ⟨delta, hdelta0, hdelta13, ?_⟩
  exact data.preserve (I := I) (M := M) hT
    (le_of_lt hdelta0) hdelta13 hpinch0

/-- Corollary 9.3 setup from a strict selected initial pinching constant. -/
theorem pinch_init_wmp_lt
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (hinit : PinchInitLt (I := I) (M := M) G Ric scalar)
    (hdata :
      ∀ delta : Real, 0 < delta -> delta < (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta < (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  rcases hinit with ⟨delta, hdelta0, hdelta13, hpinch0⟩
  let data := hdata delta hdelta0 hdelta13
  refine ⟨delta, hdelta0, hdelta13, ?_⟩
  exact data.preserve (I := I) (M := M) hT
    (le_of_lt hdelta0) (le_of_lt hdelta13) hpinch0

/-- Corollary 9.3 conditional form: strict initial Ricci positivity supplies a
pinching constant, and Lemma 9.2 preserves it. -/
theorem strict_pinch_wmp
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (hpos : RicciPosInit (I := I) (M := M) Ric)
    (hselect : BoundsOfPosRic (I := I) (M := M) G Ric scalar)
    (hdata :
      ∀ delta : Real, 0 < delta -> delta <= (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta <= (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInit_of_pos (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) hpos hselect)
    hdata

/-- Strict-`delta` Corollary 9.3 conditional form: strict initial Ricci
positivity supplies `0 < delta < 1/3`, and Lemma 9.2 preserves it. -/
theorem strict_pinch_wmp_lt
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (hpos : RicciPosInit (I := I) (M := M) Ric)
    (hselect : BoundsOfPosRic (I := I) (M := M) G Ric scalar)
    (hdata :
      ∀ delta : Real, 0 < delta -> delta < (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta < (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp_lt (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInitLt_of_pos (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) hpos hselect)
    hdata

/-- Corollary 9.3 conditional form using a realized continuous base
Ricci-minimum function instead of a raw compactness selector. -/
theorem strict_pinch_min
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [CompactSpace M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (hmin : RicMinData (I := I) (M := M) G Ric ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x))
    (hdata :
      ∀ delta : Real, 0 < delta -> delta <= (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta <= (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInit_ricMin (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) (ricMin := ricMin) hmin hscalar)
    hdata

/-- Strict-`delta` version using a realized continuous base Ricci-minimum
function instead of a raw compactness selector. -/
theorem strict_pinch_min_lt
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [CompactSpace M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (hmin : RicMinData (I := I) (M := M) G Ric ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x))
    (hdata :
      ∀ delta : Real, 0 < delta -> delta < (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta < (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp_lt (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInitLt_ricMin (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) (ricMin := ricMin) hmin hscalar)
    hdata

/-- Corollary 9.3 conditional form with the initial Ricci tensor realized from
the initial metric. -/
theorem strict_pinch_metric
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hmin : MetricRicciMin (I := I) (M := M) D ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x))
    (hdata :
      ∀ delta : Real, 0 < delta -> delta <= (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta <= (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInit_metric (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) (ricMin := ricMin) D hmin hscalar)
    hdata

/-- Strict-`delta` version with the initial Ricci tensor realized from the
initial metric. -/
theorem strict_pinch_metric_lt
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {ricMin : M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hmin : MetricRicciMin (I := I) (M := M) D ricMin)
    (hscalar : Continuous (fun x : M => scalar 0 x))
    (hdata :
      ∀ delta : Real, 0 < delta -> delta < (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta < (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp_lt (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInitLt_metric (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) (ricMin := ricMin) D hmin hscalar)
    hdata

/-- Corollary 9.3 conditional form using the unit tangent compact-minimum
selector. -/
theorem strict_pinch_pos
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D)
    (hscalar : Continuous (fun x : M => scalar 0 x))
    (hdata :
      ∀ delta : Real, 0 < delta -> delta <= (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta <= (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInit_pos (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) D hpos hscalar)
    hdata

/-- Strict-`delta` version using the unit tangent compact-minimum selector. -/
theorem strict_pinch_pos_lt
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]
    {G : Real -> SmoothRiemannianMetric I M}
    {Ric : TwoTensorFamily (I := I) (M := M)}
    {scalar : Real -> M -> Real}
    {T : Real}
    (hT : 0 <= T)
    (D : MetricRicciData (I := I) (M := M) G Ric)
    (hpos : MetricRicciPos (I := I) (M := M) D)
    (hscalar : Continuous (fun x : M => scalar 0 x))
    (hdata :
      ∀ delta : Real, 0 < delta -> delta < (1 : Real) / 3 ->
        PinchWMPData (I := I) (M := M) G Ric scalar T delta) :
    ∃ delta : Real,
      0 < delta ∧ delta < (1 : Real) / 3 ∧
        PinchPres (I := I) (M := M) G Ric scalar T delta := by
  exact pinch_init_wmp_lt (I := I) (M := M) (G := G) (Ric := Ric)
    (scalar := scalar) (T := T) hT
    (pinchInitLt_pos (I := I) (M := M) (G := G) (Ric := Ric)
      (scalar := scalar) D hpos hscalar)
    hdata

end RicciFlow
end RicciFlower
