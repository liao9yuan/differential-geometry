import RicciFlower.DimensionThree.PinchingAlgebra
import Mathlib.Tactic

/-!
# Three-dimensional Ricci controls curvature algebra

This file contains the pure eigenvalue estimate behind Hamilton's Corollary
11.4.  The geometric bridge from an actual `Rm04` tensor norm to the sectional
model below is a separate realization step.
-/

noncomputable section

namespace RicciFlower
namespace DimensionThree

/-- Sectional curvature `K_12` in dimension three, written in Ricci eigenvalues. -/
def sec12Ric3 (l1 l2 l3 : Real) : Real :=
  (l1 + l2 - l3) / 2

/-- Sectional curvature `K_13` in dimension three, written in Ricci eigenvalues. -/
def sec13Ric3 (l1 l2 l3 : Real) : Real :=
  (l1 + l3 - l2) / 2

/-- Sectional curvature `K_23` in dimension three, written in Ricci eigenvalues. -/
def sec23Ric3 (l1 l2 l3 : Real) : Real :=
  (l2 + l3 - l1) / 2

/-- A coarse squared norm model for a three-dimensional curvature tensor from
the three sectional curvatures in an orthonormal basis.  The factor `4` is the
standard multiplicity factor for the independent sectional components. -/
def rmSecNormSq3 (K12 K13 K23 : Real) : Real :=
  4 * (K12 ^ 2 + K13 ^ 2 + K23 ^ 2)

private theorem sq_le_of_abs_le {a b : Real} (h : |a| <= b) :
    a ^ 2 <= b ^ 2 := by
  rcases abs_le.mp h with ⟨hlo, hhi⟩
  have hleft : 0 <= b + a := by linarith
  have hright : 0 <= b - a := by linarith
  have hprod : 0 <= (b + a) * (b - a) := mul_nonneg hleft hright
  nlinarith

/-- If the Ricci eigenvalues are nonnegative, each sectional curvature has
absolute value at most `R / 2`. -/
theorem secAbsLe3
    (l1 l2 l3 : Real) (h1 : 0 <= l1) (h2 : 0 <= l2) (h3 : 0 <= l3) :
    |sec12Ric3 l1 l2 l3| <= ricciEigenScalar3 l1 l2 l3 / 2 ∧
      |sec13Ric3 l1 l2 l3| <= ricciEigenScalar3 l1 l2 l3 / 2 ∧
      |sec23Ric3 l1 l2 l3| <= ricciEigenScalar3 l1 l2 l3 / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · apply abs_le.mpr
    constructor <;> unfold sec12Ric3 ricciEigenScalar3 <;> nlinarith
  · apply abs_le.mpr
    constructor <;> unfold sec13Ric3 ricciEigenScalar3 <;> nlinarith
  · apply abs_le.mpr
    constructor <;> unfold sec23Ric3 ricciEigenScalar3 <;> nlinarith

/-- Corollary 11.4, pure eigenvalue form: with nonnegative Ricci eigenvalues,
the squared curvature norm model is bounded by the coarse constant `100^2 R^2`.

This is intentionally stronger than needed for the display constant, and avoids
choosing a square-root norm at the algebra layer. -/
theorem rmSqLe100ScalSq3
    (l1 l2 l3 : Real) (h1 : 0 <= l1) (h2 : 0 <= l2) (h3 : 0 <= l3) :
    rmSecNormSq3 (sec12Ric3 l1 l2 l3) (sec13Ric3 l1 l2 l3)
        (sec23Ric3 l1 l2 l3) <=
      (100 : Real) ^ 2 * ricciEigenScalar3 l1 l2 l3 ^ 2 := by
  let R := ricciEigenScalar3 l1 l2 l3
  rcases secAbsLe3 l1 l2 l3 h1 h2 h3 with ⟨h12, h13, h23⟩
  have h12sq : sec12Ric3 l1 l2 l3 ^ 2 <= (R / 2) ^ 2 :=
    sq_le_of_abs_le h12
  have h13sq : sec13Ric3 l1 l2 l3 ^ 2 <= (R / 2) ^ 2 :=
    sq_le_of_abs_le h13
  have h23sq : sec23Ric3 l1 l2 l3 ^ 2 <= (R / 2) ^ 2 :=
    sq_le_of_abs_le h23
  have hsum :
      rmSecNormSq3 (sec12Ric3 l1 l2 l3) (sec13Ric3 l1 l2 l3)
          (sec23Ric3 l1 l2 l3) <= 4 * (3 * (R / 2) ^ 2) := by
    unfold rmSecNormSq3
    nlinarith
  have hcoarse : 4 * (3 * (R / 2) ^ 2) <= (100 : Real) ^ 2 * R ^ 2 := by
    nlinarith [sq_nonneg R]
  exact le_trans hsum hcoarse

end DimensionThree
end RicciFlower
