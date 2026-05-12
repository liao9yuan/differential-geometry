import Mathlib.Tactic.Ring

/-!
# Three-dimensional pinching algebra

This file contains the pure eigenvalue algebra used in Hamilton's three
dimensional pinching argument.  It is intentionally independent of the synthetic
Ricci-flow layer and of geometric realization data.
-/

namespace RicciFlower
namespace DimensionThree

variable {R : Type*}

/-- Scalar curvature written as the sum of three Ricci eigenvalues. -/
def ricciEigenScalar3 [CommRing R] (l1 l2 l3 : R) : R :=
  l1 + l2 + l3

/-- Squared Ricci norm written in Ricci eigenvalues. -/
def ricciEigenNormSq3 [CommRing R] (l1 l2 l3 : R) : R :=
  l1 ^ 2 + l2 ^ 2 + l3 ^ 2

/-- Cubic trace `tr(Ric^3)` written in Ricci eigenvalues. -/
def ricciEigenTraceCube3 [CommRing R] (l1 l2 l3 : R) : R :=
  l1 ^ 3 + l2 ^ 3 + l3 ^ 3

/-- Hamilton's cubic reaction quantity `Q` in dimension three, in Ricci eigenvalues. -/
def hamiltonCubicQ3 [CommRing R] (l1 l2 l3 : R) : R :=
  2 * ricciEigenNormSq3 l1 l2 l3 ^ 2 +
    ricciEigenScalar3 l1 l2 l3 ^ 4 -
    5 * ricciEigenScalar3 l1 l2 l3 ^ 2 * ricciEigenNormSq3 l1 l2 l3 +
    4 * ricciEigenScalar3 l1 l2 l3 * ricciEigenTraceCube3 l1 l2 l3

/-- Factorized form of Hamilton's cubic `Q`, Lemma 10.7 in eigenvalue form. -/
def hamiltonCubicQFactorized3 [CommRing R] (l1 l2 l3 : R) : R :=
  (l1 - l2) ^ 2 * (ricciEigenScalar3 l1 l2 l3 - 2 * l3) ^ 2 +
    (l1 - l3) ^ 2 * (ricciEigenScalar3 l1 l2 l3 - 2 * l2) ^ 2 +
    (l2 - l3) ^ 2 * (ricciEigenScalar3 l1 l2 l3 - 2 * l1) ^ 2

/-- LaTeX Lemma 10.7: Hamilton's cubic `Q` factorizes into eigenvalue gaps. -/
theorem hamiltonCubicQ3_factorized [CommRing R] (l1 l2 l3 : R) :
    hamiltonCubicQ3 l1 l2 l3 = hamiltonCubicQFactorized3 l1 l2 l3 := by
  unfold hamiltonCubicQ3 hamiltonCubicQFactorized3 ricciEigenScalar3 ricciEigenNormSq3
    ricciEigenTraceCube3
  ring

end DimensionThree
end RicciFlower
