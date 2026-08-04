import DifferentialGeometry.Topology.Morse.Defs
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.LinearAlgebra.QuadraticForm.Signature

namespace DifferentialGeometry.Topology.Morse

open QuadraticForm

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def morseNormalFormWeights (morseIndex : ℕ) : Fin (Module.finrank ℝ E) → ℝ :=
  fun i => if (i : ℕ) < morseIndex then -1 else 1

theorem chartHessian_weightedSumSquares_normalForm (g : E → ℝ)
    (hnd : (QuadraticMap.associated (R := ℝ) (chartHessian g)).SeparatingLeft) :
    ∃ w : Fin (Module.finrank ℝ E) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧
        QuadraticMap.Equivalent (chartHessian g) (QuadraticMap.weightedSumSquares ℝ w) ∧
          {i : Fin (Module.finrank ℝ E) | w i < 0}.ncard = sigNeg (chartHessian g) := by
  rcases QuadraticForm.equivalent_one_neg_one_weighted_sum_squared (chartHessian g) hnd with
    ⟨w, hw, hEq⟩
  refine ⟨w, hw, hEq, ?_⟩
  exact (QuadraticForm.sigNeg_of_equiv_weightedSumSquares hEq).symm

end DifferentialGeometry.Topology.Morse
