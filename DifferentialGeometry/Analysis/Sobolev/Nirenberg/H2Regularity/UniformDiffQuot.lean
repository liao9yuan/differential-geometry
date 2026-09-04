import DifferentialGeometry.Analysis.Sobolev.Nirenberg.CrossTermBoundsNonSmooth.CrossBoundsNonSmooth


noncomputable section

open MeasureTheory Set
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth
open scoped ENNReal BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- An integral bound for the sum of squared difference quotients controls the
`L²` seminorm of each component. -/
theorem dq_norm_of_sum
    {g : Fin d → E → ℝ}
    (hg : ∀ j, MemLp (g j) 2 (volume : Measure E))
    {V : Set E} (hV : MeasurableSet V)
    {S : ℝ} (hS : 0 ≤ S)
    (i k : Fin d) (h : ℝ)
    (hsum : ∫ x in V, ∑ j : Fin d, (diffQuot k h (g j) x) ^ 2
        ∂(volume : Measure E) ≤ S) :
    eLpNorm (diffQuot k h (g i)) 2 ((volume : Measure E).restrict V) ≤
      ENNReal.ofReal (Real.sqrt S) := by
  let μ : Measure E := (volume : Measure E).restrict V
  have hdq : ∀ j, MemLp (diffQuot k h (g j)) 2 μ := fun j ↦
    (memLp_diffQuot_two (d := d) k h (hg j)).mono_measure Measure.restrict_le_self
  have hsum_int : Integrable (fun x ↦ ∑ j : Fin d, (diffQuot k h (g j) x) ^ 2) μ :=
    integrable_finset_sum Finset.univ fun j _ ↦ (hdq j).integrable_sq
  have hi_sum : ∀ᵐ x ∂μ, (diffQuot k h (g i) x) ^ 2 ≤
      ∑ j : Fin d, (diffQuot k h (g j) x) ^ 2 := by
    rw [show μ = (volume : Measure E).restrict V from rfl, ae_restrict_iff' hV]
    exact Filter.Eventually.of_forall fun x _ ↦
      Finset.single_le_sum (fun j _ ↦ sq_nonneg (diffQuot k h (g j) x))
        (Finset.mem_univ i)
  have hi_le : ∫ x, (diffQuot k h (g i) x) ^ 2 ∂μ ≤ S := by
    exact (integral_mono_ae (hdq i).integrable_sq hsum_int hi_sum).trans hsum
  rw [(hdq i).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num [← Real.sqrt_eq_rpow]
  exact (Real.sqrt_le_sqrt_iff hS).2 hi_le

end DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
