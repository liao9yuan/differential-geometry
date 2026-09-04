import DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.HomogeneousWeakSolution

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace
  RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A scalar-source weak equation may be tested against the localized standard
Nirenberg difference-quotient test using the supplied weak-gradient witness. -/
theorem srcSol_substOn
    {Omega : Set E} (hOmega : IsOpen Omega)
    {A : DeGiorgi.EllipticCoeff d Omega} {u f : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Omega)
    (hweak : ∀ v, DeGiorgi.MemH01 v Omega →
      ∀ hv : DeGiorgi.MemW1pWitness 2 v Omega,
        DeGiorgi.bilinFormOfCoeff A hu hv =
          ∫ x in Omega, f x * v x ∂(volume : Measure E))
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta) (k : Fin d) (h : ℝ)
    (hroom : Metric.cthickening |h| (tsupport eta) ⊆ Omega) :
    ∫ x in Omega, ∑ i : Fin d,
        (∑ j : Fin d, A.a x i j * hu.weakGrad x j) *
          diffQuot k (-h) (fun y =>
            (eta y) ^ 2 * diffQuot k h (fun z => hu.weakGrad z i) y +
              2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
                diffQuot k h u y) x
      ∂(volume : Measure E) =
        ∫ x in Omega, f x * standardNirenbergTest k h eta u x
          ∂(volume : Measure E) := by
  let htest := stdTestWitnessOn (d := d) hOmega hu heta heta_cpt k h hroom
  have hsrc := hweak (standardNirenbergTest k h eta u)
    (stdTest_memH01On (d := d) hOmega hu heta heta_cpt k h hroom)
    htest
  rw [DeGiorgi.bilinFormOfCoeff] at hsrc
  have htest_grad : ∀ x i, htest.weakGrad x i =
      diffQuot k (-h) (fun y =>
        (eta y) ^ 2 * diffQuot k h (fun z => hu.weakGrad z i) y +
          2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
            diffQuot k h u y) x := by
    intro x i
    exact stdTest_grad (d := d) hOmega hu heta heta_cpt k h hroom x i
  have hscalar : ∀ a b : ℝ, ⟪a, b⟫_ℝ = a * b := by
    intro a b
    simpa using (RCLike.inner_apply' a b)
  simpa [DeGiorgi.bilinFormIntegrandOfCoeff, PiLp.inner_apply,
    DeGiorgi.matMulE_apply, Matrix.mulVec, dotProduct, hscalar, htest_grad]
    using hsrc

end DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous
