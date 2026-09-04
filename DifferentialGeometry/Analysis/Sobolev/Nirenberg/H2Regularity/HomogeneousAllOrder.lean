import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.SourceAllOrder

/-!
# All-Order Interior Regularity for Homogeneous Equations

This module specializes the scalar-source all-order Nirenberg producer to an
actual homogeneous De Giorgi solution.  The source is the zero function at
every Sobolev order.
-/

noncomputable section

open MeasureTheory Set
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A homogeneous divergence-form weak solution with smooth coefficients has
arbitrary interior Sobolev regularity on every precompact open subset. -/
theorem homSol_memWkp_on
    (m : ℕ) {Omega V : Set E} (hOmega : IsOpen Omega)
    (hV_open : IsOpen V) (hV_compact : IsCompact (closure V))
    (hV_Omega : closure V ⊆ Omega)
    {A : DeGiorgi.EllipticCoeff d Omega} {u : E → ℝ}
    (hsol : DeGiorgi.IsSolution A u)
    (B : SmoothEllipticBilinearForm d Set.univ)
    {rho : ℝ} (hrho : 0 < rho)
    (hcoeff : ∀ x ∈ Omega, ∀ i j : Fin d,
      A.a x i j = rho * B.a x i j)
    (hc : ∀ x : E, B.c x = 0) :
    MemWkp (d := d) (m + 2) 2 u V := by
  let hhom : DeGiorgi.IsHomogeneousWeakSolution A u :=
    hsol.to_homogeneous hOmega
  let hu : DeGiorgi.MemW1pWitness 2 u Omega := hhom.1.someWitness
  have hf0 : MemWkp (d := d) m 2 (fun _ : E => (0 : ℝ)) Omega :=
    MemWkp_zero_fun (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hOmega
  have hweak0 : ∀ v, DeGiorgi.MemH01 v Omega →
      ∀ hv : DeGiorgi.MemW1pWitness 2 v Omega,
        DeGiorgi.bilinFormOfCoeff A hu hv =
          ∫ x in Omega, (fun _ : E => (0 : ℝ)) x * v x
            ∂(volume : Measure E) := by
    intro v hv0 hv
    simpa only [zero_mul, integral_zero] using hhom.2 hu v hv0 hv
  exact srcSol_memWkp_on (d := d) m hOmega hV_open hV_compact hV_Omega
    hu hf0 hweak0 B hrho hcoeff hc

end DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous
