import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.Source

noncomputable section

open MeasureTheory Metric Set
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A scalar-source weak solution belongs to `W^{2,2}` on every precompact
open subset of its equation domain. -/
theorem srcSol_memW2_on
    {Omega V : Set E} (hOmega : IsOpen Omega)
    (hV_open : IsOpen V) (hV_compact : IsCompact (closure V))
    (hV_Omega : closure V ⊆ Omega)
    {A : DeGiorgi.EllipticCoeff d Omega} {u f : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Omega)
    (hf : MemLp f 2 ((volume : Measure E).restrict Omega))
    (hweak : ∀ v, DeGiorgi.MemH01 v Omega →
      ∀ hv : DeGiorgi.MemW1pWitness 2 v Omega,
        DeGiorgi.bilinFormOfCoeff A hu hv =
          ∫ x in Omega, f x * v x ∂(volume : Measure E))
    (B : SmoothEllipticBilinearForm d Set.univ)
    {rho : ℝ} (hrho : 0 < rho)
    (hcoeff : ∀ x ∈ Omega, ∀ i j : Fin d,
      A.a x i j = rho * B.a x i j)
    (hc : ∀ x : E, B.c x = 0) :
    MemWkp (d := d) 2 2 u V := by
  classical
  obtain ⟨_delta, eta, _hdelta, _hdelta_room, heta, heta_cpt, heta_range,
      heta_one, heta_supp⟩ :=
    exists_smooth_cutoff_with_neighborhood
      (d := d) hV_compact hOmega hV_Omega
  have heta_one_closure : ∀ x ∈ closure V, eta x = 1 := by
    intro x hx
    exact heta_one x (Metric.self_subset_cthickening (closure V) hx)
  obtain ⟨R₀, hR₀, hR₀_room⟩ :=
    heta_cpt.isCompact.exists_cthickening_subset_open hOmega heta_supp
  have hcoeff_room : ∀ x ∈ Metric.cthickening R₀ (tsupport eta),
      ∀ i j : Fin d, A.a x i j = rho * B.a x i j := by
    intro x hx
    exact hcoeff x (hR₀_room hx)
  have heta_deriv_cont : Continuous (fderiv ℝ eta) :=
    heta.continuous_fderiv (by simp)
  have heta_deriv_cpt : HasCompactSupport (fderiv ℝ eta) :=
    heta_cpt.fderiv (𝕜 := ℝ)
  obtain ⟨N, hN⟩ :=
    heta_deriv_cont.bounded_above_of_compact_support heta_deriv_cpt
  exact srcSol_memW2 (d := d) (Omega := Omega) (V := V)
    hOmega hu hf hweak B hrho heta heta_cpt heta_range hR₀ hR₀_room
    hcoeff_room hc hV_open hV_compact heta_one_closure (N := N) hN

end DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous
