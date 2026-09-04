import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.DifferentiatedWeak
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.Source

noncomputable section

open MeasureTheory Metric Set
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem one_subset_tsupp
    {V : Set E} {eta : E → ℝ}
    (heta_one : ∀ x ∈ closure V, eta x = 1) :
    closure V ⊆ tsupport eta := by
  intro x hx
  apply subset_tsupport eta
  intro hzero
  have hone := heta_one x hx
  rw [hzero] at hone
  norm_num at hone

/-- A homogeneous divergence-form weak solution with two weak derivatives on a
relatively compact outer set belongs locally to `W^{3,2}`. -/
theorem homSol_memW3
    {Omega : Set E} (hOmega : IsOpen Omega)
    (hOmega_compact : IsCompact (closure Omega))
    {A : DeGiorgi.EllipticCoeff d Omega} {u : E → ℝ}
    (hsol : DeGiorgi.IsSolution A u)
    (B : SmoothEllipticBilinearForm d Set.univ)
    {rho : ℝ} (hrho : 0 < rho)
    (hcoeff : ∀ x ∈ Omega, ∀ i j : Fin d,
      A.a x i j = rho * B.a x i j)
    (hu2 : MemWkp (d := d) 2 2 u Omega)
    (hc : ∀ x : E, B.c x = 0)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta)
    (heta_range : Set.range eta ⊆ Set.Icc (0 : ℝ) 1)
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hK_Omega : Metric.cthickening R₀ (tsupport eta) ⊆ Omega)
    {V : Set E} (hV_open : IsOpen V)
    (hV_compact : IsCompact (closure V))
    (heta_one : ∀ x ∈ closure V, eta x = 1)
    {N : ℝ} (hderiv : ∀ x : E, ‖fderiv ℝ eta x‖ ≤ N) :
    MemWkp (d := d) 3 2 u V := by
  have hV_tsupp : closure V ⊆ tsupport eta := one_subset_tsupp heta_one
  have htsupp_K : tsupport eta ⊆ Metric.cthickening R₀ (tsupport eta) :=
    Metric.self_subset_cthickening (tsupport eta)
  have hV_Omega : V ⊆ Omega :=
    ((subset_closure.trans hV_tsupp).trans htsupp_K).trans hK_Omega
  rw [MemWkp_succ]
  refine ⟨MemW1p.mono_set hV_open hV_Omega hu2.memW1p, ?_⟩
  intro l
  have hdu1 : DeGiorgi.MemW1p 2
      (chosenWeakPartial' 2 l u Omega) Omega :=
    (hu2.chosenWeakPartial_mem l).memW1p
  let hw : DeGiorgi.MemW1pWitness 2
      (chosenWeakPartial' 2 l u Omega) Omega := hdu1.someWitness
  have hsource : MemLp
      (fun x => rho * homDiffSource B u Omega l x) 2
      ((volume : Measure E).restrict Omega) :=
    (homDiffSource_memLp hOmega hOmega_compact B hu2 l).const_mul rho
  have hdu2 : MemWkp (d := d) 2 2
      (chosenWeakPartial' 2 l u Omega) V := by
    apply srcSol_memW2 (d := d) hOmega hw hsource
      (fun v hv hvw => homDiff_weak_eq
        (d := d) (A := A) (u := u) (rho := rho) (v := v)
        hOmega hOmega_compact hsol B hrho hcoeff hu2 l hw hv hvw)
      B hrho heta heta_cpt heta_range hR₀ hK_Omega
      (fun x hx => hcoeff x (hK_Omega hx)) hc hV_open hV_compact
      heta_one hderiv
  have hmono := chosenWeakPartial'_mono_set_ae (d := d)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hV_open hV_Omega hu2.memW1p l
  exact (MemWkp_congr_ae (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hV_open hmono).mp hdu2

end DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous
