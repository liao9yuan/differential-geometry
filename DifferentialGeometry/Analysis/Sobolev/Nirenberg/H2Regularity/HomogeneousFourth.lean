import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.DifferentiatedSourceW1
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.DifferentiatedWeak
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.SourceThird

/-!
# Fourth-Order Interior Regularity for Homogeneous Solutions

This module performs the fixed `W^{3,2} -> W^{4,2}` smoke test for the
Nirenberg bootstrap.  It reuses the differentiated homogeneous equation and
the scalar-source third-order interior endpoint.
-/

noncomputable section

open MeasureTheory Set
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A homogeneous divergence-form weak solution in `W^{3,2}` belongs to
`W^{4,2}` on every precompact open subset of its equation domain. -/
theorem homSol_memW4_on
    {Omega V : Set E} (hOmega : IsOpen Omega)
    (hOmega_compact : IsCompact (closure Omega))
    (hV_open : IsOpen V) (hV_compact : IsCompact (closure V))
    (hV_Omega : closure V ⊆ Omega)
    {A : DeGiorgi.EllipticCoeff d Omega} {u : E → ℝ}
    (hsol : DeGiorgi.IsSolution A u)
    (B : SmoothEllipticBilinearForm d Set.univ)
    {rho : ℝ} (hrho : 0 < rho)
    (hcoeff : ∀ x ∈ Omega, ∀ i j : Fin d,
      A.a x i j = rho * B.a x i j)
    (hu3 : MemWkp (d := d) 3 2 u Omega)
    (hc : ∀ x : E, B.c x = 0) :
    MemWkp (d := d) 4 2 u V := by
  have hV_Omega' : V ⊆ Omega := subset_closure.trans hV_Omega
  have hu2 : MemWkp (d := d) 2 2 u Omega :=
    hu3.le_of_le (by norm_num)
  rw [MemWkp_succ]
  refine ⟨MemW1p.mono_set hV_open hV_Omega' hu3.memW1p, ?_⟩
  intro l
  have hw_mem : DeGiorgi.MemW1p 2
      (chosenWeakPartial' 2 l u Omega) Omega :=
    (hu3.chosenWeakPartial_mem l).memW1p
  let hw : DeGiorgi.MemW1pWitness 2
      (chosenWeakPartial' 2 l u Omega) Omega := hw_mem.someWitness
  let f : E → ℝ := fun x => rho * homDiffSource B u Omega l x
  have hf1 : MemWkp (d := d) 1 2 f Omega := by
    simpa only [f] using
      (homDiff_memW1 hOmega hOmega_compact B hu3 l).const_smul
        (by norm_num) hOmega rho
  have hweak : ∀ v, DeGiorgi.MemH01 v Omega →
      ∀ hv : DeGiorgi.MemW1pWitness 2 v Omega,
        DeGiorgi.bilinFormOfCoeff A hw hv =
          ∫ x in Omega, f x * v x ∂(volume : Measure E) := by
    intro v hv0 hv
    simpa only [f] using homDiff_weak_eq
      (d := d) (A := A) (u := u) (rho := rho) (v := v)
      hOmega hOmega_compact hsol B hrho hcoeff hu2 l hw hv0 hv
  have hdu3 : MemWkp (d := d) 3 2
      (chosenWeakPartial' 2 l u Omega) V :=
    srcSol_memW3_on (d := d) hOmega hOmega_compact hV_open hV_compact
      hV_Omega hw hweak hf1 B hrho hcoeff
      (hu3.chosenWeakPartial_mem l) hc
  have hmono := chosenWeakPartial'_mono_set_ae (d := d)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hV_open hV_Omega' hu3.memW1p l
  exact (MemWkp_congr_ae (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hV_open hmono).mp hdu3

end DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous
