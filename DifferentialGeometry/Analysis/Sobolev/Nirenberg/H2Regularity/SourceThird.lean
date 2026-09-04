import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.Interior
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.SourceDifferentiated

/-!
# Third-Order Interior Regularity with Scalar Source

This module performs the first source-sensitive Nirenberg recursion step.  A
scalar-source weak solution whose source has one weak derivative and whose
solution already lies in `W^{2,2}` belongs locally to `W^{3,2}`.
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

/-- A scalar-source divergence-form weak solution with source in `W^{1,2}`
and solution in `W^{2,2}` belongs locally to `W^{3,2}`. -/
theorem srcSol_memW3_on
    {Omega V : Set E} (hOmega : IsOpen Omega)
    (hOmega_compact : IsCompact (closure Omega))
    (hV_open : IsOpen V) (hV_compact : IsCompact (closure V))
    (hV_Omega : closure V ⊆ Omega)
    {A : DeGiorgi.EllipticCoeff d Omega} {u f : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Omega)
    (hweak : ∀ v, DeGiorgi.MemH01 v Omega →
      ∀ hv : DeGiorgi.MemW1pWitness 2 v Omega,
        DeGiorgi.bilinFormOfCoeff A hu hv =
          ∫ x in Omega, f x * v x ∂(volume : Measure E))
    (hf1 : MemWkp (d := d) 1 2 f Omega)
    (B : SmoothEllipticBilinearForm d Set.univ)
    {rho : ℝ} (hrho : 0 < rho)
    (hcoeff : ∀ x ∈ Omega, ∀ i j : Fin d,
      A.a x i j = rho * B.a x i j)
    (hu2 : MemWkp (d := d) 2 2 u Omega)
    (hc : ∀ x : E, B.c x = 0) :
    MemWkp (d := d) 3 2 u V := by
  have hV_Omega' : V ⊆ Omega := subset_closure.trans hV_Omega
  rw [MemWkp_succ]
  refine ⟨MemW1p.mono_set hV_open hV_Omega' hu2.memW1p, ?_⟩
  intro l
  have hdu1 : DeGiorgi.MemW1p 2
      (chosenWeakPartial' 2 l u Omega) Omega := by
    rw [← MemWkp.one_iff_memW1p]
    exact hu2.chosenWeakPartial_mem l
  let hw : DeGiorgi.MemW1pWitness 2
      (chosenWeakPartial' 2 l u Omega) Omega := hdu1.someWitness
  let q : E → ℝ := fun x =>
    chosenWeakPartial' 2 l f Omega x +
      rho * homDiffSource B u Omega l x
  have hq : MemLp q 2 ((volume : Measure E).restrict Omega) := by
    have hdf := chosenWeakPartial'_memLp_of_mem hf1.memW1p l
    have hhom := homDiffSource_memLp hOmega hOmega_compact B hu2 l
    simpa only [q] using hdf.add (hhom.const_mul rho)
  have hdu2 : MemWkp (d := d) 2 2
      (chosenWeakPartial' 2 l u Omega) V := by
    apply srcSol_memW2_on (d := d) hOmega hV_open hV_compact hV_Omega
      hw hq
      (fun v hv0 hv => by
        simpa only [q] using srcDiff_weak_eq
          (d := d) (A := A) (u := u) (f := f)
          hOmega hOmega_compact hu hweak hf1 B hrho hcoeff hu2 l hw v hv0 hv)
      B hrho hcoeff hc
  have hmono := chosenWeakPartial'_mono_set_ae (d := d)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hV_open hV_Omega' hu2.memW1p l
  exact (MemWkp_congr_ae (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hV_open hmono).mp hdu2

end DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous
