import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.DifferentiatedSourceK
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.Interior
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.Restriction
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.SourceDifferentiated

/-!
# All-Order Interior Regularity for Scalar-Source Equations

This module iterates the scalar Nirenberg interior estimate.  At each step one
precompact intermediate domain supplies both the compact closure needed by the
differentiated-source estimate and the room needed for the next interior
application.
-/

noncomputable section

open MeasureTheory Set
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A scalar-source divergence-form weak solution whose source has `m` weak
derivatives belongs locally to `W^{m+2,2}`. -/
theorem srcSol_memWkp_on
    (m : ℕ) {Omega V : Set E} (hOmega : IsOpen Omega)
    (hV_open : IsOpen V) (hV_compact : IsCompact (closure V))
    (hV_Omega : closure V ⊆ Omega)
    {A : DeGiorgi.EllipticCoeff d Omega} {u f : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Omega)
    (hf : MemWkp (d := d) m 2 f Omega)
    (hweak : ∀ v, DeGiorgi.MemH01 v Omega →
      ∀ hv : DeGiorgi.MemW1pWitness 2 v Omega,
        DeGiorgi.bilinFormOfCoeff A hu hv =
          ∫ x in Omega, f x * v x ∂(volume : Measure E))
    (B : SmoothEllipticBilinearForm d Set.univ)
    {rho : ℝ} (hrho : 0 < rho)
    (hcoeff : ∀ x ∈ Omega, ∀ i j : Fin d,
      A.a x i j = rho * B.a x i j)
    (hc : ∀ x : E, B.c x = 0) :
    MemWkp (d := d) (m + 2) 2 u V := by
  classical
  induction m generalizing Omega V A u f with
  | zero =>
      apply srcSol_memW2_on (d := d) hOmega hV_open hV_compact hV_Omega
        hu (by simpa only [MemWkp_zero] using hf) hweak B hrho hcoeff hc
  | succ m ih =>
      obtain ⟨U, hU_open, hV_U, hU_Omega, hU_compact⟩ :=
        exists_open_between_and_isCompact_closure hV_compact hOmega hV_Omega
      have hU_sub : U ⊆ Omega := subset_closure.trans hU_Omega
      have hV_sub_U : V ⊆ U := subset_closure.trans hV_U
      have hV_sub_Omega : V ⊆ Omega := hV_sub_U.trans hU_sub
      have huU_high : MemWkp (d := d) (m + 2) 2 u U :=
        ih (Omega := Omega) (V := U) (A := A) (u := u) (f := f)
          hOmega hU_open hU_compact hU_Omega hu hf.le_succ hweak hcoeff
      let AU : DeGiorgi.EllipticCoeff d U := A.restrict hU_sub
      let huU : DeGiorgi.MemW1pWitness 2 u U := hu.restrict hU_open hU_sub
      have hweakU : ∀ v, DeGiorgi.MemH01 v U →
          ∀ hv : DeGiorgi.MemW1pWitness 2 v U,
            DeGiorgi.bilinFormOfCoeff AU huU hv =
              ∫ x in U, f x * v x ∂(volume : Measure E) := by
        intro v hv0 hv
        simpa only [AU, huU] using
          srcEq_restrict (d := d) hOmega hU_open hU_sub hu hweak hv0 hv
      have hcoeffU : ∀ x ∈ U, ∀ i j : Fin d,
          AU.a x i j = rho * B.a x i j := by
        intro x hx i j
        simpa only [AU, DeGiorgi.EllipticCoeff.restrict_a] using
          hcoeff x (hU_sub hx) i j
      have hfU : MemWkp (d := d) (m + 1) 2 f U :=
        hf.mono_set (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          hOmega hU_open hU_sub
      have hfU1 : MemWkp (d := d) 1 2 f U :=
        hfU.le_of_le (by omega)
      have huU2 : MemWkp (d := d) 2 2 u U :=
        huU_high.le_of_le (by omega)
      rw [show m.succ + 2 = (m + 2) + 1 by omega, MemWkp_succ]
      refine ⟨(hu.restrict hV_open hV_sub_Omega).memW1p, ?_⟩
      intro l
      have hduU1 : DeGiorgi.MemW1p 2
          (chosenWeakPartial' 2 l u U) U :=
        (huU_high.chosenWeakPartial_mem l).memW1p
      let hw : DeGiorgi.MemW1pWitness 2
          (chosenWeakPartial' 2 l u U) U := hduU1.someWitness
      let q : E → ℝ := fun x =>
        chosenWeakPartial' 2 l f U x +
          rho * homDiffSource B u U l x
      have hdf : MemWkp (d := d) m 2
          (chosenWeakPartial' 2 l f U) U :=
        hfU.chosenWeakPartial_mem l
      have hhom : MemWkp (d := d) m 2
          (homDiffSource B u U l) U :=
        homDiff_memWkp (d := d) m hU_open hU_compact B huU_high l
      have hq : MemWkp (d := d) m 2 q U := by
        simpa only [q] using MemWkp.add (d := d)
          (by norm_num : (1 : ℝ≥0∞) ≤ 2) hU_open hdf
          (hhom.const_smul (by norm_num : (1 : ℝ≥0∞) ≤ 2)
            hU_open rho)
      have hdu_weak : ∀ v, DeGiorgi.MemH01 v U →
          ∀ hv : DeGiorgi.MemW1pWitness 2 v U,
            DeGiorgi.bilinFormOfCoeff AU hw hv =
              ∫ x in U, q x * v x ∂(volume : Measure E) := by
        intro v hv0 hv
        simpa only [q] using srcDiff_weak_eq
          (d := d) (A := AU) (u := u) (f := f)
          hU_open hU_compact huU hweakU hfU1 B hrho hcoeffU huU2
          l hw v hv0 hv
      have hdu_high : MemWkp (d := d) (m + 2) 2
          (chosenWeakPartial' 2 l u U) V :=
        ih (Omega := U) (V := V) (A := AU)
          (u := chosenWeakPartial' 2 l u U) (f := q)
          hU_open hV_open hV_compact hV_U hw hq hdu_weak hcoeffU
      have hmono := chosenWeakPartial'_mono_set_ae (d := d)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hV_open hV_sub_U huU.memW1p l
      exact (MemWkp_congr_ae (d := d)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hV_open hmono).mp hdu_high

end DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous
