import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.DifferentiatedSource
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.HomogeneousDifferentiated

/-!
# The Differentiated Weak Equation

This module promotes the smooth-test differentiated identity to the full
`H₀¹` weak equation and identifies its divergence-form right-hand side with
the canonical scalar source.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Each canonical first weak partial of a homogeneous solution satisfies the
inhomogeneous weak equation whose source is the divergence of the differentiated
coefficient field. -/
theorem homDiff_weak_eq
    {Omega : Set E} (hOmega : IsOpen Omega)
    (hOmega_compact : IsCompact (closure Omega))
    {A : DeGiorgi.EllipticCoeff d Omega} {u : E → ℝ}
    (hsol : DeGiorgi.IsSolution A u)
    (B : SmoothEllipticBilinearForm d (Set.univ : Set E))
    {rho : ℝ} (hrho : 0 < rho)
    (hcoeff : ∀ x ∈ Omega, ∀ i j : Fin d,
      A.a x i j = rho * B.a x i j)
    (hu2 : MemWkp (d := d) 2 2 u Omega)
    (l : Fin d)
    (hw : DeGiorgi.MemW1pWitness 2
      (chosenWeakPartial' 2 l u Omega) Omega)
    (v : E → ℝ) (hv0 : DeGiorgi.MemH01 v Omega)
    (hv : DeGiorgi.MemW1pWitness 2 v Omega) :
    DeGiorgi.bilinFormOfCoeff A hw hv =
      ∫ x in Omega, (rho * homDiffSource B u Omega l x) * v x := by
  classical
  let F : E → E := homDiffField B u Omega l
  let g : E → ℝ := homDiffSource B u Omega l
  let rhs : (E → ℝ) → ℝ := fun z =>
    rho * DeGiorgi.weakProblemRHSOfField (Ω := Omega) F z
  have hF : MemLp F 2 ((volume : Measure E).restrict Omega) := by
    simpa [F] using homDiffField_memLp hOmega hOmega_compact B hu2 l
  have hg : MemLp g 2 ((volume : Measure E).restrict Omega) := by
    simpa [g] using homDiffSource_memLp hOmega hOmega_compact B hu2 l
  have hdiv : DeGiorgi.HasWeakDiv g F Omega := by
    simpa [F, g] using homDiff_hasDiv hOmega hOmega_compact B hu2 l
  have hw_mem : DeGiorgi.MemW1p 2
      (chosenWeakPartial' 2 l u Omega) Omega := by
    rw [← MemWkp.one_iff_memW1p]
    exact hu2.chosenWeakPartial_mem l
  let hwc : DeGiorgi.MemW1pWitness 2
      (chosenWeakPartial' 2 l u Omega) Omega :=
    DeGiorgi.MemW1p.someWitness hw_mem
  have hrhs_add : ∀ z w : E → ℝ,
      DeGiorgi.MemH01 z Omega → DeGiorgi.MemH01 w Omega →
      rhs (fun x => z x + w x) = rhs z + rhs w := by
    intro z w hz0 hw0
    let hz : DeGiorgi.MemW1pWitness 2 z Omega :=
      DeGiorgi.MemW1p.someWitness (DeGiorgi.MemW01p.memW1p hz0)
    let hww : DeGiorgi.MemW1pWitness 2 w Omega :=
      DeGiorgi.MemW1p.someWitness (DeGiorgi.MemW01p.memW1p hw0)
    have hzw0 : DeGiorgi.MemH01 (fun x => z x + w x) Omega :=
      DeGiorgi.MemW01p.add hz0 hw0
    let hzw : DeGiorgi.MemW1pWitness 2 (fun x => z x + w x) Omega :=
      hz.add hww
    have hraw :
        DeGiorgi.weakProblemRHSOfField (Ω := Omega) F
              (fun x => z x + w x) =
            DeGiorgi.weakProblemRHSOfField (Ω := Omega) F z +
              DeGiorgi.weakProblemRHSOfField (Ω := Omega) F w := by
      calc
        _ = DeGiorgi.divergenceRHSOfField F hzw := by
              exact DeGiorgi.weakProblemRHSOfField_eq_of_memH01
                hOmega hzw0 hzw
        _ = DeGiorgi.divergenceRHSOfField F hz +
              DeGiorgi.divergenceRHSOfField F hww := by
                exact DeGiorgi.divergenceRHSOfField_add hF hz hww
        _ = _ := by
              rw [DeGiorgi.weakProblemRHSOfField_eq_of_memH01 hOmega hz0 hz,
                DeGiorgi.weakProblemRHSOfField_eq_of_memH01 hOmega hw0 hww]
    simp only [rhs]
    rw [hraw]
    ring
  have hrhs_smul : ∀ c : ℝ, ∀ z : E → ℝ,
      DeGiorgi.MemH01 z Omega →
      rhs (fun x => c * z x) = c * rhs z := by
    intro c z hz0
    let hz : DeGiorgi.MemW1pWitness 2 z Omega :=
      DeGiorgi.MemW1p.someWitness (DeGiorgi.MemW01p.memW1p hz0)
    have hcz0 : DeGiorgi.MemH01 (fun x => c * z x) Omega := by
      simpa [Pi.smul_apply, smul_eq_mul] using
        (DeGiorgi.MemW01p.smul c hz0)
    let hcz : DeGiorgi.MemW1pWitness 2 (fun x => c * z x) Omega :=
      hz.smul c
    have hraw :
        DeGiorgi.weakProblemRHSOfField (Ω := Omega) F
              (fun x => c * z x) =
            c * DeGiorgi.weakProblemRHSOfField (Ω := Omega) F z := by
      calc
        _ = DeGiorgi.divergenceRHSOfField F hcz := by
              exact DeGiorgi.weakProblemRHSOfField_eq_of_memH01
                hOmega hcz0 hcz
        _ = c * DeGiorgi.divergenceRHSOfField F hz := by
              exact DeGiorgi.divergenceRHSOfField_smul c hz
        _ = _ := by
              rw [DeGiorgi.weakProblemRHSOfField_eq_of_memH01 hOmega hz0 hz]
    change rho * DeGiorgi.weakProblemRHSOfField (Ω := Omega) F
        (fun x => c * z x) =
      c * (rho * DeGiorgi.weakProblemRHSOfField (Ω := Omega) F z)
    rw [hraw]
    ring
  let C_rhs : ℝ := rho *
    (∫ x, ‖F x‖ ^ (2 : ℝ) ∂((volume : Measure E).restrict Omega)) ^
      (1 / (2 : ℝ))
  have hrhs_bound : ∀ z : E → ℝ, DeGiorgi.MemH01 z Omega →
      ∀ hwz : DeGiorgi.MemW1pWitness 2 z Omega,
      |rhs z| ≤ C_rhs *
        (∫ x, ‖hwz.weakGrad x‖ ^ (2 : ℝ)
          ∂((volume : Measure E).restrict Omega)) ^ (1 / (2 : ℝ)) := by
    intro z hz0 hwz
    have hraw := DeGiorgi.weakProblemRHSOfField_bound
      hOmega hF z hz0 hwz
    calc
      |rhs z| = rho *
          |DeGiorgi.weakProblemRHSOfField (Ω := Omega) F z| := by
            simp [rhs, abs_mul, abs_of_pos hrho]
      _ ≤ rho *
          ((∫ x, ‖F x‖ ^ (2 : ℝ)
              ∂((volume : Measure E).restrict Omega)) ^ (1 / (2 : ℝ)) *
            (∫ x, ‖hwz.weakGrad x‖ ^ (2 : ℝ)
              ∂((volume : Measure E).restrict Omega)) ^ (1 / (2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hraw hrho.le
      _ = C_rhs *
          (∫ x, ‖hwz.weakGrad x‖ ^ (2 : ℝ)
            ∂((volume : Measure E).restrict Omega)) ^ (1 / (2 : ℝ)) := by
            simp [C_rhs, mul_assoc]
  have hsmooth : ∀ {phi : E → ℝ} (hphi : DeGiorgi.IsSmoothTestOn Omega phi),
      DeGiorgi.bilinFormOfCoeff A hw
          (DeGiorgi.smoothTestWitness hOmega hphi) = rhs phi := by
    intro phi hphi
    have hscalar : ∀ a b : ℝ, ⟪a, b⟫_ℝ = a * b := by
      intro a b
      simpa using RCLike.inner_apply' a b
    have hwc_grad_ae : ∀ j : Fin d,
        (fun x => hwc.weakGrad x j) =ᵐ[(volume : Measure E).restrict Omega]
          chosenWeakPartial' 2 j
            (chosenWeakPartial' 2 l u Omega) Omega := by
      intro j
      exact DeGiorgi.HasWeakPartialDeriv.ae_eq hOmega
        (hwc.isWeakGrad j)
        (chosenWeakPartial'_isWeakPartial_of_mem hw_mem j)
        ((hwc.weakGrad_component_memLp j).locallyIntegrable (by norm_num))
        ((chosenWeakPartial'_memLp_of_mem hw_mem j).locallyIntegrable
          (by norm_num))
    have hwc_grad_all : ∀ᵐ x ∂((volume : Measure E).restrict Omega),
        ∀ j : Fin d,
          hwc.weakGrad x j =
            chosenWeakPartial' 2 j
              (chosenWeakPartial' 2 l u Omega) Omega x :=
      ae_all_iff.2 hwc_grad_ae
    have hleft :
        DeGiorgi.bilinFormOfCoeff A hwc
            (DeGiorgi.smoothTestWitness hOmega hphi) =
          ∫ x in Omega, ∑ i : Fin d,
            (∑ j : Fin d, A.a x i j *
              chosenWeakPartial' 2 j
                (chosenWeakPartial' 2 l u Omega) Omega x) *
              (fderiv ℝ phi x) (EuclideanSpace.single i 1) := by
      rw [DeGiorgi.bilinFormOfCoeff]
      apply integral_congr_ae
      filter_upwards [hwc_grad_all] with x hx
      simp [DeGiorgi.bilinFormIntegrandOfCoeff, DeGiorgi.matMulE_apply,
        Matrix.mulVec, dotProduct, PiLp.inner_apply,
        DeGiorgi.smoothTestWitness, DeGiorgi.smoothGradField, hx, hscalar]
    have hscaled :
        (∫ x in Omega, ∑ i : Fin d,
          (∑ j : Fin d, A.a x i j *
            chosenWeakPartial' 2 j
              (chosenWeakPartial' 2 l u Omega) Omega x) *
            (fderiv ℝ phi x) (EuclideanSpace.single i 1)) =
          rho * ∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
            B.a x i j *
              chosenWeakPartial' 2 j
                (chosenWeakPartial' 2 l u Omega) Omega x *
              (fderiv ℝ phi x) (EuclideanSpace.single i 1) := by
      calc
        _ = ∫ x in Omega, rho * (∑ i : Fin d, ∑ j : Fin d,
            B.a x i j *
              chosenWeakPartial' 2 j
                (chosenWeakPartial' 2 l u Omega) Omega x *
              (fderiv ℝ phi x) (EuclideanSpace.single i 1)) := by
                refine setIntegral_congr_fun hOmega.measurableSet
                  (fun x hx => ?_)
                simp_rw [hcoeff x hx]
                calc
                  _ = ∑ i : Fin d,
                      (rho * ∑ j : Fin d,
                        B.a x i j *
                          chosenWeakPartial' 2 j
                            (chosenWeakPartial' 2 l u Omega) Omega x) *
                        (fderiv ℝ phi x) (EuclideanSpace.single i 1) := by
                          refine Finset.sum_congr rfl (fun i _ => ?_)
                          congr 1
                          rw [Finset.mul_sum]
                          refine Finset.sum_congr rfl (fun j _ => ?_)
                          ring
                  _ = ∑ i : Fin d, rho *
                      ((∑ j : Fin d,
                        B.a x i j *
                          chosenWeakPartial' 2 j
                            (chosenWeakPartial' 2 l u Omega) Omega x) *
                        (fderiv ℝ phi x) (EuclideanSpace.single i 1)) := by
                          refine Finset.sum_congr rfl (fun i _ => ?_)
                          ring
                  _ = rho * ∑ i : Fin d,
                      ((∑ j : Fin d,
                        B.a x i j *
                          chosenWeakPartial' 2 j
                            (chosenWeakPartial' 2 l u Omega) Omega x) *
                        (fderiv ℝ phi x) (EuclideanSpace.single i 1)) := by
                          rw [Finset.mul_sum]
                  _ = _ := by
                          congr 1
                          refine Finset.sum_congr rfl (fun i _ => ?_)
                          rw [Finset.sum_mul]
        _ = _ := integral_const_mul rho _
    have hdiff := homSol_diff_id hOmega hsol B hrho hcoeff hu2 l
      hphi.1 hphi.2.1 hphi.2.2
    have hfield_int :
        (∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
          (fderiv ℝ (fun y : E => B.a y i j) x)
              (EuclideanSpace.single l 1) *
            chosenWeakPartial' 2 j u Omega x *
            (fderiv ℝ phi x) (EuclideanSpace.single i 1)) =
          ∫ x in Omega, ∑ i : Fin d,
            F x i * (fderiv ℝ phi x) (EuclideanSpace.single i 1) := by
      refine setIntegral_congr_fun hOmega.measurableSet (fun x _hx => ?_)
      simp [F, homDiffField, PiLp.toLp_apply, Finset.sum_mul]
    have hdiv_test := hdiv phi hphi.1 hphi.2.1 hphi.2.2
    have hsource :
        (∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
          B.a x i j *
            chosenWeakPartial' 2 j
              (chosenWeakPartial' 2 l u Omega) Omega x *
            (fderiv ℝ phi x) (EuclideanSpace.single i 1)) =
          ∫ x in Omega, g x * phi x := by
      calc
        _ = -(∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
            (fderiv ℝ (fun y : E => B.a y i j) x)
                (EuclideanSpace.single l 1) *
              chosenWeakPartial' 2 j u Omega x *
              (fderiv ℝ phi x) (EuclideanSpace.single i 1)) := hdiff
        _ = -(∫ x in Omega, ∑ i : Fin d,
            F x i * (fderiv ℝ phi x) (EuclideanSpace.single i 1)) := by
              rw [hfield_int]
        _ = -(-(∫ x in Omega, g x * phi x)) := by rw [hdiv_test]
        _ = _ := by ring
    have hphi0 : DeGiorgi.MemH01 phi Omega :=
      DeGiorgi.smoothTest_memH01 hOmega hphi
    have hrhs_int :
        DeGiorgi.weakProblemRHSOfField (Ω := Omega) F phi =
          ∫ x in Omega, g x * phi x :=
      DeGiorgi.weakRHS_eq_integral hOmega hF hg hdiv hphi0
        (DeGiorgi.smoothTestWitness hOmega hphi)
    calc
      DeGiorgi.bilinFormOfCoeff A hw
          (DeGiorgi.smoothTestWitness hOmega hphi) =
          DeGiorgi.bilinFormOfCoeff A hwc
            (DeGiorgi.smoothTestWitness hOmega hphi) :=
        DeGiorgi.bilinFormOfCoeff_eq_left hOmega A hw hwc
          (DeGiorgi.smoothTestWitness hOmega hphi)
      _ = rho * ∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
          B.a x i j *
            chosenWeakPartial' 2 j
              (chosenWeakPartial' 2 l u Omega) Omega x *
            (fderiv ℝ phi x) (EuclideanSpace.single i 1) := hleft.trans hscaled
      _ = rho * ∫ x in Omega, g x * phi x := by rw [hsource]
      _ = rho * DeGiorgi.weakProblemRHSOfField (Ω := Omega) F phi := by
        rw [hrhs_int]
      _ = rhs phi := rfl
  have hweak := DeGiorgi.weak_eq_of_smooth hOmega A rhs
    hrhs_add hrhs_smul C_rhs hrhs_bound hw hsmooth hw v hv0 hv
  have hrhs_int :
      DeGiorgi.weakProblemRHSOfField (Ω := Omega) F v =
        ∫ x in Omega, g x * v x :=
    DeGiorgi.weakRHS_eq_integral hOmega hF hg hdiv hv0 hv
  calc
    DeGiorgi.bilinFormOfCoeff A hw hv = rhs v := hweak
    _ = rho * DeGiorgi.weakProblemRHSOfField (Ω := Omega) F v := rfl
    _ = rho * ∫ x in Omega, g x * v x := by rw [hrhs_int]
    _ = ∫ x in Omega, rho * (g x * v x) :=
      (integral_const_mul rho _).symm
    _ = ∫ x in Omega, (rho * homDiffSource B u Omega l x) * v x := by
      refine setIntegral_congr_fun hOmega.measurableSet (fun x _hx => ?_)
      simp [g, mul_assoc]

end DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous
