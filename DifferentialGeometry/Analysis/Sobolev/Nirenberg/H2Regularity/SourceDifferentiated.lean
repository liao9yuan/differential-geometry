import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.DifferentiatedSource
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.HomogeneousDifferentiated

/-!
# Differentiated Scalar-Source Weak Equations

This module differentiates a scalar-source weak equation once.  The derivative
of the scalar source and the coefficient-derivative source are assembled as one
square-integrable weak divergence, so the smooth-test identity extends to all
`H₀¹` tests without a separate Poincare estimate.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem hasWeakDiv_add_smul
    {Omega : Set E} (hOmega : IsOpen Omega)
    {F₁ F₂ : E → E} (hF₁ : MemLp F₁ 2 (volume.restrict Omega))
    (hF₂ : MemLp F₂ 2 (volume.restrict Omega))
    {g₁ g₂ : E → ℝ} (hg₁ : MemLp g₁ 2 (volume.restrict Omega))
    (hg₂ : MemLp g₂ 2 (volume.restrict Omega))
    (hdiv₁ : DeGiorgi.HasWeakDiv g₁ F₁ Omega)
    (hdiv₂ : DeGiorgi.HasWeakDiv g₂ F₂ Omega) (c : ℝ) :
    DeGiorgi.HasWeakDiv (fun x => g₁ x + c * g₂ x)
      (fun x => F₁ x + c • F₂ x) Omega := by
  intro phi hphi hphi_cpt hphi_sub
  let hphi_test : DeGiorgi.IsSmoothTestOn Omega phi :=
    ⟨hphi, hphi_cpt, hphi_sub⟩
  let hphi_w : DeGiorgi.MemW1pWitness 2 phi Omega :=
    DeGiorgi.smoothTestWitness hOmega hphi_test
  have hscalar : ∀ a b : ℝ, ⟪a, b⟫_ℝ = a * b := by
    intro a b
    simpa using RCLike.inner_apply' a b
  have hF₁_int : Integrable (fun x => ∑ i : Fin d,
      F₁ x i * (fderiv ℝ phi x) (EuclideanSpace.single i 1))
      (volume.restrict Omega) := by
    refine (DeGiorgi.integrable_divergenceRHSIntegrandOfField hF₁ hphi_w).congr
      (Filter.Eventually.of_forall (fun x => ?_))
    simp [DeGiorgi.divergenceRHSIntegrandOfField, PiLp.inner_apply,
      hphi_w, DeGiorgi.smoothTestWitness, DeGiorgi.smoothGradField,
      hscalar]
  have hF₂_int : Integrable (fun x => ∑ i : Fin d,
      F₂ x i * (fderiv ℝ phi x) (EuclideanSpace.single i 1))
      (volume.restrict Omega) := by
    refine (DeGiorgi.integrable_divergenceRHSIntegrandOfField hF₂ hphi_w).congr
      (Filter.Eventually.of_forall (fun x => ?_))
    simp [DeGiorgi.divergenceRHSIntegrandOfField, PiLp.inner_apply,
      hphi_w, DeGiorgi.smoothTestWitness, DeGiorgi.smoothGradField,
      hscalar]
  have hg₁_int : Integrable (fun x => g₁ x * phi x)
      (volume.restrict Omega) := by
    have hloc := hg₁.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hint :=
      hloc.integrable_smul_left_of_hasCompactSupport hphi.continuous hphi_cpt
    simpa [smul_eq_mul, mul_comm] using hint
  have hg₂_int : Integrable (fun x => g₂ x * phi x)
      (volume.restrict Omega) := by
    have hloc := hg₂.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hint :=
      hloc.integrable_smul_left_of_hasCompactSupport hphi.continuous hphi_cpt
    simpa [smul_eq_mul, mul_comm] using hint
  calc
    ∫ x in Omega, ∑ i : Fin d,
        (F₁ x + c • F₂ x) i *
          (fderiv ℝ phi x) (EuclideanSpace.single i 1) =
        ∫ x in Omega,
          (∑ i : Fin d, F₁ x i *
            (fderiv ℝ phi x) (EuclideanSpace.single i 1)) +
          c * (∑ i : Fin d, F₂ x i *
            (fderiv ℝ phi x) (EuclideanSpace.single i 1)) := by
      refine setIntegral_congr_fun hOmega.measurableSet (fun x _ => ?_)
      change (∑ i : Fin d, (F₁ x i + c * F₂ x i) *
          (fderiv ℝ phi x) (EuclideanSpace.single i 1)) = _
      simp only [add_mul, Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    _ = (∫ x in Omega, ∑ i : Fin d, F₁ x i *
          (fderiv ℝ phi x) (EuclideanSpace.single i 1)) +
        ∫ x in Omega, c * (∑ i : Fin d, F₂ x i *
          (fderiv ℝ phi x) (EuclideanSpace.single i 1)) := by
      rw [integral_add hF₁_int (hF₂_int.const_mul c)]
    _ = (∫ x in Omega, ∑ i : Fin d, F₁ x i *
          (fderiv ℝ phi x) (EuclideanSpace.single i 1)) +
        c * ∫ x in Omega, ∑ i : Fin d, F₂ x i *
          (fderiv ℝ phi x) (EuclideanSpace.single i 1) := by
      rw [integral_const_mul]
    _ = -(∫ x in Omega, g₁ x * phi x) +
        c * (-(∫ x in Omega, g₂ x * phi x)) := by
      rw [hdiv₁ phi hphi hphi_cpt hphi_sub,
        hdiv₂ phi hphi hphi_cpt hphi_sub]
    _ = -((∫ x in Omega, g₁ x * phi x) +
        c * ∫ x in Omega, g₂ x * phi x) := by ring
    _ = -(∫ x in Omega,
        g₁ x * phi x + c * (g₂ x * phi x)) := by
      rw [integral_add hg₁_int (hg₂_int.const_mul c), integral_const_mul]
    _ = -(∫ x in Omega, (g₁ x + c * g₂ x) * phi x) := by
      refine congrArg Neg.neg ?_
      refine setIntegral_congr_fun hOmega.measurableSet (fun x _ => ?_)
      ring

private theorem weak_eq_of_div
    {Omega : Set E} (hOmega : IsOpen Omega)
    (A : DeGiorgi.EllipticCoeff d Omega)
    {w : E → ℝ} (hw : DeGiorgi.MemW1pWitness 2 w Omega)
    {F : E → E} (hF : MemLp F 2 (volume.restrict Omega))
    (hsmooth : ∀ {phi : E → ℝ} (hphi : DeGiorgi.IsSmoothTestOn Omega phi),
      DeGiorgi.bilinFormOfCoeff A hw
        (DeGiorgi.smoothTestWitness hOmega hphi) =
        DeGiorgi.weakProblemRHSOfField (Ω := Omega) F phi)
    {v : E → ℝ} (hv0 : DeGiorgi.MemH01 v Omega)
    (hv : DeGiorgi.MemW1pWitness 2 v Omega) :
    DeGiorgi.bilinFormOfCoeff A hw hv =
      DeGiorgi.weakProblemRHSOfField (Ω := Omega) F v := by
  let rhs : (E → ℝ) → ℝ :=
    DeGiorgi.weakProblemRHSOfField (Ω := Omega) F
  have hrhs_add : ∀ z q : E → ℝ,
      DeGiorgi.MemH01 z Omega → DeGiorgi.MemH01 q Omega →
      rhs (fun x => z x + q x) = rhs z + rhs q := by
    intro z q hz0 hq0
    let hz : DeGiorgi.MemW1pWitness 2 z Omega :=
      DeGiorgi.MemW1p.someWitness (DeGiorgi.MemW01p.memW1p hz0)
    let hq : DeGiorgi.MemW1pWitness 2 q Omega :=
      DeGiorgi.MemW1p.someWitness (DeGiorgi.MemW01p.memW1p hq0)
    have hzq0 : DeGiorgi.MemH01 (fun x => z x + q x) Omega :=
      DeGiorgi.MemW01p.add hz0 hq0
    let hzq : DeGiorgi.MemW1pWitness 2 (fun x => z x + q x) Omega := hz.add hq
    calc
      rhs (fun x => z x + q x) = DeGiorgi.divergenceRHSOfField F hzq :=
        DeGiorgi.weakProblemRHSOfField_eq_of_memH01 hOmega hzq0 hzq
      _ = DeGiorgi.divergenceRHSOfField F hz +
          DeGiorgi.divergenceRHSOfField F hq :=
        DeGiorgi.divergenceRHSOfField_add hF hz hq
      _ = rhs z + rhs q := by
        exact congrArg₂ (· + ·)
          (DeGiorgi.weakProblemRHSOfField_eq_of_memH01 hOmega hz0 hz).symm
          (DeGiorgi.weakProblemRHSOfField_eq_of_memH01 hOmega hq0 hq).symm
  have hrhs_smul : ∀ c : ℝ, ∀ z : E → ℝ,
      DeGiorgi.MemH01 z Omega →
      rhs (fun x => c * z x) = c * rhs z := by
    intro c z hz0
    let hz : DeGiorgi.MemW1pWitness 2 z Omega :=
      DeGiorgi.MemW1p.someWitness (DeGiorgi.MemW01p.memW1p hz0)
    have hcz0 : DeGiorgi.MemH01 (fun x => c * z x) Omega := by
      simpa [Pi.smul_apply, smul_eq_mul] using
        (DeGiorgi.MemW01p.smul c hz0)
    let hcz : DeGiorgi.MemW1pWitness 2 (fun x => c * z x) Omega := hz.smul c
    calc
      rhs (fun x => c * z x) = DeGiorgi.divergenceRHSOfField F hcz :=
        DeGiorgi.weakProblemRHSOfField_eq_of_memH01 hOmega hcz0 hcz
      _ = c * DeGiorgi.divergenceRHSOfField F hz :=
        DeGiorgi.divergenceRHSOfField_smul c hz
      _ = c * rhs z := by
        exact congrArg (c * ·)
          (DeGiorgi.weakProblemRHSOfField_eq_of_memH01 hOmega hz0 hz).symm
  let C_rhs : ℝ :=
    (∫ x, ‖F x‖ ^ (2 : ℝ) ∂(volume.restrict Omega)) ^ (1 / (2 : ℝ))
  have hrhs_bound : ∀ z : E → ℝ, DeGiorgi.MemH01 z Omega →
      ∀ hwz : DeGiorgi.MemW1pWitness 2 z Omega,
      |rhs z| ≤ C_rhs *
        (∫ x, ‖hwz.weakGrad x‖ ^ (2 : ℝ)
          ∂(volume.restrict Omega)) ^ (1 / (2 : ℝ)) := by
    intro z hz0 hwz
    simpa [rhs, C_rhs] using
      (DeGiorgi.weakProblemRHSOfField_bound hOmega hF z hz0 hwz)
  exact DeGiorgi.weak_eq_of_smooth hOmega A rhs
    hrhs_add hrhs_smul C_rhs hrhs_bound hw hsmooth hw v hv0 hv

/-- A canonical first weak partial of a scalar-source solution satisfies the
differentiated scalar-source weak equation. -/
theorem srcDiff_weak_eq
    {Omega : Set E} (hOmega : IsOpen Omega)
    (hOmega_compact : IsCompact (closure Omega))
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
    (hu2 : MemWkp (d := d) 2 2 u Omega) (l : Fin d)
    (hw : DeGiorgi.MemW1pWitness 2
      (chosenWeakPartial' 2 l u Omega) Omega)
    (v : E → ℝ) (hv0 : DeGiorgi.MemH01 v Omega)
    (hv : DeGiorgi.MemW1pWitness 2 v Omega) :
    DeGiorgi.bilinFormOfCoeff A hw hv =
      ∫ x in Omega,
        (chosenWeakPartial' 2 l f Omega x +
          rho * homDiffSource B u Omega l x) * v x
        ∂(volume : Measure E) := by
  classical
  let df : E → ℝ := chosenWeakPartial' 2 l f Omega
  let F₀ : E → E := fun x => WithLp.toLp 2 fun i : Fin d =>
    if i = l then f x else 0
  let F₁ : E → E := homDiffField B u Omega l
  let g₁ : E → ℝ := homDiffSource B u Omega l
  let F : E → E := fun x => F₀ x + rho • F₁ x
  let g : E → ℝ := fun x => df x + rho * g₁ x
  have hf : MemLp f 2 (volume.restrict Omega) := hf1.memW1p.1
  have hdf : MemLp df 2 (volume.restrict Omega) := by
    simpa [df] using chosenWeakPartial'_memLp_of_mem hf1.memW1p l
  have hF₀ : MemLp F₀ 2 (volume.restrict Omega) := by
    refine MemLp.of_eval_piLp ?_
    intro i
    by_cases hi : i = l
    · simpa [F₀, PiLp.toLp_apply, hi] using hf
    · simp [F₀, hi]
  have hF₁ : MemLp F₁ 2 (volume.restrict Omega) := by
    simpa [F₁] using homDiffField_memLp hOmega hOmega_compact B hu2 l
  have hg₁ : MemLp g₁ 2 (volume.restrict Omega) := by
    simpa [g₁] using homDiffSource_memLp hOmega hOmega_compact B hu2 l
  have hF : MemLp F 2 (volume.restrict Omega) := by
    simpa [F] using hF₀.add (hF₁.const_smul rho)
  have hg : MemLp g 2 (volume.restrict Omega) := by
    simpa [g] using hdf.add (hg₁.const_mul rho)
  have hdiv₀ : DeGiorgi.HasWeakDiv df F₀ Omega := by
    have hraw := DeGiorgi.hasWeakDiv_of_parts
      (F := F₀) (G := fun i x => if i = l then df x else 0)
      (fun i => by
        by_cases hi : i = l
        · simpa [F₀, PiLp.toLp_apply, hi] using
            hf.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        · simpa [F₀, PiLp.toLp_apply, hi] using
            (MemLp.zero : MemLp (fun _ : E => (0 : ℝ)) 2
              (volume.restrict Omega)).locallyIntegrable
                (by norm_num : (1 : ℝ≥0∞) ≤ 2))
      (fun i => by
        by_cases hi : i = l
        · simpa [df, hi] using
            hdf.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        · simpa [hi] using
            (MemLp.zero : MemLp (fun _ : E => (0 : ℝ)) 2
              (volume.restrict Omega)).locallyIntegrable
                (by norm_num : (1 : ℝ≥0∞) ≤ 2))
      (fun i => by
        by_cases hi : i = l
        · subst i
          simpa [F₀, df, PiLp.toLp_apply] using
            (chosenWeakPartial'_isWeakPartial_of_mem hf1.memW1p l)
        · intro phi hphi hphi_cpt hphi_sub
          simp [F₀, hi])
    simpa [F₀, df, PiLp.toLp_apply] using hraw
  have hdiv₁ : DeGiorgi.HasWeakDiv g₁ F₁ Omega := by
    simpa [F₁, g₁] using homDiff_hasDiv hOmega hOmega_compact B hu2 l
  have hdiv : DeGiorgi.HasWeakDiv g F Omega := by
    simpa [F, g] using
      hasWeakDiv_add_smul hOmega hF₀ hF₁ hdf hg₁ hdiv₀ hdiv₁ rho
  have hsmooth : ∀ {phi : E → ℝ} (hphi : DeGiorgi.IsSmoothTestOn Omega phi),
      DeGiorgi.bilinFormOfCoeff A hw
          (DeGiorgi.smoothTestWitness hOmega hphi) =
        DeGiorgi.weakProblemRHSOfField (Ω := Omega) F phi := by
    intro phi hphi
    have hleft := diff_bilin_scaled hOmega B hcoeff hu2 l hw hphi
    have hdiff := srcSol_diff_id hOmega hu hweak hf1 B hrho hcoeff hu2 l
      hphi.1 hphi.2.1 hphi.2.2
    have hfield_int :
        (∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
          (fderiv ℝ (fun y : E => B.a y i j) x)
              (EuclideanSpace.single l 1) *
            chosenWeakPartial' 2 j u Omega x *
            (fderiv ℝ phi x) (EuclideanSpace.single i 1)) =
          ∫ x in Omega, ∑ i : Fin d,
            F₁ x i * (fderiv ℝ phi x) (EuclideanSpace.single i 1) := by
      refine setIntegral_congr_fun hOmega.measurableSet (fun x _ => ?_)
      simp [F₁, homDiffField, PiLp.toLp_apply, Finset.sum_mul]
    have hdiv₁_test := hdiv₁ phi hphi.1 hphi.2.1 hphi.2.2
    have hB_source :
        (∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
          B.a x i j *
            chosenWeakPartial' 2 j
              (chosenWeakPartial' 2 l u Omega) Omega x *
            (fderiv ℝ phi x) (EuclideanSpace.single i 1)) =
          rho⁻¹ * (∫ x in Omega, df x * phi x) +
            (∫ x in Omega, g₁ x * phi x) := by
      calc
        _ = rho⁻¹ * (∫ x in Omega, df x * phi x) -
            (∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
              (fderiv ℝ (fun y : E => B.a y i j) x)
                  (EuclideanSpace.single l 1) *
                chosenWeakPartial' 2 j u Omega x *
                (fderiv ℝ phi x) (EuclideanSpace.single i 1)) := by
              simpa [df] using hdiff
        _ = rho⁻¹ * (∫ x in Omega, df x * phi x) -
            (∫ x in Omega, ∑ i : Fin d,
              F₁ x i * (fderiv ℝ phi x) (EuclideanSpace.single i 1)) := by
              rw [hfield_int]
        _ = _ := by rw [hdiv₁_test]; ring
    have hrhs_int :
        DeGiorgi.weakProblemRHSOfField (Ω := Omega) F phi =
          ∫ x in Omega, g x * phi x :=
      DeGiorgi.weakRHS_eq_integral hOmega hF hg hdiv
        (DeGiorgi.smoothTest_memH01 hOmega hphi)
        (DeGiorgi.smoothTestWitness hOmega hphi)
    calc
      DeGiorgi.bilinFormOfCoeff A hw
          (DeGiorgi.smoothTestWitness hOmega hphi) =
          rho * (∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
            B.a x i j *
              chosenWeakPartial' 2 j
                (chosenWeakPartial' 2 l u Omega) Omega x *
              (fderiv ℝ phi x) (EuclideanSpace.single i 1)) := hleft
      _ = (∫ x in Omega, df x * phi x) +
          rho * (∫ x in Omega, g₁ x * phi x) := by
        rw [hB_source]
        field_simp [hrho.ne']
      _ = ∫ x in Omega, (df x + rho * g₁ x) * phi x := by
        rw [← integral_const_mul, ← integral_add]
        · refine setIntegral_congr_fun hOmega.measurableSet (fun x _ => ?_)
          ring
        · exact hdf.integrable_mul
            (DeGiorgi.smoothTestWitness hOmega hphi).memLp
        · refine ((hg₁.const_mul rho).integrable_mul
              (DeGiorgi.smoothTestWitness hOmega hphi).memLp).congr
            (Filter.Eventually.of_forall (fun x => ?_))
          simp only [Pi.mul_apply, mul_assoc]
      _ = ∫ x in Omega, g x * phi x := by rfl
      _ = DeGiorgi.weakProblemRHSOfField (Ω := Omega) F phi := hrhs_int.symm
  have hweak_diff := weak_eq_of_div hOmega A hw hF hsmooth hv0 hv
  have hrhs_int :
      DeGiorgi.weakProblemRHSOfField (Ω := Omega) F v =
        ∫ x in Omega, g x * v x :=
    DeGiorgi.weakRHS_eq_integral hOmega hF hg hdiv hv0 hv
  calc
    DeGiorgi.bilinFormOfCoeff A hw hv =
        DeGiorgi.weakProblemRHSOfField (Ω := Omega) F v := hweak_diff
    _ = ∫ x in Omega, g x * v x := hrhs_int
    _ = ∫ x in Omega,
        (chosenWeakPartial' 2 l f Omega x +
          rho * homDiffSource B u Omega l x) * v x := by rfl

end DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous
