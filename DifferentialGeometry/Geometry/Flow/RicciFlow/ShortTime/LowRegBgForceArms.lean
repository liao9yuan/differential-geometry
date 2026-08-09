import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegForceArms

/-!
# Fixed-background forcing arms

This file begins the fixed-background Galerkin forcing layer.  The Sobolev
scale and spectral data remain attached to the state metric `g₀`, while the
Ricci--DeTurck nonlinearity is evaluated against an independent background
metric `g_bg`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- The dense fixed-background nonlinearity on a Galerkin trajectory is the
genuine smooth Ricci--DeTurck nonlinearity at its smooth representative. -/
theorem galN_evalBg (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal
        ⟨galTameStateC (I := I) (M := M) g₀ 1 R S c,
          galTameStateC_mem (I := I) (M := M) g₀ 1 hR.le S c⟩ =
      deTurckSmoothN (I := I) (M := M) g₀ g_bg 1
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
        (galRepFib (I := I) (M := M) g₀ hR.le hreal S c) := by
  have hsub :
      (⟨galTameStateC (I := I) (M := M) g₀ 1 R S c,
        galTameStateC_mem (I := I) (M := M) g₀ 1 hR.le S c⟩ :
          lowerState (I := I) (M := M) g₀ 1 R) =
        ⟨smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
            (galCoreRep (I := I) (M := M) g₀ R S c),
          galCoreRep_ball (I := I) (M := M) g₀ hR.le S c⟩ :=
    Subtype.ext (galCoreRep_eq (I := I) (M := M) g₀ R S c).symm
  rw [hsub]
  exact lowRegN_on_smooth (I := I) (M := M) g₀ g_bg hR hδ hreal hcore
    (galCoreRep (I := I) (M := M) g₀ R S c)
    (galCoreRep_ball (I := I) (M := M) g₀ hR.le S c)

/-- Along a fixed-background Galerkin trajectory, the forcing minus its static
seed is the order-one embedding of the two canonical low-base arms. -/
theorem galArmIdBg (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal
          ⟨galTameStateC (I := I) (M := M) g₀ 1 R S c,
            galTameStateC_mem (I := I) (M := M) g₀ 1 hR.le S c⟩ -
        lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal
          ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩ =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
        ((lowBaseData (I := I) (M := M) g₀ g_bg
              (symmS (I := I) (M := M) g₀
                (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
              (galRepFib (I := I) (M := M) g₀ hR.le hreal S c)
              (lowregFibZero (I := I) (M := M) g₀ hR.le hreal)).a2
            (I := I) (M := M)
            (symmS (I := I) (M := M) g₀
              (galCoreRep (I := I) (M := M) g₀ R S c)) +
          (lowBaseData (I := I) (M := M) g₀ g_bg
              (symmS (I := I) (M := M) g₀
                (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
              (galRepFib (I := I) (M := M) g₀ hR.le hreal S c)
              (lowregFibZero (I := I) (M := M) g₀ hR.le hreal)).a1
            (I := I) (M := M)
            (symmS (I := I) (M := M) g₀
              (galCoreRep (I := I) (M := M) g₀ R S c))) := by
  obtain ⟨_, _, hsplit⟩ := lowData_split (I := I) (M := M) g₀ g_bg
  calc
    lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal
          ⟨galTameStateC (I := I) (M := M) g₀ 1 R S c,
            galTameStateC_mem (I := I) (M := M) g₀ 1 hR.le S c⟩ -
        lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal
          ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩ =
      deTurckSmoothN (I := I) (M := M) g₀ g_bg 1
            (symmS (I := I) (M := M) g₀
              (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
            (galRepFib (I := I) (M := M) g₀ hR.le hreal S c) -
          deTurckSmoothN (I := I) (M := M) g₀ g_bg 1
            (0 : SmoothCcTensor g₀ 0 2) hδ
            (lowregFibZero (I := I) (M := M) g₀ hR.le hreal) := by
        rw [galN_evalBg (I := I) (M := M) g₀ g_bg hR hδ hreal hcore S c,
          nZero_eq_static (I := I) (M := M) g₀ g_bg hR hδ hreal hcore,
          ← deTurckSmoothN_zero (I := I) (M := M) g₀ g_bg 1 hδ
            (lowregFibZero (I := I) (M := M) g₀ hR.le hreal)]
    _ = smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
          (deTurckSmoothRemainder (I := I) g₀ g_bg
              (symmS (I := I) (M := M) g₀
                (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
              (galRepFib (I := I) (M := M) g₀ hR.le hreal S c) -
            deTurckSmoothRemainder (I := I) g₀ g_bg
              (0 : SmoothCcTensor g₀ 0 2) hδ
              (lowregFibZero (I := I) (M := M) g₀ hR.le hreal)) :=
        deTurckSmoothN_sub_eq_smoothCcToTensorHs_remainderSub
          (I := I) (M := M) g₀ g_bg 1 _ _ hδ _ hδ _
    _ = _ :=
        congrArg (smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ))
          (hsplit _
            (DeTurckRemainderTameLipschitz.ccTensorBilin_symmS_symm
              (I := I) (M := M) g₀
              (galCoreRep (I := I) (M := M) g₀ R S c))
            hδ3 hδ0 (galRepFib (I := I) (M := M) g₀ hR.le hreal S c)
            (lowregFibZero (I := I) (M := M) g₀ hR.le hreal)).1

/-- The complete second-order coefficient along a fixed-background Galerkin
trajectory has one cap independent of the mode set and coefficients. -/
theorem galArmCapBg (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ) :
    ∃ Cδ : ℝ, 0 ≤ Cδ ∧
      ∀ (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
        (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x
            ((lowBaseData (I := I) (M := M) g₀ g_bg
              (symmS (I := I) (M := M) g₀
                (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
              (galRepFib (I := I) (M := M) g₀ hR hreal S c)
              (lowregFibZero (I := I) (M := M) g₀ hR hreal)).C2.toSection x) ≤
          Cδ ^ 2 := by
  obtain ⟨K, hK, hsplit⟩ := lowData_split (I := I) (M := M) g₀ g_bg
  refine ⟨K * (δ / (1 - δ) ^ 2),
    mul_nonneg hK (div_nonneg hδ0 (sq_nonneg _)), ?_⟩
  intro S c x
  exact (hsplit _
    (DeTurckRemainderTameLipschitz.ccTensorBilin_symmS_symm (I := I) (M := M)
      g₀ (galCoreRep (I := I) (M := M) g₀ R S c))
    hδ3 hδ0 (galRepFib (I := I) (M := M) g₀ hR hreal S c)
      (lowregFibZero (I := I) (M := M) g₀ hR hreal)).2 x

/-- The seed-subtracted forcing arm for an arbitrary fixed DeTurck background.

The Sobolev scale, eigenbasis, and trajectory representative stay attached to
`g₀`; only the second slot of `lowBaseData` is freed to `g_bg`. -/
def galArmVecBg (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ) :=
  smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
    ((lowBaseData (I := I) (M := M) g₀ g_bg
          (symmS (I := I) (M := M) g₀
            (galCoreRep (I := I) (M := M) g₀ R F c)) hδ
          (galRepFib (I := I) (M := M) g₀ hR hreal F c)
          (lowregFibZero (I := I) (M := M) g₀ hR hreal)).a2
        (I := I) (M := M)
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R F c)) +
      (lowBaseData (I := I) (M := M) g₀ g_bg
          (symmS (I := I) (M := M) g₀
            (galCoreRep (I := I) (M := M) g₀ R F c)) hδ
          (galRepFib (I := I) (M := M) g₀ hR hreal F c)
          (lowregFibZero (I := I) (M := M) g₀ hR hreal)).a1
        (I := I) (M := M)
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R F c)))

open scoped Classical in
/-- Each fixed-background Galerkin forcing coordinate is the static seed plus
the embedded low-base arm sum on the truncation, and vanishes off it. -/
theorem galForceArmBg (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ Ctop B1 ρ P : ℝ} (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ
      (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
        hP.le hreal)))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    galTameForce (I := I) (M := M) g₀ 1
        (lowregStateRad_pos hCtop hB1 hρ hP).le
        (lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
        S c i =
      if i ∈ S then
        (lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal
            ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
              (lowregStateRad_pos hCtop hB1 hρ hP).le⟩).coeff i +
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
            ((lowBaseData (I := I) (M := M) g₀ g_bg
                  (symmS (I := I) (M := M) g₀
                    (galCoreRep (I := I) (M := M) g₀
                      (lowregStateRad Ctop B1 ρ P) S c)) hδ
                  (galRepFib (I := I) (M := M) g₀
                    (lowregStateRad_pos hCtop hB1 hρ hP).le
                    (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal) S c)
                  (lowregFibZero (I := I) (M := M) g₀
                    (lowregStateRad_pos hCtop hB1 hρ hP).le
                    (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal))).a2 (I := I) (M := M)
                (symmS (I := I) (M := M) g₀
                  (galCoreRep (I := I) (M := M) g₀
                    (lowregStateRad Ctop B1 ρ P) S c)) +
              (lowBaseData (I := I) (M := M) g₀ g_bg
                  (symmS (I := I) (M := M) g₀
                    (galCoreRep (I := I) (M := M) g₀
                      (lowregStateRad Ctop B1 ρ P) S c)) hδ
                  (galRepFib (I := I) (M := M) g₀
                    (lowregStateRad_pos hCtop hB1 hρ hP).le
                    (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal) S c)
                  (lowregFibZero (I := I) (M := M) g₀
                    (lowregStateRad_pos hCtop hB1 hρ hP).le
                    (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal))).a1 (I := I) (M := M)
                (symmS (I := I) (M := M) g₀
                  (galCoreRep (I := I) (M := M) g₀
                    (lowregStateRad Ctop B1 ρ P) S c)))).coeff i
      else 0 := by
  have harm := galArmIdBg (I := I) (M := M) g₀ g_bg
    (lowregStateRad_pos hCtop hB1 hρ hP) hδ hδ0 hδ3
    (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
      hP.le hreal) hcore S c
  have hval :
      lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal
          ⟨galTameStateC (I := I) (M := M) g₀ 1
              (lowregStateRad Ctop B1 ρ P) S c,
            galTameStateC_mem (I := I) (M := M) g₀ 1
              (lowregStateRad_pos hCtop hB1 hρ hP).le S c⟩ =
        lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal
            ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
              (lowregStateRad_pos hCtop hB1 hρ hP).le⟩ +
          smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
            ((lowBaseData (I := I) (M := M) g₀ g_bg
                  (symmS (I := I) (M := M) g₀
                    (galCoreRep (I := I) (M := M) g₀
                      (lowregStateRad Ctop B1 ρ P) S c)) hδ
                  (galRepFib (I := I) (M := M) g₀
                    (lowregStateRad_pos hCtop hB1 hρ hP).le
                    (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal) S c)
                  (lowregFibZero (I := I) (M := M) g₀
                    (lowregStateRad_pos hCtop hB1 hρ hP).le
                    (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal))).a2 (I := I) (M := M)
                (symmS (I := I) (M := M) g₀
                  (galCoreRep (I := I) (M := M) g₀
                    (lowregStateRad Ctop B1 ρ P) S c)) +
              (lowBaseData (I := I) (M := M) g₀ g_bg
                  (symmS (I := I) (M := M) g₀
                    (galCoreRep (I := I) (M := M) g₀
                      (lowregStateRad Ctop B1 ρ P) S c)) hδ
                  (galRepFib (I := I) (M := M) g₀
                    (lowregStateRad_pos hCtop hB1 hρ hP).le
                    (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal) S c)
                  (lowregFibZero (I := I) (M := M) g₀
                    (lowregStateRad_pos hCtop hB1 hρ hP).le
                    (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal))).a1 (I := I) (M := M)
                (symmS (I := I) (M := M) g₀
                  (galCoreRep (I := I) (M := M) g₀
                    (lowregStateRad Ctop B1 ρ P) S c))) :=
    sub_eq_iff_eq_add'.mp harm
  rw [galTameForce_apply]
  by_cases hi : i ∈ S
  · rw [if_pos hi, if_pos hi, hval, tensorHs.add_coeff]
  · rw [if_neg hi, if_neg hi]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
