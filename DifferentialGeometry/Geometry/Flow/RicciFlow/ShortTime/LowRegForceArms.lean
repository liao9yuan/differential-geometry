import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegSmoothBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegGalerkinSol
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifNZeroBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseAction

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

def galCoreRep (g₀ : SmoothRiemannianMetric I M) (R : ℝ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    SmoothCcTensor g₀ 0 2 :=
  (min 1 (R / ‖galLowView (I := I) (M := M) g₀ 1
      (finiteEigenComboHs (I := I) (M := M) g₀ S c (((1 : ℕ) : ℝ) + 2))‖)) •
    finiteEigenCombo (I := I) (M := M) g₀ S c

theorem galCoreRep_eq (g₀ : SmoothRiemannianMetric I M) (R : ℝ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
        (galCoreRep (I := I) (M := M) g₀ R S c) =
      galTameStateC (I := I) (M := M) g₀ 1 R S c := by
  rw [galCoreRep, smoothCcToTensorHs_smul, ← finiteEigenComboHs_eq, galTameStateC]

theorem galRepHs_scale (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    {R : ℝ} (hR : 0 ≤ R)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    let θ : ℝ := min 1 (R / ‖galLowView (I := I) (M := M) g₀ 1
      (finiteEigenComboHs (I := I) (M := M) g₀ F c (((1 : ℕ) : ℝ) + 2))‖)
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R F c))‖ ≤
      θ * Real.sqrt (∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i σ * (c i) ^ 2) := by
  let θ : ℝ := min 1 (R / ‖galLowView (I := I) (M := M) g₀ 1
    (finiteEigenComboHs (I := I) (M := M) g₀ F c (((1 : ℕ) : ℝ) + 2))‖)
  have hθ0 : 0 ≤ θ := by
    dsimp only [θ]
    exact le_min zero_le_one (div_nonneg hR (norm_nonneg _))
  refine (norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ σ _).trans ?_
  have hrep : galCoreRep (I := I) (M := M) g₀ R F c =
      θ • finiteEigenCombo (I := I) (M := M) g₀ F c := rfl
  rw [hrep, smoothCcToTensorHs_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hθ0]
  have hnorm :
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
          (finiteEigenCombo (I := I) (M := M) g₀ F c)‖ =
        Real.sqrt (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i σ * (c i) ^ 2) := by
    rw [← finiteEigenComboHs_eq]
    rw [← Real.sqrt_sq (norm_nonneg _),
      finiteEigenCombo_spectral_normSq (I := I) (M := M)]
    rfl
  rw [hnorm]

theorem galRepHs_le (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    {R : ℝ} (hR : 0 ≤ R)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R F c))‖ ≤
      Real.sqrt (∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i σ * (c i) ^ 2) := by
  refine (norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ σ _).trans ?_
  let θ : ℝ := min 1 (R / ‖galLowView (I := I) (M := M) g₀ 1
    (finiteEigenComboHs (I := I) (M := M) g₀ F c (((1 : ℕ) : ℝ) + 2))‖)
  have hθ0 : 0 ≤ θ := by
    dsimp only [θ]
    exact le_min zero_le_one (div_nonneg hR (norm_nonneg _))
  have hθ1 : θ ≤ 1 := by
    dsimp only [θ]
    exact min_le_left _ _
  have hrep : galCoreRep (I := I) (M := M) g₀ R F c =
      θ • finiteEigenCombo (I := I) (M := M) g₀ F c := rfl
  rw [hrep, smoothCcToTensorHs_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hθ0]
  have hnorm :
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
          (finiteEigenCombo (I := I) (M := M) g₀ F c)‖ =
        Real.sqrt (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i σ * (c i) ^ 2) := by
    rw [← finiteEigenComboHs_eq]
    rw [← Real.sqrt_sq (norm_nonneg _),
      finiteEigenCombo_spectral_normSq (I := I) (M := M)]
    rfl
  calc
    θ * ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (finiteEigenCombo (I := I) (M := M) g₀ F c)‖ ≤
        1 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
          (finiteEigenCombo (I := I) (M := M) g₀ F c)‖ :=
      mul_le_mul_of_nonneg_right hθ1 (norm_nonneg _)
    _ = _ := by rw [one_mul, hnorm]

theorem galCoreRep_ball (g₀ : SmoothRiemannianMetric I M) {R : ℝ} (hR : 0 ≤ R)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
        (smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
          (galCoreRep (I := I) (M := M) g₀ R S c))‖ ≤ R := by
  rw [galCoreRep_eq]
  exact galTameStateC_mem (I := I) (M := M) g₀ 1 hR S c

theorem galState_core (g₀ : SmoothRiemannianMetric I M) {R : ℝ} (hR : 0 ≤ R)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    (⟨galTameStateC (I := I) (M := M) g₀ 1 R S c,
        galTameStateC_mem (I := I) (M := M) g₀ 1 hR S c⟩ :
        lowerState (I := I) (M := M) g₀ 1 R) ∈
      smoothCore (I := I) (M := M) g₀ R :=
  ⟨galCoreRep (I := I) (M := M) g₀ R S c,
    galCoreRep_eq (I := I) (M := M) g₀ R S c⟩

theorem galRepFib (g₀ : SmoothRiemannianMetric I M) {R δ : ℝ} (hR : 0 ≤ R)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R S c))) δ :=
  hreal _ (symm_h2_of_state (I := I) (M := M) g₀
    (galCoreRep (I := I) (M := M) g₀ R S c)
    (galCoreRep_ball (I := I) (M := M) g₀ hR S c))

theorem lowregFibZero (g₀ : SmoothRiemannianMetric I M) {R δ : ℝ} (hR : 0 ≤ R)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ) :
    gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ := by
  refine hreal (0 : SmoothCcTensor g₀ 0 2) ?_
  rw [smoothCcToTensorHs_zero, norm_zero]
  exact hR

theorem galN_eval (g₀ : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g₀ hδ hreal))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    lowRegN (I := I) (M := M) g₀ g₀ hR hδ hreal
        ⟨galTameStateC (I := I) (M := M) g₀ 1 R S c,
          galTameStateC_mem (I := I) (M := M) g₀ 1 hR.le S c⟩ =
      deTurckSmoothN (I := I) (M := M) g₀ g₀ 1
        (symmS (I := I) (M := M) g₀
          (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
        (galRepFib (I := I) (M := M) g₀ hR.le hreal S c) := by
  have hsub : (⟨galTameStateC (I := I) (M := M) g₀ 1 R S c,
        galTameStateC_mem (I := I) (M := M) g₀ 1 hR.le S c⟩ :
        lowerState (I := I) (M := M) g₀ 1 R) =
      ⟨smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
          (galCoreRep (I := I) (M := M) g₀ R S c),
        galCoreRep_ball (I := I) (M := M) g₀ hR.le S c⟩ :=
    Subtype.ext (galCoreRep_eq (I := I) (M := M) g₀ R S c).symm
  rw [hsub]
  exact lowRegN_on_smooth (I := I) (M := M) g₀ g₀ hR hδ hreal hcore
    (galCoreRep (I := I) (M := M) g₀ R S c)
    (galCoreRep_ball (I := I) (M := M) g₀ hR.le S c)

theorem galArmId (g₀ : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g₀ hδ hreal))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    lowRegN (I := I) (M := M) g₀ g₀ hR hδ hreal
          ⟨galTameStateC (I := I) (M := M) g₀ 1 R S c,
            galTameStateC_mem (I := I) (M := M) g₀ 1 hR.le S c⟩ -
        lowRegN (I := I) (M := M) g₀ g₀ hR hδ hreal
          ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩ =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
        ((lowBaseData (I := I) (M := M) g₀ g₀
              (symmS (I := I) (M := M) g₀
                (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
              (galRepFib (I := I) (M := M) g₀ hR.le hreal S c)
              (lowregFibZero (I := I) (M := M) g₀ hR.le hreal)).a2
            (I := I) (M := M)
            (symmS (I := I) (M := M) g₀
              (galCoreRep (I := I) (M := M) g₀ R S c)) +
          (lowBaseData (I := I) (M := M) g₀ g₀
              (symmS (I := I) (M := M) g₀
                (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
              (galRepFib (I := I) (M := M) g₀ hR.le hreal S c)
              (lowregFibZero (I := I) (M := M) g₀ hR.le hreal)).a1
            (I := I) (M := M)
            (symmS (I := I) (M := M) g₀
              (galCoreRep (I := I) (M := M) g₀ R S c))) := by
  obtain ⟨_, _, hsplit⟩ := lowData_split (I := I) (M := M) g₀ g₀
  calc lowRegN (I := I) (M := M) g₀ g₀ hR hδ hreal
          ⟨galTameStateC (I := I) (M := M) g₀ 1 R S c,
            galTameStateC_mem (I := I) (M := M) g₀ 1 hR.le S c⟩ -
        lowRegN (I := I) (M := M) g₀ g₀ hR hδ hreal
          ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩
      = deTurckSmoothN (I := I) (M := M) g₀ g₀ 1
            (symmS (I := I) (M := M) g₀
              (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
            (galRepFib (I := I) (M := M) g₀ hR.le hreal S c) -
          deTurckSmoothN (I := I) (M := M) g₀ g₀ 1
            (0 : SmoothCcTensor g₀ 0 2) hδ
            (lowregFibZero (I := I) (M := M) g₀ hR.le hreal) := by
        rw [galN_eval (I := I) (M := M) g₀ hR hδ hreal hcore S c,
          nZero_eq_static (I := I) (M := M) g₀ g₀ hR hδ hreal hcore,
          ← deTurckSmoothN_zero (I := I) (M := M) g₀ g₀ 1 hδ
            (lowregFibZero (I := I) (M := M) g₀ hR.le hreal)]
    _ = smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
          (deTurckSmoothRemainder (I := I) g₀ g₀
              (symmS (I := I) (M := M) g₀
                (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
              (galRepFib (I := I) (M := M) g₀ hR.le hreal S c) -
            deTurckSmoothRemainder (I := I) g₀ g₀
              (0 : SmoothCcTensor g₀ 0 2) hδ
              (lowregFibZero (I := I) (M := M) g₀ hR.le hreal)) :=
        deTurckSmoothN_sub_eq_smoothCcToTensorHs_remainderSub (I := I) (M := M)
          g₀ g₀ 1 _ _ hδ _ hδ _
    _ = _ :=
        congrArg (smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ))
          (hsplit _
            (ccTensorBilin_symmS_symm
              (I := I) (M := M) g₀ (galCoreRep (I := I) (M := M) g₀ R S c))
            hδ3 hδ0 (galRepFib (I := I) (M := M) g₀ hR.le hreal S c)
            (lowregFibZero (I := I) (M := M) g₀ hR.le hreal)).1

theorem galArmCap (g₀ : SmoothRiemannianMetric I M) {R δ : ℝ}
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
            ((lowBaseData (I := I) (M := M) g₀ g₀
              (symmS (I := I) (M := M) g₀
                (galCoreRep (I := I) (M := M) g₀ R S c)) hδ
              (galRepFib (I := I) (M := M) g₀ hR hreal S c)
              (lowregFibZero (I := I) (M := M) g₀ hR hreal)).C2.toSection x) ≤
          Cδ ^ 2 := by
  obtain ⟨K, hK, hsplit⟩ := lowData_split (I := I) (M := M) g₀ g₀
  refine ⟨K * (δ / (1 - δ) ^ 2),
    mul_nonneg hK (div_nonneg hδ0 (sq_nonneg _)), ?_⟩
  intro S c x
  exact (hsplit _
    (ccTensorBilin_symmS_symm (I := I) (M := M)
      g₀ (galCoreRep (I := I) (M := M) g₀ R S c))
    hδ3 hδ0 (galRepFib (I := I) (M := M) g₀ hR hreal S c)
    (lowregFibZero (I := I) (M := M) g₀ hR hreal)).2 x

open scoped Classical in
theorem galForceArm (g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B1 ρ P : ℝ} (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g₀ hδ
      (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
        hP.le hreal)))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    galTameForce (I := I) (M := M) g₀ 1
        (lowregStateRad_pos hCtop hB1 hρ hP).le
        (lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal) S c i =
      if i ∈ S then
        (lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal
            ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
              (lowregStateRad_pos hCtop hB1 hρ hP).le⟩).coeff i +
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
            ((lowBaseData (I := I) (M := M) g₀ g₀
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
              (lowBaseData (I := I) (M := M) g₀ g₀
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
  classical
  have harm := galArmId (I := I) (M := M) g₀
    (lowregStateRad_pos hCtop hB1 hρ hP) hδ hδ0 hδ3
    (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
      hP.le hreal) hcore S c
  have hval : lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal
        ⟨galTameStateC (I := I) (M := M) g₀ 1
            (lowregStateRad Ctop B1 ρ P) S c,
          galTameStateC_mem (I := I) (M := M) g₀ 1
            (lowregStateRad_pos hCtop hB1 hρ hP).le S c⟩ =
      lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal
          ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
            (lowregStateRad_pos hCtop hB1 hρ hP).le⟩ +
        smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
          ((lowBaseData (I := I) (M := M) g₀ g₀
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
            (lowBaseData (I := I) (M := M) g₀ g₀
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
