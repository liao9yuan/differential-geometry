import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralEigenSeriesJointGram
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralPointwiseFlowDeriv
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Integration.L2.ParametricFiberInnerSmooth
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.SimpLemmas

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private theorem exists_smoothCcTensor_of_allOrder_spectralMass
    (g₀ : SmoothRiemannianMetric I M)
    (d : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hmass : ∀ σ : ℝ, 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, tensorSobolevWeight (I := I) (M := M) i σ * (d i) ^ 2 ≤ B i) :
    ∃ S : SmoothCcTensor g₀ 0 2, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i = d i := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  obtain ⟨B0, hB0s, hB0le⟩ := hmass 0 le_rfl
  set v0 : tensorHs (I := I) (M := M) g₀ 0 2 0 :=
    tensorHs_of_spectralMass_majorant (I := I) (M := M) d B0 hB0s hB0le with hv0_def
  set u : TensorL2 0 2 g₀ :=
    tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc le_rfl v0 with hu_def
  have hu_coeff : ∀ i, tensorL2Coeff (I := I) (M := M) hc u i = d i := by
    intro i
    rw [hu_def, tensorHsToL2_tensorL2Coeff]
    simp only [hv0_def, tensorHs_of_spectralMass_majorant_coeff]
  have hsum_u : ∀ σ : ℝ, 0 ≤ σ →
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g₀ 0 2 =>
        tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) hc u i) ^ 2) := by
    intro σ hσ
    obtain ⟨B, hBs, hBle⟩ := hmass σ hσ
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hBs
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _)
    · rw [hu_coeff i]; exact hBle i
  have hmem : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ vσ : tensorHs (I := I) (M := M) g₀ 0 2 σ,
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc hσ vσ = u :=
    allHs_of_weighted_summable_pub (I := I) (M := M) g₀ u hsum_u
  obtain ⟨S, hS⟩ := spectralSmoothRealizesAsSmooth_holds (I := I) (M := M) (g := g₀) u hmem
  refine ⟨S, fun i => ?_⟩
  have hSL2 : SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S = u := by
    rw [show SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S
        = (S : TensorL2 0 2 g₀) from rfl, hS]
  rw [hSL2, hu_coeff i]

private def deTurckRHSReconSection (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    SmoothCcTensor g₀ 0 2 :=
  { toSection :=
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection
    hasCompactSupport :=
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).hasCompactSupport }

private theorem deTurckRHSSection_realize_path_tensorInner_eigenSmooth_jointContMDiffOn
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
          ((Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i).toFun
            p.1)
          ((deTurckRHSReconSection (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toFun p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
  sorry

private theorem deTurckRemainder_pathCoeff_timeContDiff
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      ContDiffOn ℝ ∞ (fun t => tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i)
        (Set.Icc (0 : ℝ) T) := by
  classical
  intro i
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  have hsplit : ∀ t : ℝ,
      tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i =
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckRHSReconSection (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i
          - tensorL2Coeff (I := I) (M := M) hc
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 (F t))) i := by
    intro t
    have hrem :
        deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t)
          = deTurckRHSReconSection (I := I) g₀ g_bg (F t) hδ_lt (hδ t)
            - rawTensorConnLapSmooth (I := I) g₀ 0 2 (F t) := by
      rfl
    rw [hrem, SmoothCcTensor.toL2_sub]
    unfold tensorL2Coeff
    rw [map_sub]
    rfl
  refine ContDiffOn.congr ?_ (fun t _ => hsplit t)
  refine ContDiffOn.sub ?_ ?_
  · have hbridge : ∀ t : ℝ,
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckRHSReconSection (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i =
          (inner ℝ (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i)
            (deTurckRHSReconSection (I := I) g₀ g_bg (F t) hδ_lt (hδ t)) : ℝ) := by
      intro t
      rw [tensorL2Coeff_eq_inner,
        Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_apply,
        ← Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_toL2 (I := I) (M := M) g₀ 0 2 i,
        ← SmoothCcTensor.toL2_apply
          (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i),
        SmoothCcTensor.inner_toL2]
    refine ContDiffOn.congr ?_ (fun t _ => hbridge t)
    exact DifferentialGeometry.Integral.L2.contDiffOn_integral_fiberInner_of_jointContMDiffOn_Icc
      (I := I) (M := M) g₀
      (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i)
      (fun t => deTurckRHSReconSection (I := I) g₀ g_bg (F t) hδ_lt (hδ t))
      (deTurckRHSSection_realize_path_tensorInner_eigenSmooth_jointContMDiffOn (I := I) (M := M)
        g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass i)
  · have hraw : ∀ t ∈ Set.Icc (0 : ℝ) T,
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 (F t))) i =
          -i.lambda * φ i t := by
      intro t ht
      rw [tensorL2Coeff_ofCompact_rawTensorConnLapSmooth (I := I) (M := M) g₀ hc (F t) i,
        hcoeff t ht i]
    refine ContDiffOn.congr ?_ (fun t ht => hraw t ht)
    exact contDiffOn_const.mul (hφ_smooth i).contDiffOn

private theorem deTurckRemainder_pathCoeff_timeJet_allOrderMass
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDerivWithin j (fun s => tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                  (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
                (Set.Icc (0 : ℝ) T) t) ^ 2 ≤ B i :=
  sorry

theorem deTurckRemainder_path_coeff_timeJet_withMass
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ∃ Rjet : ℕ → ℝ → SmoothCcTensor g₀ 0 2,
      (∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
          ContDiffOn ℝ ∞ (fun t => tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i)
            (Set.Icc (0 : ℝ) T)) ∧
        (∀ (j : ℕ) (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            iteratedDerivWithin j (fun s => tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
              (Set.Icc (0 : ℝ) T) t =
              tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjet j t)) i) ∧
        (∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
          ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
            ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
              tensorSobolevWeight (I := I) (M := M) i σ *
                  (tensorL2Coeff (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                    (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjet j t)) i) ^ 2 ≤ B i) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  set cpath : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i t => tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i with hcpath_def
  have hsmooth : ∀ i, ContDiffOn ℝ ∞ (cpath i) (Set.Icc (0 : ℝ) T) :=
    deTurckRemainder_pathCoeff_timeContDiff (I := I) (M := M)
      g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  have hmass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDerivWithin j (cpath i) (Set.Icc (0 : ℝ) T) t) ^ 2 ≤ B i :=
    deTurckRemainder_pathCoeff_timeJet_allOrderMass (I := I) (M := M)
      g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  have hconstruct : ∀ (j : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
      ∃ S : SmoothCcTensor g₀ 0 2, ∀ i,
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i =
          iteratedDerivWithin j (cpath i) (Set.Icc (0 : ℝ) T) t := by
    intro j t ht
    refine exists_smoothCcTensor_of_allOrder_spectralMass (I := I) (M := M)
      g₀ (fun i => iteratedDerivWithin j (cpath i) (Set.Icc (0 : ℝ) T) t) (fun σ hσ => ?_)
    obtain ⟨B, hBs, hBle⟩ := hmass j σ hσ
    exact ⟨B, hBs, fun i => hBle i t ht⟩
  choose! Rjet hRjet using hconstruct
  have hR_coeff : ∀ (j : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T → ∀ i,
      tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjet j t)) i =
        iteratedDerivWithin j (cpath i) (Set.Icc (0 : ℝ) T) t := by
    intro j t ht i
    exact hRjet j t ht i
  refine ⟨Rjet, hsmooth, ?_, ?_⟩
  · intro j i t ht
    rw [hR_coeff j t ht i]
  · intro j σ hσ
    obtain ⟨B, hBs, hBle⟩ := hmass j σ hσ
    refine ⟨B, hBs, fun i t ht => ?_⟩
    rw [hR_coeff j t ht i]
    exact hBle i t ht

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
