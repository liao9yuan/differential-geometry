import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifClassBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2PointwiseUnif
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifMorreyTwo
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifCurvActionZero

noncomputable section

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

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

structure LowRegRealizeData where
  threshold : ℝ
  radius : ℝ

structure IsLowRealizeUnif
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ)
    (R : LowRegRealizeData) : Prop where
  threshold_nonneg : 0 ≤ R.threshold
  threshold_le_third : R.threshold ≤ 1 / 3
  threshold_lt : R.threshold < 1
  radius_pos : 0 < R.radius
  realize : ∀ (g : SmoothRiemannianMetric I M),
    MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
    (∀ a : ℕ, a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
    ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) T‖ ≤ R.radius →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) R.threshold

noncomputable def lowRealizeData
    (gBase : SmoothRiemannianMetric I M) (Λ Kb₀ Kb₁ : ℝ) : LowRegRealizeData where
  threshold := deTurckArmContractionThresholdSharp (Module.finrank ℝ E)
  radius := actionRealizeRad (morreyTwoC (I := I) (M := M) gBase Λ)
    (unifPtCurvZeroC (Module.finrank ℝ E) Λ Kb₀ Kb₁)
    (Module.finrank ℝ E)

theorem lowRealize_unif_of
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ Kb₀ Kb₁ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hKb₀_nonneg : 0 ≤ Kb₀)
    (hKb₀ : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (LeviCivita (I := I) gBase) x v w u)
          (riemannOp (LeviCivita (I := I) gBase) x v w u) ≤
        Kb₀ * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hKb₁_nonneg : 0 ≤ Kb₁)
    (hKb₁ : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁) :
    IsLowRealizeUnif (I := I) (M := M) gBase Λ
      (lowRealizeData (I := I) (M := M) gBase Λ Kb₀ Kb₁) := by
  have hMorreyDim : Module.finrank ℝ E / 2 + 2 = 3 := by
    rw [hDim]
  obtain ⟨hCpt, hmorrey⟩ :=
    morreyTwoC_spec (I := I) (M := M) gBase (le_trans zero_le_one hΛ) hMorreyDim
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (deTurckArmContractionThreshold''_pos (Module.finrank ℝ E)).le
  · exact deTurckArmContractionThreshold''_le_third' (Module.finrank ℝ E)
  · exact deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)
  · exact actionRealizeRad_pos hCpt
      (unifPtCurvZeroC (Module.finrank ℝ E) Λ Kb₀ Kb₁)
      (Module.finrank ℝ E)
  · intro g hEq hjet T hT
    have hjet1 := hjet 1 (by norm_num)
    have hjet2 := hjet 2 (by norm_num)
    have hjet3 := hjet 3 (by norm_num)
    have hcomp : ∀ (x : M) (v : TangentSpace I x),
        Λ⁻¹ * gBase.inner x v v ≤ g.inner x v v ∧
          g.inner x v v ≤ Λ * gBase.inner x v v :=
      fun x v => hEq.2 x (Set.mem_univ x) v
    have hact := unifCurvAction0_of (I := I) (M := M) gBase g hΛ
      hKb₀_nonneg hKb₀ hKb₁_nonneg hKb₁ hcomp hjet1 hjet2 hjet3
    have hreal := realize_at_action (I := I) (M := M) hDim g hact hCpt
      (hmorrey g hEq hjet1 hjet2)
    simpa only [lowRealizeData] using hreal T hT

theorem exists_lowRealize
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ R : LowRegRealizeData,
      IsLowRealizeUnif (I := I) (M := M) gBase Λ R := by
  obtain ⟨Kb₀, hKb₀_nonneg, hKb₀⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (I := I) (M := M) gBase
  obtain ⟨Kb₁, hKb₁_nonneg, hKb₁⟩ :=
    exists_curvJet_sup (I := I) (M := M) gBase 1
  have hKb₁' : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁ := by
    intro x
    simpa using hKb₁ x
  exact ⟨lowRealizeData (I := I) (M := M) gBase Λ Kb₀ Kb₁,
    lowRealize_unif_of (I := I) (M := M) hDim gBase hΛ
      hKb₀_nonneg hKb₀ hKb₁_nonneg hKb₁'⟩

theorem horizon_action_pos {Ctop B0 B1 D ρ Cpt K : ℝ} (d : ℕ)
    (hCtop : 0 ≤ Ctop) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hD : 0 ≤ D) (hρ : 0 < ρ)
    (hCpt : 0 ≤ Cpt) :
    0 < lowregHorizon Ctop B0 B1 D ρ (actionRealizeRad Cpt K d) :=
  lowregHorizon_pos hCtop hB0 hB1 hD hρ (actionRealizeRad_pos hCpt K d)

theorem lowregHorizon_unif_pos {Ctop B0 B1 D ρ Cpt : ℝ} {Fc : ℕ → ℝ} (d : ℕ)
    (hCtop : 0 ≤ Ctop) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hD : 0 ≤ D) (hρ : 0 < ρ)
    (hCpt : 0 ≤ Cpt) (hFc : ∀ p, 0 ≤ Fc p) :
    0 < lowregHorizon Ctop B0 B1 D ρ (unifRealizeRad Cpt Fc d) :=
  lowregHorizon_pos hCtop hB0 hB1 hD hρ (unifRealizeRad_pos hCpt hFc d)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
