import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgHigherRung
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegHigherRung

/-!
# All-order mass at an arbitrary fixed DeTurck background

This module closes the fixed-background Galerkin ladder into one coherent
all-rung path and then applies the background-neutral Fatou mass theorem.  The
Sobolev scale and all spectral objects remain based at the state metric `g₀`;
only the nonlinear coefficient package uses the independent background
`g_bg`.
-/

open Bundle Manifold MeasureTheory Set Filter
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- An adapted fixed-background solve carries one coherent projected path with
uniform energy bounds at every integer rung `5 + k`. -/
theorem lowregAllRungsAtBg
    (g₀ g_bg : SmoothRiemannianMetric I M) (K : LowRegBoundData)
    {Rcap Ctop₂ Kr2 Kr1 Kcap T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      ((1 : ℕ) : ℝ) T)
    (gforce : timeL2
      (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsAdaptedLowSolveBg (I := I) (M := M) g₀ g_bg K hT hT1
      u gforce Rcap Ctop₂ Kr2 Kr1 Kcap) :
    ∃ (fseq : ℕ → timeL2
        (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T),
      IsAllRungPath (I := I) (M := M) g₀ gforce fseq := by
  classical
  have hsol := hlo.toIsBgSolveAt
  obtain ⟨fseq, hpath⟩ := lowregRung5PathAtBg (I := I) (M := M)
    g₀ g_bg K hT hT1 u gforce hlo
  obtain ⟨A, B, hgate, _hA3, _hB3, ε, hε, hbudget⟩ := hlo.toGatePack
  obtain ⟨κ, hhm, hκA⟩ := hgate.2.2.2.2.2
  have hrate : 0 ≤ K.threshold / (1 - K.threshold) ^ 2 :=
    div_nonneg hsol.hδ0 (sq_nonneg _)
  have hstate : 0 ≤ lowregStateRad K.top K.slope K.outer K.realize :=
    (lowregStateRad_pos hsol.hCtop hsol.hB1 hsol.hρ hsol.hP).le
  have hκrate : κ * (K.threshold / (1 - K.threshold) ^ 2) ≤
      A * (K.threshold / (1 - K.threshold) ^ 2) :=
    mul_le_mul_of_nonneg_right hκA hrate
  have hBstate : 0 ≤ B * lowregStateRad K.top K.slope K.outer K.realize :=
    mul_nonneg hgate.2.1 hstate
  have habs : κ * (K.threshold / (1 - K.threshold) ^ 2) + ε < 1 := by
    linarith only [hκrate, hBstate, hbudget]
  have hhigh := lowregHighRungsBg (I := I) (M := M)
    g₀ g_bg K u gforce Rcap hsol hpath hhm hε habs
  refine ⟨fseq, hpath.1, ?_⟩
  intro k
  cases k with
  | zero =>
      obtain ⟨Φ5, hE5⟩ := hpath.2.2.2.2
      refine ⟨Φ5, ?_⟩
      simpa only [Nat.cast_zero, add_zero] using hE5
  | succ k =>
      obtain ⟨Φ, hΦ⟩ := hhigh k
      refine ⟨Φ, ?_⟩
      intro N t ht
      have hidx : (5 : ℝ) + ((Nat.succ k : ℕ) : ℝ) = 6 + (k : ℝ) := by
        push_cast
        ring
      rw [hidx]
      exact hΦ N t ht

/-- Fatou closure of the fixed-background all-rung path: every real Sobolev
exponent has a uniform limiting spectral mass bound for the forcing path. -/
theorem lowregAllMassAtBg
    (g₀ g_bg : SmoothRiemannianMetric I M) (K : LowRegBoundData)
    {Rcap Ctop₂ Kr2 Kr1 Kcap T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      ((1 : ℕ) : ℝ) T)
    (gforce : timeL2
      (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsAdaptedLowSolveBg (I := I) (M := M) g₀ g_bg K hT hT1
      u gforce Rcap Ctop₂ Kr2 Kr1 Kcap) :
    ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t) ^ 2 ≤
          Cσ := by
  classical
  obtain ⟨fseq, hpath⟩ := lowregAllRungsAtBg (I := I) (M := M)
    g₀ g_bg K hT hT1 u gforce hlo
  intro σ
  obtain ⟨k, hk⟩ := exists_nat_ge (σ - 5)
  have hστ : σ ≤ 5 + (k : ℝ) := by linarith
  obtain ⟨Φ, hΦ⟩ := hpath.2 k
  refine ⟨Φ, ?_⟩
  exact lowregMassOfEnergy (I := I) (M := M)
    g₀ gforce fseq hpath.1 hστ hΦ

/-- Public fixed-background all-order mass endpoint.  The dimension-three
hypothesis matches the smoothing consumer; the spectral mass proof itself is
dimension-neutral. -/
theorem lowreg_loMassBg (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M) (K : LowRegBoundData)
    {Rcap Ctop₂ Kr2 Kr1 Kcap T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      ((1 : ℕ) : ℝ) T)
    (gforce : timeL2
      (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsAdaptedLowSolveBg (I := I) (M := M) g₀ g_bg K hT hT1
      u gforce Rcap Ctop₂ Kr2 Kr1 Kcap)
    (σ : ℝ) :
    ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t) ^ 2 ≤
          Cσ := by
  exact (fun _hDim : Module.finrank ℝ E = 3 =>
    lowregAllMassAtBg (I := I) (M := M)
      g₀ g_bg K hT hT1 u gforce hlo σ) hDim

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
