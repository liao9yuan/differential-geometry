import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegUnifBounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private theorem exists_lowRealize_below
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ deltaCap Rcap : ℝ}
    (hΛ : 1 ≤ Λ) (hdeltaCap : 0 < deltaCap) (hRcap : 0 < Rcap) :
    ∃ D : LowRegRealizeData,
      IsLowRealizeUnif (I := I) (M := M) gBase Λ D ∧
        D.threshold ≤ deltaCap ∧ D.radius ≤ Rcap := by
  obtain ⟨D0, hD0⟩ := exists_lowRealize (I := I) (M := M) hDim gBase hΛ
  let delta : ℝ := min (deltaCap / 2) (1 / 6)
  let radius : ℝ := min (delta * D0.radius / 2) Rcap
  let D : LowRegRealizeData := { threshold := delta, radius := radius }
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min (by positivity) (by norm_num)
  have hdeltathird : delta ≤ 1 / 3 := by
    exact (min_le_right _ _).trans (by norm_num)
  have hdeltacap : delta ≤ deltaCap := by
    exact (min_le_left _ _).trans (by linarith)
  have hradius : 0 < radius := by
    dsimp only [radius]
    exact lt_min (div_pos (mul_pos hdelta hD0.radius_pos) (by norm_num)) hRcap
  have hradiuscap : radius ≤ Rcap := min_le_right _ _
  refine ⟨D, ?_, ?_, ?_⟩
  · refine ⟨hdelta.le, hdeltathird,
      hdeltathird.trans_lt (by norm_num), hradius, ?_⟩
    intro g hEq hjet T hT
    obtain ⟨C, hC, hlin, hCP⟩ := realize_h2_bound (I := I) (M := M) g
      hD0.radius_pos (hD0.threshold_le_third.trans (by norm_num))
      (hD0.realize g hEq hjet)
    have hCP2 : C * D0.radius ≤ 2 := by
      have hmul := (le_div_iff₀ (by positivity : 0 < 2 * C)).mp hCP
      nlinarith
    have hTradius :
        ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) T‖ ≤ delta * D0.radius / 2 := by
      exact hT.trans (min_le_left _ _)
    have hcoeff : C * ‖smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ delta := by
      calc
        _ ≤ C * (delta * D0.radius / 2) :=
          mul_le_mul_of_nonneg_left hTradius hC.le
        _ = delta / 2 * (C * D0.radius) := by ring
        _ ≤ delta / 2 * 2 :=
          mul_le_mul_of_nonneg_left hCP2 (by positivity)
        _ = delta := by ring
    exact gFibreOpBound_mono_of_le (I := I) (M := M) g _ hcoeff (hlin T)
  · simpa only [D] using hdeltacap
  · simpa only [D] using hradiuscap

theorem exists_lowBounds_below
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ deltaCap Rcap : ℝ}
    (hΛ : 1 ≤ Λ) (hdeltaCap : 0 < deltaCap) (hRcap : 0 < Rcap) :
    ∃ K : LowRegBoundData,
      IsLowBoundsUnif (I := I) (M := M) gBase Λ K ∧
        K.threshold ≤ deltaCap ∧
        lowregStateRad K.top K.slope K.outer K.realize ≤ Rcap := by
  obtain ⟨RD, hRD, hRDdelta, hRDradius⟩ :=
    exists_lowRealize_below (I := I) (M := M) hDim gBase hΛ
      hdeltaCap hRcap
  obtain ⟨ZD, hZD⟩ := exists_lowZero (I := I) (M := M) gBase hΛ
  obtain ⟨rho, Ctop, B0, B1, hrho, hCtop, hB0, hB1, houter⟩ :=
    lowRegN_outer_unif (I := I) (M := M) hDim gBase hΛ
      hRD.threshold_nonneg hRD.threshold_lt
  let Q : ℝ := lowregOuterRad Ctop rho RD.radius
  have hQpos : 0 < Q := by
    simpa only [Q] using lowregOuterRad_pos hCtop hrho hRD.radius_pos
  have hB1Q : 0 ≤ B1 Q := hB1 Q hQpos.le
  have hSpos : 0 < lowregStateRad Ctop (B1 Q) rho RD.radius :=
    lowregStateRad_pos hCtop hB1Q hrho hRD.radius_pos
  have hQrho : Q ≤ rho := by
    have hhalf := lowregOuterRad_le_rho
      (Ctop := Ctop) (ρ := rho) (P := RD.radius)
    dsimp only [Q]
    linarith
  have hQP : Q ≤ RD.radius := by
    have hhalf := lowregOuterRad_le_P
      (Ctop := Ctop) (ρ := rho) (P := RD.radius)
    dsimp only [Q]
    linarith
  have hSQ : lowregStateRad Ctop (B1 Q) rho RD.radius ≤ Q := by
    have hhalf := lowregStateRad_le_Q
      (Ctop := Ctop) (B1 := B1 Q) (ρ := rho) (P := RD.radius)
    linarith
  let K : LowRegBoundData := {
    threshold := RD.threshold
    top := Ctop
    base := B0 Q
    slope := B1 Q
    zeroBd := ZD.zeroBd
    outer := rho
    realize := RD.radius
    threshold_lt := hRD.threshold_lt
    top_nonneg := hCtop
    base_nonneg := hB0 Q hQpos.le
    slope_nonneg := hB1Q
    zero_nonneg := hZD.zero_nonneg
    outer_pos := hrho
    realize_pos := hRD.radius_pos
  }
  have hstatecap :
      lowregStateRad K.top K.slope K.outer K.realize ≤ Rcap := by
    exact (lowregStateRad_le_P K.realize_pos.le).trans hRDradius
  refine ⟨K, { bounds := ?_ }, ?_, hstatecap⟩
  · intro g hEq hjet
    have hreal := hRD.realize g hEq hjet
    have hrealQ : ∀ T : SmoothCcTensor g 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g
            (((1 : ℕ) : ℝ) + 1) T‖ ≤ Q →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) RD.threshold :=
      realizeOfLE (I := I) (M := M) g hQP hreal
    obtain ⟨hcont0, hcore0, htame0⟩ :=
      houter g hEq hjet hQpos.le hQrho hSpos hSQ hrealQ
    have hcore' : Continuous
        (coreN (I := I) (M := M) g gBase hRD.threshold_lt
          (lowregRealRad (I := I) (M := M) g
            (Ctop := Ctop) (B1 := B1 Q) (ρ := rho)
            hRD.radius_pos.le hreal)) := by
      simpa only using hcore0
    have hzero0 := lowZero_nfun (I := I) (M := M) hZD g hEq hjet
      hRD.threshold_lt hCtop hB1Q hrho hRD.radius_pos hreal hcore'
    have hrealK : ∀ T : SmoothCcTensor g 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g
            (((1 : ℕ) : ℝ) + 1) T‖ ≤ K.realize →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) K.threshold := by
      simpa only [K] using hreal
    refine {
      threshold_nonneg := by simpa only [K] using hRD.threshold_nonneg
      threshold_le_third := by simpa only [K] using hRD.threshold_le_third
      hreal := hrealK
      hcont := ?_
      htame := ?_
      hzero := ?_
      core_cont := ?_ }
    · simpa only [K, Q, lowregNfun] using hcont0
    · simpa only [K, Q, lowregNfun] using htame0
    · simpa only [K, Q] using hzero0
    · simpa only [K, Q] using hcore'
  · simpa only [K] using hRDdelta

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
