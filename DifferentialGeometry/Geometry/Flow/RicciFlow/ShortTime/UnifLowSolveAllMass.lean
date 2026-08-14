import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegFatouMass
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifLowRegHigherAffine
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifLowSolveH4

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
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
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

theorem lowreg_solve_all_mass_unif
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ K : LowRegBoundData,
      IsLowBoundsUnif (I := I) (M := M) gBase Λ K ∧
        ∃ (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1),
          ∀ (g : SmoothRiemannianMetric I M),
            MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
            (∀ a : ℕ, a ≤ 3 →
              MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
            ∃ (u : MaxRegSolutionSpace (I := I) (M := M)
                ((1 : ℕ) : ℝ) T)
              (gforce : timeL2
                (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T),
              IsBgSolveAt (I := I) (M := M) g gBase K hT hT1
                  u gforce (lowregStateRad K.top K.slope K.outer K.realize) ∧
                ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
                  Summable (fun i =>
                    tensorSobolevWeight (I := I) (M := M) i σ *
                      (perModeConv
                        (TensorEigenIdx.lambda (I := I) (M := M) i)
                        (fun s => (timeModeCoeff (I := I) (M := M)
                          gforce i) s) t) ^ 2) ∧
                  ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
                    (perModeConv
                      (TensorEigenIdx.lambda (I := I) (M := M) i)
                      (fun s => (timeModeCoeff (I := I) (M := M)
                        gforce i) s) t) ^ 2 ≤ Cσ := by
  obtain ⟨ρarm, Karm, hρarm, hKarm, harm⟩ :=
    gal_arm_mass_affine_unif (I := I) (M := M) hDim gBase hΛ
  let q : ℝ := 1 / (32 * (Karm + 1))
  have hKone : 0 < Karm + 1 := by linarith
  have hq : 0 < q := by
    dsimp only [q]
    exact one_div_pos.mpr (mul_pos (by norm_num) hKone)
  let δcap : ℝ := min (1 / 4) q
  let Rcap : ℝ := min ρarm q
  have hδcap : 0 < δcap := lt_min (by norm_num) hq
  have hRcap : 0 < Rcap := lt_min hρarm hq
  obtain ⟨K, hKunif, hKδcap, hKRcap, T, hT, hT1, hsolve⟩ :=
    lowreg_solve_h4_unif_below (I := I) (M := M) hDim gBase hΛ hδcap hRcap
  have hδquarter : K.threshold ≤ 1 / 4 :=
    hKδcap.trans (min_le_left _ _)
  have hδq : K.threshold ≤ q := hKδcap.trans (min_le_right _ _)
  have hRq : lowregStateRad K.top K.slope K.outer K.realize ≤ q :=
    hKRcap.trans (min_le_right _ _)
  have hRρ : lowregStateRad K.top K.slope K.outer K.realize ≤ ρarm :=
    hKRcap.trans (min_le_left _ _)
  have hden : 1 / 2 ≤ (1 - K.threshold) ^ 2 := by
    nlinarith [sq_nonneg (K.threshold - 1 / 4)]
  have hdenpos : 0 < (1 - K.threshold) ^ 2 := lt_of_lt_of_le (by norm_num) hden
  have hratio : Karm * (3 * q) < 1 / 4 := by
    have hdenK : 0 < 32 * (Karm + 1) := mul_pos (by norm_num) hKone
    calc
      Karm * (3 * q) = (3 * Karm) / (32 * (Karm + 1)) := by
        dsimp only [q]
        field_simp
      _ < 1 / 4 := (div_lt_iff₀ hdenK).2 (by nlinarith)
  refine ⟨K, hKunif, T, hT, hT1, ?_⟩
  intro g hEq hjet
  obtain ⟨u, gforce, fseq, _Φ3, Φ4, Φ5, hK, hsolveAt, hconv,
      hderiv, _hE3, hE4, hE5⟩ := hsolve g hEq hjet
  have hRpos : 0 < lowregStateRad K.top K.slope K.outer K.realize :=
    lowregStateRad_pos K.top_nonneg K.slope_nonneg K.outer_pos K.realize_pos
  have hfrac : K.threshold / (1 - K.threshold) ^ 2 ≤ 2 * K.threshold := by
    apply (div_le_iff₀ hdenpos).2
    have hfactor : 0 ≤ 2 * (1 - K.threshold) ^ 2 - 1 := by linarith
    have hmul := mul_nonneg hsolveAt.hδ0 hfactor
    nlinarith
  have hsum : K.threshold / (1 - K.threshold) ^ 2 +
      lowregStateRad K.top K.slope K.outer K.realize ≤ 3 * q := by
    linarith
  have habs : Karm * (K.threshold / (1 - K.threshold) ^ 2 +
      lowregStateRad K.top K.slope K.outer K.realize) < 1 / 4 :=
    (mul_le_mul_of_nonneg_left hsum hKarm).trans_lt hratio
  let hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) S‖ ≤
        lowregStateRad K.top K.slope K.outer K.realize →
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g S) K.threshold :=
    lowregRealRad (I := I) (M := M) g
      (Ctop := K.top) (B1 := K.slope) (ρ := K.outer)
      K.realize_pos.le hK.hreal
  obtain ⟨Ca2, Ca1, _hCa2, _hCa1, hmass⟩ :=
    harm (δ := K.threshold) hsolveAt.hδ3 hsolveAt.hδ0
      (R := lowregStateRad K.top K.slope K.outer K.realize) hRpos.le hRρ
      g hEq hjet hreal
  have hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g N,
      ContinuousOn
        (fun t => lowregProjMode (I := I) (M := M) g fseq N t i)
        (Set.Icc (0 : ℝ) T) :=
    fun N i _ => lowregProjMode_cont (I := I) (M := M) g hT.le fseq N i
  have hUinit : ∀ N i, lowregProjMode (I := I) (M := M) g fseq N 0 i = 0 :=
    fun N i => lowregProjMode_zero (I := I) (M := M) g fseq N i
  have hhigh := lowreg_high_rungs_affine_at_bg (I := I) (M := M)
    g gBase K u gforce hsolveAt hUcont hderiv hUinit hE4 hE5 hKarm
    (by simpa only [hreal] using hmass) habs
  refine ⟨u, gforce, hsolveAt, ?_⟩
  intro σ
  obtain ⟨k, hk⟩ := exists_nat_ge (σ - 5)
  have hστ : σ ≤ 5 + (k : ℝ) := by linarith
  obtain ⟨Φ, hΦ⟩ := hhigh k
  refine ⟨Φ, ?_⟩
  exact lowregMassOfEnergy (I := I) (M := M)
    g gforce fseq hconv hστ hΦ

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
