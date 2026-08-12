import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifGalRungThreeFour
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifLowBoundsSmall
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifLowRegH4Diss
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgGalerkinIdent

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

theorem lowreg_solve_h4_unif
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
                (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
              (fseq : ℕ → timeL2
                (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
              (Φ3 Φ4 Φ5 : ℝ),
              IsBgSolveAt (I := I) (M := M) g gBase K
                  hT hT1
                  u gforce (lowregStateRad K.top K.slope K.outer K.realize) ∧
                (∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
                  ∀ t ∈ Set.Icc (0 : ℝ) T,
                    Tendsto
                      (fun N => lowregProjMode (I := I) (M := M) g fseq N t i)
                      atTop
                      (𝓝 (perModeConv
                        (TensorEigenIdx.lambda (I := I) (M := M) i)
                        (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t))) ∧
                (∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
                  galerkinEnergy (I := I) (M := M)
                    (eigenIdxFinset (I := I) (M := M) g N)
                    (lowregProjMode (I := I) (M := M) g fseq N) 3 t ≤ Φ3) ∧
                (∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
                  galerkinEnergy (I := I) (M := M)
                    (eigenIdxFinset (I := I) (M := M) g N)
                    (lowregProjMode (I := I) (M := M) g fseq N) 4 t ≤ Φ4) ∧
                ∀ N : ℕ, ∫ t,
                  galerkinEnergy (I := I) (M := M)
                    (eigenIdxFinset (I := I) (M := M) g N)
                    (lowregProjMode (I := I) (M := M) g fseq N) 5 t
                    ∂(timeMeasure T) ≤ Φ5 := by
  obtain ⟨delta, R0, hdelta, hdeltathird, hR0, _hR0one, hpairs⟩ :=
    gal_arm_pair3_pair4_unif_of_mem (I := I) (M := M)
      hDim gBase hΛ one_pos one_pos
  obtain ⟨K, hKunif, hKdelta, hKstate⟩ :=
    exists_lowBounds_at (I := I) (M := M) hDim gBase hΛ
      hdelta hdeltathird hR0
  subst delta
  let T : ℝ :=
    lowregHorizon K.top K.base K.slope K.zeroBd K.outer K.realize
  have hT : 0 < T := by
    exact lowregHorizon_pos K.top_nonneg K.base_nonneg K.slope_nonneg
      K.zero_nonneg K.outer_pos K.realize_pos
  have hT1 : T ≤ 1 := lowregHorizon_le_one
  refine ⟨K, hKunif, T, hT, hT1, ?_⟩
  intro g hEq hjet
  have hK := hKunif.bounds g hEq hjet
  obtain ⟨u, gforce, hsolve⟩ :=
    lowreg_sol_of_data (I := I) (M := M) g gBase K hK hT le_rfl hT1
  let hsolveAt : IsBgSolveAt (I := I) (M := M) g gBase K hT hT1
      u gforce (lowregStateRad K.top K.slope K.outer K.realize) := {
    bounds := hK
    solve := hsolve
    hTτ := le_rfl
    hcap := le_rfl
  }
  obtain ⟨fseq, _hconv, hmode, hpack⟩ :=
    lowreg_projMode_atBg (I := I) (M := M) g gBase K hT hT1
      u gforce hsolveAt
  obtain ⟨G3, G4, hG3, hG4, hpair3G, hpair4G⟩ := hpairs g hEq hjet
  let R : ℝ := lowregStateRad K.top K.slope K.outer K.realize
  have hR : 0 ≤ R :=
    (lowregStateRad_pos K.top_nonneg K.slope_nonneg
      K.outer_pos K.realize_pos).le
  let hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) K.threshold :=
    lowregRealRad (I := I) (M := M) g K.realize_pos.le hK.hreal
  have hpair3' := hpair3G hR hKstate K.threshold_lt hreal
  have hpair4' := hpair4G hR hKstate K.threshold_lt hreal
  have hpair3'' : ∀
      (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
      (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ),
      ‖galLowView (I := I) (M := M) g 1
          (finiteEigenComboHs (I := I) (M := M) g F c
            (((1 : ℕ) : ℝ) + 2))‖ ≤ R →
      2 * |∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
            (c i * (galArmVecBg (I := I) (M := M) g gBase hR
              K.threshold_lt hreal F c).coeff i)| ≤
        (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) +
          G3 * ((∑ i ∈ F,
            tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2) +
            (∑ i ∈ F,
              tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
                (c i) ^ 2) ^ 2) := by
    intro F c hc
    simpa only [one_mul, R] using hpair3' F c hc
  have hpair4'' : ∀
      (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
      (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ),
      ‖galLowView (I := I) (M := M) g 1
          (finiteEigenComboHs (I := I) (M := M) g F c
            (((1 : ℕ) : ℝ) + 2))‖ ≤ R →
      2 * |∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
            (c i * (galArmVecBg (I := I) (M := M) g gBase hR
              K.threshold_lt hreal F c).coeff i)| ≤
        (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (5 : ℝ) * (c i) ^ 2) +
          G4 * ((∑ i ∈ F,
            tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) +
            (∑ i ∈ F,
              tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
                (c i) ^ 2) *
              (∑ i ∈ F,
                tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
                  (c i) ^ 2) +
            (∑ i ∈ F,
              tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
                (c i) ^ 2) ^ 2) := by
    intro F c hc
    simpa only [one_mul, R] using hpair4' F c hc
  have hL2H3 : ∀ N : ℕ, ∫ t,
      galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N)
        (lowregProjMode (I := I) (M := M) g fseq N) 3 t ∂(timeMeasure T) ≤
      ((1 + T) * (R / 4)) ^ 2 := by
    intro N
    exact lowregL2H3 (I := I) (M := M) g hT hT1 N fseq _
      ((hpack N).2.2.1) ((hpack N).2.2.2.2.2)
  obtain ⟨Φ3, ΦD4, hΦ3, hΦD4⟩ :=
    lowregFatouE3D4AtBg_of_pair (I := I) (M := M) g gBase hT hT1
      K.threshold_lt hK.threshold_nonneg hK.threshold_le_third
      K.top_nonneg K.base_nonneg K.slope_nonneg K.outer_pos K.realize_pos
      hK.hreal hK.core_cont hK.htame hG3
      (by simpa only [R, hreal] using hpair3'') fseq
      (fun N => (hpack N).2.1) (fun N => (hpack N).2.2.1) hL2H3
  obtain ⟨Φ4, Φ5, hΦ4, hΦ5⟩ :=
    lowregFatouE4D5AtBg_of_pair (I := I) (M := M) g gBase hT hT1
      K.threshold_lt hK.threshold_nonneg hK.threshold_le_third
      K.top_nonneg K.base_nonneg K.slope_nonneg K.outer_pos K.realize_pos
      hK.hreal hK.core_cont hK.htame hG4
      (by simpa only [R, hreal] using hpair4'') fseq
      (fun N => (hpack N).2.1) (fun N => (hpack N).2.2.1) hΦ3 hΦD4
  refine ⟨u, gforce, fseq, Φ3, Φ4, Φ5, hsolveAt, ?_, hΦ3, hΦ4, hΦ5⟩
  intro i t ht
  simpa only [lowregProjMode] using hmode i t ht

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
