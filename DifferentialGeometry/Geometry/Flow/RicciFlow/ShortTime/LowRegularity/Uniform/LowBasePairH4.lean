import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.EdgeCarrierH4
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.TopPathPair
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.FullSlopePairing

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle intervalIntegral
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Sobolev (iteratedCovGrad)
open DifferentialGeometry.Analysis.Spectral
  (appCc ccTensorToHs ccTensorToHs_smul deTurckPhiMetTotal oneMinusConnLapSmooth
   phiMetCurvCoeff)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem low_base_pair_h4_unif_below
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∀ {eta : ℝ}, 0 < eta →
      ∃ delta0 : ℝ,
        0 < delta0 ∧ delta0 ≤ 1 / 3 ∧
        ∀ {delta : ℝ}, 0 < delta → delta ≤ delta0 →
        ∃ R0 : ℝ, 0 < R0 ∧ R0 ≤ 1 ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
          ∃ G : ℝ, 0 ≤ G ∧
            ∀ (T : SmoothCcTensor g 0 2)
              (_hTsymm : ∀ (x : M) (u v : TangentSpace I x),
                ccTensorBilin (I := I) g T x u v =
                  ccTensorBilin (I := I) g T x v u)
              (hdelta_lt : delta < 1)
              (hdelta : gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g T) delta)
              (hdeltaZ : gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g
                  (0 : SmoothCcTensor g 0 2)) delta)
              {R : ℝ}, 0 ≤ R → R ≤ R0 →
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
              let A := lowBaseData (I := I) (M := M) g gBase T
                hdelta_lt hdelta hdeltaZ
              let V := oneMinusConnLapSmooth (I := I) g 0 2
                (oneMinusConnLapSmooth (I := I) g 0 2 T)
              2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
                    (oneMinusConnLapSmooth (I := I) g 0 2
                      (A.a2 (I := I) (M := M) T +
                        A.a1 (I := I) (M := M) T)).toFun| ≤
                eta * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                  G * (‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 +
                    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 4) := by
  intro eta heta
  let e : ℝ := eta / 3
  have he : 0 < e := by dsimp only [e]; positivity
  obtain ⟨delta0, Re, hdelta0, hdelta0third, hRe, hReone, hedge⟩ :=
    edge_center_path_h4_unif (I := I) (M := M) hDim gBase hΛ he
  refine ⟨delta0, hdelta0, hdelta0third, ?_⟩
  intro delta hdelta hdelta_le
  have hdeltathird : delta ≤ 1 / 3 := hdelta_le.trans hdelta0third
  have hdeltalt : delta < 1 := lt_of_le_of_lt hdeltathird (by norm_num)
  obtain ⟨Rl, Gl, hRl, hRlone, hGl, hlow⟩ :=
    low1_pair_abs_unif (I := I) (M := M) hDim gBase hΛ
      hdelta.le hdeltalt he
  obtain ⟨Rt, hRt, htop⟩ :=
    top_pair_abs_unif (I := I) (M := M) hDim gBase hΛ he
  let R0 : ℝ := min Re (min Rl Rt)
  have hR0 : 0 < R0 := by
    dsimp only [R0]
    exact lt_min hRe (lt_min hRl hRt)
  have hR0one : R0 ≤ 1 := by
    exact (min_le_left Re (min Rl Rt)).trans hReone
  refine ⟨R0, hR0, hR0one, ?_⟩
  intro g hEq hjet
  obtain ⟨Ge, hGe, hedgeG⟩ := hedge g hEq hjet
  let G : ℝ := Ge + Gl
  have hG : 0 ≤ G := add_nonneg hGe hGl
  refine ⟨G, hG, ?_⟩
  intro T hTsymm hdelta_lt hdeltaT hdeltaZ R hR hRR0 hT2
  let A := lowBaseData (I := I) (M := M) g gBase T
    hdelta_lt hdeltaT hdeltaZ
  let P0 := rhsLow0PathIntegral (I := I) (M := M) g gBase T 0
    hdelta_lt hdeltaT hdelta_lt hdeltaZ
  let P1 := rhsLow1PathIntegral (I := I) (M := M) g gBase T 0
    hdelta_lt hdeltaT hdelta_lt hdeltaZ
  let P2 := rhsTopPathIntegral (I := I) (M := M) g gBase T 0
    hdelta_lt hdeltaT hdelta_lt hdeltaZ
  let Φ0 := deTurckPhiMetTotal (I := I) (M := M) g gBase g
  let K0 := phiMetCurvCoeff (I := I) g gBase g
  let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
  let HT := iteratedCovGrad (I := I) g 0 2 2 T
  let HLT := iteratedCovGrad (I := I) g 0 2 2 LT
  let B02 :=
    oneMinusConnLapSmooth (I := I) g 0 2
        (appCc (I := I) (M := M) g 2 2 P0 T) +
      (oneMinusConnLapSmooth (I := I) g 0 2
          (appCc (I := I) (M := M) g 4 2 P2 HT) -
        appCc (I := I) (M := M) g 4 2 P2 HLT)
  let Y1 := oneMinusConnLapSmooth (I := I) g 0 2
    (appCc (I := I) (M := M) g 3 2 P1
      (iteratedCovGrad (I := I) g 0 2 1 T))
  let Y2 := appCc (I := I) (M := M) g 4 2 (P2 - Φ0) HLT
  let X := B02 + appCc (I := I) (M := M) g 2 2 K0 LT
  let V := oneMinusConnLapSmooth (I := I) g 0 2 LT
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  have hRRe : R ≤ Re := hRR0.trans (min_le_left _ _)
  have hRRl : R ≤ Rl := hRR0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRRt : R ≤ Rt := hRR0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcenter := hedgeG T hTsymm (delta := delta) hdelta_le hdelta.le
    hdelta_lt hdeltaT hdeltaZ hR hRRe hT2
  have hlow1 := hlow g hEq hjet T hdeltaT hdeltaZ hR hRRl hT2
  have hzero : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
      (0 : SmoothCcTensor g 0 2)‖ ≤ R := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) from (zero_smul ℝ _).symm,
      ccTensorToHs_smul, zero_smul, norm_zero]
    exact hR
  have htop2 := htop g hEq hjet T (0 : SmoothCcTensor g 0 2)
    hdelta_lt hdeltaT hdelta_lt hdeltaZ hR hRRt hT2 hzero T
  have hnf := lowBase_L_nf (I := I) (M := M) g gBase T hTsymm
    hdeltathird hdelta.le hdeltaT hdeltaZ
  have hdecomp :
      oneMinusConnLapSmooth (I := I) g 0 2
          (A.a2 (I := I) (M := M) T + A.a1 (I := I) (M := M) T) =
        X + Y1 + Y2 := by
    dsimp only [A, X, Y1, Y2, B02, P0, P1, P2, Φ0, K0, LT, HT, HLT]
    dsimp only at hnf
    rw [sub_eq_iff_eq_add] at hnf
    rw [hnf]
    module
  have htri :
      2 * |Inner.inner ℝ V (X + Y1 + Y2)| ≤
        2 * |Inner.inner ℝ V X| +
          2 * |Inner.inner ℝ V Y1| +
            2 * |Inner.inner ℝ V Y2| := by
    rw [inner_add_right, inner_add_right]
    nlinarith [abs_add_le (Inner.inner ℝ V X) (Inner.inner ℝ V Y1),
      abs_add_le (Inner.inner ℝ V X + Inner.inner ℝ V Y1)
        (Inner.inner ℝ V Y2)]
  have hcenter' : 2 * |Inner.inner ℝ V X| ≤ e * z ^ 2 + Ge * (y ^ 2 + y ^ 4) := by
    simpa only [V, X, B02, P0, P2, K0, LT, HT, HLT, y, z,
      SmoothCcTensor.inner_def] using hcenter
  have hlow1' : 2 * |Inner.inner ℝ V Y1| ≤ e * z ^ 2 + Gl * y ^ 2 := by
    simpa only [V, Y1, P1, LT, y, z, SmoothCcTensor.inner_def] using hlow1
  have htop2' : 2 * |Inner.inner ℝ V Y2| ≤ e * z ^ 2 := by
    simpa only [V, Y2, P2, Φ0, LT, HLT, z, SmoothCcTensor.inner_def] using htop2
  change 2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
      (oneMinusConnLapSmooth (I := I) g 0 2
        (A.a2 (I := I) (M := M) T + A.a1 (I := I) (M := M) T)).toFun| ≤
    eta * z ^ 2 + G * (y ^ 2 + y ^ 4)
  rw [hdecomp, ← SmoothCcTensor.inner_def]
  calc
    2 * |Inner.inner ℝ
          (oneMinusConnLapSmooth (I := I) g 0 2 LT) (X + Y1 + Y2)| ≤
        2 * |Inner.inner ℝ V X| +
          2 * |Inner.inner ℝ V Y1| + 2 * |Inner.inner ℝ V Y2| := by
      simpa only [V] using htri
    _ ≤ (e * z ^ 2 + Ge * (y ^ 2 + y ^ 4)) +
          (e * z ^ 2 + Gl * y ^ 2) + e * z ^ 2 := by
      gcongr
    _ ≤ eta * z ^ 2 + G * (y ^ 2 + y ^ 4) := by
      dsimp only [e, G]
      nlinarith [mul_nonneg hGl (sq_nonneg y), mul_nonneg hGl (by positivity)]
    _ = eta * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
          G * (‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 +
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 4) := by
      rfl

theorem low_base_pair_h4_unif
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∀ {eta : ℝ}, 0 < eta →
      ∃ delta R0 : ℝ,
        0 < delta ∧ delta ≤ 1 / 3 ∧ 0 < R0 ∧ R0 ≤ 1 ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
          ∃ G : ℝ, 0 ≤ G ∧
            ∀ (T : SmoothCcTensor g 0 2)
              (_hTsymm : ∀ (x : M) (u v : TangentSpace I x),
                ccTensorBilin (I := I) g T x u v =
                  ccTensorBilin (I := I) g T x v u)
              (hdelta_lt : delta < 1)
              (hdelta : gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g T) delta)
              (hdeltaZ : gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g
                  (0 : SmoothCcTensor g 0 2)) delta)
              {R : ℝ}, 0 ≤ R → R ≤ R0 →
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
              let A := lowBaseData (I := I) (M := M) g gBase T
                hdelta_lt hdelta hdeltaZ
              let V := oneMinusConnLapSmooth (I := I) g 0 2
                (oneMinusConnLapSmooth (I := I) g 0 2 T)
              2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
                    (oneMinusConnLapSmooth (I := I) g 0 2
                      (A.a2 (I := I) (M := M) T +
                        A.a1 (I := I) (M := M) T)).toFun| ≤
                eta * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                  G * (‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 +
                    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 4) := by
  intro eta heta
  obtain ⟨delta, hdelta, hdeltathird, hpair⟩ :=
    low_base_pair_h4_unif_below (I := I) (M := M) hDim gBase hΛ heta
  obtain ⟨R0, hR0, hR0one, hpair0⟩ := hpair hdelta le_rfl
  exact ⟨delta, R0, hdelta, hdeltathird, hR0, hR0one, hpair0⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
