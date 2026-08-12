import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowBaseFullSlopePairing
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifEdgePathH5
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifLow1PathH5
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifTopPathPair

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle intervalIntegral
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
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem low_base_pair_h5_unif
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
                (oneMinusConnLapSmooth (I := I) g 0 2
                  (oneMinusConnLapSmooth (I := I) g 0 2 T))
              2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
                    (oneMinusConnLapSmooth (I := I) g 0 2
                      (A.a2 (I := I) (M := M) T +
                        A.a1 (I := I) (M := M) T)).toFun| ≤
                eta * ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ^ 2 +
                  G *
                    (‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 *
                        ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 4) := by
  intro eta heta
  let e : ℝ := eta / 3
  have he : 0 < e := by dsimp only [e]; positivity
  obtain ⟨delta, Re, hdelta, hdeltathird, hRe, hReone, hedge⟩ :=
    edge_center_path_h5_unif (I := I) (M := M) hDim gBase hΛ he
  obtain ⟨Gl, hGl, hlow⟩ :=
    low1_pair_h5_unif (I := I) (M := M) hDim gBase hΛ
      hdelta.le hdeltathird he
  obtain ⟨Rt0, Ct, hRt0, hCt, htop⟩ :=
    top_pair_h5_unif (I := I) (M := M) hDim gBase hΛ
  let Dt : ℝ := 2 * (Ct + 1)
  have hDt : 0 < Dt := by dsimp only [Dt]; positivity
  let Rt : ℝ := min Rt0 (e / Dt)
  have hRt : 0 < Rt := by
    dsimp only [Rt]
    exact lt_min hRt0 (div_pos he hDt)
  let R0 : ℝ := min Re Rt
  have hR0 : 0 < R0 := by
    dsimp only [R0]
    exact lt_min hRe hRt
  have hR0one : R0 ≤ 1 := (min_le_left Re Rt).trans hReone
  refine ⟨delta, R0, hdelta, hdeltathird, hR0, hR0one, ?_⟩
  intro g hEq hjet
  obtain ⟨Ge, hGe, hedgeG⟩ := hedge g hEq hjet
  obtain ⟨Fl, hFl, hlowF⟩ := hlow g hEq hjet
  let G : ℝ := Ge + Gl + Fl
  have hG : 0 ≤ G := by dsimp only [G]; positivity
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
  let V := oneMinusConnLapSmooth (I := I) g 0 2
    (oneMinusConnLapSmooth (I := I) g 0 2 LT)
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let q : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖
  let P : ℝ := q ^ 2 + y ^ 2 * q ^ 2 + y ^ 4
  have hy : 0 ≤ y := norm_nonneg _
  have hq : 0 ≤ q := norm_nonneg _
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hRRe : R ≤ Re := hRR0.trans (min_le_left _ _)
  have hRRt : R ≤ Rt := hRR0.trans (min_le_right _ _)
  have hRRt0 : R ≤ Rt0 := hRRt.trans (min_le_left _ _)
  have hRRsmall : R ≤ e / Dt := hRRt.trans (min_le_right _ _)
  have hDtR : R * Dt ≤ e := (le_div_iff₀ hDt).mp hRRsmall
  have htopCoeff : 2 * (Ct * R) ≤ e := by
    dsimp only [Dt] at hDtR
    nlinarith
  have hcenter := hedgeG T hTsymm (delta := delta) le_rfl hdelta.le
    hdelta_lt hdeltaT hdeltaZ hR hRRe hT2
  have hRone : R ≤ 1 := hRR0.trans hR0one
  have hlow1 := hlowF T hTsymm hdeltaT hdeltaZ (hT2.trans hRone)
  have hzero : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
      (0 : SmoothCcTensor g 0 2)‖ ≤ R := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) from (zero_smul ℝ _).symm,
      ccTensorToHs_smul, zero_smul, norm_zero]
    exact hR
  have htop0 := htop g hEq hjet T (0 : SmoothCcTensor g 0 2)
    hdelta_lt hdeltaT hdelta_lt hdeltaZ hR hRRt0 hT2 hzero T
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
  have hcenter' : 2 * |Inner.inner ℝ V X| ≤ e * z ^ 2 + Ge * P := by
    simpa only [V, X, B02, P0, P2, K0, LT, HT, HLT, y, q, z, P,
      SmoothCcTensor.inner_def] using hcenter
  have hlow1' : 2 * |Inner.inner ℝ V Y1| ≤
      e * z ^ 2 + Gl * q ^ 2 +
        Fl * (y ^ 2 + y ^ 2 * q ^ 2 + y ^ 4) := by
    simpa only [V, Y1, P1, LT, y, q, z, SmoothCcTensor.inner_def] using hlow1
  have htop0' : 2 * |Inner.inner ℝ V Y2| ≤ e * z ^ 2 := by
    have htop0raw : |Inner.inner ℝ V Y2| ≤ Ct * R * z ^ 2 := by
      simpa only [V, Y2, P2, Φ0, LT, HLT, z,
        SmoothCcTensor.inner_def] using htop0
    calc
      2 * |Inner.inner ℝ V Y2| ≤ 2 * (Ct * R * z ^ 2) :=
        mul_le_mul_of_nonneg_left htop0raw (by norm_num)
      _ = (2 * (Ct * R)) * z ^ 2 := by ring
      _ ≤ e * z ^ 2 :=
        mul_le_mul_of_nonneg_right htopCoeff (sq_nonneg z)
  have hyq : y ≤ q := by
    dsimp only [y, q]
    exact ccToHs_norm_mono (I := I) (M := M) g 2 (by norm_num) T
  have hy2q2 : y ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hy hyq 2
  have hlowShape : y ^ 2 + y ^ 2 * q ^ 2 + y ^ 4 ≤ P := by
    dsimp only [P]
    linarith
  change 2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
      (oneMinusConnLapSmooth (I := I) g 0 2
        (A.a2 (I := I) (M := M) T + A.a1 (I := I) (M := M) T)).toFun| ≤
    eta * z ^ 2 + G * P
  rw [hdecomp, ← SmoothCcTensor.inner_def]
  calc
    2 * |Inner.inner ℝ
          (oneMinusConnLapSmooth (I := I) g 0 2
            (oneMinusConnLapSmooth (I := I) g 0 2 LT)) (X + Y1 + Y2)| ≤
        2 * |Inner.inner ℝ V X| +
          2 * |Inner.inner ℝ V Y1| + 2 * |Inner.inner ℝ V Y2| := by
      simpa only [V] using htri
    _ ≤ (e * z ^ 2 + Ge * P) +
          (e * z ^ 2 + Gl * q ^ 2 +
            Fl * (y ^ 2 + y ^ 2 * q ^ 2 + y ^ 4)) +
          e * z ^ 2 := by
      gcongr
    _ ≤ eta * z ^ 2 + G * P := by
      have hqP : q ^ 2 ≤ P := by
        dsimp only [P]
        calc
          q ^ 2 ≤ q ^ 2 + y ^ 2 * q ^ 2 :=
            le_add_of_nonneg_right (mul_nonneg (sq_nonneg y) (sq_nonneg q))
          _ ≤ q ^ 2 + y ^ 2 * q ^ 2 + y ^ 4 :=
            le_add_of_nonneg_right (by positivity)
      have hGlP := mul_le_mul_of_nonneg_left hqP hGl
      have hFlP := mul_le_mul_of_nonneg_left hlowShape hFl
      dsimp only [e, G]
      linarith [mul_nonneg hGe hP]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
