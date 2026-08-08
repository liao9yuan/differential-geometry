import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RicciTopFibreBound
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2PrincipalPair
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifConvexJets

/-!
# Class-first principal-face pairing for the centered top kernel

The coefficient left after subtracting the metric principal deviation is
uniformly small in the fibre radius.  Pairing it against the order-four energy
therefore costs only a class-first small multiple of the `H⁴` norm squared.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Bundle Manifold Set Filter Topology Tensor0SBundle ContinuousLinearMap
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- One coefficient fixed before the class metric varies controls the centered
top-kernel principal face at order four. -/
theorem bcD2_pair_h4_unif
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T : SmoothCcTensor g 0 2)
          (_hT : ∀ (x : M) (u v : TangentSpace I x),
            ccTensorBilin (I := I) g T x u v =
              ccTensorBilin (I := I) g T x v u)
          {δ : ℝ}, δ ≤ 1 / 3 → 0 ≤ δ →
          ∀ (hδ : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g T) δ)
            (hδZ : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g
                (0 : SmoothCcTensor g 0 2)) δ)
            {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
          ∀ U : SmoothCcTensor g 0 2,
          let gm := realizedFam (I := I) g T 0 hδ hδZ s
          let Φ :=
            lieRefold2 (I := I) (M := M) g T hδ hδZ s +
              (-2 * s : ℝ) •
                LowBaseInternal.ricciTop (I := I) (M := M) g gm T
          |tensorL2Inner (I := I) (M := M) g 0 2
              (oneMinusConnLapSmooth (I := I) g 0 2
                (oneMinusConnLapSmooth (I := I) g 0 2 U)).toFun
              (appCc (I := I) (M := M) g 4 2 Φ
                (iteratedCovGrad (I := I) g 0 2 2
                  (oneMinusConnLapSmooth (I := I) g 0 2 U))).toFun| ≤
            C * (δ / (1 - δ) ^ 2) *
              ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 := by
  obtain ⟨Ktop, hKtop0, htop⟩ :=
    LowBaseInternal.topKer_cap_unif (I := I) (M := M)
  obtain ⟨Kcurv, hKcurv⟩ :=
    exists_curv_actions (I := I) (M := M) gBase hΛ
  let C : ℝ := Ktop * h2CovsumC Kcurv.rankTwo
  refine ⟨C, mul_nonneg hKtop0 (h2CovsumC_nonneg Kcurv.rankTwo), ?_⟩
  intro g hEq hjet T hT δ hδ_le hδ0 hδ hδZ s hs U
  dsimp only
  let r : ℝ := δ / (1 - δ) ^ 2
  let Φ : SmoothCcTensor g 4 2 :=
    lieRefold2 (I := I) (M := M) g T hδ hδZ s +
      (-2 * s : ℝ) •
        LowBaseInternal.ricciTop (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδ hδZ s) T
  have hr : 0 ≤ r := div_nonneg hδ0 (sq_nonneg _)
  have hΦ : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          (Φ.toSection x) ≤ (Ktop * r) ^ 2 := by
    intro x
    simpa only [Φ, r] using
      htop g T hT hδ_le hδ0 hδ hδZ hs x
  have hact : IsCurvAction0 (I := I) (M := M) g 2 Kcurv.rankTwo :=
    (hKcurv.bounds g hEq hjet).1
  have hpair := appD2_pair_h4 (I := I) (M := M) g hact
    (mul_nonneg hKtop0 hr) Φ hΦ U
  change
    |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 U)).toFun
        (appCc (I := I) (M := M) g 4 2 Φ
          (iteratedCovGrad (I := I) g 0 2 2
            (oneMinusConnLapSmooth (I := I) g 0 2 U))).toFun| ≤
      C * r * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2
  calc
    _ ≤ (Ktop * r) * h2CovsumC Kcurv.rankTwo *
        ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 := hpair
    _ = C * r *
        ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 := by
      simp only [C]
      ring

/-- After choosing the fibre radius before the class metric varies, the
centered top-kernel principal face is absorbed by any prescribed order-four
energy coefficient. -/
theorem bcD2_pair_abs_unif
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∀ {η : ℝ}, 0 < η →
      ∃ δ₂ : ℝ, 0 < δ₂ ∧ δ₂ ≤ 1 / 3 ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
          ∀ (T : SmoothCcTensor g 0 2)
            (_hT : ∀ (x : M) (u v : TangentSpace I x),
              ccTensorBilin (I := I) g T x u v =
                ccTensorBilin (I := I) g T x v u)
            {δ : ℝ}, δ ≤ δ₂ → 0 ≤ δ →
            ∀ (hδ : gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g T) δ)
              (hδZ : gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g
                  (0 : SmoothCcTensor g 0 2)) δ)
              {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
            ∀ U : SmoothCcTensor g 0 2,
            let gm := realizedFam (I := I) g T 0 hδ hδZ s
            let Φ :=
              lieRefold2 (I := I) (M := M) g T hδ hδZ s +
                (-2 * s : ℝ) •
                  LowBaseInternal.ricciTop (I := I) (M := M) g gm T
            2 * |tensorL2Inner (I := I) (M := M) g 0 2
                (oneMinusConnLapSmooth (I := I) g 0 2
                  (oneMinusConnLapSmooth (I := I) g 0 2 U)).toFun
                (appCc (I := I) (M := M) g 4 2 Φ
                  (iteratedCovGrad (I := I) g 0 2 2
                    (oneMinusConnLapSmooth (I := I) g 0 2 U))).toFun| ≤
              η * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 := by
  intro η hη
  obtain ⟨C, hC0, hpair⟩ := bcD2_pair_h4_unif
    (I := I) (M := M) gBase hΛ
  let δ₂ : ℝ := min (1 / 4 : ℝ) (η / (4 * (C + 1)))
  have hCp : 0 < C + 1 := by linarith
  have hδ₂0 : 0 < δ₂ := lt_min (by norm_num)
    (div_pos hη (mul_pos (by norm_num) hCp))
  have hδ₂third : δ₂ ≤ 1 / 3 :=
    (min_le_left _ _).trans (by norm_num)
  refine ⟨δ₂, hδ₂0, hδ₂third, ?_⟩
  intro g hEq hjet T hT δ hδ_le hδ0 hδ hδZ s hs U
  dsimp only
  let r : ℝ := δ / (1 - δ) ^ 2
  let Φ : SmoothCcTensor g 4 2 :=
    lieRefold2 (I := I) (M := M) g T hδ hδZ s +
      (-2 * s : ℝ) •
        LowBaseInternal.ricciTop (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδ hδZ s) T
  have hδ_quarter : δ ≤ 1 / 4 :=
    hδ_le.trans (min_le_left _ _)
  have hδ_third : δ ≤ 1 / 3 := hδ_le.trans hδ₂third
  have hbase : 0 < 1 - δ := by linarith
  have hsq : (1 / 2 : ℝ) ≤ (1 - δ) ^ 2 := by
    nlinarith [sq_nonneg δ]
  have hr : r ≤ 2 * δ := by
    dsimp only [r]
    rw [div_le_iff₀ (sq_pos_of_pos hbase)]
    nlinarith [mul_le_mul_of_nonneg_left hsq hδ0]
  have hδ_frac : δ ≤ η / (4 * (C + 1)) :=
    hδ_le.trans (min_le_right _ _)
  have hδ_scaled : δ * (4 * (C + 1)) ≤ η :=
    (le_div_iff₀ (mul_pos (by norm_num) hCp)).mp hδ_frac
  have hcoef : 4 * C * δ ≤ η := by
    calc
      4 * C * δ ≤ 4 * (C + 1) * δ := by
        apply mul_le_mul_of_nonneg_right _ hδ0
        nlinarith
      _ ≤ η := by
        nlinarith
  have hpair' :
      |tensorL2Inner (I := I) (M := M) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2
            (oneMinusConnLapSmooth (I := I) g 0 2 U)).toFun
          (appCc (I := I) (M := M) g 4 2 Φ
            (iteratedCovGrad (I := I) g 0 2 2
              (oneMinusConnLapSmooth (I := I) g 0 2 U))).toFun| ≤
        C * r *
          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 := by
    simpa only [Φ, r] using
      hpair g hEq hjet T hT hδ_third hδ0 hδ hδZ hs U
  have hCr : 2 * C * r ≤ 4 * C * δ := by
    calc
      2 * C * r ≤ 2 * C * (2 * δ) :=
        mul_le_mul_of_nonneg_left hr (mul_nonneg (by norm_num) hC0)
      _ = 4 * C * δ := by ring
  calc
    2 * |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 U)).toFun
        (appCc (I := I) (M := M) g 4 2 Φ
          (iteratedCovGrad (I := I) g 0 2 2
            (oneMinusConnLapSmooth (I := I) g 0 2 U))).toFun| ≤
      2 * (C * r *
        ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hpair' (by norm_num)
    _ = (2 * C * r) *
        ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 := by ring
    _ ≤ (4 * C * δ) *
        ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hCr (sq_nonneg _)
    _ ≤ η * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
