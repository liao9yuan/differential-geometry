import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.CcTensorFibreCauchySchwarz
import DifferentialGeometry.Analysis.Sobolev.Embedding.TensorSobolevEmbeddingCm
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderReduction
import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRSRiemannianBundle
import DifferentialGeometry.Analysis.Elliptic.MetricBounds

/-! # The `C⁰`-Sobolev fibre bound on the symmetric bilinear extraction

For a closed Riemannian manifold `(M, g)` the symmetric bilinear extraction
`ccTensorBilinSymm g T` of a smooth compactly-supported `(0,2)`-tensor section `T`
is `g`-fibre controlled by `C · ‖T.toHs (2k)‖` at every supercritical Sobolev order
`2k > dim M + 4`, with a fixed constant `C`.

This is the pointwise (`0`-jet, no-derivative) instance of the Morrey/Sobolev embedding
`H^{2k} ↪ C⁰`: the realized perturbation fibre value is bounded by the intrinsic
`g`-fibre Cauchy–Schwarz `ccTensorBilin_sq_le_gInner_riemannianFiberNormSq` against the
Riemannian fibre norm squared `riemannianFiberNormSq g 0 2 x (T.toSection x) = ‖T.toSection x‖²`,
and the fibre norm is then controlled by `C · ‖T.toHs (2k)‖` via the tensor Sobolev embedding
`tensorPouSobolevHilbert_embedding_Ck`.

It is the `fibreSmall`-arm input that turns an `H^{2k}`-controlled smoothing realization
into metric-realize fibre smallness; it is genuinely analytic (a Sobolev embedding fibre
estimate) and lives in the spectral metric-realization home, below the DeTurck flow tower. -/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.Chart

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **`C⁰`-Sobolev embedding at the `0`-jet fibre level.**

On a closed Riemannian manifold `(M, g)` there is a fixed constant `C ≥ 0` such that,
for every supercritical Sobolev order `2k` (`2k > dim M + 4`) and every smooth
compactly-supported `(0,2)`-tensor section `T`, the symmetric bilinear extraction
`ccTensorBilinSymm g T` is `g`-fibre controlled by `C · ‖T.toHs (2k)‖`:
`|ccTensorBilinSymm g T x v w| ≤ (C · ‖T.toHs (2k)‖) · √(g x v v) · √(g x w w)`
uniformly over base points `x` and tangent vectors `v, w`.

This is the pointwise (`0`-jet, no-derivative) analogue of the chart-`2`-jet seminorm
bound `chartMetricJet2DiffSup_realizeMetricAt_le_toHs_unconditional`
(`RealizedCovGradJetInput.lean`): both are instances of the Morrey/Sobolev embedding
`H^{2k} ↪ C⁰` for `2k > dim M + 4`.  Here the realized perturbation fibre value is
bounded by the intrinsic `g`-fibre Cauchy–Schwarz
`ccTensorBilin_sq_le_gInner_riemannianFiberNormSq` against the Riemannian fibre norm
squared `riemannianFiberNormSq g 0 2 x (T.toSection x) = ‖T.toSection x‖²`, and the
fibre norm is then controlled by `C · ‖T.toHs (2k)‖` via the tensor Sobolev embedding
`tensorPouSobolevHilbert_embedding_Ck` (read at `m = 2`, i.e. `2k > dim M + 4`). -/
theorem gFibreOpBound_ccTensorBilinSymm_le_tensorHsNorm
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), 2 * k > Module.finrank ℝ E + 4 →
      ∀ T : Integral.L2.SmoothCcTensor g 0 2,
        gFibreOpBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T)
          (C * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k) T‖) := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 2
  set k₀ : ℕ := (Module.finrank ℝ E + 4) / 2 + 1 with hk₀_def
  have hk₀_super : 2 * k₀ > Module.finrank ℝ E + 4 := by rw [hk₀_def]; omega
  obtain ⟨C, hC_pos, hC⟩ :=
    DifferentialGeometry.PDE.RicciFlow.tensorPouSobolevHilbert_embedding_Ck
      (I := I) (M := M) (g := g) (r := 0) (s := 2) (k := k₀) (m := 2)
      (by rw [show 2 * 2 = 4 from rfl]; exact hk₀_super)
  refine ⟨C, le_of_lt hC_pos, fun k hk T x v w => ?_⟩
  -- For each valid order `k`, `k₀ ≤ k`, so the fixed embedding norm is dominated.
  have hk₀_le : k₀ ≤ k := by rw [hk₀_def]; omega
  have hnorm_mono :
      ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k₀) T‖ ≤
        ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k) T‖ :=
    toHs_norm_mono_order (I := I) (M := M) g (by omega) T
  -- Fibre value bound from the intrinsic `g`-Cauchy–Schwarz against `‖T.toSection x‖`.
  have hsec_norm_sq :
      ‖T.toSection x‖ ^ 2 =
        Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (T.toSection x) := by
    have h_inner :
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
            (I := I) (M := M) g 0 2 x (T.toSection x) (T.toSection x) : ℝ) =
          Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (T.toSection x) := by
      rw [DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply]
      exact (Integral.Connection.riemannianFiberNormSq_eq_tensorInnerPointwise
        (I := I) (M := M) g 0 2 x (T.toSection x)).symm
    have hself :
        (inner ℝ (T.toSection x) (T.toSection x) : ℝ) =
          Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (T.toSection x) := by
      rw [← h_inner]; rfl
    rw [← hself, real_inner_self_eq_norm_sq]
  have hbound : ∀ (p q : TangentSpace I x),
      |ccTensorBilin (I := I) g T x p q| ≤
        ‖T.toSection x‖ * Real.sqrt (g.inner x p p) * Real.sqrt (g.inner x q q) := by
    intro p q
    have hsq := ccTensorBilin_sq_le_gInner_riemannianFiberNormSq (I := I) g T x p q
    rw [← hsec_norm_sq] at hsq
    have hpp : 0 ≤ g.inner x p p := DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g x p
    have hqq : 0 ≤ g.inner x q q := DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g x q
    have hrhs_nn :
        0 ≤ ‖T.toSection x‖ * Real.sqrt (g.inner x p p) * Real.sqrt (g.inner x q q) := by
      have := Real.sqrt_nonneg (g.inner x p p)
      have := Real.sqrt_nonneg (g.inner x q q)
      positivity
    have hsq' : (ccTensorBilin (I := I) g T x p q) ^ 2 ≤
        (‖T.toSection x‖ * Real.sqrt (g.inner x p p) *
          Real.sqrt (g.inner x q q)) ^ 2 := by
      refine hsq.trans (le_of_eq ?_)
      rw [mul_pow, mul_pow, Real.sq_sqrt hpp, Real.sq_sqrt hqq]
      ring
    calc |ccTensorBilin (I := I) g T x p q|
        = Real.sqrt ((ccTensorBilin (I := I) g T x p q) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((‖T.toSection x‖ * Real.sqrt (g.inner x p p) *
            Real.sqrt (g.inner x q q)) ^ 2) := Real.sqrt_le_sqrt hsq'
      _ = ‖T.toSection x‖ * Real.sqrt (g.inner x p p) * Real.sqrt (g.inner x q q) :=
          Real.sqrt_sq hrhs_nn
  -- Symmetrize and absorb into the supercritical Sobolev norm.
  rw [ccTensorBilinSymm_apply]
  have hbvw : |ccTensorBilin (I := I) g T x v w| ≤
      ‖T.toSection x‖ * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) :=
    hbound v w
  have hbwv : |ccTensorBilin (I := I) g T x w v| ≤
      ‖T.toSection x‖ * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by
    have h := hbound w v
    calc |ccTensorBilin (I := I) g T x w v|
        ≤ ‖T.toSection x‖ * Real.sqrt (g.inner x w w) *
            Real.sqrt (g.inner x v v) := h
      _ = ‖T.toSection x‖ * Real.sqrt (g.inner x v v) *
            Real.sqrt (g.inner x w w) := by ring
  have hsymm_bound :
      |(1 / 2 : ℝ) * (ccTensorBilin (I := I) g T x v w +
          ccTensorBilin (I := I) g T x w v)| ≤
        ‖T.toSection x‖ * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have htri := (abs_add_le (ccTensorBilin (I := I) g T x v w)
      (ccTensorBilin (I := I) g T x w v)).trans (add_le_add hbvw hbwv)
    nlinarith [htri, Real.sqrt_nonneg (g.inner x v v), Real.sqrt_nonneg (g.inner x w w),
      norm_nonneg (T.toSection x)]
  refine hsymm_bound.trans ?_
  have hsec_le :
      ‖T.toSection x‖ ≤
        C * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k) T‖ := by
    refine (hC T x).trans ?_
    exact mul_le_mul_of_nonneg_left hnorm_mono (le_of_lt hC_pos)
  have hsqv : 0 ≤ Real.sqrt (g.inner x v v) := Real.sqrt_nonneg _
  have hsqw : 0 ≤ Real.sqrt (g.inner x w w) := Real.sqrt_nonneg _
  calc ‖T.toSection x‖ * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w)
      ≤ (C * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k) T‖) *
          Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by
        refine mul_le_mul_of_nonneg_right ?_ hsqw
        exact mul_le_mul_of_nonneg_right hsec_le hsqv

end DifferentialGeometry.PDE.RicciFlow
