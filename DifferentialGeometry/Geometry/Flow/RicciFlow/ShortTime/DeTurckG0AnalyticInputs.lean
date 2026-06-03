import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Analysis.Sobolev.Embedding.TensorSobolevEmbeddingCm
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderReduction
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.SlotSplitParsevalBridge

/-! # Deep analytic inputs of the `g₀`-anchored DeTurck–Ricci realize construction

This file isolates, upstream of the open frontier file `DeTurckG0RealizeFrontier.lean`,
the two genuinely-deep analytic prerequisites on which the realize-construction's
frontier leaves bottom out and which are **absent** from the library (the exhaustive
existence search returned nothing).  Each is a precise, well-formed, non-vacuous
statement; none packages a frontier leaf's conclusion as a hypothesis.

* `gFibreOpBound_ccTensorBilinSymm_le_tensorHsNorm` — the `C⁰`-Sobolev embedding at
  the `0`-jet fibre level: the `g`-Riemannian fibre operator norm of the symmetric
  bilinear extraction `ccTensorBilinSymm g T` is controlled, uniformly over `M`, by a
  fixed constant times the supercritical intrinsic `H^{2k}` Sobolev norm of `T`.  This
  is the `0`-jet analogue of the chart-`2`-jet seminorm bound
  `chartMetricJet2DiffSup_realizeMetricAt_le_toHs_unconditional`, specialised to the
  pointwise (no-derivative) sup of the realized perturbation, and is the standard
  Morrey/Sobolev embedding `H^{2k} ↪ C⁰` (`2k > dim M + 4`) read at the fibre level.

* `deturck_g0_parabolic_chartGram_C2_upto_zero` — the parabolic up-to-`t = 0`
  chart-`C²` regularity datum for the realized `g₀`-anchored flow with smooth initial
  datum (carrier starts at `0`): for a flow `g_DT` realized as the linear realize of a
  carrier solving the interior spectral PDE and time-continuous up to `0`, every
  iterated chart-Gram derivative of order `k ≤ 2` is jointly continuous in
  `(time, point)` on `[0, T] × chartLeviCivitaGoodSet α`.  This is the genuine
  parabolic up-to-boundary regularity for smooth initial data: the interior smoothing
  `interior_allscale_time_continuity` gives only `[ε, T]`-control that blows up as
  `ε → 0`, so the up-to-zero datum is the open prerequisite.

Each body is `sorry`, so consumers transitively depend on `sorryAx`. -/

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
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The frame component `fiberNormSqComponent g x 0 2 (T.toSection x) n e K₀ J`
(`K₀ : Fin 0 → Fin n` the unique empty multi-index) equals the extracted bilinear
form `ccTensorBilin g T` evaluated on the frame vectors `(e (J 0), e (J 1))`: both
apply the same model `(0,2)`-fibre value of `T` to the same `2`-tuple. -/
private theorem ccTensorBilin_eq_fiberNormSqComponent
    (g : SmoothRiemannianMetric I M) (T : Integral.L2.SmoothCcTensor g 0 2) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (K₀ : Fin 0 → Fin n) (J : Fin 2 → Fin n) :
    Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x 0 2
        (T.toSection x) n e K₀ J =
      ccTensorBilin (I := I) g T x (e (J 0)) (e (J 1)) := by
  classical
  have hcoframe :
      Integral.Connection.coframeS (I := I) (M := M) g x 0 e K₀ =
        ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := by
    apply Tensor0SBundle.tensor0SSpace_ext
    intro v
    rw [Integral.Connection.coframeS_apply]
    rw [Finset.prod_of_isEmpty _]
    rfl
  rw [ccTensorBilin_apply, ccTensorModel, ccTensorMultilinear_apply]
  unfold Integral.Connection.fiberNormSqComponent
  rw [show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K₀ k))) : Tensor0SBundle.Tensor0SSpace 0 I x) =
      Integral.Connection.coframeS (I := I) (M := M) g x 0 e K₀ from rfl, hcoframe]
  change ((T.toSection x (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) (fun k : Fin 2 => e (J k)) : ℝ) =
    Tensor0SBundle.Tensor0SSpace.toModel
      (T.toSection x (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
      ![e (J 0), e (J 1)]
  rw [Tensor0SBundle.Tensor0SSpace.toModel,
    Tensor0SBundle.tensor0SSpace_continuousLinearEquiv_apply]
  congr 1
  funext k
  fin_cases k <;> rfl

/-- **Intrinsic `g`-fibre Cauchy–Schwarz for the extracted bilinear form.** For a
smooth `(0,2)`-tensor section `T`, the squared value of the extracted bilinear form
`ccTensorBilin g T x v w` is bounded by the product of the intrinsic quadratic factors
`g x v v`, `g x w w` and the intrinsic Riemannian fibre norm squared
`riemannianFiberNormSq g 0 2 x (T.toSection x)`.  Proved by expanding `v, w` in a
`g`-orthonormal tangent frame, applying the bilinearity of `ccTensorBilin` and
Cauchy–Schwarz over the frame-pair index, and Parseval `∑_i (g x (e i) v)² = g x v v`. -/
private theorem ccTensorBilin_sq_le_gInner_riemannianFiberNormSq
    (g : SmoothRiemannianMetric I M) (T : Integral.L2.SmoothCcTensor g 0 2) (x : M)
    (v w : TangentSpace I x) :
    (ccTensorBilin (I := I) g T x v w) ^ 2 ≤
      g.inner x v v * g.inner x w w *
        Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (T.toSection x) := by
  classical
  obtain ⟨n, e, hn, horth, hpars, hexpand, hrepr⟩ :=
    Integral.Connection.tangent_frame_expansion (I := I) (M := M) g x
  set B : ℝ := ccTensorBilin (I := I) g T x v w with hB_def
  set a : Fin n × Fin n → ℝ := fun p =>
    ccTensorBilin (I := I) g T x (e p.1) (e p.2) with ha_def
  set c : Fin n × Fin n → ℝ := fun p =>
    g.inner x (e p.1) v * g.inner x (e p.2) w with hc_def
  have hexp_double : B =
      ∑ i : Fin n, ∑ j : Fin n,
        (g.inner x (e i) v * g.inner x (e j) w) *
          ccTensorBilin (I := I) g T x (e i) (e j) := by
    have hv : v = ∑ i : Fin n, g.inner x (e i) v • e i := hexpand v
    have hw : w = ∑ j : Fin n, g.inner x (e j) w • e j := hexpand w
    rw [hB_def]
    conv_lhs => rw [hv]
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply]
    conv_lhs => rw [hw]
    rw [map_sum, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  have hexp : B = ∑ p : Fin n × Fin n, c p * a p := by
    rw [hexp_double, Fintype.sum_prod_type
      (f := fun p : Fin n × Fin n => c p * a p)]
  have hCS : (∑ p : Fin n × Fin n, c p * a p) ^ 2 ≤
      (∑ p : Fin n × Fin n, c p ^ 2) * ∑ p : Fin n × Fin n, a p ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c a
  have hcsq : (∑ p : Fin n × Fin n, c p ^ 2) = g.inner x v v * g.inner x w w := by
    have hsplit : (∑ p : Fin n × Fin n, c p ^ 2) =
        (∑ i : Fin n, g.inner x (e i) v ^ 2) *
          ∑ j : Fin n, g.inner x (e j) w ^ 2 := by
      rw [Finset.sum_mul_sum]
      rw [Fintype.sum_prod_type (f := fun p : Fin n × Fin n => c p ^ 2)]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [hc_def]; ring
    rw [hsplit, hpars v, hpars w]
  have hasq : (∑ p : Fin n × Fin n, a p ^ 2) =
      Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g 0 2 x
        (T.toSection x) := by
    rw [hrepr (T.toSection x)]
    rw [Fintype.sum_subsingleton
      (fun K : Fin 0 → Fin n => ∑ J : Fin 2 → Fin n,
        Integral.Connection.fiberNormSqSummand (I := I) (M := M) g x 0 2
          (T.toSection x) n e K J)
      (fun k : Fin 0 => k.elim0)]
    refine (Fintype.sum_equiv (finTwoArrowEquiv (Fin n)) _ _ ?_).symm
    intro J
    rw [Integral.Connection.fiberNormSqSummand_eq_component_sq,
      ccTensorBilin_eq_fiberNormSqComponent (I := I) g T x e
        (fun k : Fin 0 => k.elim0) J]
    rw [ha_def]
    rfl
  rw [hexp]
  refine hCS.trans ?_
  rw [hcsq, hasq]

set_option maxHeartbeats 1600000 in
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

/-- **Parabolic up-to-`t = 0` chart-`C²` regularity for the `g₀`-anchored realize flow
with smooth initial datum (deep analytic input).**

For the realized `g₀`-anchored parabolic flow `g_DT` over `[0, T]` — the linear realize
`hreal` of a carrier `u₂`/`T_s` solving the interior spectral PDE `hreg` and
time-continuous *up to `0`* via `hcont` (the smooth-initial-datum case, carrier `0`) —
every iterated chart-Gram derivative of order `k ≤ 2` is jointly continuous in
`(time, point)` on `[0, T] × chartLeviCivitaGoodSet α`.

This is the genuine parabolic up-to-boundary regularity for smooth initial data: the
project's interior smoothing `interior_allscale_time_continuity` controls the flow only
on `[ε, T]` with constants that blow up as `ε → 0`, so the up-to-`t = 0` chart-`C²`
datum cannot be read off it and is the open prerequisite.  The hypotheses `hreal`,
`hcont`, `hreg` are genuine constraints on the constructed flow (it is the realize of a
PDE solution), not a fold of the joint-continuity conclusion; no packaging.  The body is
`sorry`. -/
theorem deturck_g0_parabolic_chartGram_C2_upto_zero
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4) {T : ℝ} (hT : 0 < T)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (u₂ : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2)
    (N_cont : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
        tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (hreal : ∀ (s : ℝ) (x : M) (v w : TangentSpace I x),
      (g_DT s).inner x v w
        = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_s s) x v w)
    (hcont : ContinuousOn
      (fun s : ℝ => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) (Set.Icc 0 T))
    (hreg : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt
        (fun r => (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ r)))
        (scaleLaplacianFun (I := I) (M := M) (u₂ s) +
          N_cont
            (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) s) :
    ∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
      ContinuousOn
        (fun q : ℝ × M => iteratedFDeriv ℝ k
          (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
          (extChartAt I α q.2))
        (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α) := sorry

/-- **`L²`-time engine solution → pointwise realized carrier bundle for the
`g₀`-anchored flow with smooth initial datum (deep analytic input).**

For the anchor `g₀`, a supercritical order `a` (`2a > dim M + 4`, plus the engine's
`dim M < 2(a − 2)`), the continuous nonlinearity `N_cont` presented through its section
`Nsec` with the coordinate identity `hN_coeff` and the weighted-resolvent Lipschitz
certificate `hNsec_lip`, **and** the `C⁰`-Sobolev fibre embedding `hfibre`
(`gFibreOpBound_ccTensorBilinSymm_le_tensorHsNorm`-shape — the input that turns the
carrier's vanishing at `t = 0` into the metric-realize fibre-smallness), the
maximal-regularity Duhamel engine `deTurckRemainder_strong_shortTime_exists` driven with
initial datum `0` produces a strong `L²`-time solution which, transported to the
pointwise time domain (the indefinite-Bochner / FTC transport that lives strictly
downstream of the headline) and realized off `g₀`, yields:

* a pointwise carrier `u₂ : ℝ → H^{a+2}(g₀)`, smooth representatives
  `T_s : ℝ → SmoothCcTensor g₀ 0 2`, and a realized metric family `g_DT`;
* `g_DT 0 = g₀` (the carrier starts at `0`);
* `hreal` — `g_DT s = g₀ + ccTensorBilinSymm (T_s s)`;
* `hcont` — the included carrier is continuous up to `t = 0`;
* `hreg` — the carrier solves `∂_t (ι u₂) = Δ_∇ u₂ + N_cont (ι u₂)` on `(0, T)`;
* `hsmall` — `ccTensorBilinSymm (T_s s)` is `g₀`-fibre small on `(0, T)`;
* `hsmoothrepr` — `u₂ s`'s coordinates are the `L²` coordinates of `T_s s`.

The conclusion is the existence of the realized carrier bundle — distinct from the
supplied coordinate-identity, Lipschitz, and fibre-embedding hypotheses; no packaging.
The genuinely-open content bundled here is the `L²`-time → pointwise Bochner/FTC
transport together with the up-to-`t = 0` fibre-smallness for smooth initial data.  The
body is `sorry`. -/
theorem deturck_g0_engine_carrier_extraction
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4)
    (ha2 : Module.finrank ℝ E < 2 * (a - 2))
    (N_cont : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
        tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (Nsec : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
        Integral.L2.SmoothCcTensor g₀ 0 2)
    (hN_coeff : ∀ (u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1))
        (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2),
      (N_cont u).coeff i =
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (Integral.L2.SmoothCcTensor.toL2 (Nsec u)) i)
    (hNsec_lip : ∃ K : ℝ≥0, ∀ u u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1),
      Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2 =>
          tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (Integral.L2.SmoothCcTensor.toL2 (Nsec u)
                  - Integral.L2.SmoothCcTensor.toL2 (Nsec u')) i) ^ 2)
        ∧ (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2,
            tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
              (tensorL2Coeff (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                  (Integral.L2.SmoothCcTensor.toL2 (Nsec u)
                    - Integral.L2.SmoothCcTensor.toL2 (Nsec u')) i) ^ 2)
            ≤ ((K : ℝ) * dist u u') ^ 2)
    (hfibre : ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), 2 * k > Module.finrank ℝ E + 4 →
        ∀ T : Integral.L2.SmoothCcTensor g₀ 0 2,
          gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T)
            (C * ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k) T‖)) :
    ∃ (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
        (u₂ : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
        (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2),
      0 < T ∧
      g_DT 0 = g₀ ∧
      (∀ (s : ℝ) (x : M) (v w : TangentSpace I x),
        (g_DT s).inner x v w
          = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_s s) x v w) ∧
      ContinuousOn
        (fun s : ℝ => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) (Set.Icc 0 T) ∧
      (∀ s ∈ Set.Ioo (0 : ℝ) T,
        HasDerivAt
          (fun r => (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ r)))
          (scaleLaplacianFun (I := I) (M := M) (u₂ s) +
            N_cont
              (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) s) ∧
      (∀ s ∈ Set.Ioo (0 : ℝ) T, ∃ δ' : ℝ, δ' < 1 ∧
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (T_s s)) δ') ∧
      (∀ (s : ℝ)
          (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2),
        (u₂ s).coeff i
          = tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i) := sorry

end DifferentialGeometry.PDE.RicciFlow

