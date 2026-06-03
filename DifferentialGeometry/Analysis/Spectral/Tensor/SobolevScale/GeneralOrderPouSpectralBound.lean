import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Order2Equivalence
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.AllOrderGardingBootstrap
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.SobolevScaleSummable
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebey

/-!
# General-order intrinsic-Sobolev control by the spectral Sobolev norm

For a closed Riemannian manifold `(M, g₀)` and a smooth compactly-supported
`(0, 2)`-tensor section `T`, the intrinsic order-`2k` Sobolev norm
`‖T.toHs (2k)‖` (the partition-of-unity Hilbert–Schmidt chart-Sobolev completion
norm, `tensorPouSobolevHilbert_norm_eq`) is controlled by the **spectral**
order-`2k` Sobolev norm of `T`, namely the square root of the weighted spectral
square-sum

  `∑ᵢ (1 + λᵢ)^{2k} · (tensorL2Coeff (T.toL2) i)²`

of the eigenbasis coordinates of `T`'s `L²` class against the connection-Laplacian
resolvent eigenbasis.  This is the general-order ("all `k`") analogue of the
order-`2` two-sided comparison
`tensorPouSobolevHs_order2_equiv_pouSobolev`/`Order2NormEquivOnSmooth`
(`Order2Equivalence.lean`): the elliptic-regularity / Gårding direction that
bounds the intrinsic chart-Sobolev norm by the `Δ_∇`-`L²` spectral norm, lifted
from order `2` to every order `2k`.

`pouSobolevToHsNorm_le_spectral`: for every order `k` there is a constant `C ≥ 0`
such that for every smooth compactly-supported `(0, 2)`-tensor `T`,

  `‖T.toHs (2k)‖ ≤ C · √(∑ᵢ (1 + λᵢ)^{4k} · (tensorL2Coeff (T.toL2) i)²)`.

## Sobolev-index bookkeeping (why the spectral weight is `4k`, not `2k`)

The intrinsic chart-Sobolev norm `‖T.toHs (2k)‖ = (tensorPouSobolevHsNorm g (2k)
T).toReal` aggregates the iterated Fréchet derivatives of the chart-frame
components up to order `2 · (2k) = 4k` (the `range (2 · (2k) + 1)` in
`tensorPouSobolevHsNorm`); equivalently, via the reverse Hebey-Sobolev bridge
`exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum`, it is
controlled by the `L²` norms of the covariant gradients `∇^j T` for `j ≤ 4k`. The
all-order intrinsic Gårding bootstrap `allOrder_covGrad_l2Norm_le_lapIter_sum`
controls `∑_{j ≤ 4k} ‖∇^j T‖_{L²}` by `∑_{i ≤ 2k} ‖Δ_∇^i T‖_{L²}`. Finally the
spectral identity `‖Δ_∇^i T‖²_{L²} = ∑ᵢ λᵢ^{2i} · cᵢ(T)²` and the termwise bound
`λᵢ^{2i} ≤ (1 + λᵢ)^{4k}` (valid for `i ≤ 2k`, i.e. `2i ≤ 4k`) collapse the
right-hand side to the single spectral weight `(1 + λᵢ)^{4k}`. The spectral
exponent is therefore `4k`, matching the `H^{4k}` regularity of `‖T.toHs (2k)‖`;
the per-order constant `C` grows with `k` (the reverse-Hebey, bootstrap, and
finite-collapse constants are all order-dependent), so it is quantified inside the
`∀ k` rather than uniformly.

This is the genuine elliptic ("Gårding") lift to general order; orders `0` and
`1` are chart-locality-free in `L2BanachIso`/`CompactInclusionIntrinsic`, and the
order-`2` Hilbert–Schmidt comparison is `tensorPouSobolevHs_order2_equiv_pouSobolev`.
It carries no chart-locality predicate (no `HasLocallyConstantChartAt`).  It rests on
the all-order bootstrap `allOrder_covGrad_l2Norm_le_lapIter_sum_unconditional`, whose
posited curvature inputs (`order2GardingFamily_holds`, `commutatorDefectBound_holds`)
are `sorry`; consumers therefore transitively depend on `sorryAx`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral
namespace SobolevScale

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **The single iterated-Laplacian `L²` norm ≤ spectral norm bound.** For a smooth
compactly-supported `(0, 2)`-tensor `T`, a gradient order `i`, and an even spectral
exponent `N` with `2 * i ≤ N`, the `L²` norm of the iterated rough Laplacian
`Δ_∇^i T` is bounded by the square root of the weighted spectral square-sum
`∑ᵢ (1 + λᵢ)^N · cᵢ(T)²`.

The squared `L²` norm of `Δ_∇^i T` equals `∑ᵢ λᵢ^{2i} · cᵢ(T)²` (Parseval applied
to the iterated `L²`-coordinate eigen-equation `cᵢ(Δ_∇^i T) = (-λᵢ)^i · cᵢ(T)`), and
`λᵢ^{2i} ≤ (1 + λᵢ)^N` termwise because `λᵢ ≥ 0`, `1 ≤ 1 + λᵢ`, and `2 * i ≤ N`;
summability of the weighted family for the smooth `T` lifts the termwise bound to the
infinite sums. -/
private theorem rawConnLapIter_l2Norm_le_sqrt_spectral
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) (i N : ℕ)
    (hiN : 2 * i ≤ N) :
    ‖SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
        (rawTensorConnLapIter (I := I) g 0 2 i T)‖ ≤
      Real.sqrt (∑' j : TensorEigenIdx (I := I) (M := M) g 0 2,
        tensorSobolevWeight (I := I) (M := M) j (N : ℝ) *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 T) j) ^ 2) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2 with hc_def
  set cT : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun j => tensorL2Coeff (I := I) (M := M) hc (SmoothCcTensor.toL2 T) j with hcT_def
  -- `‖Δ_∇^i T‖² = ∑ⱼ λⱼ^{2i} · cⱼ(T)²`.
  have hsq_eq :
      ‖SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
          (rawTensorConnLapIter (I := I) g 0 2 i T)‖ ^ 2 =
        ∑' j : TensorEigenIdx (I := I) (M := M) g 0 2,
          (TensorEigenIdx.lambda (I := I) (M := M) j) ^ (2 * i) * (cT j) ^ 2 := by
    rw [← tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 i T))]
    refine tsum_congr (fun j => ?_)
    rw [rawConnLapIter_tensorL2Coeff (I := I) (M := M) g T j i]
    rw [mul_pow, ← pow_mul, mul_comm i 2,
      (even_two_mul i).neg_pow (TensorEigenIdx.lambda (I := I) (M := M) j)]
  -- The weighted family `(1 + λⱼ)^N · cⱼ(T)²` is summable.
  have hsummable :
      Summable (fun j : TensorEigenIdx (I := I) (M := M) g 0 2 =>
        tensorSobolevWeight (I := I) (M := M) j (N : ℝ) * (cT j) ^ 2) :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g (N : ℝ) T hc
  -- Termwise domination `λⱼ^{2i} · cⱼ² ≤ (1 + λⱼ)^N · cⱼ²`.
  have hterm : ∀ j : TensorEigenIdx (I := I) (M := M) g 0 2,
      (TensorEigenIdx.lambda (I := I) (M := M) j) ^ (2 * i) * (cT j) ^ 2 ≤
        tensorSobolevWeight (I := I) (M := M) j (N : ℝ) * (cT j) ^ 2 := by
    intro j
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hlam_nn : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) j :=
      tensor_lambda_nonneg (I := I) (M := M) j
    have h_one_le : (1 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) j := by linarith
    have h_base_le : TensorEigenIdx.lambda (I := I) (M := M) j ≤
        1 + TensorEigenIdx.lambda (I := I) (M := M) j := by linarith
    have h1 : (TensorEigenIdx.lambda (I := I) (M := M) j) ^ (2 * i) ≤
        (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ (2 * i) :=
      pow_le_pow_left₀ hlam_nn h_base_le (2 * i)
    have h2 : (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ (2 * i) ≤
        (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ N :=
      pow_le_pow_right₀ h_one_le hiN
    have hw : tensorSobolevWeight (I := I) (M := M) j (N : ℝ) =
        (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ N := by
      unfold tensorSobolevWeight
      rw [Real.rpow_natCast]
    rw [hw]
    exact le_trans h1 h2
  -- The summability of the smaller family follows by domination.
  have hsummable_small :
      Summable (fun j : TensorEigenIdx (I := I) (M := M) g 0 2 =>
        (TensorEigenIdx.lambda (I := I) (M := M) j) ^ (2 * i) * (cT j) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun j => ?_) hterm hsummable
    have hlam_nn : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) j :=
      tensor_lambda_nonneg (I := I) (M := M) j
    positivity
  -- Lift the termwise bound to the tsums.
  have htsum_le :
      ∑' j : TensorEigenIdx (I := I) (M := M) g 0 2,
          (TensorEigenIdx.lambda (I := I) (M := M) j) ^ (2 * i) * (cT j) ^ 2 ≤
        ∑' j : TensorEigenIdx (I := I) (M := M) g 0 2,
          tensorSobolevWeight (I := I) (M := M) j (N : ℝ) * (cT j) ^ 2 :=
    Summable.tsum_le_tsum hterm hsummable_small hsummable
  -- Conclude via square roots.
  have hnn : 0 ≤ ‖SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
      (rawTensorConnLapIter (I := I) g 0 2 i T)‖ := norm_nonneg _
  rw [← Real.sqrt_sq hnn, hsq_eq]
  exact Real.sqrt_le_sqrt htsum_le

set_option linter.unusedSectionVars false in
/-- **General-order intrinsic-Sobolev control by the spectral Sobolev norm
(deep elliptic / Gårding lift).**

For every order `k` there is a constant `C ≥ 0` such that for every smooth
compactly-supported `(0, 2)`-tensor section `T`, the intrinsic order-`2k`
partition-of-unity Hilbert–Schmidt chart-Sobolev norm `‖T.toHs (2k)‖` (an `H^{4k}`
chart-Sobolev norm) is bounded by `C` times the square root of the weighted spectral
square-sum `∑ᵢ (1 + λᵢ)^{4k} · (tensorL2Coeff (T.toL2) i)²` of the eigenbasis
coordinates of `T`'s `L²` class.

This is the general-order ("all `k`") elliptic-regularity / Gårding lift of the
order-`2` two-sided norm comparison `tensorPouSobolevHs_order2_equiv_pouSobolev`: the
intrinsic chart-Sobolev norm is controlled by the `Δ_∇`-`L²` spectral norm at the
matching order `4k`.  It carries no chart-locality predicate.  The conclusion is a
norm bound, structurally distinct from any spectral-decay hypothesis (no packaging).

The Sobolev exponent on the right is `4k = 2 · (2k)`, matching the `H^{4k}`
regularity of `‖T.toHs (2k)‖`; the constant `C` depends on `k` (it is quantified
inside the `∀ k`). The proof composes the reverse Hebey-Sobolev bridge
(`exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum`, chart
`H^{4k}` ≤ `L²` of `∇^{≤ 4k}`), the all-order intrinsic Gårding bootstrap
(`allOrder_covGrad_l2Norm_le_lapIter_sum_unconditional`, `∑_{j ≤ 4k} ‖∇^j T‖ ≤
∑_{i ≤ 2k} ‖Δ_∇^i T‖`), and the spectral collapse
`rawConnLapIter_l2Norm_le_sqrt_spectral` (each `‖Δ_∇^i T‖`, `i ≤ 2k`, bounded by the
single spectral weight `(1 + λ)^{4k}`). -/
theorem pouSobolevToHsNorm_le_spectral
    (g₀ : SmoothRiemannianMetric I M) :
    ∀ (k : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : SmoothCcTensor g₀ 0 2),
      ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k) T‖ ≤
        C * Real.sqrt (∑' i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
          tensorSobolevWeight (I := I) (M := M) i ((2 * (2 * k) : ℕ) : ℝ) *
            (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 T) i) ^ 2) := by
  classical
  intro k
  -- Reverse Hebey-Sobolev bridge: `‖T.toHs (2k)‖ ≤ C_B · ∑_{j ≤ 4k} ‖∇^j T‖_{L²}`.
  obtain ⟨CB, hCB_nn, hCB⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum
      (I := I) (M := M) g₀ 0 2 (2 * k)
  -- All-order intrinsic Gårding bootstrap at order `2k`:
  -- `∑_{j ≤ 4k} ‖∇^j T‖_{L²} ≤ C₁ · ∑_{i ≤ 2k} ‖Δ_∇^i T‖_{L²}`.
  obtain ⟨C₁, hC₁_nn, hC₁⟩ :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.allOrder_covGrad_l2Norm_le_lapIter_sum_unconditional
      (I := I) (M := M) g₀ (2 * k)
  refine ⟨CB * (C₁ * (2 * k + 1)), by positivity, fun T => ?_⟩
  set Nspec : ℝ := Real.sqrt (∑' i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      tensorSobolevWeight (I := I) (M := M) i ((2 * (2 * k) : ℕ) : ℝ) *
        (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 T) i) ^ 2) with hNspec_def
  have hNspec_nn : 0 ≤ Nspec := Real.sqrt_nonneg _
  -- Step 1: chart `H^{4k}` norm.
  rw [tensorPouSobolevHilbert_norm_eq (I := I) (M := M) g₀ (2 * k) T]
  -- Bound the bootstrap right-hand side: each `‖Δ_∇^i T‖_{L²} ≤ Nspec` for `i ≤ 2k`.
  set GradSum : ℝ := ∑ j ∈ Finset.range (2 * (2 * k) + 1),
    tensorL2Norm (I := I) (M := M) g₀ 0 (2 + j)
      (iteratedCovGrad g₀ 0 2 j T).toFun with hGradSum_def
  set LapSum : ℝ := ∑ i ∈ Finset.range (2 * k + 1),
    ‖SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
      (rawTensorConnLapIter (I := I) g₀ 0 2 i T)‖ with hLapSum_def
  have hLapSum_le : LapSum ≤ (2 * k + 1 : ℝ) * Nspec := by
    rw [hLapSum_def]
    have hterm : ∀ i ∈ Finset.range (2 * k + 1),
        ‖SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (rawTensorConnLapIter (I := I) g₀ 0 2 i T)‖ ≤ Nspec := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hiN : 2 * i ≤ 2 * (2 * k) := by omega
      rw [hNspec_def]
      exact rawConnLapIter_l2Norm_le_sqrt_spectral (I := I) (M := M) g₀ T i
        (2 * (2 * k)) hiN
    calc ∑ i ∈ Finset.range (2 * k + 1),
            ‖SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (rawTensorConnLapIter (I := I) g₀ 0 2 i T)‖
        ≤ ∑ _i ∈ Finset.range (2 * k + 1), Nspec := Finset.sum_le_sum hterm
      _ = (Finset.range (2 * k + 1)).card • Nspec := by rw [Finset.sum_const]
      _ = (2 * k + 1 : ℝ) * Nspec := by
            rw [Finset.card_range, nsmul_eq_mul]; push_cast; ring
  -- Assemble.
  have hbootstrap : GradSum ≤ C₁ * LapSum := hC₁ T
  have hreverse :
      (tensorPouSobolevHsNorm (I := I) (M := M) g₀ (2 * k) T).toReal ≤ CB * GradSum :=
    hCB T
  calc (tensorPouSobolevHsNorm (I := I) (M := M) g₀ (2 * k) T).toReal
      ≤ CB * GradSum := hreverse
    _ ≤ CB * (C₁ * LapSum) := by
          exact mul_le_mul_of_nonneg_left hbootstrap hCB_nn
    _ ≤ CB * (C₁ * ((2 * k + 1 : ℝ) * Nspec)) := by
          have h := mul_le_mul_of_nonneg_left hLapSum_le hC₁_nn
          exact mul_le_mul_of_nonneg_left h hCB_nn
    _ = CB * (C₁ * (2 * k + 1)) * Nspec := by ring

end SobolevScale
end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
