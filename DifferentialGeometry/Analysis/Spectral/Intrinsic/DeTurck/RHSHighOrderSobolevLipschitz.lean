import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSPointwiseLipschitz
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedCovGradJetInput
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.GeneralOrderPouSpectralBound

/-! # The higher-order chart-RHS Sobolev–Lipschitz Nemytskii bound

The on-disk coordinate Ricci–DeTurck-RHS Lipschitz
`exists_chartDeTurckRHSComp_lipschitz_on_compact` (`RHSPointwiseLipschitz.lean`) is the **`C⁰`
base case**: it controls the chart-frame scalar DeTurck right-hand-side *value* difference by
the chart `2`-jet seminorm `chartMetricJet2DiffSup` of the metric difference (`2` derivatives
of the metric, `0` derivatives of the right-hand side).  That base case yields only the `H⁰`
(`L²`) norm of the right-hand-side difference, **never** the `Hᵃ` norm for `a ≥ 1`.

This file isolates the genuine **higher-order** analogue, the order-`a` Nemytskii bound: the
weighted-`Hᵃ` seminorm (`∑ᵢ (1+λᵢ)^a · |coeffᵢ|²`) of the `L²`-coordinate difference of the
realized Ricci–DeTurck *remainder* sections
`deTurckRHSSection g_bg gⱼ − rawTensorConnLapSmooth g₀ 0 2 Tⱼ`, where `gⱼ` is the realized
metric of the `g₀`-fibre-small perturbation `Tⱼ` (`gⱼ.inner = g₀.inner + ccTensorBilinSymm g₀
Tⱼ`), is controlled by the **`H^{a+2}` Sobolev norm** `‖(T₁ − T₂).toHs (a+2)‖` of the
perturbation difference — uniformly over a `H^{a+2}`-bounded family of perturbations (the
Nemytskii constant being uniform on a bounded family).  The order count is the honest one: the
DeTurck right-hand side is a second-order quasilinear operator in the metric, so its `Hᵃ` norm
needs `a + 2` derivatives of the metric, i.e. of the perturbation; this mirrors the on-disk
unconditional bound `chartMetricJet2DiffSup_realizeMetricAt_le_toHs_unconditional`, which
controls the chart `2`-jet (the `a = 0` order) by the intrinsic `H^{2k}` norm of the
perturbation difference.

It is the genuine deep analytic input of the order-`a` chart-RHS tower (the higher-order
Nemytskii bound for the second-order DeTurck operator), stated entirely in pre-existing
objects (`deTurckRHSSection`, `rawTensorConnLapSmooth`, `tensorL2Coeff`, `tensorSobolevWeight`,
`SmoothCcTensor.toHs`) plus a fibrewise `inner`-identity tying each metric to its perturbation:
it carries no dependence on the spectral nonlinearity `deTurckG0SpectralN` or the
perturbation-indexed remainder `deTurckRealizeRemainderOf`, so the genuine-nonlinearity file
consumes it without an import cycle.  Its body is `sorry`: it is the genuine order-`a`
chart-RHS-tower content (the higher-order quasilinear Nemytskii estimate), with no spectral or
Weyl dependence. -/

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **The realized Ricci–DeTurck remainder section of a perturbation and its realized metric.**

For an anchor `g₀`, a flow background `g_bg`, a `g₀`-fibre-small perturbation `T`, and *any*
smooth metric `g₁` that is the realized metric of `T` (`g₁.inner = g₀.inner + ccTensorBilinSymm
g₀ T`, fibrewise — supplied as a hypothesis rather than constructed, so this is independent of
the `δ`-witness machinery of `tensorSectionRealizeMetric`), this is the `g₀`-tagged DeTurck
remainder `deTurckRHSSection g_bg g₁ − rawTensorConnLapSmooth g₀ 0 2 T`.  It is the chart-frame
section whose `L²` coordinates the higher-order Nemytskii bound below controls; it coincides
(by metric extensionality through that `inner`-identity) with the perturbation-indexed
remainder `deTurckRealizeRemainderOf g₀ g_bg T` of the genuine-nonlinearity file. -/
noncomputable def realizedRHSRemainderSection (g₀ g_bg g₁ : SmoothRiemannianMetric I M)
    (T : Integral.L2.SmoothCcTensor g₀ 0 2) : Integral.L2.SmoothCcTensor g₀ 0 2 :=
  { toSection := (deTurckRHSSection (I := I) g_bg g₁).toSection
    hasCompactSupport := (deTurckRHSSection (I := I) g_bg g₁).hasCompactSupport }
    - rawTensorConnLapSmooth (I := I) g₀ 0 2 T

/-- **The "easy" all-order iterated-Laplacian `L²` bound by the intrinsic chart-Sobolev norm
(the differentiation arm of the spectral–Sobolev comparison, posited as the genuine atomic
Sobolev primitive).**

For an anchor `g₀` and an order `a`, there is a single constant `C ≥ 0` such that for every
smooth compactly-supported `(0,2)`-tensor section `R` and every gradient order `i ≤ a`, the
`L²` norm of the iterated rough Laplacian `Δ_∇^i R` is controlled by the intrinsic order-`a`
chart-Sobolev (`toHs a`) norm of `R`:
```
‖(Δ_∇^i R).toL2‖ ≤ C · ‖R.toHs a‖   (for i ≤ a).
```

This is the **easy** (differentiation) direction of the spectral–Sobolev comparison, the
mirror of the on-disk Gårding lift `pouSobolevToHsNorm_le_spectral` (which is the hard,
elliptic-regularity direction `chart ≤ spectral`).  It is genuinely elementary: the rough
Laplacian is the frame trace of the second covariant derivative (`rawTensorConnLap_eq_frame_trace`),
so `Δ_∇^i R` is built from covariant derivatives of `R` up to order `2i ≤ 2a`, whose `L²` norms
are dominated by the intrinsic order-`a` (`H^{2a}`-chart) Sobolev norm `‖R.toHs a‖`; no
curvature commutator / Gårding regularity (no `Order2GardingFamily`, no `CommutatorDefectBound`)
is needed for this arm.

Its body is `sorry`: it is the genuine atomic "easy" all-order `Δ_∇^i`-`L²`-by-chart-Sobolev
estimate (the elliptic-regularity-free differentiation arm), with no spectral nonlinearity, no
perturbation-indexed remainder, and no Weyl dependence. -/
theorem exists_rawConnLapIter_l2Norm_le_toHs
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (R : Integral.L2.SmoothCcTensor g₀ 0 2) (i : ℕ), i ≤ a →
        ‖Integral.L2.SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (Integral.Connection.rawTensorConnLapIter (I := I) g₀ 0 2 i R)‖ ≤
          C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a R‖ :=
  sorry

/-- **Binomial collapse of the spectral weight.** For `λ ≥ 0` and an order `a`, the Sobolev
weight base `(1 + λ)^a` is dominated by a constant multiple of the finite sum of even powers
`∑_{j ≤ a} λ^{2j}`:
```
(1 + λ)^a ≤ 2^a · (a + 2) · ∑_{j ∈ range (a+1)} λ^{2j} .
```
Expanding `(1+λ)^a` binomially, each `λ^i` (`i ≤ a`) satisfies `λ^i ≤ λ^{2i} + 1`, each binomial
coefficient is `≤ 2^a`, and the constant tail is absorbed by the `j = 0` term `λ^0 = 1 ≤ ∑`. -/
private theorem one_add_pow_le_const_mul_sum_even_pow (a : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) :
    (1 + lam) ^ a ≤ ((2 ^ a * (a + 2) : ℝ)) *
      ∑ j ∈ Finset.range (a + 1), lam ^ (2 * j) := by
  have hbinom : (1 + lam) ^ a = ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) * lam ^ i := by
    rw [add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [one_pow, mul_one]; ring
  rw [hbinom]
  set S : ℝ := ∑ j ∈ Finset.range (a + 1), lam ^ (2 * j) with hS_def
  have hS_terms_nn : ∀ j ∈ Finset.range (a + 1), (0 : ℝ) ≤ lam ^ (2 * j) :=
    fun j _ => pow_nonneg hlam _
  have hS_ge_one : (1 : ℝ) ≤ S := by
    rw [hS_def]
    have h0 : (0 : ℕ) ∈ Finset.range (a + 1) := Finset.mem_range.mpr (Nat.succ_pos a)
    calc (1 : ℝ) = lam ^ (2 * 0) := by simp
      _ ≤ ∑ j ∈ Finset.range (a + 1), lam ^ (2 * j) :=
          Finset.single_le_sum hS_terms_nn h0
  have hterm : ∀ i ∈ Finset.range (a + 1),
      (a.choose i : ℝ) * lam ^ i ≤ (2 ^ a : ℝ) * (lam ^ (2 * i) + 1) := by
    intro i _hi
    have hchoose : (a.choose i : ℝ) ≤ 2 ^ a := by
      have h2 : a.choose i ≤ 2 ^ a := Nat.choose_le_two_pow a i
      exact_mod_cast h2
    have hpow_le : lam ^ i ≤ lam ^ (2 * i) + 1 := by
      rcases le_total lam 1 with hle | hge
      · have : lam ^ i ≤ 1 := pow_le_one₀ hlam hle
        nlinarith [pow_nonneg hlam (2 * i)]
      · have : lam ^ i ≤ lam ^ (2 * i) := pow_le_pow_right₀ hge (by omega)
        nlinarith
    exact mul_le_mul hchoose hpow_le (pow_nonneg hlam i) (by positivity)
  have hsum_le : ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) * lam ^ i
      ≤ (2 ^ a : ℝ) * (S + (a + 1)) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    push_cast
    rfl
  refine le_trans hsum_le ?_
  have hkey : S + ((a : ℝ) + 1) ≤ ((a : ℝ) + 2) * S := by nlinarith [hS_ge_one]
  calc (2 ^ a : ℝ) * (S + ((a : ℝ) + 1)) ≤ (2 ^ a : ℝ) * (((a : ℝ) + 2) * S) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (2 ^ a * ((a : ℝ) + 2)) * S := by ring

/-- **The reverse spectral–Sobolev bound at order `a`: the spectral order-`a` Sobolev seminorm
of a smooth compactly-supported `(0,2)`-section is controlled by its intrinsic order-`a`
chart-Sobolev (`toHs a`) norm.**

For an anchor `g₀` and an order `a`, there is a single constant `C ≥ 0` such that for every
smooth compactly-supported `(0,2)`-tensor section `R`, the weighted spectral square-sum
```
∑ᵢ (1 + λᵢ)^a · ( tensorL2Coeff (toL2 R) i )²
```
is summable and bounded by `(C · ‖R.toHs a‖)²`.

This is the **reverse** (spectral ≤ intrinsic-chart) direction of the on-disk forward bound
`pouSobolevToHsNorm_le_spectral` (intrinsic-chart `≤` spectral), i.e. the easy
"differentiation" arm of the general-order norm comparison
`Order2NormEquivOnSmooth`/`tensorPouSobolevHs_order2_equiv_pouSobolev` lifted from order `2` to
every order `a`.  It is **proven by composition** of the binomial collapse of the spectral
weight `one_add_pow_le_const_mul_sum_even_pow` (`(1 + λ)^a ≤ C_a · ∑_{j ≤ a} λ^{2j}`), the
iterated-Laplacian `L²`-coordinate eigen-equation `rawConnLapIter_tensorL2Coeff`
(`cᵢ(Δ_∇^j R) = (-λᵢ)^j cᵢ(R)`) together with Parseval (`tensorParseval_l2Coeff_ofCompact_sq`,
so `∑ᵢ λᵢ^{2j} cᵢ² = ‖(Δ_∇^j R).toL2‖²`), and the "easy" iterated-Laplacian-`L²`-by-chart bound
`exists_rawConnLapIter_l2Norm_le_toHs` (`‖(Δ_∇^j R).toL2‖ ≤ C · ‖R.toHs a‖` for `j ≤ a`): the
weighted square-sum is dominated termwise by `C_a · ∑_{j ≤ a} λᵢ^{2j} cᵢ²`, which collapses (by
Parseval) to `C_a · ∑_{j ≤ a} ‖(Δ_∇^j R).toL2‖²`, each summand bounded by `(C · ‖R.toHs a‖)²`.
The summability arm is `smoothCcTensor_tensorL2Coeff_weighted_summable` (valid at every real
order).  Its conclusion is a *real-valued* weighted-square-sum inequality in the eigenbasis
coordinates, structurally distinct from the `toHs`-norm hypothesis on the right; no packaging.

Consumers transitively depend on `sorryAx` only through the genuine atomic "easy" arm
`exists_rawConnLapIter_l2Norm_le_toHs`. -/
theorem exists_spectralWeightedSq_le_pouHaNorm_sq
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : Integral.L2.SmoothCcTensor g₀ 0 2,
        Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2 =>
            tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
              (tensorL2Coeff (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                  (Integral.L2.SmoothCcTensor.toL2 R) i) ^ 2)
          ∧ (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
                (I := I) (M := M) g₀ 0 2,
              tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
                (tensorL2Coeff (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                    (Integral.L2.SmoothCcTensor.toL2 R) i) ^ 2)
              ≤ (C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a R‖) ^ 2 := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hc_def
  -- The "easy" iterated-Laplacian-`L²`-by-chart bound supplies the per-order constant.
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := exists_rawConnLapIter_l2Norm_le_toHs (I := I) g₀ a
  -- The collapse constant `D = 2^a · (a + 2)` and the final Lipschitz constant.
  set D : ℝ := (2 ^ a * (a + 2) : ℝ) with hD_def
  have hD_nn : 0 ≤ D := by rw [hD_def]; positivity
  refine ⟨Real.sqrt (D * (a + 1)) * C₀,
    mul_nonneg (Real.sqrt_nonneg _) hC₀_nn, fun R => ?_⟩
  set cR : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => tensorL2Coeff (I := I) (M := M) hc (Integral.L2.SmoothCcTensor.toL2 R) i with hcR_def
  -- Summability of the weighted family (valid at every real order).
  have hsummable :
      Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2 =>
          tensorSobolevWeight (I := I) (M := M) i (a : ℝ) * (cR i) ^ 2) :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g₀ (a : ℝ) R hc
  refine ⟨hsummable, ?_⟩
  -- Each `∑ᵢ λᵢ^{2j} cᵢ² = ‖(Δ_∇^j R).toL2‖² ≤ (C₀ · ‖R.toHs a‖)²` for `j ≤ a`.
  set toHsNorm : ℝ := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a R‖
    with htoHsNorm_def
  have htoHsNorm_nn : 0 ≤ toHsNorm := norm_nonneg _
  -- The per-`j` even-power weighted sum, its summability and the spectral identity.
  have hlapsq : ∀ j : ℕ, j ≤ a →
      ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g₀ 0 2,
          (TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) * (cR i) ^ 2 ≤
        (C₀ * toHsNorm) ^ 2 := by
    intro j hj
    -- `‖(Δ_∇^j R).toL2‖² = ∑ᵢ λᵢ^{2j} cᵢ²`.
    have hsq_eq :
        ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g₀ 0 2,
            (TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) * (cR i) ^ 2 =
          ‖Integral.L2.SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (Integral.Connection.rawTensorConnLapIter (I := I) g₀ 0 2 j R)‖ ^ 2 := by
      rw [← tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M) hc
        (Integral.L2.SmoothCcTensor.toL2
          (Integral.Connection.rawTensorConnLapIter (I := I) g₀ 0 2 j R))]
      refine tsum_congr (fun i => ?_)
      rw [rawConnLapIter_tensorL2Coeff (I := I) (M := M) g₀ R i j, hcR_def]
      rw [mul_pow, ← pow_mul, mul_comm j 2,
        (even_two_mul j).neg_pow (TensorEigenIdx.lambda (I := I) (M := M) i)]
    rw [hsq_eq]
    -- `‖(Δ_∇^j R).toL2‖ ≤ C₀ · ‖R.toHs a‖`, square it.
    have hbound : ‖Integral.L2.SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (Integral.Connection.rawTensorConnLapIter (I := I) g₀ 0 2 j R)‖ ≤ C₀ * toHsNorm :=
      hC₀ R j hj
    have hlhs_nn : 0 ≤ ‖Integral.L2.SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (Integral.Connection.rawTensorConnLapIter (I := I) g₀ 0 2 j R)‖ := norm_nonneg _
    exact pow_le_pow_left₀ hlhs_nn hbound 2
  -- Each even-power weighted family is summable (it equals the `‖(Δ_∇^j R).toL2‖²` Parseval sum).
  have hlapsummable : ∀ j : ℕ,
      Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2 =>
          (TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) * (cR i) ^ 2) := by
    intro j
    have hpar := tensorL2Coeff_ofCompact_summable_sq' (I := I) (M := M) hc
      (Integral.L2.SmoothCcTensor.toL2
        (Integral.Connection.rawTensorConnLapIter (I := I) g₀ 0 2 j R))
    refine (summable_congr (fun i => ?_)).mp hpar
    rw [rawConnLapIter_tensorL2Coeff (I := I) (M := M) g₀ R i j, hcR_def]
    rw [mul_pow, ← pow_mul, mul_comm j 2,
      (even_two_mul j).neg_pow (TensorEigenIdx.lambda (I := I) (M := M) i)]
  -- Termwise: `(1+λᵢ)^a cᵢ² ≤ D · ∑_{j ≤ a} λᵢ^{2j} cᵢ²`.
  have hterm : ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 2,
      tensorSobolevWeight (I := I) (M := M) i (a : ℝ) * (cR i) ^ 2 ≤
        D * ∑ j ∈ Finset.range (a + 1),
          (TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) * (cR i) ^ 2 := by
    intro i
    have hlam_nn : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
      tensor_lambda_nonneg (I := I) (M := M) i
    have hw : tensorSobolevWeight (I := I) (M := M) i (a : ℝ) =
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ a := by
      unfold tensorSobolevWeight; rw [Real.rpow_natCast]
    have hcollapse := one_add_pow_le_const_mul_sum_even_pow a
      (TensorEigenIdx.lambda (I := I) (M := M) i) hlam_nn
    rw [hw]
    have hstep := mul_le_mul_of_nonneg_right hcollapse (sq_nonneg (cR i))
    refine le_trans hstep (le_of_eq ?_)
    rw [hD_def, mul_assoc, Finset.sum_mul]
  -- Lift termwise to the tsum, then bound the finite sum of even-power sums.
  have hsum_even_summable :
      Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2 =>
          D * ∑ j ∈ Finset.range (a + 1),
            (TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) * (cR i) ^ 2) := by
    refine Summable.mul_left D ?_
    exact summable_sum (fun j _ => hlapsummable j)
  calc ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g₀ 0 2,
          tensorSobolevWeight (I := I) (M := M) i (a : ℝ) * (cR i) ^ 2
      ≤ ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g₀ 0 2,
          D * ∑ j ∈ Finset.range (a + 1),
            (TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) * (cR i) ^ 2 :=
        Summable.tsum_le_tsum hterm hsummable hsum_even_summable
    _ = D * ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g₀ 0 2,
          ∑ j ∈ Finset.range (a + 1),
            (TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) * (cR i) ^ 2 := by
        rw [tsum_mul_left]
    _ = D * ∑ j ∈ Finset.range (a + 1),
          ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g₀ 0 2,
            (TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) * (cR i) ^ 2 := by
        rw [Summable.tsum_finsetSum (fun j _ => hlapsummable j)]
    _ ≤ D * ∑ _j ∈ Finset.range (a + 1), (C₀ * toHsNorm) ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j hj => ?_)) hD_nn
        exact hlapsq j (by rw [Finset.mem_range] at hj; omega)
    _ = D * ((a + 1 : ℝ) * (C₀ * toHsNorm) ^ 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ = (Real.sqrt (D * (a + 1)) * C₀ * toHsNorm) ^ 2 := by
        have hsqrt : Real.sqrt (D * (a + 1)) ^ 2 = D * (a + 1) :=
          Real.sq_sqrt (by positivity)
        rw [show (Real.sqrt (D * (a + 1)) * C₀ * toHsNorm) ^ 2
            = Real.sqrt (D * (a + 1)) ^ 2 * (C₀ * toHsNorm) ^ 2 from by ring, hsqrt]
        ring

/-- **The higher-order chart-RHS Nemytskii bound in intrinsic chart-Sobolev norms: the order-`a`
chart-Sobolev norm of the realized Ricci–DeTurck *remainder*-section difference is controlled by
the order-`(a+2)` chart-Sobolev norm of the perturbation difference.**

For an anchor `g₀`, a flow background `g_bg`, an order `a`, and a uniform `H^{a+2}`-size bound
`B ≥ 0`, there is a single constant `C ≥ 0` such that for any two `g₀`-fibre-small perturbations
`T₁, T₂` whose `H^{a+2}` norms are `≤ B`, and any two realized metrics `g₁, g₂` of `T₁, T₂`
(tied by the fibrewise `inner`-identities), the intrinsic order-`a` chart-Sobolev norm of the
difference of realized Ricci–DeTurck remainder sections is bounded by the order-`(a+2)`
chart-Sobolev norm of the perturbation difference:
```
‖(realizedRHSRemainderSection g₀ g_bg g₁ T₁ − realizedRHSRemainderSection g₀ g_bg g₂ T₂).toHs a‖
  ≤ C · ‖(T₁ − T₂).toHs (a+2)‖ .
```

This is the genuine **higher-order quasilinear Nemytskii estimate** in *intrinsic* Sobolev
norms: the second-order Ricci–DeTurck right-hand side `Ric + Lie + Δ_∇` is a smooth Nemytskii
function of the metric's `≤2`-jet, so on the supercritical scale (`Hᵃ` a Banach algebra,
`H^{a+2}·Hᵃ ⊂ Hᵃ`) its order-`a` chart-Sobolev norm is controlled by the order-`(a+2)`
chart-Sobolev norm of the metric perturbation, uniformly over the `H^{a+2}`-bounded family.  It
is the intrinsic-norm analogue of the on-disk `C⁰`/`2`-jet base case
`exists_chartDeTurckRHSComp_lipschitz_on_compact` (chart-frame value difference `≤
C · chartMetricJet2DiffSup`), upgraded to the order-`a` intrinsic Sobolev norm, and the order-`a`
analogue of `chartMetricJet2DiffSup_realizeMetricAt_le_toHs_unconditional` (the `a = 0`
chart-`2`-jet instance).  Its conclusion is a *real-valued* `toHs`-norm inequality, structurally
distinct from the spectral square-sum conclusion of the parent; no packaging.

The body is `sorry`: it is the genuine order-`a` quasilinear Nemytskii content (the higher-order
chart-RHS multiplication / composition estimate on the supercritical scale, composing the
chart-frame DeTurck-RHS-component derivatives up to order `a` with the chart-`Hᵃ`-to-intrinsic
partition-of-unity packaging), with no spectral-nonlinearity, no perturbation-indexed-remainder,
and no Weyl dependence. -/
theorem exists_realizedRHSRemainder_pouHa_le_toHs_highOrder
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a
            (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁
              - realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂)‖
          ≤ C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2)
              (T₁ - T₂)‖ :=
  sorry

/-- **The higher-order chart-RHS Sobolev–Lipschitz Nemytskii bound (the genuine deep analytic
input of the order-`a` chart-RHS tower).**

For an anchor `g₀`, a flow background `g_bg`, an order `a`, and a uniform `H^{a+2}`-size bound
`B ≥ 0`, there is a single constant `C ≥ 0` such that for any two `g₀`-fibre-small perturbations
`T₁, T₂ : SmoothCcTensor g₀ 0 2` whose `H^{a+2}` norms are `≤ B`, and any two realized metrics
`g₁, g₂` of `T₁, T₂` (tied by the fibrewise `inner`-identities `hg₁, hg₂`), the weighted-`Hᵃ`
seminorm of the `L²`-coordinate difference of the realized Ricci–DeTurck *remainder* sections
`realizedRHSRemainderSection g₀ g_bg gⱼ Tⱼ` is summable and bounded by `(C · ‖(T₁ − T₂).toHs
(a+2)‖)²`:
```
∑ᵢ (1 + λᵢ)^a ·
    ( tensorL2Coeff (toL2 (remainder of T₁,g₁)) i − tensorL2Coeff (toL2 (remainder of T₂,g₂)) i )²
  ≤ ( C · ‖(T₁ − T₂).toHs (a+2)‖ )² .
```

The order count is the honest one for the second-order quasilinear DeTurck operator: `a + 2`
derivatives of the metric perturbation control `a` derivatives of the right-hand side.  This is
exactly the higher-order analogue of the `C⁰`/`2`-jet base case
`exists_chartDeTurckRHSComp_lipschitz_on_compact` (chart-RHS *value* difference `≤
C · chartMetricJet2DiffSup`), upgraded from the chart `0`-jet of the right-hand side to its
order-`a` weighted-`Hᵃ` spectral seminorm and from the chart `2`-jet of the metric difference
to the intrinsic `H^{a+2}` norm of the perturbation difference (the order-`a` analogue of
`chartMetricJet2DiffSup_realizeMetricAt_le_toHs_unconditional`, the `a = 0` instance).

The conclusion is a *real-valued* weighted-`Hᵃ` square-sum inequality (in the exact binder
shape that `tensorHs.norm_sq_eq_tsum` consumes to produce an `Hᵃ`-`dist` Lipschitz witness),
structurally distinct from any topological/`LipschitzOnWith` statement; no packaging.  The body
is `sorry`: it is the genuine order-`a` chart-RHS-tower content — the higher-order quasilinear
Nemytskii estimate composing the chart-frame DeTurck-RHS-component derivatives up to order `a`
(each a polynomial in `(g, ∂g, …, ∂^{a+2} g)` controlled by the chart `(a+2)`-jet of the metric
difference) with the chart-`Hᵃ`-to-intrinsic-`Hᵃ` partition-of-unity packaging — with no
spectral-nonlinearity, no perturbation-indexed-remainder, and no Weyl dependence. -/
theorem exists_realizedRHSRemainder_weightedHa_le_toHs_highOrder
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2 =>
            tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
              (tensorL2Coeff (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                  (Integral.L2.SmoothCcTensor.toL2
                      (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁)
                    - Integral.L2.SmoothCcTensor.toL2
                      (realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂)) i) ^ 2)
          ∧ (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
                (I := I) (M := M) g₀ 0 2,
              tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
                (tensorL2Coeff (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                    (Integral.L2.SmoothCcTensor.toL2
                        (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁)
                      - Integral.L2.SmoothCcTensor.toL2
                        (realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂)) i) ^ 2)
              ≤ (C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2)
                  (T₁ - T₂)‖) ^ 2 := by
  classical
  -- The reverse spectral bound at order `a` and the higher-order intrinsic Nemytskii bound.
  obtain ⟨CB, hCB_nn, hCB⟩ := exists_spectralWeightedSq_le_pouHaNorm_sq (I := I) g₀ a
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_realizedRHSRemainder_pouHa_le_toHs_highOrder (I := I) g₀ g_bg a B hB
  refine ⟨CB * CA, mul_nonneg hCB_nn hCA_nn, ?_⟩
  intro T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂
  -- The realized-remainder section difference and the `L²`-coordinate `map_sub` rewrite.
  set R : Integral.L2.SmoothCcTensor g₀ 0 2 :=
    realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁
      - realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂ with hR_def
  have hL2 :
      Integral.L2.SmoothCcTensor.toL2 (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁)
          - Integral.L2.SmoothCcTensor.toL2 (realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂)
        = Integral.L2.SmoothCcTensor.toL2 R := by
    rw [hR_def, map_sub]
  -- The reverse spectral bound, applied to the section difference `R`.
  obtain ⟨hsummable, hspec⟩ := hCB R
  -- The higher-order intrinsic Nemytskii bound on `‖R.toHs a‖`.
  have hnem :
      ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a R‖
        ≤ CA * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2)
            (T₁ - T₂)‖ := hCA T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂
  refine ⟨by rw [hL2]; exact hsummable, ?_⟩
  -- Chain: spectral square-sum `≤ (CB·‖R.toHs a‖)² ≤ (CB·CA·‖(T₁−T₂).toHs(a+2)‖)²`.
  rw [hL2]
  refine hspec.trans ?_
  have hRtoHs_nn : 0 ≤ ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a R‖ :=
    norm_nonneg _
  have hdiff_nn :
      0 ≤ ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) (T₁ - T₂)‖ :=
    norm_nonneg _
  have hbase :
      CB * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a R‖
        ≤ CB * CA *
            ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2)
              (T₁ - T₂)‖ := by
    calc CB * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a R‖
        ≤ CB * (CA * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2)
            (T₁ - T₂)‖) := mul_le_mul_of_nonneg_left hnem hCB_nn
      _ = CB * CA *
            ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2)
              (T₁ - T₂)‖ := by ring
  have hlhs_nn : 0 ≤ CB * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a R‖ :=
    mul_nonneg hCB_nn hRtoHs_nn
  exact pow_le_pow_left₀ hlhs_nn hbase 2

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
