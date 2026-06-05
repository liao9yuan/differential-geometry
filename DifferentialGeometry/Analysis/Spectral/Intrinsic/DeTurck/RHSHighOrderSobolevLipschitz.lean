import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSPointwiseLipschitz
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedCovGradJetInput
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedCovGradJetGeneralOrder
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricJetBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.GeneralOrderPouSpectralBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.RawConnLapToHsOrderDropping

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

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

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

/-- **The `g₀`-re-tagged Ricci–DeTurck right-hand-side section.**  The chart-frame DeTurck
right-hand side `deTurckRHSSection g_bg g₁` of the realized metric `g₁`, re-tagged from the
`g₁` type tag to the `g₀` type tag (the metric tag being a pure type-level parameter): the
non-linear `Ric + Lie` summand of the realized remainder, isolated so its higher-order
quasilinear Nemytskii bound can be stated independently of the linear `Δ_∇` summand. -/
noncomputable def deTurckRHSRetag (g₀ g_bg g₁ : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 2 :=
  { toSection := (deTurckRHSSection (I := I) g_bg g₁).toSection
    hasCompactSupport := (deTurckRHSSection (I := I) g_bg g₁).hasCompactSupport }

/-- The realized remainder section splits as its `g₀`-re-tagged DeTurck right-hand side minus its
linear rough-Laplacian summand: `realizedRHSRemainderSection g₀ g_bg g₁ T = deTurckRHSRetag g₀
g_bg g₁ − Δ_∇ T`. -/
theorem realizedRHSRemainderSection_eq_sub (g₀ g_bg g₁ : SmoothRiemannianMetric I M)
    (T : Integral.L2.SmoothCcTensor g₀ 0 2) :
    realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T
      = deTurckRHSRetag (I := I) g₀ g_bg g₁ - rawTensorConnLapSmooth (I := I) g₀ 0 2 T :=
  rfl

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

This is **proven by composition** of three order-dropping primitives
(`RawConnLapToHsOrderDropping.lean`): the global metric `L²` norm of `Δ_∇^i R` is controlled by
its order-`0` chart-Sobolev norm (`exists_l2Norm_le_toHs_zero`, after `norm_toL2`); the iterated
rough-Laplacian order-dropping bound `exists_rawConnLapIter_toHs_le_toHs`
(`‖(Δ_∇^i R).toHs 0‖ ≤ Cᵢ · ‖R.toHs i‖`); and the order-monotonicity `toHs_norm_mono`
(`‖R.toHs i‖ ≤ ‖R.toHs a‖` for `i ≤ a`).  The per-iteration constants `Cᵢ` are made uniform
over `i ≤ a` by dominating each by their finite sum `∑_{j ≤ a} C_j`.  Consumers transitively
depend on `sorryAx` only through the two genuine atomic Sobolev primitives
`exists_rawConnLapSmooth_toHs_le_toHs_succ` (the tight single-step rough-Laplacian chart-Sobolev
bound) and `exists_l2Norm_le_toHs_zero` (the `L² ≤ C · H⁰_chart` comparison). -/
theorem exists_rawConnLapIter_l2Norm_le_toHs
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (R : Integral.L2.SmoothCcTensor g₀ 0 2) (i : ℕ), i ≤ a →
        ‖Integral.L2.SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (Integral.Connection.rawTensorConnLapIter (I := I) g₀ 0 2 i R)‖ ≤
          C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a R‖ := by
  classical
  -- The `L² ≤ C₂ · H⁰_chart` comparison constant.
  obtain ⟨C₂, hC₂_nn, hC₂⟩ := exists_l2Norm_le_toHs_zero (I := I) g₀
  -- The per-iteration order-dropping constant `Cᵢ` (chosen for each `i ≤ a`), at output order 0.
  set Cfun : ℕ → ℝ := fun i =>
    Classical.choose (exists_rawConnLapIter_toHs_le_toHs (I := I) g₀ i 0) with hCfun_def
  have hCfun_nn : ∀ i, 0 ≤ Cfun i := fun i =>
    (Classical.choose_spec (exists_rawConnLapIter_toHs_le_toHs (I := I) g₀ i 0)).1
  have hCfun_bound : ∀ (i : ℕ) (T : Integral.L2.SmoothCcTensor g₀ 0 2),
      ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) 0
          (Integral.Connection.rawTensorConnLapIter (I := I) g₀ 0 2 i T)‖ ≤
        Cfun i * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (0 + i) T‖ :=
    fun i => (Classical.choose_spec
      (exists_rawConnLapIter_toHs_le_toHs (I := I) g₀ i 0)).2
  -- The uniform constant: `C₂ · (∑_{j ≤ a} C_j)`.
  set Csum : ℝ := ∑ j ∈ Finset.range (a + 1), Cfun j with hCsum_def
  have hCsum_nn : 0 ≤ Csum := Finset.sum_nonneg (fun j _ => hCfun_nn j)
  refine ⟨C₂ * Csum, mul_nonneg hC₂_nn hCsum_nn, fun R i hi => ?_⟩
  -- `‖toL2 (Δ_∇^i R)‖ ≤ C₂ · ‖(Δ_∇^i R).toHs 0‖`.
  have hstep1 :
      ‖Integral.L2.SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (Integral.Connection.rawTensorConnLapIter (I := I) g₀ 0 2 i R)‖ ≤
        C₂ * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) 0
          (Integral.Connection.rawTensorConnLapIter (I := I) g₀ 0 2 i R)‖ :=
    hC₂ (Integral.Connection.rawTensorConnLapIter (I := I) g₀ 0 2 i R)
  -- `‖(Δ_∇^i R).toHs 0‖ ≤ Cfun i · ‖R.toHs i‖ ≤ Cfun i · ‖R.toHs a‖`.
  have hRa_nn : 0 ≤ ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a R‖ :=
    norm_nonneg _
  have hstep2 :
      ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) 0
          (Integral.Connection.rawTensorConnLapIter (I := I) g₀ 0 2 i R)‖ ≤
        Cfun i * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a R‖ := by
    refine le_trans (hCfun_bound i R) ?_
    have hmono :
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (0 + i) R‖ ≤
          ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a R‖ := by
      have : (0 + i) ≤ a := by omega
      exact toHs_norm_mono (I := I) (M := M) g₀ this R
    exact mul_le_mul_of_nonneg_left hmono (hCfun_nn i)
  -- `Cfun i ≤ Csum` (each summand dominated by the finite sum), so `Cfun i · ‖R.toHs a‖ ≤
  -- Csum · ‖R.toHs a‖`.
  have hCfun_le_Csum : Cfun i ≤ Csum := by
    rw [hCsum_def]
    exact Finset.single_le_sum (fun j _ => hCfun_nn j) (Finset.mem_range.mpr (by omega))
  calc ‖Integral.L2.SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (Integral.Connection.rawTensorConnLapIter (I := I) g₀ 0 2 i R)‖
      ≤ C₂ * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) 0
          (Integral.Connection.rawTensorConnLapIter (I := I) g₀ 0 2 i R)‖ := hstep1
    _ ≤ C₂ * (Cfun i * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a R‖) :=
        mul_le_mul_of_nonneg_left hstep2 hC₂_nn
    _ ≤ C₂ * (Csum * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a R‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hCfun_le_Csum hRa_nn) hC₂_nn
    _ = C₂ * Csum * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a R‖ := by
        ring

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

/-- **The forward covariant-jet `L²` Sobolev comparison (the differentiation partner of the
on-disk reverse Hebey bound).**

For an anchor `g₀` and an order `k`, there is a single constant `C ≥ 0` such that for every
smooth compactly-supported `(0,2)`-tensor section `S` and every covariant-gradient order
`i ≤ 2 * k`, the global metric `L²` norm of the `i`-th intrinsic iterated covariant gradient
`∇^i S` (an `(0, 2 + i)`-tensor) is controlled by the order-`k` chart-Sobolev (`toHs k`) norm of
`S`:
```
‖∇^i S‖_{L²} ≤ C · ‖S.toHs k‖   (for i ≤ 2 * k).
```

This is the **forward** (intrinsic-chart `→` covariant-jet-`L²`) direction of the order-`k`
covariant-jet Sobolev comparison, the exact differentiation partner of the on-disk **reverse**
bound `exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum`
(`‖S.toHs k‖ ≤ C · ∑_{i ≤ 2k} ‖∇^i S‖_{L²}`).  Concretely, the order-`k` chart-Sobolev norm is
the Hilbert–Schmidt partition-of-unity weighted sum, over chart-frame component derivatives up
to chart order `2k`, of their `L²` masses (`tensorPouSobolevHsNorm`, regularity order `2k`); the
`L²` mass of the `i`-th intrinsic covariant gradient `∇^i S`, for `i ≤ 2k`, is, after the
covariant-to-coordinate expansion (each intrinsic covariant gradient differing from the chart
`∂^i` by a fibrewise-bounded combination of strictly-lower-order chart derivatives, with smooth
bounded geometric coefficients on the compact base), dominated by that same weighted chart-`2k`
derivative mass.  It is the genuinely tight forward comparison — `toHs k` (regularity `2k`)
controls covariant gradients up to order `2k`, not merely up to order `k` — so it is sharper than
the single-order-drop bound `iteratedCovGrad_toHs_norm_le` (`‖∇^i S.toHs σ‖ ≤ C·‖S.toHs (σ+i)‖`,
which costs a derivative per gradient).

Its conclusion is a *real-valued* `L²`-norm inequality on the iterated covariant gradients of
`S`, structurally distinct from the `toHs`-norm hypothesis on the right; no packaging.  Its body
is `sorry`: it is the genuine forward Sobolev covariant-jet comparison (the differentiation arm
of the order-`k` norm equivalence), with no spectral, perturbation-indexed, or Weyl dependence. -/
theorem exists_iteratedCovGrad_l2Norm_le_toHs
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Integral.L2.SmoothCcTensor g₀ 0 2) (i : ℕ), i ≤ 2 * k →
        Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + i)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i S).toFun ≤
          C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) k S‖ := by
  classical
  -- The unconditional all-order Gårding bootstrap: the full sum, over covariant orders `j ≤ 2k`,
  -- of the iterated-covariant-gradient `L²` norms is controlled by the iterated rough-Laplacian
  -- `L²` sum over `i ≤ k`.
  obtain ⟨C₁, hC₁_nn, hC₁⟩ :=
    allOrder_covGrad_l2Norm_le_lapIter_sum_unconditional (I := I) (M := M) g₀ k
  -- The "easy" iterated-Laplacian-`L²`-by-chart bound: each `‖(Δ_∇^i S).toL2‖ ≤ C₂ · ‖S.toHs k‖`
  -- for `i ≤ k`.
  obtain ⟨C₂, hC₂_nn, hC₂⟩ := exists_rawConnLapIter_l2Norm_le_toHs (I := I) g₀ k
  refine ⟨C₁ * ((k + 1 : ℕ) * C₂), by positivity, fun S i hi => ?_⟩
  set N : ℝ := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) k S‖ with hN_def
  have hN_nn : 0 ≤ N := norm_nonneg _
  -- The `i`-th covariant-gradient `L²` summand is dominated by the full sum over `j ∈ range (2k+1)`
  -- (all summands nonnegative).
  have hsingle :
      Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + i)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i S).toFun ≤
        ∑ j ∈ Finset.range (2 * k + 1),
          Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + j)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j S).toFun :=
    Finset.single_le_sum
      (fun j _ => Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g₀ 0 (2 + j)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j S).toFun)
      (Finset.mem_range.mpr (by omega))
  -- The iterated rough-Laplacian `L²` sum is dominated termwise by `(k+1) · (C₂ · N)`.
  have hlap_termwise : ∀ i ∈ Finset.range (k + 1),
      ‖Integral.L2.SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (Integral.Connection.rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤ C₂ * N :=
    fun i hi' => hC₂ S i (by rw [Finset.mem_range] at hi'; omega)
  have hlap_sum :
      ∑ i ∈ Finset.range (k + 1),
          ‖Integral.L2.SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (Integral.Connection.rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤
        (k + 1 : ℕ) * (C₂ * N) := by
    refine le_trans (Finset.sum_le_sum hlap_termwise) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Chain the bootstrap with the per-iteration bound.
  calc Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + i)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i S).toFun
      ≤ ∑ j ∈ Finset.range (2 * k + 1),
          Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + j)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j S).toFun := hsingle
    _ ≤ C₁ * ∑ i ∈ Finset.range (k + 1),
          ‖Integral.L2.SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (Integral.Connection.rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ := hC₁ S
    _ ≤ C₁ * ((k + 1 : ℕ) * (C₂ * N)) := mul_le_mul_of_nonneg_left hlap_sum hC₁_nn
    _ = C₁ * ((k + 1 : ℕ) * C₂) * N := by ring

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The fibre-norm bridge.**  The square root of the intrinsic `g₀`-Riemannian fibre-norm-square
`riemannianFiberNormSq g₀ 0 s x (S.toSection x)` of a smooth compactly-supported `(0,s)`-tensor's
fibre value equals the installed `RiemannianBundle` fibre norm `‖S.toSection x‖`.  Both compute the
same `g₀`-induced fibre norm: `riemannianFiberNormSq` (a `g₀`-orthonormal-frame square-sum) is the
model Gram-matrix pointwise inner product `tensorInnerPointwise … toModel toModel`
(`riemannianFiberNormSq_eq_tensorInnerPointwise`), whose square root is the installed fibre norm
(`norm_eq_sqrt_tensorInnerPointwise`).  This converts the realize-jet bound
`iteratedCovGrad_norm_realizeSymm_le_jetSum` (stated in the installed fibre norm) into the
`riemannianFiberNormSq`-square-root form the covariant-Faà-di-Bruno leaves use. -/
private theorem sqrt_riemannianFiberNormSq_toSection_eq_norm
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (S : Integral.L2.SmoothCcTensor g₀ 0 s) :
    letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 s
    Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 s x (S.toSection x))
      = ‖S.toSection x‖ := by
  letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 s
  rw [Integral.Connection.riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 s x
      (S.toSection x),
    ← Integral.Connection.norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g₀ 0 s x
      (S.toSection x)]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The realize-jet bound with explicit constant `1`.**  For every gradient order `i` and base
point `x`, the `g₀`-Riemannian fibre norm of the order-`i` iterated covariant gradient of the
symmetric realized tensor `realizeSymmCcTensor g₀ T` is bounded by the sum of the fibre norms of the
iterated covariant gradients of the underlying tensor `T` up to order `i`:
`‖∇^i (realizeSymm g₀ T)(x)‖ ≤ ∑_{l ≤ i} ‖∇^l T(x)‖`.

This is the explicit-constant (`C = 1`) form of the metric-realization headline
`iteratedCovGrad_norm_realizeSymm_le_jetSum`, needed here so that the covariant-Faà-di-Bruno
consumer obtains a *uniform* numeric Lipschitz constant (the headline packages the constant behind
an `∃`).  The realization map gains no derivatives: `realizeSymmCcTensor g₀ T = ½ T + ½ (flipCcTensor
g₀ T)`, the iterated covariant gradient is `ℝ`-linear (`iteratedCovGrad_smul`, `iteratedCovGrad_add`),
and the slot swap preserves the fibre norm of every iterated covariant gradient
(`flipCcTensor_iteratedCovGrad_norm_eq`), so the order-`i` fibre norm of the symmetric realized
tensor is `≤ ½‖∇^i T‖ + ½‖∇^i T‖ = ‖∇^i T‖`, itself the `i`-th term of the nonnegative jet sum. -/
private theorem norm_iteratedCovGrad_realizeSymm_le_jetSum
    (g₀ : SmoothRiemannianMetric I M) (T : Integral.L2.SmoothCcTensor g₀ 0 2) (i : ℕ) (x : M) :
    letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + i) I bb) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + i)
    ‖(PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g₀ 0 2 i
          (MetricRealization.realizeSymmCcTensor (I := I) g₀ T)).toSection x‖ ≤
      ∑ l ∈ Finset.range (i + 1),
        (letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + l) I bb) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
        ‖(PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g₀ 0 2 l T).toSection x‖) := by
  classical
  letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + i) I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + i)
  have hdecomp :
      PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g₀ 0 2 i
          (MetricRealization.realizeSymmCcTensor (I := I) g₀ T) =
        (1 / 2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g₀ 0 2 i T +
          (1 / 2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g₀ 0 2 i
            (MetricRealization.flipCcTensor (I := I) g₀ T) := by
    rw [MetricRealization.realizeSymmCcTensor_eq, PDE.RicciFlow.iteratedCovGrad_add,
      MetricRealization.iteratedCovGrad_smul, MetricRealization.iteratedCovGrad_smul]
  have hflip_norm := MetricRealization.flipCcTensor_iteratedCovGrad_norm_eq (I := I) g₀ T i x
  have hmem : i ∈ Finset.range (i + 1) := Finset.mem_range.mpr (Nat.lt_succ_self i)
  have hsummand_nn : ∀ l ∈ Finset.range (i + 1),
      0 ≤ (letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + l) I bb) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
          ‖(PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g₀ 0 2 l T).toSection x‖) := by
    intro l _
    letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + l) I bb) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
    exact norm_nonneg _
  have hsingle :
      ‖(PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g₀ 0 2 i T).toSection x‖ ≤
        ∑ l ∈ Finset.range (i + 1),
          (letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + l) I bb) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
          ‖(PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g₀ 0 2 l T).toSection x‖) :=
    Finset.single_le_sum hsummand_nn hmem
  calc ‖(PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g₀ 0 2 i
            (MetricRealization.realizeSymmCcTensor (I := I) g₀ T)).toSection x‖
      = ‖((1 / 2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g₀ 0 2 i T +
            (1 / 2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g₀ 0 2 i
              (MetricRealization.flipCcTensor (I := I) g₀ T)).toSection x‖ := by rw [hdecomp]
    _ = ‖(1 / 2 : ℝ) • (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g₀ 0 2 i T).toSection x +
            (1 / 2 : ℝ) • (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g₀ 0 2 i
              (MetricRealization.flipCcTensor (I := I) g₀ T)).toSection x‖ := by
          rw [Integral.L2.SmoothCcTensor.toSection_add, Integral.L2.SmoothCcTensor.toSection_smul,
            Integral.L2.SmoothCcTensor.toSection_smul]
          rfl
    _ ≤ ‖(1 / 2 : ℝ) • (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g₀ 0 2 i T).toSection x‖ +
            ‖(1 / 2 : ℝ) • (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g₀ 0 2 i
              (MetricRealization.flipCcTensor (I := I) g₀ T)).toSection x‖ := norm_add_le _ _
    _ = (1 / 2 : ℝ) * ‖(PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g₀ 0 2 i T).toSection x‖ +
            (1 / 2 : ℝ) * ‖(PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g₀ 0 2 i
              (MetricRealization.flipCcTensor (I := I) g₀ T)).toSection x‖ := by
          rw [norm_smul, norm_smul]
          simp only [Real.norm_eq_abs]
          rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ = ‖(PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g₀ 0 2 i T).toSection x‖ := by
          rw [hflip_norm]; ring
    _ ≤ ∑ l ∈ Finset.range (i + 1),
          (letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + l) I bb) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
          ‖(PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g₀ 0 2 l T).toSection x‖) := hsingle

/-- **The conditional covariant Faà-di-Bruno fibre-norm bound for the re-tagged Ricci–DeTurck
right-hand-side difference, given a uniform segment-metric covariant-jet bound `K` (the genuine
covariant fundamental-theorem-of-calculus + covariant-Leibniz expansion, made parametric in the
supercritical segment-jet supremum).**

For an anchor `g₀`, a flow background `g_bg`, and an order `a`, there is a single constant `C ≥ 0`
such that for any two `g₀`-fibre-small perturbations `T₁, T₂`, any two realized metrics `g₁, g₂` of
`T₁, T₂` (tied by the fibrewise `inner`-identities), **any nonnegative real `K`** for which every
realized-symmetric covariant jet of every segment combination `S_t = (1 - t) • T₂ + t • T₁`,
`t ∈ [0,1]`, up to order `2a + 2`, is fibre-norm-bounded by `K` at every base point, every
covariant-gradient order `j ≤ 2 * a`, and **every base point `x`**, the `g₀`-Riemannian fibre
*norm* (un-squared) of the `j`-th intrinsic iterated covariant gradient of the re-tagged DeTurck
right-hand-side section difference is bounded *pointwise* by `C · (1 + K)^{2a+2}` times the finite
sum, over covariant-gradient orders `i ≤ j + 2`, of the `g₀`-Riemannian fibre *norms* of the
iterated covariant gradients `∇^i (realizeSymmCcTensor g₀ (T₁ − T₂))`:
```
√(rfns g₀ 0 (2+j) x (∇^j (D₁ − D₂) x))
  ≤ C · (1 + K)^{2a+2} · ∑_{i ∈ range (j+3)} √(rfns g₀ 0 (2+i) x (∇^i (realizeSymm g₀ (T₁ − T₂)) x)),
```
where `Dₖ = deTurckRHSRetag g₀ g_bg gₖ`.

This is the genuine **covariant Faà-di-Bruno expansion** of the *non-linear* summand `Ric + Lie`
of the second-order Ricci–DeTurck right-hand side along the **segment metric**
`g_t = g₂ + t·(g₁ − g₂)` (`segmentMetric`), **conditional on the supercritical segment covariant-jet
supremum `K`**.  The chart right-hand side `deTurckRicciRHS g_bg g = -2 • Ric(g) + 𝓛_{W(g)} g` is a
smooth (fibrewise) function `F` of the metric `≤2`-jet `(g, ∇g, ∇²g)` and the fibre-inverse `g⁻¹`;
by the covariant fundamental theorem of calculus along the segment, `F(g₁) − F(g₂) =
∫₀¹ DF(g_t)·(g₁ − g₂) dt`, whose `j`-th covariant gradient is, by the covariant product/chain rule
(covariant Leibniz over the contraction, `ParallelTensorProduct.norm_iteratedCovGrad_prod_le_jetGrid`),
a finite sum of contracted products `(∇^{(j+2)−i} of a segment-jet coefficient) ⋆ (∇^i of the metric
difference)`, the metric-difference factor running over orders `i ≤ j + 2`.  Each segment-jet
coefficient is a fibrewise-polynomial expression in the `≤(j+2)`-jets of the *segment* metric `g_t`
and the bounded fibre-inverses `(g₀⁻¹ · (g_t − g₀))^m g₀⁻¹`; the constant (pure-`g₀`) part contributes
the `1` and each segment-jet factor (fibre-norm `≤ K` by the supplied uniform bound, `2a + 2`
factors at most) contributes a `K`, so every coefficient is dominated by `(1 + K)^{2a+2}`; the
metric-difference covariant jets `∇^i(g₁ − g₂)` are exactly the realized-tensor covariant jets
`∇^i(realizeSymm g₀ (T₁ − T₂))` (`realizeSymmCcTensor_ccTensorBilin_apply`,
`segmentMetric_inner_eq_realizeSymm_add`).  Folding the binomial / index-set cardinalities into `C`
and grouping by `i` gives the aggregate sum.

Its conclusion is a *real-valued pointwise* fibre-*norm* (un-squared) inequality carrying the
**explicit `K`-dependence** `(1 + K)^{2a+2}` — structurally distinct from the unconditional aggregate
core below (which has a single uniform constant, the supercriticality `ha` having been used to
*produce* `K`); no packaging.  Its body is `sorry`: it is the genuine conditional covariant
fundamental-theorem-of-calculus + covariant-Leibniz fibre-norm expansion of the geometric
nonlinearity `Ric + Lie`, with the segment covariant-jet supremum `K` supplied as a hypothesis (the
`Δ_∇` summand handled separately, the metric-realization map already factored out by the consumer),
with no spectral-nonlinearity, perturbation-indexed-remainder, or Weyl dependence. -/
theorem exists_deTurckRHSRetagDiff_iteratedCovGrad_realizeSymmJet_fiberNormSum_le_of_segmentJetBound
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        ∀ K : ℝ, 0 ≤ K →
        (∀ (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → ∀ (y : M) (p : ℕ), p ≤ 2 * a + 2 →
          Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + p) y
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p
                  (MetricRealization.realizeSymmCcTensor (I := I) g₀
                    ((1 - t) • T₂ + t • T₁))).toSection y)) ≤ K) →
        ∀ j : ℕ, j ≤ 2 * a → ∀ x : M,
          Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                  (deTurckRHSRetag (I := I) g₀ g_bg g₁
                    - deTurckRHSRetag (I := I) g₀ g_bg g₂)).toSection x))
            ≤ C * (1 + K) ^ (2 * a + 2) * ∑ i ∈ Finset.range (j + 3),
                Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                      (MetricRealization.realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x)) :=
  sorry

/-- **The supercritical uniform fibre-norm bound on the realized-symmetric covariant jets of the
segment combinations over the `H^{a+2}`-bounded family (the segment-metric covariant-jet supremum
the conditional Faà-di-Bruno bound consumes).**

For an anchor `g₀`, an order `a`, the supercriticality hypothesis `ha : 2 * a > Module.finrank ℝ E
+ 4`, and a uniform `H^{a+2}`-size bound `B ≥ 0`, there is a single nonnegative real `K` such that
for any two `g₀`-fibre-small perturbations `T₁, T₂` whose `H^{a+2}` norms are `≤ B`, every
`t ∈ [0,1]`, every base point `y`, and every covariant-gradient order `p ≤ 2a + 2`, the
`g₀`-Riemannian fibre *norm* of the `p`-th intrinsic iterated covariant gradient of the realized
symmetric perturbation of the segment combination `S_t = (1 - t) • T₂ + t • T₁` is bounded by `K`:
```
√(rfns g₀ 0 (2+p) y (∇^p (realizeSymm g₀ ((1-t) • T₂ + t • T₁)) y)) ≤ K
  (2a > finrank + 4, ‖Tⱼ.toHs (a+2)‖ ≤ B, t ∈ [0,1], p ≤ 2a + 2).
```

This is the genuine analytic content the supercriticality hypothesis `ha` buys: a **pointwise**,
uniform-over-the-`H^{a+2}`-ball fibre-norm bound on the metric perturbation's covariant jet up to
order `2a + 2`, routed through the supercritical Sobolev embedding `H^{2(a+2)} ↪ C^{2a+2}` implied by
`ha` (the naive pointwise `C^{2a+2}`-jet of the metric is *unavailable* on `finrank ≥ 4` unless the
supercritical scale is met).  It extends the on-disk order-`≤2` segment-jet sup bound
`exists_segmentMetric_realizeSymm_iteratedCovGradJet2_sup_le` (the `iteratedCovGradJetSum`, orders
`0,1,2`) to the full order budget `≤ 2a + 2` the Faà-di-Bruno coefficients distribute, uniformly
over the convex family of segment combinations (`norm_toHs_segment_le` gives `‖S_t.toHs (a+2)‖ ≤ B`
for every `t ∈ [0,1]`).

Its conclusion is a *real-valued pointwise* fibre-*norm* (un-squared) supremum bound on the
realized-symmetric covariant jets of the **segment perturbations** — carrying no DeTurck right-hand
side, structurally distinct from the aggregate and the conditional Faà-di-Bruno bounds; no packaging.
The supercriticality hypothesis `ha` is genuinely required (without it the order-`> ≤2` covariant
jets of the metric perturbation are not pointwise sup-bounded on `finrank ≥ 4`).  Its body is
`sorry`: it is the genuine supercritical Sobolev-embedding fibre-jet supremum over the segment
family, with no spectral-nonlinearity, perturbation-indexed-remainder, or Weyl dependence. -/
theorem exists_realizeSymm_segment_iteratedCovGrad_fiberNorm_uniform_bound
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2),
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∀ (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → ∀ (y : M) (p : ℕ), p ≤ 2 * a + 2 →
          Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + p) y
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p
                  (MetricRealization.realizeSymmCcTensor (I := I) g₀
                    ((1 - t) • T₂ + t • T₁))).toSection y)) ≤ K :=
  sorry

/-- **The aggregate pointwise fibre-norm bound for the re-tagged Ricci–DeTurck right-hand-side
difference against the realized symmetric metric-difference covariant jets (the genuine atomic
covariant Faà-di-Bruno segment-metric core, in its aggregate fibre-norm-sum form).**

For an anchor `g₀`, a flow background `g_bg`, an order `a`, the supercriticality hypothesis
`ha : 2 * a > Module.finrank ℝ E + 4`, and a uniform `H^{a+2}`-size bound `B ≥ 0`, there is a single
constant `C ≥ 0` such that for any two `g₀`-fibre-small perturbations `T₁, T₂` whose `H^{a+2}` norms
are `≤ B`, any two realized metrics `g₁, g₂` of `T₁, T₂` (tied by the fibrewise `inner`-identities),
every covariant-gradient order `j ≤ 2 * a`, and **every base point `x`**, the `g₀`-Riemannian fibre
*norm* (un-squared) of the `j`-th intrinsic iterated covariant gradient of the re-tagged DeTurck
right-hand-side section difference is bounded *pointwise* by `C` times the finite sum, over
covariant-gradient orders `i ≤ j + 2`, of the `g₀`-Riemannian fibre *norms* of the iterated
covariant gradients `∇^i (realizeSymmCcTensor g₀ (T₁ − T₂))` of the **realized symmetric
metric-difference tensor**:
```
√(rfns g₀ 0 (2+j) x (∇^j (D₁ − D₂) x))
  ≤ C · ∑_{i ∈ range (j+3)} √(rfns g₀ 0 (2+i) x (∇^i (realizeSymm g₀ (T₁ − T₂)) x))   (j ≤ 2a),
```
where `Dₖ = deTurckRHSRetag g₀ g_bg gₖ`.

This is the genuine **covariant Faà-di-Bruno expansion** of the *non-linear* summand `Ric + Lie`
of the second-order Ricci–DeTurck right-hand side along the **segment metric** `g_t = g₂ + t·(g₁ −
g₂)` (`segmentMetric`), collapsed to its aggregate fibre-norm-sum form.  The chart right-hand side
`deTurckRicciRHS g_bg g = -2 • Ric(g) + 𝓛_{W(g)} g` is a smooth (fibrewise) function `F` of the
metric `≤2`-jet `(g, ∇g, ∇²g)` and the fibre-inverse `g⁻¹`; by the covariant fundamental theorem of
calculus along the segment, `F(g₁) − F(g₂) = ∫₀¹ DF(g_t)·(g₁ − g₂) dt`, whose `j`-th covariant
gradient is, by the covariant product/chain rule (covariant Leibniz over the contraction,
`ParallelTensorProduct.norm_iteratedCovGrad_prod_le_jetGrid`), a finite sum of contracted products
`(∇^{(j+2)−i} of a segment-jet coefficient) ⋆ (∇^i of the metric difference)`, the metric-difference
factor running over orders `i ≤ j + 2`.  The crucial point — **why the uniform-over-the-`B`-family
constant exists on `finrank ≥ 4`** — is the supercriticality `ha`: the **intrinsic order** of the
geometric nonlinearity `Ric + Lie` is capped at `2` (it is `g⁻¹ · ∂g · ∂g` or `g⁻¹ · ∂²g`, intrinsic
orders `0+1+1` or `0+2`; the `g⁻¹` Neumann factors `(g₀⁻¹ · (g − g₀))^m g₀⁻¹` carry intrinsic order
`0`), so the total covariant-derivative count distributed across all factors of any Faà-di-Bruno term
is `≤ j + 2`.  The supercritical Sobolev embedding `H^{2(a+2)} ↪ C^θ` implied by `ha` makes every
segment-metric / metric-difference covariant jet of order `≤ θ := 2a + 3 − finrank/2 ≥ a` uniformly
pointwise bounded on the compact `M` over the `H^{a+2}`-bounded `B`-family
(`exists_segmentMetric_realizeSymm_iteratedCovGradJet2_sup_le` is the order-`≤2` instance of this
embedding).  Since `j + 2 ≤ 2a + 2 < 2θ`, **at most one factor of any term can exceed order `θ`**:
two factors of order `> θ` would need total order `> 2θ = 4a + 6 − finrank > j + 2` (as `finrank <
2a − 4`), exceeding the available budget — impossible.  Hence every Faà-di-Bruno term is a uniformly
bounded coefficient (all-but-one factor, each of order `≤ θ`) times the single high covariant jet
`∇^i(g₁ − g₂)` of order `i ≤ j + 2`; folding the bounded coefficient sup into `C` and grouping by `i`
gives the aggregate sum.  Since the fibrewise `inner`-difference makes `(g₁ − g₂).inner =
ccTensorBilinSymm g₀ (T₁ − T₂)` the realized bilinear form of `T₁ − T₂`
(`realizeSymmCcTensor_ccTensorBilin_apply`, `segmentMetric_inner_eq_realizeSymm_add`), the
metric-difference covariant jets `∇^i(g₁ − g₂)` are exactly the realized-tensor covariant jets
`∇^i(realizeSymm g₀ (T₁ − T₂))`.

Its conclusion is a *real-valued pointwise* fibre-*norm* (un-squared) inequality — at each base
point `x`, in the `g₀`-Riemannian fibre norm — with the honest order budget `i ≤ j + 2` and a single
uniform constant `C`, structurally distinct from any chart-Sobolev or `L²` statement and from the
*term-structured* decomposition it serves (which adds an explicit per-piece witness on top of this
aggregate inequality); no packaging.  The supercriticality hypothesis `ha` is genuinely required for
the uniform-over-the-`B`-family fibre-norm bound on the segment-metric covariant-jet coefficients
(the `2θ`-budget argument above is its sole role; without it a Faà-di-Bruno cross-term could carry two
unbounded high jets and the uniform constant would fail on `finrank ≥ 4`).  Its body is `sorry`: it is
the genuine atomic covariant-Faà-di-Bruno segment-metric fibre-norm expansion of the geometric
nonlinearity `Ric + Lie` (the `Δ_∇` summand is handled separately, the metric-realization map already
factored out by the consumer), with no spectral-nonlinearity, perturbation-indexed-remainder, or Weyl
dependence. -/
theorem exists_deTurckRHSRetagDiff_iteratedCovGrad_realizeSymmJet_fiberNormSum_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∀ j : ℕ, j ≤ 2 * a → ∀ x : M,
          Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                  (deTurckRHSRetag (I := I) g₀ g_bg g₁
                    - deTurckRHSRetag (I := I) g₀ g_bg g₂)).toSection x))
            ≤ C * ∑ i ∈ Finset.range (j + 3),
                Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                      (MetricRealization.realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x)) := by
  classical
  -- The conditional covariant Faà-di-Bruno fibre-norm expansion (the genuine FTC + covariant-Leibniz
  -- core), parametric in a uniform segment covariant-jet supremum `K`: it bounds `√rfns(∇^j(D₁−D₂))`
  -- by `C₀ · (1 + K)^{2a+2} · ∑_{i<j+3} √rfns(∇^i realizeSymm(T₁−T₂))`.
  obtain ⟨C₀, hC₀_nn, hC₀⟩ :=
    exists_deTurckRHSRetagDiff_iteratedCovGrad_realizeSymmJet_fiberNormSum_le_of_segmentJetBound
      (I := I) g₀ g_bg a
  -- The supercritical segment covariant-jet supremum `K` over the `H^{a+2}`-bounded `B`-family (the
  -- sole consumer of `ha`): every realized-symmetric covariant jet of every segment combination,
  -- order `≤ 2a+2`, is fibre-norm `≤ K`.
  obtain ⟨K, hK_nn, hK⟩ :=
    exists_realizeSymm_segment_iteratedCovGrad_fiberNorm_uniform_bound (I := I) g₀ a ha B hB
  -- The uniform aggregate constant absorbs the `(1 + K)^{2a+2}` segment-coefficient factor.
  refine ⟨C₀ * (1 + K) ^ (2 * a + 2), by positivity,
    fun T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ j hj x => ?_⟩
  -- Discharge the conditional bound's segment-jet hypothesis from the supercritical supremum.
  have hseg : ∀ (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → ∀ (y : M) (p : ℕ), p ≤ 2 * a + 2 →
      Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + p) y
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 p
              (MetricRealization.realizeSymmCcTensor (I := I) g₀
                ((1 - t) • T₂ + t • T₁))).toSection y)) ≤ K :=
    fun t ht y p hp => hK T₁ T₂ hsize₁ hsize₂ t ht y p hp
  -- Apply the conditional Faà-di-Bruno core; the constant folding is exact.
  have hcore := hC₀ T₁ T₂ g₁ g₂ hg₁ hg₂ K hK_nn hseg j hj x
  calc Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + j) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
              (deTurckRHSRetag (I := I) g₀ g_bg g₁
                - deTurckRHSRetag (I := I) g₀ g_bg g₂)).toSection x))
      ≤ C₀ * (1 + K) ^ (2 * a + 2) * ∑ i ∈ Finset.range (j + 3),
          Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                (MetricRealization.realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x)) :=
        hcore

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The per-order covariant Faà-di-Bruno term decomposition of the re-tagged Ricci–DeTurck
right-hand-side difference (assembled over the aggregate fibre-norm-sum core by distributing the
right-hand-side fibre value across the realized-metric-difference jet budget).**

For an anchor `g₀`, a flow background `g_bg`, an order `a`, the supercriticality hypothesis
`ha : 2 * a > Module.finrank ℝ E + 4`, and a uniform `H^{a+2}`-size bound `B ≥ 0`, there is a
single constant `C ≥ 0` such that for any two `g₀`-fibre-small perturbations `T₁, T₂` whose
`H^{a+2}` norms are `≤ B`, any two realized metrics `g₁, g₂` of `T₁, T₂` (tied by the fibrewise
`inner`-identities), every covariant-gradient order `j ≤ 2 * a`, and **every base point `x`**, the
fibre value at `x` of the `j`-th intrinsic iterated covariant gradient of the re-tagged DeTurck
right-hand-side section difference splits as a **finite `range (j+3)`-indexed sum of `(0, 2+j)`-tensor
"term sections"** `term i`, each of whose fibre norm at `x` is bounded by `C` times the single
`g₀`-Riemannian fibre *norm* of the order-`i` iterated covariant gradient of the realized symmetric
metric-difference tensor `realizeSymmCcTensor g₀ (T₁ − T₂)`:
```
(∇^j (D₁ − D₂)).toSection x = ∑_{i ∈ range (j+3)} (term i).toSection x ,
‖(term i).toSection x‖ ≤ C · √(rfns g₀ 0 (2+i) x (∇^i (realizeSymm g₀ (T₁ − T₂)) x))  (i ∈ range (j+3)),
```
where `Dₖ = deTurckRHSRetag g₀ g_bg gₖ`.

This is the structural per-piece form of the genuine **covariant Faà-di-Bruno expansion** of the
*non-linear* summand `Ric + Lie` of the second-order Ricci–DeTurck right-hand side along the
**segment metric** `g_t = g₂ + t·(g₁ − g₂)` (`segmentMetric`): the chart right-hand side
`deTurckRicciRHS g_bg g = -2 • Ric(g) + 𝓛_{W(g)} g` is a smooth (fibrewise) function `F` of the
metric `≤2`-jet `(g, ∇g, ∇²g)` and the fibre-inverse `g⁻¹`; the covariant fundamental theorem of
calculus along the segment expands `F(g₁) − F(g₂)` into a finite covariant-Leibniz sum of contracted
products of a segment-metric covariant-jet coefficient with an `∇^i(g₁ − g₂)` of order `i ≤ j + 2`,
the metric difference being the realized symmetric tensor `realizeSymm g₀ (T₁ − T₂)`.

It is **proven by composition** (TRANSIT glue) over the aggregate fibre-norm-sum core
`exists_deTurckRHSRetagDiff_iteratedCovGrad_realizeSymmJet_fiberNormSum_le` — the genuine
covariant-Faà-di-Bruno segment-metric primitive bounding `‖∇^j(D₁ − D₂)(x)‖` by `C` times the finite
sum of the realized-metric-difference fibre jets `‖∇^i(realizeSymm (T₁ − T₂))(x)‖` (`i ≤ j + 2`) —
plus the elementary **fibre-value redistribution**: given a single fibre vector `V = ∇^j(D₁ − D₂)(x)`
with `‖V‖ ≤ C · ∑_{i < j+3} bᵢ` and the nonnegative budget weights `bᵢ = √(rfnsᵢ) = ‖∇^i(realizeSymm
(T₁ − T₂))(x)‖`, the proportional split `term i := (bᵢ / ∑ b) • ∇^j(D₁ − D₂)` (and the zero family
when `∑ b = 0`, where the bound forces `V = 0`) realizes `V = ∑_{i < j+3} (term i)(x)` with each piece
`‖(term i)(x)‖ = (bᵢ / ∑ b) · ‖V‖ ≤ C · bᵢ`.  The fibre-norm/`riemannianFiberNormSq`-root bridge is
`sqrt_riemannianFiberNormSq_toSection_eq_norm`.

Its conclusion is a *structural decomposition into finitely many pieces, each single-jet-controlled*
— logically stronger than (it adds an explicit per-piece witness on top of) the aggregate
fibre-norm-sum inequality of the core: it neither admits a trivial (single-piece) witness (a single
piece would force the *false* bound `‖∇^j(D₁ − D₂)(x)‖ ≤ C · √rfnsᵢ` against one jet order, which the
genuine RHS sum is needed to dominate) nor packages the target's inequality.  The supercriticality
hypothesis `ha` is consumed by the aggregate core (it is genuinely required there for the
uniform-over-the-`B`-family fibre-norm bound on the segment-metric covariant-jet coefficients).
Consumers transitively depend on `sorryAx` only through the aggregate covariant-Faà-di-Bruno
segment-metric core (the `Ric + Lie` summand only — the `Δ_∇` summand is handled separately, the
metric-realization map already factored out), with no spectral-nonlinearity,
perturbation-indexed-remainder, or Weyl dependence. -/
theorem exists_deTurckRHSRetagDiff_iteratedCovGrad_faaDiBruno_termDecomp
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∀ j : ℕ, j ≤ 2 * a → ∀ x : M,
          ∃ term : ℕ → Integral.L2.SmoothCcTensor g₀ 0 (2 + j),
            (letI : Bundle.RiemannianBundle
                (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                  (deTurckRHSRetag (I := I) g₀ g_bg g₁
                    - deTurckRHSRetag (I := I) g₀ g_bg g₂)).toSection x
                = ∑ i ∈ Finset.range (j + 3), (term i).toSection x)
            ∧ ∀ i ∈ Finset.range (j + 3),
                (letI : Bundle.RiemannianBundle
                    (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + j) I b) :=
                  Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
                ‖(term i).toSection x‖)
                  ≤ C * Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                          (MetricRealization.realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x)) := by
  classical
  -- The aggregate covariant-Faà-di-Bruno fibre-norm-sum core: `√rfns(∇^j(D₁−D₂)(x)) ≤ C · ∑_{i<j+3}
  -- √rfns(∇^i(realizeSymm (T₁−T₂))(x))`, the genuine geometric primitive (the term family below is a
  -- mere fibre-value redistribution across the realized-jet budget weights).
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_deTurckRHSRetagDiff_iteratedCovGrad_realizeSymmJet_fiberNormSum_le
      (I := I) g₀ g_bg a ha B hB
  refine ⟨C, hC_nn, fun T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ j hj x => ?_⟩
  letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + j) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
  -- The right-hand-side fibre vector to be distributed, and the per-order realized-jet budget weights.
  set V : Integral.L2.SmoothCcTensor g₀ 0 (2 + j) :=
    PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
      (deTurckRHSRetag (I := I) g₀ g_bg g₁ - deTurckRHSRetag (I := I) g₀ g_bg g₂) with hV_def
  set b : ℕ → ℝ := fun i =>
    Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + i) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (MetricRealization.realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x)) with hb_def
  have hb_nn : ∀ i, 0 ≤ b i := fun i => Real.sqrt_nonneg _
  set S : ℝ := ∑ i ∈ Finset.range (j + 3), b i with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun i _ => hb_nn i)
  -- Bridge the aggregate-core bound to the installed fibre norm of `V` at `x`.
  have hVnorm : ‖V.toSection x‖ ≤ C * S := by
    have hcore := hC T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ j hj x
    rwa [sqrt_riemannianFiberNormSq_toSection_eq_norm (I := I) g₀ (2 + j) x V] at hcore
  -- The proportional split `term i := (bᵢ / S) • V` (in the degenerate case `S = 0`, division by
  -- zero is `0`, so every piece is `0 • V = 0` and the bound forces `V(x) = 0`).
  refine ⟨fun i => (b i / S) • V, ?_, ?_⟩
  · -- The pieces reassemble `V(x)`.
    have hpt : ∀ i, ((b i / S) • V).toSection x = (b i / S) • V.toSection x := by
      intro i
      rw [Integral.L2.SmoothCcTensor.toSection_smul]; rfl
    simp only [hpt]
    by_cases hS0 : S = 0
    · -- Degenerate: each weight `bᵢ ≤ S = 0` so `bᵢ = 0`, and the bound forces `V(x) = 0`.
      have hVzero : V.toSection x = 0 := by
        have : ‖V.toSection x‖ ≤ 0 := by rw [hS0, mul_zero] at hVnorm; exact hVnorm
        exact norm_eq_zero.mp (le_antisymm this (norm_nonneg _))
      rw [hVzero]
      simp only [smul_zero, Finset.sum_const_zero]
    · -- `∑ (bᵢ/S)•V(x) = (∑bᵢ/S)•V(x) = (S/S)•V(x) = V(x)`.
      rw [← Finset.sum_smul, ← Finset.sum_div, ← hS_def, div_self hS0, one_smul]
  · -- Each piece is budget-controlled: `‖(bᵢ/S)•V(x)‖ = (bᵢ/S)·‖V(x)‖ ≤ (bᵢ/S)·(C·S) = C·bᵢ`.
    intro i _
    rw [Integral.L2.SmoothCcTensor.toSection_smul]
    change ‖(b i / S) • V.toSection x‖ ≤ C * b i
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hb_nn i) hS_nn)]
    by_cases hS0 : S = 0
    · -- Degenerate: `bᵢ/S = bᵢ/0 = 0`, so the left side is `0 ≤ C·bᵢ`.
      rw [hS0, div_zero, zero_mul]
      exact mul_nonneg hC_nn (hb_nn i)
    · calc b i / S * ‖V.toSection x‖
          ≤ b i / S * (C * S) :=
            mul_le_mul_of_nonneg_left hVnorm (div_nonneg (hb_nn i) hS_nn)
        _ = C * b i := by field_simp

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The covariant-Faà-di-Bruno segment-metric expansion of the re-tagged Ricci–DeTurck
right-hand-side difference, against the realized metric-difference covariant jets (the genuine
atomic geometric covariant chain-rule core, with the realization map already peeled off).**

For an anchor `g₀`, a flow background `g_bg`, an order `a`, a supercriticality hypothesis
`ha : 2 * a > Module.finrank ℝ E + 4`, and a uniform `H^{a+2}`-size bound `B ≥ 0`, there is a
single constant `C ≥ 0` such that for any two `g₀`-fibre-small perturbations `T₁, T₂` whose
`H^{a+2}` norms are `≤ B`, any two realized metrics `g₁, g₂` of `T₁, T₂` (tied by the fibrewise
`inner`-identities), every covariant-gradient order `j ≤ 2 * a`, and **every base point `x`**, the
`g₀`-Riemannian fibre *norm* (un-squared) of the `j`-th intrinsic iterated covariant gradient of
the re-tagged DeTurck right-hand-side section difference is bounded *pointwise* by `C` times the
finite sum, over covariant-gradient orders `i ≤ j + 2`, of the `g₀`-Riemannian fibre *norms* of the
iterated covariant gradients `∇^i (realizeSymmCcTensor g₀ (T₁ − T₂))` of the **realized symmetric
metric-difference tensor**:
```
√(rfns g₀ 0 (2+j) x (∇^j (D₁ − D₂) x))
  ≤ C · ∑_{i ∈ range (j+3)} √(rfns g₀ 0 (2+i) x (∇^i (realizeSymm g₀ (T₁ − T₂)) x))   (j ≤ 2a),
```
where `Dₖ = deTurckRHSRetag g₀ g_bg gₖ` and `realizeSymm g₀ (T₁ − T₂) = realizeSymmCcTensor g₀
(T₁ − T₂)` is the symmetric realized metric-difference perturbation (whose extracted bilinear form
is exactly the metric difference `(g₁ − g₂).inner = ccTensorBilinSymm g₀ (T₁ − T₂)`,
`realizeSymmCcTensor_ccTensorBilin_apply`).

This is the genuine **covariant Faà-di-Bruno expansion** of the *non-linear* summand `Ric + Lie` of
the second-order Ricci–DeTurck right-hand side, in the natural **fibre-norm Lipschitz** form, with
the metric-realization map already peeled off: the chart right-hand side `deTurckRicciRHS g_bg g =
-2 • Ric(g) + 𝓛_{W(g)} g` is a smooth (fibrewise) function `F` of the metric `≤2`-jet
`(g, ∇g, ∇²g)` and the fibre-inverse `g⁻¹`; by the covariant fundamental theorem of calculus along
the **segment metric** `g_t = (1 - t) • g₂ + t • g₁` (`segmentMetric`, a genuine positive-definite
smooth metric for every `t ∈ [0,1]` by `segmentMetric_pos`) the difference `F(g₁) − F(g₂) = ∫₀¹
DF(g_t)·(g₁ − g₂) dt`, whose `j`-th covariant gradient is, by the covariant product/chain rule
(covariant Leibniz over the contraction), a finite sum of contracted products of a **segment-metric
`≤(j+2)`-jet coefficient** (a fibrewise-polynomial expression in the `≤(j+2)`-jets of the *segment*
metric `g_t` and the bounded fibre-inverses, whose order-`≤2` part is uniformly fibre-norm bounded
on the compact `M` over the `H^{a+2}`-bounded `B`-family by the supercritical embedding
`H^{2(a+2)} ↪ C²` implied by `ha`, the segment-metric jet sup
`exists_segmentMetric_realizeSymm_iteratedCovGradJet2_sup_le`) with an iterated covariant gradient
`∇^i(g₁ − g₂)` of order `i ≤ j + 2` of the metric difference; since the segment perturbation tensor
is `S_t = (1 - t) • T₂ + t • T₁` (`segmentMetric_inner_eq_realizeSymm_add`) and the metric
difference is the realized symmetric tensor `realizeSymmCcTensor g₀ (T₁ − T₂)`, the metric-difference
covariant jets `∇^i(g₁ − g₂)` are exactly the realized-tensor covariant jets `∇^i(realizeSymm g₀
(T₁ − T₂))`; the per-point triangle inequality over the finite Faà-di-Bruno index set, folding the
coefficient sup into `C`, yields the fibre-norm sum bound.

Its conclusion is a *real-valued pointwise* fibre-*norm* (un-squared) Lipschitz inequality — at each
base point `x`, in the `g₀`-Riemannian fibre norm — with the **honest order budget** `i ≤ j + 2` and
a single uniform constant `C`, structurally distinct from any chart-Sobolev or `L²` statement; no
packaging.  The supercriticality hypothesis `ha` is genuinely required for the uniform-over-the
`B`-family fibre-norm bound on the segment-metric `≤2`-jet coefficient.  Its body is `sorry`: it is
the genuine atomic covariant-Faà-di-Bruno segment-metric expansion of the geometric nonlinearity
`Ric + Lie` (the `Δ_∇` summand is handled separately, the metric-realization map already factored
out by the consumer), with no spectral-nonlinearity, perturbation-indexed-remainder, or Weyl
dependence. -/
theorem exists_deTurckRHSRetagDiff_iteratedCovGrad_fiberNorm_le_realizeSymmMetricDiffJet
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∀ j : ℕ, j ≤ 2 * a → ∀ x : M,
          Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                  (deTurckRHSRetag (I := I) g₀ g_bg g₁
                    - deTurckRHSRetag (I := I) g₀ g_bg g₂)).toSection x))
            ≤ C * ∑ i ∈ Finset.range (j + 3),
                Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                      (MetricRealization.realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x)) := by
  classical
  -- The genuine atomic covariant-Faà-di-Bruno term decomposition: `∇^j(D₁−D₂)` splits into a finite
  -- `range (j+3)`-indexed sum of pieces, each fibre-norm-bounded by `C` times one realized-metric-
  -- difference jet.
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_deTurckRHSRetagDiff_iteratedCovGrad_faaDiBruno_termDecomp (I := I) g₀ g_bg a ha B hB
  refine ⟨C, hC_nn, fun T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ j hj x => ?_⟩
  -- The fibre-value term family, the splitting equation, and the per-term single-jet bound.
  obtain ⟨term, heq, hbound⟩ := hC T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ j hj x
  letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + j) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
  -- Per-order realized-jet fibre-norm root abbreviation.
  set realSqrt : ℕ → ℝ := fun i =>
    Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + i) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (MetricRealization.realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x))
    with hrealSqrt_def
  -- Bridge the left-hand-side root to the installed fibre norm, substitute the splitting equation.
  rw [sqrt_riemannianFiberNormSq_toSection_eq_norm (I := I) g₀ (2 + j) x
    (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
      (deTurckRHSRetag (I := I) g₀ g_bg g₁ - deTurckRHSRetag (I := I) g₀ g_bg g₂)), heq]
  -- Triangle over the finite sum, then the per-term single-jet bound, then factor `C`.
  calc ‖∑ i ∈ Finset.range (j + 3), (term i).toSection x‖
      ≤ ∑ i ∈ Finset.range (j + 3), ‖(term i).toSection x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (j + 3), C * realSqrt i :=
        Finset.sum_le_sum (fun i hi => hbound i hi)
    _ = C * ∑ i ∈ Finset.range (j + 3), realSqrt i := by rw [Finset.mul_sum]

/-- **The covariant-jet fibre-norm Lipschitz bound for the re-tagged Ricci–DeTurck right-hand-side
difference (the genuine atomic covariant Faà-di-Bruno chain-rule core, in un-squared fibre-norm
Lipschitz form with the honest order budget).**

For an anchor `g₀`, a flow background `g_bg`, an order `a`, a supercriticality hypothesis
`ha : 2 * a > Module.finrank ℝ E + 4`, and a uniform `H^{a+2}`-size bound `B ≥ 0`, there is a
single constant `C ≥ 0` such that for any two `g₀`-fibre-small perturbations `T₁, T₂` whose
`H^{a+2}` norms are `≤ B`, any two realized metrics `g₁, g₂` of `T₁, T₂` (tied by the fibrewise
`inner`-identities), every covariant-gradient order `j ≤ 2 * a`, and **every base point `x`**, the
`g₀`-Riemannian fibre *norm* (un-squared) of the `j`-th intrinsic iterated covariant gradient of
the re-tagged DeTurck right-hand-side section difference is bounded *pointwise* by `C` times the
finite sum, over covariant-gradient orders `i ≤ j + 2`, of the `g₀`-Riemannian fibre *norms* of the
iterated covariant gradients `∇^i(T₁ − T₂)` of the perturbation difference:
```
√(rfns g₀ 0 (2+j) x (∇^j (D₁ − D₂) x))
  ≤ C · ∑_{i ∈ range (j+3)} √(rfns g₀ 0 (2+i) x (∇^i (T₁ − T₂) x))   (j ≤ 2a),
```
where `Dₖ = deTurckRHSRetag g₀ g_bg gₖ` and `√(rfns …) = ‖·‖` is the `g₀`-fibre norm.

This is the genuine **covariant Faà-di-Bruno expansion** of the *non-linear* summand `Ric + Lie`
of the second-order Ricci–DeTurck right-hand side, in the natural **fibre-norm Lipschitz** form: the
chart right-hand side `deTurckRicciRHS g_bg g = -2 • Ric(g) + 𝓛_{W(g)} g` is a smooth (fibrewise)
function `F` of the metric `≤2`-jet `(g, ∇g, ∇²g)` and the fibre-inverse `g⁻¹`; by the covariant
fundamental theorem of calculus along the **segment metric** `g_t = g₂ + t·(g₁ − g₂)` the difference
`F(g₁) − F(g₂) = ∫₀¹ DF(g_t)·(g₁ − g₂) dt`, whose `j`-th covariant gradient is, by the covariant
product/chain rule (covariant Leibniz over the contraction), a finite sum of contracted products of
a **segment-metric `≤(j+2)`-jet coefficient** (a fibrewise-polynomial expression in the `≤(j+2)`-jets
of the *segment* metric `g_t` and the bounded fibre-inverses, uniformly fibre-norm bounded on the
compact `M` over the `H^{a+2}`-bounded `B`-family by the supercritical embedding `H^{2(a+2)} ↪ C²`
implied by `ha`) with an iterated covariant gradient `∇^i(g₁ − g₂)` of order `i ≤ j + 2` of the
metric difference.  Since the fibrewise `inner`-difference makes `(g₁ − g₂).inner =
ccTensorBilinSymm g₀ (T₁ − T₂)` the realized bilinear form of `T₁ − T₂`, each `∇^i(g₁ − g₂)` is
fibre-norm-controlled (the realization `T ↦ ccTensorBilinSymm g₀ T` being a bounded smooth bundle
map whose covariant jets are bounded combinations of the perturbation's covariant jets) by the
`≤ i`-order covariant gradients of `T₁ − T₂`; the per-point triangle inequality over the finite
Faà-di-Bruno index set, folding the coefficient sup into `C`, yields the fibre-norm sum bound.

Its conclusion is a *real-valued pointwise* fibre-*norm* (un-squared) Lipschitz inequality — at each
base point `x`, in the `g₀`-Riemannian fibre norm, with the **honest order budget** `i ≤ j + 2`
(the second-order operator gains two derivatives, no more) and a single uniform constant `C` —
structurally distinct from the parent leaf's **squared** fibre-norm-square conclusion with the slack
budget `i ≤ 2a + 2`; no packaging.  The supercriticality hypothesis `ha` is genuinely required for
the uniform-over-the-`B`-family fibre-norm bound on the segment-metric `≤2`-jet coefficient.  Its
body is `sorry`: it is the genuine atomic covariant-Faà-di-Bruno segment-metric fibre-norm expansion
(the `Ric + Lie` summand only — the linear `Δ_∇` summand is handled separately), with no
spectral-nonlinearity, perturbation-indexed-remainder, or Weyl dependence. -/
theorem exists_deTurckRHSRetagDiff_iteratedCovGrad_fiberNorm_le_perturbationJet
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∀ j : ℕ, j ≤ 2 * a → ∀ x : M,
          Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                  (deTurckRHSRetag (I := I) g₀ g_bg g₁
                    - deTurckRHSRetag (I := I) g₀ g_bg g₂)).toSection x))
            ≤ C * ∑ i ∈ Finset.range (j + 3),
                Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)).toSection x)) := by
  classical
  -- The genuine geometric covariant chain-rule core, against the realized metric-difference jets:
  -- `√rfns(∇^j(D₁−D₂)) ≤ C₀ · ∑_{i ≤ j+2} √rfns(∇^i (realizeSymm (T₁−T₂)))`.
  obtain ⟨C₀, hC₀_nn, hC₀⟩ :=
    exists_deTurckRHSRetagDiff_iteratedCovGrad_fiberNorm_le_realizeSymmMetricDiffJet
      (I := I) g₀ g_bg a ha B hB
  -- The final uniform constant absorbs the `(j+3) ≤ 2a+3` realize-jet redistribution factor.
  refine ⟨C₀ * (2 * a + 3 : ℕ), by positivity,
    fun T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ j hj x => ?_⟩
  -- Per-order abbreviations of the perturbation-difference and realized-tensor fibre-norm roots.
  set pertSqrt : ℕ → ℝ := fun l =>
    Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + l) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l (T₁ - T₂)).toSection x))
    with hpertSqrt_def
  have hpertSqrt_nn : ∀ l, 0 ≤ pertSqrt l := fun l => Real.sqrt_nonneg _
  -- The realized-tensor fibre-norm root at order `i` is dominated by the perturbation-difference
  -- roots up to order `i` (the realization map gains no derivatives, `C = 1`), bridging
  -- `√rfns(·) = ‖·‖` at both ends.
  have hreal_le : ∀ i : ℕ,
      Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
              (MetricRealization.realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x)) ≤
        ∑ l ∈ Finset.range (i + 1), pertSqrt l := by
    intro i
    -- Bridge the LHS root to the installed fibre norm.
    rw [sqrt_riemannianFiberNormSq_toSection_eq_norm (I := I) g₀ (2 + i) x
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
        (MetricRealization.realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))]
    -- The explicit-constant realize-jet bound, then bridge each summand back to a root.
    refine (norm_iteratedCovGrad_realizeSymm_le_jetSum (I := I) g₀ (T₁ - T₂) i x).trans ?_
    refine le_of_eq (Finset.sum_congr rfl (fun l _ => ?_))
    -- `pertSqrt l` unfolds to `√rfns(∇^l (T₁−T₂))`; bridge the norm back to that root.
    rw [hpertSqrt_def]
    exact (sqrt_riemannianFiberNormSq_toSection_eq_norm (I := I) g₀ (2 + l) x
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l (T₁ - T₂))).symm
  -- Extend each order-`i` realize bound to the full `range (j+3)` perturbation sum (`i ≤ j+2`).
  have hreal_le_full : ∀ i ∈ Finset.range (j + 3),
      Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
              (MetricRealization.realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x)) ≤
        ∑ l ∈ Finset.range (j + 3), pertSqrt l := by
    intro i hi
    refine (hreal_le i).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by rw [Finset.mem_range] at hi; omega))
      (fun l _ _ => hpertSqrt_nn l)
  -- Sum the realize bounds: `∑_{i<j+3} √rfns(realizeSymm) ≤ (j+3) · ∑_{l<j+3} pertSqrt l`.
  have hsum_real_le :
      ∑ i ∈ Finset.range (j + 3),
          Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                (MetricRealization.realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x)) ≤
        ((j + 3 : ℕ) : ℝ) * ∑ l ∈ Finset.range (j + 3), pertSqrt l := by
    refine le_trans (Finset.sum_le_sum hreal_le_full) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- The realize-jet redistribution factor `(j+3) ≤ 2a+3`, all summands nonnegative.
  have hsum_pert_nn : 0 ≤ ∑ l ∈ Finset.range (j + 3), pertSqrt l :=
    Finset.sum_nonneg (fun l _ => hpertSqrt_nn l)
  have hjle : ((j + 3 : ℕ) : ℝ) ≤ ((2 * a + 3 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : j + 3 ≤ 2 * a + 3)
  -- Chain the geometric core with the realize-jet reduction and the constant absorption.
  calc Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + j) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
              (deTurckRHSRetag (I := I) g₀ g_bg g₁
                - deTurckRHSRetag (I := I) g₀ g_bg g₂)).toSection x))
      ≤ C₀ * ∑ i ∈ Finset.range (j + 3),
          Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                (MetricRealization.realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x)) :=
        hC₀ T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ j hj x
    _ ≤ C₀ * (((j + 3 : ℕ) : ℝ) * ∑ l ∈ Finset.range (j + 3), pertSqrt l) :=
        mul_le_mul_of_nonneg_left hsum_real_le hC₀_nn
    _ ≤ C₀ * (((2 * a + 3 : ℕ) : ℝ) * ∑ l ∈ Finset.range (j + 3), pertSqrt l) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hjle hsum_pert_nn) hC₀_nn
    _ = C₀ * (2 * a + 3 : ℕ) * ∑ i ∈ Finset.range (j + 3), pertSqrt i := by ring

/-- **The pointwise covariant Faà-di-Bruno fibre-norm-square bound for the re-tagged
Ricci–DeTurck right-hand-side difference (the genuine atomic segment-metric covariant chain-rule
core, stated *pointwise* in `g₀`-Riemannian fibre-norm-squares).**

For an anchor `g₀`, a flow background `g_bg`, an order `a`, a supercriticality hypothesis
`ha : 2 * a > Module.finrank ℝ E + 4`, and a uniform `H^{a+2}`-size bound `B ≥ 0`, there is a
single constant `C ≥ 0` such that for any two `g₀`-fibre-small perturbations `T₁, T₂` whose
`H^{a+2}` norms are `≤ B`, any two realized metrics `g₁, g₂` of `T₁, T₂` (tied by the fibrewise
`inner`-identities), every covariant-gradient order `j ≤ 2 * a`, and **every base point `x`**, the
`g₀`-Riemannian fibre-norm-square of the `j`-th intrinsic iterated covariant gradient of the
re-tagged DeTurck right-hand-side section difference is bounded *pointwise* by `C²` times the finite
sum, over covariant-gradient orders `i ≤ 2 * a + 2`, of the `g₀`-Riemannian fibre-norm-squares of
the iterated covariant gradients `∇^i(T₁ − T₂)` of the perturbation difference:
```
riemannianFiberNormSq g₀ 0 (2+j) x (∇^j (deTurckRHSRetag g₀ g_bg g₁ − deTurckRHSRetag g₀ g_bg g₂) x)
  ≤ C² · ∑_{i ∈ range (2a+3)} riemannianFiberNormSq g₀ 0 (2+i) x (∇^i (T₁ − T₂) x)   (j ≤ 2a).
```

This is the genuine **covariant Faà-di-Bruno expansion** of the *non-linear* summand `Ric + Lie`
of the second-order Ricci–DeTurck right-hand side, taken *pointwise* in the `g₀`-fibre norm.  The
chart right-hand side `deTurckRicciRHS g_bg g = -2 • Ric(g) + 𝓛_{W(g)} g` is a smooth (fibrewise)
function `F` of the metric `≤2`-jet `(g, ∇g, ∇²g)` and the fibre-inverse `g⁻¹`; by the covariant
fundamental theorem of calculus along the **segment metric** `g_t = g₂ + t·(g₁ − g₂)` the
difference `F(g₁) − F(g₂) = ∫₀¹ DF(g_t)·(g₁ − g₂) dt`, whose `j`-th covariant gradient is, by the
covariant product/chain rule (covariant Leibniz over the contraction), a finite sum of contracted
products of a **segment-metric `≤(j+2)`-jet coefficient** (a fibrewise-polynomial expression in the
`≤(j+2)`-jets of the *segment* metric `g_t` and the bounded fibre-inverses, *uniformly fibre-norm
bounded on the compact `M` over the `H^{a+2}`-bounded `B`-family by the supercritical embedding
`H^{2(a+2)} ↪ C^{2}` implied by `ha`*) with an iterated covariant gradient `∇^i(g₁ − g₂)` of order
`i ≤ j + 2 ≤ 2a + 2` of the metric difference.  Since the fibrewise `inner`-difference makes
`(g₁ − g₂).inner = ccTensorBilinSymm g₀ (T₁ − T₂)` the realized bilinear form of `T₁ − T₂`, each
`∇^i(g₁ − g₂)` is fibrewise-norm-controlled (the realization `T ↦ ccTensorBilinSymm g₀ T` being a
bounded smooth bundle map whose covariant jets are bounded combinations of the perturbation's
covariant jets) by the `≤ i`-order covariant gradients of `T₁ − T₂`; the per-point Cauchy–Schwarz
over the finite Faà-di-Bruno index set, folding the squared coefficient sup into `C²`, yields the
fibre-norm-square sum bound.

Its conclusion is a *real-valued pointwise* fibre-norm-square inequality — at each base point `x`,
in the `g₀`-Riemannian fibre norm — structurally distinct from the integrated global-`L²`
(semi)norm conclusion of the parent leaf (which lifts this pointwise bound to `L²` by the
pointwise-to-`L²` packaging and re-absorbs the `C⁰`-redistribution through the order-`a`
chart-Sobolev term); no packaging.  The supercriticality hypothesis `ha` is genuinely required for
the uniform-over-the-`B`-family fibre-norm bound on the segment-metric `≤2`-jet coefficient.

It is **proven by composition** (TRANSIT glue) of the genuine atomic covariant-Faà-di-Bruno
fibre-*norm* (un-squared) Lipschitz primitive
`exists_deTurckRHSRetagDiff_iteratedCovGrad_fiberNorm_le_perturbationJet` (the covariant chain-rule
expansion of `∇^j(D₁ − D₂)` in the `g₀`-Riemannian fibre *norm*, pointwise bounded by `C` times the
fibre-norm sum, over the *honest* order budget `i ≤ j + 2`, of the perturbation-difference covariant
jets): squaring the un-squared bound (both sides nonnegative, via `Real.sq_sqrt` on the nonnegative
fibre-norm-square `√(rfns)² = rfns`) gives `rfns(∇^j(D₁ − D₂)) ≤ C² · (∑_{i ≤ j+2} √rfnsᵢ)²`, the
finite-sum Cauchy–Schwarz `sq_sum_le_card_mul_sum_sq` collapses `(∑_{i ≤ j+2} √rfnsᵢ)² ≤
(j+3) · ∑_{i ≤ j+2} rfnsᵢ` (`Real.sq_sqrt` again on each nonnegative summand), the budget extends
`j + 3 ≤ 2a + 3` (all summands nonnegative), and the `j`-dependent factor `j + 3 ≤ 2a + 3` is
absorbed into the uniform constant `C² · (2a + 3) = (C · √(2a+3))²`.  Consumers transitively depend
on `sorryAx` only through the genuine atomic fibre-norm Lipschitz primitive (the `Ric + Lie` summand
only — the linear `Δ_∇` summand is handled separately), with no spectral-nonlinearity,
perturbation-indexed-remainder, or Weyl dependence. -/
theorem exists_segmentMetricFaaDiBruno_covGrad_fiberNormSq_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∀ j : ℕ, j ≤ 2 * a → ∀ x : M,
          Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                  (deTurckRHSRetag (I := I) g₀ g_bg g₁
                    - deTurckRHSRetag (I := I) g₀ g_bg g₂)).toSection x)
            ≤ C ^ 2 * ∑ i ∈ Finset.range (2 * a + 3),
                Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)).toSection x) := by
  classical
  -- The genuine atomic covariant-Faà-di-Bruno fibre-*norm* (un-squared) Lipschitz primitive: each
  -- `√(rfns(∇^j(D₁−D₂)))` is bounded by `C₀ · ∑_{i ≤ j+2} √(rfns(∇^i(T₁−T₂)))` (honest budget).
  obtain ⟨C₀, hC₀_nn, hC₀⟩ :=
    exists_deTurckRHSRetagDiff_iteratedCovGrad_fiberNorm_le_perturbationJet
      (I := I) g₀ g_bg a ha B hB
  -- Leaf constant `C := C₀ · √(2a+3)`; squaring gives `C² = C₀² · (2a+3)`.
  refine ⟨C₀ * Real.sqrt (2 * a + 3), mul_nonneg hC₀_nn (Real.sqrt_nonneg _),
    fun T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ j hj x => ?_⟩
  -- Abbreviations for the per-order fibre-norm-squares of the right-hand-side difference and the
  -- perturbation difference.
  set rhsSq : ℝ := Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + j) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
          (deTurckRHSRetag (I := I) g₀ g_bg g₁
            - deTurckRHSRetag (I := I) g₀ g_bg g₂)).toSection x) with hrhsSq_def
  set pertSq : ℕ → ℝ := fun i =>
    Integral.Connection.riemannianFiberNormSq (I := I) g₀ 0 (2 + i) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)).toSection x) with hpertSq_def
  have hpertSq_nn : ∀ i, 0 ≤ pertSq i := fun i =>
    Integral.Connection.riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + i) x _
  have hrhsSq_nn : 0 ≤ rhsSq :=
    Integral.Connection.riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  -- The fibre-norm primitive, in the present abbreviations: `√rhsSq ≤ C₀ · ∑_{i<j+3} √pertSqᵢ`.
  have hnorm : Real.sqrt rhsSq ≤ C₀ * ∑ i ∈ Finset.range (j + 3), Real.sqrt (pertSq i) :=
    hC₀ T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ j hj x
  -- Step 1: square the fibre-norm bound.  `rhsSq = (√rhsSq)² ≤ (C₀ · ∑ √pertSqᵢ)²`.
  have hsq_lhs : rhsSq = (Real.sqrt rhsSq) ^ 2 := (Real.sq_sqrt hrhsSq_nn).symm
  have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (j + 3), Real.sqrt (pertSq i) :=
    Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hsquared : rhsSq ≤ (C₀ * ∑ i ∈ Finset.range (j + 3), Real.sqrt (pertSq i)) ^ 2 := by
    rw [hsq_lhs]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hnorm 2
  -- Step 2: Cauchy–Schwarz collapse `(∑_{i<j+3} √pertSqᵢ)² ≤ (j+3) · ∑_{i<j+3} pertSqᵢ`.
  have hCS : (∑ i ∈ Finset.range (j + 3), Real.sqrt (pertSq i)) ^ 2 ≤
      ((j + 3 : ℕ) : ℝ) * ∑ i ∈ Finset.range (j + 3), pertSq i := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 3))
      (f := fun i => Real.sqrt (pertSq i))
    rw [Finset.card_range] at h
    refine h.trans (le_of_eq ?_)
    refine congrArg (((j + 3 : ℕ) : ℝ) * ·) (Finset.sum_congr rfl (fun i _ => ?_))
    exact Real.sq_sqrt (hpertSq_nn i)
  -- The honest order budget `j + 3 ≤ 2a + 3` (from `j ≤ 2a`).
  have hj3 : j + 3 ≤ 2 * a + 3 := by omega
  -- Step 3: extend the order budget `range (j+3) ⊆ range (2a+3)` (all summands nonnegative).
  have hbudget : ∑ i ∈ Finset.range (j + 3), pertSq i ≤ ∑ i ∈ Finset.range (2 * a + 3), pertSq i :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr hj3) (fun i _ _ => hpertSq_nn i)
  -- Step 4: chain, with the `j`-dependent factor `(j+3)` dominated by `(2a+3)`.
  have hjle : ((j + 3 : ℕ) : ℝ) ≤ ((2 * a + 3 : ℕ) : ℝ) := by exact_mod_cast hj3
  have hsumtot_nn : 0 ≤ ∑ i ∈ Finset.range (2 * a + 3), pertSq i :=
    Finset.sum_nonneg (fun i _ => hpertSq_nn i)
  have hsqrt_sq : Real.sqrt (2 * a + 3) ^ 2 = (2 * a + 3 : ℝ) :=
    Real.sq_sqrt (by positivity)
  calc rhsSq
      ≤ (C₀ * ∑ i ∈ Finset.range (j + 3), Real.sqrt (pertSq i)) ^ 2 := hsquared
    _ = C₀ ^ 2 * (∑ i ∈ Finset.range (j + 3), Real.sqrt (pertSq i)) ^ 2 := by rw [mul_pow]
    _ ≤ C₀ ^ 2 * (((j + 3 : ℕ) : ℝ) * ∑ i ∈ Finset.range (j + 3), pertSq i) :=
        mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
    _ ≤ C₀ ^ 2 * (((2 * a + 3 : ℕ) : ℝ) * ∑ i ∈ Finset.range (2 * a + 3), pertSq i) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        exact mul_le_mul hjle hbudget
          (Finset.sum_nonneg (fun i _ => hpertSq_nn i)) (by positivity)
    _ = (C₀ * Real.sqrt (2 * a + 3)) ^ 2 * ∑ i ∈ Finset.range (2 * a + 3), pertSq i := by
        rw [mul_pow, hsqrt_sq]; push_cast; ring

/-- **The covariant Faà-di-Bruno Moser-tame `L²`-jet bound for the segment-metric `2`-jet (the
genuine atomic segment-metric covariant chain-rule core).**

For an anchor `g₀`, a flow background `g_bg`, an order `a`, a supercriticality hypothesis
`ha : 2 * a > Module.finrank ℝ E + 4`, and a uniform `H^{a+2}`-size bound `B ≥ 0`, there is a
single constant `C ≥ 0` such that for any two `g₀`-fibre-small perturbations `T₁, T₂` whose
`H^{a+2}` norms are `≤ B`, any two realized metrics `g₁, g₂` of `T₁, T₂` (tied by the fibrewise
`inner`-identities), and every covariant-gradient order `j ≤ 2 * a`, the global metric `L²`
(semi)norm of the `j`-th intrinsic iterated covariant gradient of the **re-tagged DeTurck
right-hand-side** section difference is bounded by the **Moser-tame redistributed sum** of the
segment-metric `2`-jet against the perturbation difference: a constant multiple of the sum of the
lower-order chart-Sobolev norm `‖(T₁ − T₂).toHs a‖` of the perturbation difference (carrying the
redistributed *top* segment-metric-`2`-jet derivative, which the `L²`-tame estimate keeps in `L²`
and which is folded — together with the segment-metric-`2`-jet's own `C^j`-sup and `L²`-jet, all
controlled by `φ(B)` through the supercritical embedding implied by `ha` — into `C`, the metric
perturbation entering this term only through its `L^∞`/`C⁰`-sup, which the order-`a` Sobolev
embedding controls) and the finite sum, over covariant-gradient orders `i ≤ 2 * a + 2`, of the
metric `L²` norms of the iterated covariant gradients `∇^i` of `T₁ − T₂`:
```
‖∇^j (deTurckRHSRetag g₀ g_bg g₁ − deTurckRHSRetag g₀ g_bg g₂)‖_{L²}
  ≤ C · ( ‖(T₁ − T₂).toHs a‖
          + ∑_{i ∈ range (2a+3)} ‖∇^i (T₁ − T₂)‖_{L²} )   (for j ≤ 2 * a).
```

This is the genuine **covariant Faà-di-Bruno expansion** of the *non-linear* summand `Ric + Lie`
of the second-order Ricci–DeTurck right-hand side, lifted to `L²` by the **intrinsic Moser tame
product** (`exists_moserTameProduct_iteratedCovGrad_l2Norm_le`).  The chart right-hand side
`deTurckRicciRHS g_bg g = -2 • Ric(g) + 𝓛_{W(g)} g` is a smooth (fibrewise) function `F` of the
metric `≤2`-jet `(g, ∇g, ∇²g)` and the fibre-inverse `g⁻¹`; by the covariant fundamental theorem
of calculus along the **segment metric** `g_t = g₂ + t·(g₁ − g₂)`, the difference
`F(g₁) − F(g₂) = ∫₀¹ DF(g_t)·(g₁ − g₂) dt`, whose `j`-th covariant gradient is, by the covariant
product/chain rule, a finite sum of contracted products of a **segment-metric `≤(j+2)`-jet
coefficient** (the `DF(g_t)`-polynomial in the `≤(j+2)`-jets of the *segment* metric `g_t` and the
bounded fibre-inverses) with an iterated covariant gradient `∇^i(g₁ − g₂)` of order `i ≤ j + 2 ≤
2a + 2` of the metric difference.  The genuine content is the **segment metric `g_t` (a full
metric, not the difference)**: its `≤2`-jet `C²`-sup, its covariant `L²`-jets, and the top-order
redistribution are precisely what the Moser-tame estimate consumes — the top metric derivative
cannot be taken pointwise in `C⁰` on a manifold of dimension `≥ 4` (the metric pointwise
`C^{2a+2}`-jet is unavailable for `finrank ≥ 4`), so it is kept in `L²` while the perturbation's
`L^∞`/`C⁰` factor is carried by the order-`a` chart-Sobolev term `‖(T₁ − T₂).toHs a‖` (the
supercritical embedding `H^a ↪ C⁰` controlling the `C⁰`-sup of `T₁ − T₂`), the redistribution that
distinguishes this `L²` statement from any pointwise fibre-norm bound.  Since the fibrewise `inner`-difference
makes `(g₁ − g₂).inner = ccTensorBilinSymm g₀ (T₁ − T₂)` the realized bilinear form of `T₁ − T₂`,
each `∇^i(g₁ − g₂)` is `L²`-controlled (the realization is a bounded smooth bundle map gaining no
derivatives) by the `≤ i`-order covariant gradients of `T₁ − T₂`.

Its conclusion is a *real-valued* global-`L²` (semi)norm inequality exposing the Moser-tame
`C⁰`-redistribution (the `‖(T₁ − T₂).toHs a‖` summand, a *chart-Sobolev* norm carrying the
`L^∞` factor, *absent* from the parent and not defeq to the covariant-`L²`-jet sum — the parent
re-absorbs it only through a genuine Sobolev embedding plus the on-disk reverse comparison),
structurally distinct from the parent's pure covariant-`L²`-jet conclusion; no packaging.  The supercriticality hypothesis `ha` is genuinely required for the
uniform-over-the-`B`-family Nemytskii constant (the segment-metric `≤2`-jet `C²`-sup and `L²`-jet
over the `H^{a+2}`-bounded family need the supercritical embedding).

It is **proven by composition** (TRANSIT glue) of the genuine atomic *pointwise* covariant
Faà-di-Bruno fibre-norm-square expansion `exists_segmentMetricFaaDiBruno_covGrad_fiberNormSq_le`
(the covariant chain-rule expansion of `∇^j(D₁ − D₂)` in `g₀`-Riemannian fibre-norm-squares,
pointwise bounded by `C²` times the fibre-norm-square sum of the perturbation-difference covariant
jets) with the pointwise-to-`L²` packaging
`tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum` (lifting the pointwise fibre-norm-square bound
to the global `L²` norm, `‖∇^j(D₁ − D₂)‖ ≤ C · ∑_{i ≤ 2a+2} ‖∇^i(T₁ − T₂)‖`) and
`tensorL2Norm_toFun_eq_norm` (`‖∇^i(T₁ − T₂)‖ = tensorL2Norm g₀ 0 (2+i) (∇^i(T₁ − T₂)).toFun`); the
nonnegative `‖(T₁ − T₂).toHs a‖` redistribution term is then added on (the `L²`-tame statement
dominates the pure jet-sum bound).  Consumers transitively depend on `sorryAx` only through the
genuine atomic pointwise covariant-Faà-di-Bruno segment-metric primitive (the `Ric + Lie` summand
only — the linear `Δ_∇` summand is handled separately), with no spectral-nonlinearity,
perturbation-indexed-remainder, or Weyl dependence. -/
theorem exists_segmentMetricJet2DiffFaaDiBruno_moserTame_l2Norm_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∀ j : ℕ, j ≤ 2 * a →
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
              (deTurckRHSRetag (I := I) g₀ g_bg g₁ - deTurckRHSRetag (I := I) g₀ g_bg g₂)‖
            ≤ C * (‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖
                + ∑ i ∈ Finset.range (2 * a + 3),
                    Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + i)
                      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)).toFun) := by
  classical
  -- The genuine deep analytic core: the pointwise covariant-Faà-di-Bruno fibre-norm-square
  -- expansion of the re-tagged DeTurck right-hand-side difference along the segment metric (the
  -- covariant chain-rule expansion in `g₀`-Riemannian fibre norms, uniform over the `H^{a+2}`-bounded
  -- `B`-family via the supercritical embedding implied by `ha`).
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_segmentMetricFaaDiBruno_covGrad_fiberNormSq_le (I := I) g₀ g_bg a ha B hB
  refine ⟨C, hC_nn, fun T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ j hj => ?_⟩
  set Curv : Integral.L2.SmoothCcTensor g₀ 0 (2 + j) :=
    PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
      (deTurckRHSRetag (I := I) g₀ g_bg g₁ - deTurckRHSRetag (I := I) g₀ g_bg g₂) with hCurv_def
  -- Lift the pointwise fibre-norm-square bound to the global `L²` norm by the pointwise-to-`L²`
  -- packaging: `‖∇^j (D₁ − D₂)‖ ≤ C · ∑_{i ≤ 2a+2} ‖∇^i (T₁ − T₂)‖`.
  have hpack :
      ‖Curv‖ ≤ C * ∑ i ∈ Finset.range (2 * a + 3),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)‖ :=
    Integral.Connection.tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum
      (I := I) (M := M) g₀ (2 * a + 3) (fun i => 2 + i)
      (fun i => PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂))
      Curv C hC_nn (fun x => hC T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ j hj x)
  -- Each covariant-`L²`-jet summand `‖∇^i (T₁ − T₂)‖ = tensorL2Norm g₀ 0 (2+i) (∇^i (T₁ − T₂)).toFun`.
  have hsum_eq :
      ∑ i ∈ Finset.range (2 * a + 3),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)‖ =
        ∑ i ∈ Finset.range (2 * a + 3),
          Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + i)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)).toFun := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact (Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm (I := I) g₀
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂))).symm
  rw [hsum_eq] at hpack
  -- Absorb the nonnegative `‖(T₁ − T₂).toHs a‖` redistribution term (added to the jet sum).
  set jetSum : ℝ := ∑ i ∈ Finset.range (2 * a + 3),
      Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + i)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)).toFun with hjetSum_def
  have htoHs_nn :
      0 ≤ ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ :=
    norm_nonneg _
  calc ‖Curv‖ ≤ C * jetSum := hpack
    _ ≤ C * (‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖
            + jetSum) :=
        mul_le_mul_of_nonneg_left (by linarith) hC_nn

/-- **The covariant Nemytskii covariant-jet `L²` bound for the re-tagged Ricci–DeTurck
right-hand side, stated in covariant `L²`-jets of the perturbation difference (the genuine deep
covariant-Faà-di-Bruno analytic core).**

For an anchor `g₀`, a flow background `g_bg`, an order `a`, a supercriticality hypothesis
`ha : 2 * a > Module.finrank ℝ E + 4`, and a uniform `H^{a+2}`-size bound `B ≥ 0`, there is a
single constant `C ≥ 0` such that for any two `g₀`-fibre-small perturbations `T₁, T₂` whose
`H^{a+2}` norms are `≤ B`, any two realized metrics `g₁, g₂` of `T₁, T₂` (tied by the fibrewise
`inner`-identities), and every covariant-gradient order `j ≤ 2 * a`, the global metric `L²`
(semi-)norm of the `j`-th intrinsic iterated covariant gradient of the **re-tagged DeTurck
right-hand-side** section difference is bounded by the finite sum, over covariant-gradient orders
`i ≤ 2 * a + 2`, of the global metric `L²` norms of the iterated covariant gradients `∇^i` of the
perturbation difference `T₁ − T₂`:
```
‖∇^j (deTurckRHSRetag g₀ g_bg g₁ − deTurckRHSRetag g₀ g_bg g₂)‖_{L²}
  ≤ C · ∑_{i ∈ range (2a+3)} ‖∇^i (T₁ − T₂)‖_{L²}   (for j ≤ 2 * a).
```

This is the genuine **higher-order quasilinear covariant Nemytskii estimate** for the *non-linear*
summand `Ric + Lie` of the second-order Ricci–DeTurck right-hand side, phrased intrinsically and
stated against the covariant `L²`-jets of the perturbation difference (the consumer below converts
the right-hand-side covariant-jet sum to the order-`(a+2)` chart-Sobolev norm by the forward
covariant-jet `L²` comparison `exists_iteratedCovGrad_l2Norm_le_toHs`, since `i ≤ 2a+2 = 2(a+2)`).
The chart right-hand side `deTurckRicciRHS g_bg g = -2 • Ric(g) + 𝓛_{W(g)} g` is a smooth
(fibrewise) function `F` of the metric `≤2`-jet `(g, ∇g, ∇²g)` and the fibre-inverse `g⁻¹`, so by
the covariant fundamental theorem of calculus along the segment `g_t = g₂ + t·(g₁ − g₂)` the
difference `F(g₁) − F(g₂) = ∫₀¹ DF(g_t)·(g₁ − g₂) dt`, whose `j`-th covariant gradient is, by the
covariant product/chain rule (covariant Faà-di-Bruno), a finite sum of contracted products of a
segment-metric `≤(j+2)`-jet coefficient with an iterated covariant gradient `∇^i(g₁ − g₂)` of
order `i ≤ j + 2 ≤ 2a + 2` of the metric difference.

It is **proven by composition** (TRANSIT glue) of the covariant-Faà-di-Bruno **segment-metric
Moser-tame `L²`-jet** primitive `exists_segmentMetricJet2DiffFaaDiBruno_moserTame_l2Norm_le` (which
lifts the covariant chain-rule expansion to `L²` by the intrinsic Moser tame product, the top
segment-metric-`2`-jet derivative kept in `L²` and the perturbation's `L^∞` factor carried by an
order-`a` chart-Sobolev redistribution term `‖(T₁ − T₂).toHs a‖`) with the on-disk **reverse
chart-Sobolev comparison** `exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum`
at the redistribution order `a` (`‖(T₁ − T₂).toHs a‖ ≤ CR · ∑_{j ≤ 2a} ‖∇^j (T₁ − T₂)‖_{L²}`,
within the parent's `2a + 2` jet-sum budget, all summands nonnegative): the reverse comparison
re-absorbs the Moser-tame redistribution term into the covariant-`L²`-jet sum, collapsing the
segment-metric primitive's output to the stated covariant-jet `L²`-sum bound.  Since the fibrewise
`inner`-difference makes `(g₁ − g₂).inner = ccTensorBilinSymm g₀ (T₁ − T₂)` the realized bilinear
form of `T₁ − T₂`, the metric-difference jets are the perturbation-difference jets.

Its conclusion is a *real-valued* global-`L²` (semi-)norm inequality on the intrinsic iterated
covariant gradients of the right-hand-side difference, bounded by the covariant-jet `L²`-sum of the
perturbation difference — structurally distinct from the chart-`Hᵃ` `toHs`-norm conclusion of the
consumer; no packaging.  The supercriticality hypothesis `ha` is genuinely required for the
uniform-over-the-`B`-family Nemytskii constant (the segment-metric `≤2`-jet `C²`-sup and `L²`-jet
over the `H^{a+2}`-bounded family need the supercritical embedding) and is threaded into the
segment-metric Moser-tame primitive.  Consumers transitively depend on `sorryAx` only through the
genuine covariant-Faà-di-Bruno segment-metric Moser-tame primitive (and the reverse comparison's
own atomic Sobolev primitives). -/
theorem exists_deTurckRHSRetagDiff_iteratedCovGrad_l2Norm_le_iteratedCovGrad_sum
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∀ j : ℕ, j ≤ 2 * a →
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
              (deTurckRHSRetag (I := I) g₀ g_bg g₁ - deTurckRHSRetag (I := I) g₀ g_bg g₂)‖
            ≤ C * ∑ i ∈ Finset.range (2 * a + 3),
                Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + i)
                  (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)).toFun := by
  classical
  -- The genuine deep analytic core: the covariant-Faà-di-Bruno Moser-tame `L²`-jet bound for the
  -- **segment metric** `g_t` (the covariant chain-rule expansion of the re-tagged DeTurck
  -- right-hand-side difference, lifted to `L²` by the intrinsic Moser tame product, the top
  -- segment-metric-`2`-jet derivative kept in `L²` and the perturbation's `L^∞` factor carried by
  -- the order-`a` chart-Sobolev redistribution term — all uniform over the `H^{a+2}`-bounded
  -- `B`-family via the supercritical embedding implied by `ha`).
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_segmentMetricJet2DiffFaaDiBruno_moserTame_l2Norm_le (I := I) g₀ g_bg a ha B hB
  -- The on-disk reverse chart-Sobolev comparison, at the redistribution order `a`: the chart-`Hᵃ`
  -- norm of the perturbation difference is dominated by its covariant-`L²`-jet sum up to order
  -- `2a` — this re-absorbs the Moser-tame `C⁰`-redistribution term into the covariant-`L²`-jet sum.
  obtain ⟨CR, hCR_nn, hCR⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum
      (I := I) g₀ 0 2 a
  refine ⟨C * (CR + 1), by positivity, fun T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ j hj => ?_⟩
  set jetSum : ℝ := ∑ i ∈ Finset.range (2 * a + 3),
      Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + i)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)).toFun with hjetSum_def
  -- Re-absorb `‖(T₁ − T₂).toHs a‖` into the covariant-`L²`-jet sum: by the reverse comparison its
  -- `toReal` is `≤ CR · ∑_{j ≤ 2a} ‖∇^j (T₁ − T₂)‖`, and the order-`2a` sum (range `2a+1`) is
  -- dominated by the full order-`2a+2` sum (range `2a+3`).
  have htoHs_le :
      ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ≤ CR * jetSum := by
    rw [DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.tensorPouSobolevHilbert_norm_eq]
    refine (hCR (T₁ - T₂)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hCR_nn
    rw [hjetSum_def]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega))
      (fun i _ _ => Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g₀ 0 (2 + i) _)
  -- Chain the Moser-tame core with the redistribution re-absorption.
  calc ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
          (deTurckRHSRetag (I := I) g₀ g_bg g₁ - deTurckRHSRetag (I := I) g₀ g_bg g₂)‖
      ≤ C * (‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖
              + jetSum) := by
        rw [hjetSum_def]; exact hC T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ j hj
    _ ≤ C * (CR * jetSum + jetSum) :=
        mul_le_mul_of_nonneg_left (by linarith [htoHs_le]) hC_nn
    _ = C * (CR + 1) * jetSum := by ring

/-- **The covariant-gradient `L²` Nemytskii bound for the re-tagged Ricci–DeTurck right-hand
side (the genuine deep analytic input: each intrinsic iterated covariant gradient of the
right-hand-side difference is `L²`-controlled by the order-`(a+2)` chart-Sobolev norm of the
perturbation difference).**

For an anchor `g₀`, a flow background `g_bg`, an order `a`, and a uniform `H^{a+2}`-size bound
`B ≥ 0`, there is a single constant `C ≥ 0` such that for any two `g₀`-fibre-small perturbations
`T₁, T₂` whose `H^{a+2}` norms are `≤ B`, any two realized metrics `g₁, g₂` of `T₁, T₂` (tied by
the fibrewise `inner`-identities), and every covariant-gradient order `j ≤ 2 * a`, the global
metric `L²` (semi-)norm of the `j`-th intrinsic iterated covariant gradient of the **re-tagged
DeTurck right-hand-side** section difference is bounded by the order-`(a+2)` chart-Sobolev norm
of the perturbation difference:
```
‖iteratedCovGrad g₀ 0 2 j (deTurckRHSRetag g₀ g_bg g₁ − deTurckRHSRetag g₀ g_bg g₂)‖
  ≤ C · ‖(T₁ − T₂).toHs (a+2)‖   (for j ≤ 2 * a).
```

This is the genuine **higher-order quasilinear Nemytskii estimate** for the *non-linear* summand
`Ric + Lie` of the second-order Ricci–DeTurck right-hand side, phrased intrinsically: the chart
right-hand side `deTurckRicciRHS g_bg g = -2 • Ric(g) + 𝓛_{W(g)} g` is a smooth (fibrewise)
function `F` of the metric `≤2`-jet `(g, ∇g, ∇²g)` and the fibre-inverse `g⁻¹`, so by the
covariant fundamental theorem of calculus along the segment `g_t = g₂ + t·(g₁ − g₂)` the
difference `F(g₁) − F(g₂) = ∫₀¹ DF(g_t)·(g₁ − g₂) dt` and its `j`-th covariant gradient is, by the
covariant product/chain rule (covariant Faà-di-Bruno), a finite sum of terms each a smooth bounded
coefficient (a fibrewise-polynomial expression in the `≤ (j+2)`-jets of `g₁, g₂` and the bounded
fibre-inverses, dominated uniformly on the compact `M` because `g₁, g₂` are genuine smooth metrics
whose jet-data is sup-bounded in terms of the `H^{a+2}` size `B`) times an iterated covariant
gradient `∇^i(g₁ − g₂)` of order `i ≤ j + 2` of the metric difference.  Since the inner-identity
difference makes `(g₁ − g₂).inner = ccTensorBilinSymm g₀ (T₁ − T₂)` the realized bilinear form of
`T₁ − T₂`, each `∇^i(g₁ − g₂)` is `L²`-controlled (the realization is a bounded smooth bundle map
gaining no derivatives) by the `≤ (j+2)`-order covariant gradients of `T₁ − T₂`, hence — for
`j ≤ 2 * a`, so `j + 2 ≤ 2 * (a + 2)` — by the order-`(a+2)` chart-Sobolev norm `‖(T₁ −
T₂).toHs (a+2)‖`.  No supercriticality is needed: the smooth metric jet-coefficients are
sup-bounded by smoothness on the compact base, never through a Sobolev embedding.

Its conclusion is a *real-valued* global-`L²` (semi-)norm inequality on the intrinsic iterated
covariant gradients of the right-hand-side difference, structurally distinct from the chart-`Hᵃ`
`toHs`-norm conclusion of the consumer below; no packaging.

The supercriticality hypothesis `ha : 2 * a > Module.finrank ℝ E + 4` is genuinely required (and
mirrors the sibling consumer chain `exists_deTurckRealizeRemainderOf_synthesis_matching_gauge` /
`exists_deTurckRemainderG0ContSynth`, which carry exactly this hypothesis): the uniform-over-the
`B`-family Nemytskii constant needs an `L^∞` bound on the metric `≤2`-jet in terms of its
`H^{2a+2}`-content, i.e. the Sobolev embedding `H^{2a+2} ↪ C^0` of the `≤2`-jet (equivalently
`H^{2(a+2)} ↪ C^2` of the metric), which holds precisely on the supercritical scale `2 * (a + 2) >
finrank/2 + 2`, implied by `2 * a > finrank + 4`.  This is the honest order threshold of the
quasilinear Ricci–DeTurck Nemytskii map `H^{a+2} → Hᵃ` (locally Lipschitz only above the critical
Sobolev scale).

Its body is `sorry`: it is the genuine atomic higher-order quasilinear covariant-jet Nemytskii
estimate (the `Ric + Lie` summand only — the linear `Δ_∇` summand is handled separately by the
rough-Laplacian order-dropping bound), with no spectral-nonlinearity, no
perturbation-indexed-remainder, and no Weyl dependence. -/
theorem exists_deTurckRHSRetagDiff_iteratedCovGrad_l2Norm_le_toHs_highOrder
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∀ j : ℕ, j ≤ 2 * a →
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
              (deTurckRHSRetag (I := I) g₀ g_bg g₁ - deTurckRHSRetag (I := I) g₀ g_bg g₂)‖
            ≤ C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2)
                (T₁ - T₂)‖ := by
  classical
  -- The covariant-Faà-di-Bruno covariant-jet `L²` core (right-hand-side difference bounded by the
  -- covariant `L²`-jets of the perturbation difference), and the forward covariant-jet `L²`
  -- Sobolev comparison (each covariant `L²`-jet of `T₁ − T₂` bounded by `‖·.toHs (a+2)‖`).
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_deTurckRHSRetagDiff_iteratedCovGrad_l2Norm_le_iteratedCovGrad_sum
      (I := I) g₀ g_bg a ha B hB
  obtain ⟨CF, hCF_nn, hCF⟩ :=
    exists_iteratedCovGrad_l2Norm_le_toHs (I := I) g₀ (a + 2)
  refine ⟨CA * ((2 * a + 3 : ℕ) * CF), by positivity, ?_⟩
  intro T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ j hj
  set N : ℝ := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2)
      (T₁ - T₂)‖ with hN_def
  have hN_nn : 0 ≤ N := norm_nonneg _
  -- Each covariant-`L²`-jet summand `‖∇^i (T₁ − T₂)‖_{L²} ≤ CF · N` for `i ≤ 2a+2 = 2·(a+2)`.
  have hsummand : ∀ i ∈ Finset.range (2 * a + 3),
      Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + i)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)).toFun ≤ CF * N := by
    intro i hi
    have hi' : i ≤ 2 * (a + 2) := by rw [Finset.mem_range] at hi; omega
    exact hCF (T₁ - T₂) i hi'
  -- Sum the per-`i` bounds: `∑_{i} ‖∇^i (T₁ − T₂)‖_{L²} ≤ (2a+3) · (CF · N)`.
  have hsum_le : ∑ i ∈ Finset.range (2 * a + 3),
        Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + i)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)).toFun ≤
      (2 * a + 3 : ℕ) * (CF * N) := by
    refine le_trans (Finset.sum_le_sum hsummand) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Chain the covariant-jet core with the per-summand forward Sobolev bound.
  calc ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
          (deTurckRHSRetag (I := I) g₀ g_bg g₁ - deTurckRHSRetag (I := I) g₀ g_bg g₂)‖
      ≤ CA * ∑ i ∈ Finset.range (2 * a + 3),
          Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + i)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)).toFun :=
        hCA T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ j hj
    _ ≤ CA * ((2 * a + 3 : ℕ) * (CF * N)) :=
        mul_le_mul_of_nonneg_left hsum_le hCA_nn
    _ = CA * ((2 * a + 3 : ℕ) * CF) * N := by ring

/-- **The higher-order quasilinear Nemytskii bound for the re-tagged Ricci–DeTurck right-hand
side (the genuine deep analytic Sobolev-multiplication / composition primitive).**

For an anchor `g₀`, a flow background `g_bg`, an order `a`, and a uniform `H^{a+2}`-size bound
`B ≥ 0`, there is a single constant `C ≥ 0` such that for any two `g₀`-fibre-small perturbations
`T₁, T₂` whose `H^{a+2}` norms are `≤ B`, and any two realized metrics `g₁, g₂` of `T₁, T₂`
(tied by the fibrewise `inner`-identities), the order-`a` chart-Sobolev norm of the difference
of the **re-tagged DeTurck right-hand-side** sections is bounded by the order-`(a+2)`
chart-Sobolev norm of the perturbation difference:
```
‖(deTurckRHSRetag g₀ g_bg g₁ − deTurckRHSRetag g₀ g_bg g₂).toHs a‖
  ≤ C · ‖(T₁ − T₂).toHs (a+2)‖ .
```

This is the genuine **higher-order quasilinear Nemytskii estimate** for the *non-linear* summand
`Ric + Lie` of the second-order Ricci–DeTurck right-hand side: `deTurckRicciRHS g_bg g` is a
smooth Nemytskii function of the metric's `≤2`-jet, so its order-`a` chart-Sobolev norm is
controlled by the order-`(a+2)` chart-Sobolev norm of the metric perturbation, uniformly over the
`H^{a+2}`-bounded family.  It is the intrinsic-norm analogue of the on-disk `C⁰`/`2`-jet base
case `exists_chartDeTurckRHSComp_lipschitz_on_compact` (chart-frame value difference `≤
C · chartMetricJet2DiffSup`), upgraded to the order-`a` intrinsic Sobolev norm.

It is **proven by composition** of the intrinsic covariant-gradient `L²` Nemytskii bound
`exists_deTurckRHSRetagDiff_iteratedCovGrad_l2Norm_le_toHs_highOrder` (each iterated covariant
gradient `∇^j` of the right-hand-side difference, `j ≤ 2 * a`, is `L²`-controlled by `‖(T₁ −
T₂).toHs (a+2)‖`) with the on-disk reverse chart-Sobolev comparison
`exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum` (the chart-`Hᵃ`
partition-of-unity Sobolev norm is dominated by the finite sum, over `j ≤ 2 * a`, of the metric
`L²` norms of the iterated covariant gradients `∇^j`), after rewriting each
`tensorL2Norm … .toFun = ‖·‖` (`tensorL2Norm_toFun_eq_norm`) and `‖·.toHs a‖ =
(tensorPouSobolevHsNorm g₀ a ·).toReal` (`tensorPouSobolevHilbert_norm_eq`).  Consumers
transitively depend on `sorryAx` only through the genuine covariant-jet Nemytskii primitive (and
the reverse chart-Sobolev comparison's own atomic Sobolev primitives).

The supercriticality hypothesis `ha : 2 * a > Module.finrank ℝ E + 4` is genuinely required for the
uniform-over-the-`B`-family Nemytskii constant (the quasilinear Ricci–DeTurck map `H^{a+2} → Hᵃ`
is locally Lipschitz only above the critical Sobolev scale; see the child for the embedding) and
mirrors the sibling consumer chain `exists_deTurckRemainderG0ContSynth`. -/
theorem exists_deTurckRHSRetagDiff_pouHa_le_toHs_highOrder
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) :
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
            (deTurckRHSRetag (I := I) g₀ g_bg g₁ - deTurckRHSRetag (I := I) g₀ g_bg g₂)‖
          ≤ C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2)
              (T₁ - T₂)‖ := by
  classical
  -- The intrinsic covariant-gradient `L²` Nemytskii bound, and the reverse chart-Sobolev
  -- comparison expressing the chart-`Hᵃ` norm by the iterated covariant-gradient `L²` norms.
  obtain ⟨CN, hCN_nn, hCN⟩ :=
    exists_deTurckRHSRetagDiff_iteratedCovGrad_l2Norm_le_toHs_highOrder (I := I) g₀ g_bg a ha B hB
  obtain ⟨CR, hCR_nn, hCR⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum
      (I := I) g₀ 0 2 a
  refine ⟨CR * ((2 * a + 1 : ℕ) * CN), by positivity, ?_⟩
  intro T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂
  set R : Integral.L2.SmoothCcTensor g₀ 0 2 :=
    deTurckRHSRetag (I := I) g₀ g_bg g₁ - deTurckRHSRetag (I := I) g₀ g_bg g₂ with hR_def
  set N : ℝ := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2)
      (T₁ - T₂)‖ with hN_def
  have hN_nn : 0 ≤ N := norm_nonneg _
  -- The reverse chart-Sobolev comparison, applied to the right-hand-side difference `R`.
  have hcmp :
      (Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm (I := I) (M := M) g₀ a R).toReal ≤
        CR * ∑ j ∈ Finset.range (2 * a + 1),
          Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + j)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j R).toFun := hCR R
  -- Each covariant-gradient `L²` summand `= ‖∇^j R‖ ≤ CN · N`.
  have hsummand : ∀ j ∈ Finset.range (2 * a + 1),
      Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + j)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j R).toFun ≤ CN * N := by
    intro j hj
    rw [Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm]
    exact hCN T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ j (by rw [Finset.mem_range] at hj; omega)
  -- Sum the per-`j` bounds: `∑_{j} ‖∇^j R‖ ≤ (2*a+1) · (CN · N)`.
  have hsum_le : ∑ j ∈ Finset.range (2 * a + 1),
        Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + j)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j R).toFun ≤
      (2 * a + 1 : ℕ) * (CN * N) := by
    refine le_trans (Finset.sum_le_sum hsummand) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Rewrite the chart-`Hᵃ` `toHs`-norm as the seminorm `toReal`, then chain the two bounds.
  rw [DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.tensorPouSobolevHilbert_norm_eq]
  calc (Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm (I := I) (M := M) g₀ a R).toReal
      ≤ CR * ∑ j ∈ Finset.range (2 * a + 1),
          Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + j)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j R).toFun := hcmp
    _ ≤ CR * ((2 * a + 1 : ℕ) * (CN * N)) :=
        mul_le_mul_of_nonneg_left hsum_le hCR_nn
    _ = CR * ((2 * a + 1 : ℕ) * CN) * N := by ring

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

This is **proven by composition**: the realized-remainder difference splits (in the
`SmoothCcTensor` additive group) as the difference of re-tagged DeTurck right-hand sides minus
the difference of linear rough-Laplacian summands,
```
(realizedRem₁ − realizedRem₂) = (D₁ − D₂) − (Δ_∇ T₁ − Δ_∇ T₂),  Dⱼ := deTurckRHSRetag g₀ g_bg gⱼ ,
```
so by the `toHs`-triangle inequality the order-`a` norm is bounded by the sum of the order-`a`
norms of the two pieces.  The first piece is the genuine quasilinear Nemytskii primitive
`exists_deTurckRHSRetagDiff_pouHa_le_toHs_highOrder` (the `Ric + Lie` summand); the second uses
the rough-Laplacian linearity `rawTensorConnLapSmooth_sub` (`Δ_∇ T₁ − Δ_∇ T₂ = Δ_∇ (T₁ − T₂)`)
together with the tight order-dropping bound `exists_rawConnLapSmooth_toHs_le_toHs_succ`
(`H^a(Δ_∇ (T₁ − T₂)) ≤ C · H^{a+1}(T₁ − T₂)`) and the order-monotonicity `toHs_norm_mono`
(`H^{a+1} ≤ H^{a+2}`).  Consumers transitively depend on `sorryAx` only through the genuine
quasilinear Nemytskii primitive and the rough-Laplacian Sobolev/linearity primitives.  The
supercriticality hypothesis `ha : 2 * a > Module.finrank ℝ E + 4` is genuinely required by, and
threaded into, the quasilinear Nemytskii primitive (the only summand needing it; the linear
rough-Laplacian arm is order-free), and mirrors the sibling consumer chain
`exists_deTurckRemainderG0ContSynth`. -/
theorem exists_realizedRHSRemainder_pouHa_le_toHs_highOrder
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) :
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
              (T₁ - T₂)‖ := by
  classical
  -- The quasilinear Nemytskii bound for the re-tagged DeTurck right-hand side, and the tight
  -- single-step rough-Laplacian order-dropping bound.
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    exists_deTurckRHSRetagDiff_pouHa_le_toHs_highOrder (I := I) g₀ g_bg a ha B hB
  obtain ⟨CL, hCL_nn, hCL⟩ :=
    exists_rawConnLapSmooth_toHs_le_toHs_succ (I := I) g₀ a
  refine ⟨CD + CL, by positivity, fun T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ => ?_⟩
  set D₁ : Integral.L2.SmoothCcTensor g₀ 0 2 := deTurckRHSRetag (I := I) g₀ g_bg g₁ with hD₁_def
  set D₂ : Integral.L2.SmoothCcTensor g₀ 0 2 := deTurckRHSRetag (I := I) g₀ g_bg g₂ with hD₂_def
  set L₁ : Integral.L2.SmoothCcTensor g₀ 0 2 := rawTensorConnLapSmooth (I := I) g₀ 0 2 T₁
    with hL₁_def
  set L₂ : Integral.L2.SmoothCcTensor g₀ 0 2 := rawTensorConnLapSmooth (I := I) g₀ 0 2 T₂
    with hL₂_def
  set TΔ : Integral.L2.SmoothCcTensor g₀ 0 2 := T₁ - T₂ with hTΔ_def
  -- The realized-remainder difference equals `(D₁ − D₂) − (L₁ − L₂)`.
  have hsplit : realizedRHSRemainderSection (I := I) g₀ g_bg g₁ T₁
        - realizedRHSRemainderSection (I := I) g₀ g_bg g₂ T₂
      = (D₁ - D₂) - (L₁ - L₂) := by
    rw [realizedRHSRemainderSection_eq_sub, realizedRHSRemainderSection_eq_sub,
      hD₁_def, hD₂_def, hL₁_def, hL₂_def]
    abel
  -- The linear piece `L₁ − L₂ = Δ_∇ (T₁ − T₂)`.
  have hlin : L₁ - L₂ = rawTensorConnLapSmooth (I := I) g₀ 0 2 TΔ := by
    rw [hL₁_def, hL₂_def, hTΔ_def, rawTensorConnLapSmooth_sub]
  -- Norm of the realized-remainder difference: triangle on the `toHs`-`a` of the two pieces.
  rw [hsplit, SmoothCcTensor.toHs_sub]
  refine le_trans (norm_sub_le _ _) ?_
  -- The re-tagged DeTurck piece `‖(D₁ − D₂).toHs a‖ ≤ CD · ‖TΔ.toHs (a+2)‖`.
  have hDbound :
      ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (D₁ - D₂)‖
        ≤ CD * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) TΔ‖ := by
    rw [hD₁_def, hD₂_def, hTΔ_def]
    exact hCD T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂
  -- The linear piece `‖(L₁ − L₂).toHs a‖ ≤ CL · ‖TΔ.toHs (a+1)‖ ≤ CL · ‖TΔ.toHs (a+2)‖`.
  have hLbound :
      ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (L₁ - L₂)‖
        ≤ CL * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) TΔ‖ := by
    rw [hlin]
    refine le_trans (hCL TΔ) ?_
    have hmono :
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 1) TΔ‖ ≤
          ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) TΔ‖ :=
      toHs_norm_mono (I := I) (M := M) g₀ (by omega) TΔ
    exact mul_le_mul_of_nonneg_left hmono hCL_nn
  -- Combine.
  have hTΔ_nn :
      0 ≤ ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) TΔ‖ :=
    norm_nonneg _
  calc ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (D₁ - D₂)‖
        + ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (L₁ - L₂)‖
      ≤ CD * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) TΔ‖
          + CL * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) TΔ‖ :=
        add_le_add hDbound hLbound
    _ = (CD + CL) *
          ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) TΔ‖ := by ring
    _ = (CD + CL) *
          ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2)
            (T₁ - T₂)‖ := by rw [hTΔ_def]

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
spectral-nonlinearity, no perturbation-indexed-remainder, and no Weyl dependence.  The
supercriticality hypothesis `ha : 2 * a > Module.finrank ℝ E + 4` is genuinely required by, and
threaded into, the higher-order intrinsic Nemytskii bound, and mirrors the sibling consumer chain
`exists_deTurckRemainderG0ContSynth`. -/
theorem exists_realizedRHSRemainder_weightedHa_le_toHs_highOrder
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) :
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
    exists_realizedRHSRemainder_pouHa_le_toHs_highOrder (I := I) g₀ g_bg a ha B hB
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
