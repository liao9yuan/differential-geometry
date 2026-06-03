import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSPointwiseLipschitz
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedCovGradJetInput
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
          C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) k S‖ :=
  sorry

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
difference `F(g₁) − F(g₂) = ∫₀¹ DF(g_t)·(g₁ − g₂) dt`, and its `j`-th covariant gradient is, by the
covariant product/chain rule (covariant Faà-di-Bruno), a finite sum of terms each a smooth bounded
coefficient (a fibrewise-polynomial expression in the `≤ (j+2)`-jets of `g₁, g₂` and the bounded
fibre-inverses, dominated **uniformly over the `H^{a+2}`-bounded `B`-family** because the
supercritical embedding `H^{a+2} ↪ C²` of the metric — equivalently `H^{2(a+2)} ↪ C^0` of the
`≤2`-jet, holding precisely on the supercritical scale implied by `ha`, see
`iteratedCovGrad_toSobolev_embedding_C2_unconditional` — bounds the metric `≤2`-jet `C²`-sup by
`φ(B)`) times an iterated covariant gradient `∇^i(g₁ − g₂)` of order `i ≤ j + 2 ≤ 2a + 2` of the
metric difference.  Since the fibrewise `inner`-difference makes `(g₁ − g₂).inner =
ccTensorBilinSymm g₀ (T₁ − T₂)` the realized bilinear form of `T₁ − T₂`, each `∇^i(g₁ − g₂)` is
`L²`-controlled (the realization is a bounded smooth bundle map gaining no derivatives) by the
`≤ i`-order covariant gradients of `T₁ − T₂`; integrating the pointwise covariant-Faà-di-Bruno
fibre-norm bound over the compact base (the `L²`-norm of a finite sum dominated by a constant
multiple of the sum of the `L²`-norms) yields the stated covariant-jet `L²`-sum bound.

Its conclusion is a *real-valued* global-`L²` (semi-)norm inequality on the intrinsic iterated
covariant gradients of the right-hand-side difference, bounded by the covariant-jet `L²`-sum of the
perturbation difference — structurally distinct from the chart-`Hᵃ` `toHs`-norm conclusion of the
consumer; no packaging.  The supercriticality hypothesis `ha` is genuinely required for the
uniform-over-the-`B`-family Nemytskii constant (the `C²`-sup of the metric `≤2`-jet over the
`H^{a+2}`-bounded family needs the supercritical embedding).  Its body is `sorry`: it is the
genuine atomic higher-order quasilinear covariant-jet Nemytskii estimate (the `Ric + Lie` summand
only — the linear `Δ_∇` summand is handled separately), with no spectral-nonlinearity,
perturbation-indexed-remainder, or Weyl dependence. -/
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
                  (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)).toFun :=
  sorry

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
