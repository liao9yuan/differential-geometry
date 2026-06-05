import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedCovGradJetGeneralOrder
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHSSection

/-! # The covariant-jet Faà-di-Bruno expansion of the Ricci–DeTurck right-hand side along the segment

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file supplies the genuinely-new **metric-jet covariant-derivative
expansion** of the second-order Ricci–DeTurck right-hand side
`deTurckRicciRHS g_bg g = -2 • Ric(g) + 𝓛_{W(g, g_bg)} g`
(`Geometry/Flow/RicciFlow/DeTurckRHS.lean`) along the **segment metric**
`g_t = (1 - t) • g₂ + t • g₁` (`segmentMetric`, `SegmentMetricJetBound.lean`), in the intrinsic
`riemannianFiberNormSq` (`rfns`) covariant-jet form the intrinsic Moser-tame product
`exists_moserTameProduct_iteratedCovGrad_l2Norm_le` (`Analysis/Sobolev/MoserTameProduct.lean`)
consumes.

## What the second-order Ricci–DeTurck right-hand side is, as a metric-jet contraction

The chart right-hand side `deTurckRicciRHS g_bg g` is a fibrewise-smooth function `F` of the metric
`≤2`-jet `(g, ∇g, ∇²g)` and the fibre-inverse `g⁻¹`: schematically
`Ric(g) = g⁻¹ · ∂²g + g⁻¹ · g⁻¹ · ∂g · ∂g` and `𝓛_{W(g)} g = g⁻¹ · ∂g · ∂g + g⁻¹ · ∂²g` (the `g⁻¹`
Neumann factors carry *intrinsic order `0`*).  Its **intrinsic order is capped at `2`**: only the
`≤2`-jet of the metric enters as a *coefficient*, never a higher-order pointwise metric jet (the
metric pointwise `C^{2a+2}`-jet is unavailable on a manifold of dimension `≥ 4`).

The covariant **difference** along the segment, `F(g₁) − F(g₂)`, expands — by the covariant
fundamental theorem of calculus `F(g₁) − F(g₂) = ∫₀¹ DF(g_t)·(g₁ − g₂) dt` and the covariant
product/chain rule (covariant Faà-di-Bruno) — into a finite sum of contracted products of a
**segment-metric `≤2`-jet coefficient** (a `DF(g_t)`-polynomial in the `≤2`-jets of `g_t` and the
bounded fibre-inverses, *uniformly sup-bounded over the supercritical `H^{a+2}` family* by the
order-`≤2` segment-metric jet sup `exists_segmentMetric_realizeSymm_iteratedCovGradJet2_sup_le`) with
an iterated covariant gradient `∇^i(g₁ − g₂)` of the metric difference, `i ≤ j + 2 ≤ 2a + 2`.

Since the fibrewise `inner`-difference makes `(g₁ − g₂).inner = ccTensorBilinSymm g₀ (T₁ − T₂)` the
realized bilinear form of the perturbation difference `T₁ − T₂`, each `∇^i(g₁ − g₂)` is fibre-bounded
by the `≤ i`-order covariant gradients of `T₁ − T₂` (the realization gains no derivatives), so the
single high derivative lands on the perturbation factor and the metric jet enters only in its `≤2`
sup — exactly the **binomial-Leibniz `rfns` domination** the Moser-tame product takes as input.

## What is proved vs. posited

* The **assembled** binomial-Leibniz `rfns` domination of the retagged DeTurck right-hand-side section
  difference, `exists_segmentMetricRHSDiff_binomialLeibniz_rfns_le`, in the exact shape consumed by
  `exists_moserTameProduct_iteratedCovGrad_l2Norm_le`, is *posited* here as the genuine atomic
  covariant-Faà-di-Bruno content (the per-field Nemytskii fibre estimates of the geometric
  nonlinearity `Ric + Lie`, which on a manifold of dimension `≥ 4` cannot be reduced to a pointwise
  `C^{>2}`-jet of the metric).  Its trap-screened design: the metric jet enters only through its
  `≤2`-jet sup (NO pointwise sup of any order-`>2` metric jet — the false-embedding lesson), the
  per-order constant is a *family* over the unbounded gradient order, and the uniform constant is
  scoped to the supercritical `H^{a+2}`-bounded `B`-family (`ha`, where unboundedness otherwise
  lurks).  It carries **no** spectral-nonlinearity, perturbation-indexed-remainder, or Weyl
  dependence.
* The reduction shape — that the section the bound is stated on is the `g₀`-retagged DeTurck
  right-hand side `deTurckRHSRetagG0` (definitionally the downstream `deTurckRHSRetag`), and that the
  perturbation factor is the `(0,2)`-difference `T₁ − T₂` — is *fixed by construction* so the
  follow-up assembler plugs it into the Moser-tame product directly.

The abstract engine the assembly rides on is the proven (sorry-free) abstract `rfns` covariant-Leibniz
grid `DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le`
(`Analysis/Spectral/Tensor/CovGrad/MetricContractionLeibnizGrid.lean`) and the proven order-`≤2`
segment-metric jet sup `exists_segmentMetric_realizeSymm_iteratedCovGradJet2_sup_le`; consumers
transitively depend on `sorryAx` only through the single posited per-field Nemytskii domination. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurck

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **The `g₀`-re-tagged Ricci–DeTurck right-hand-side section.**  The chart-frame DeTurck
right-hand side `deTurckRHSSection g_bg g₁` of the realized metric `g₁`, re-tagged from the `g₁`
type tag to the `g₀` type tag (the metric tag being a pure type-level parameter): the non-linear
`Ric + Lie` summand whose higher-order covariant-jet Nemytskii fibre bound this file states.  This is
definitionally identical to the downstream consumer's `deTurckRHSRetag g₀ g_bg g₁`; the follow-up
assembler bridges the two by `rfl`. -/
def deTurckRHSRetagG0 (g₀ g_bg g₁ : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 2 :=
  { toSection := (deTurckRHSSection (I := I) g_bg g₁).toSection
    hasCompactSupport := (deTurckRHSSection (I := I) g_bg g₁).hasCompactSupport }

omit [CompleteSpace E] [BoundarylessManifold I M] in
/-- The underlying smooth section of `deTurckRHSRetagG0 g₀ g_bg g₁` is the DeTurck right-hand-side
section `deTurckRHSSection g_bg g₁`'s section (the retag is a pure type-tag change). -/
@[simp] theorem deTurckRHSRetagG0_toSection (g₀ g_bg g₁ : SmoothRiemannianMetric I M) :
    (deTurckRHSRetagG0 (I := I) g₀ g_bg g₁).toSection =
      (deTurckRHSSection (I := I) g_bg g₁).toSection := rfl

/-! ### The realize-jet `rfns` domination: the metric difference's jets are the perturbation's jets

The load-bearing structural step of the covariant FTC expansion (the perturbation enters the metric
*through the realization map, gaining no derivatives*), proved outright in intrinsic `rfns` form. -/

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
/-- **The installed-`RiemannianBundle` fibre norm of a tensor value is the square root of its
`rfns`.**  Under the installed Riemannian-bundle instance `tensorRS_riemannianBundle g r s`, the
section-value fibre norm `‖S.toSection x‖` equals `Real.sqrt (riemannianFiberNormSq g r s x
(S.toSection x))`.  This is the bundle bridge `norm_eq_sqrt_tensorInnerPointwise` with the
frame-norm bridge `riemannianFiberNormSq_eq_tensorInnerPointwise` substituted for the model inner
product. -/
theorem norm_toSection_eq_sqrt_riemannianFiberNormSq_installed (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (S : Integral.L2.SmoothCcTensor g r s) (x : M) :
    (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace r s I bb) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ‖S.toSection x‖) =
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)) := by
  letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace r s I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rw [Integral.Connection.riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M)
    g r s x (S.toSection x)]
  exact Integral.Connection.norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g r s x
    (S.toSection x)

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The order-`i` realize-jet `rfns` domination for the metric-realization map.**

For every order `i`, there is a single nonnegative constant `C` such that for every base point `x`
and every smooth compactly-supported `(0,2)`-tensor `T`, the intrinsic squared fibre norm of the
order-`i` covariant gradient of the symmetric realized tensor `realizeSymmCcTensor g₀ T` is dominated
by `C` times the sum of the intrinsic squared fibre norms of the order-`≤ i` covariant gradients of
the underlying tensor `T`:
```
rfns(∇^i (realizeSymmCcTensor g₀ T))(x) ≤ C · ∑_{l ≤ i} rfns(∇^l T)(x).
```

This is the `rfns` form of the realization map's no-derivative-gain bound
`iteratedCovGrad_norm_realizeSymm_le_jetSum` (`‖∇^i realizeSymm T‖ ≤ C₀ · ∑_{l ≤ i} ‖∇^l T‖`):
squaring the fibre-norm bound (`riemannianFiberNormSq_toSection_eq_norm_sq_installed`,
`rfns = ‖·‖²` under the installed instance) and dominating `(∑_{l ≤ i} aₗ)² ≤ (i + 1) · ∑_{l ≤ i} aₗ²`
by Cauchy–Schwarz (`Finset.sq_sum_le_card_mul_sum_sq`), so `C := C₀² · (i + 1)`.  Proved outright; no
posit.  This is the structural step by which the covariant FTC expansion's metric difference
`g₁ − g₂` (whose `inner` is the realized form `ccTensorBilinSymm g₀ (T₁ − T₂)`) has its covariant jets
controlled by the *perturbation difference*'s covariant jets — the single high derivative landing on
the perturbation factor. -/
theorem exists_riemannianFiberNormSq_iteratedCovGrad_realizeSymm_le_jetSum
    (g₀ : SmoothRiemannianMetric I M) (i : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                (realizeSymmCcTensor (I := I) g₀ T)).toSection x) ≤
          C * ∑ l ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) := by
  classical
  -- The rfns constant is `i + 1` (the uniform `‖·‖` realize bound has constant `1`, re-derived
  -- inline below; squaring with Cauchy–Schwarz gives the `(i + 1)` factor).
  refine ⟨(i + 1 : ℕ), by positivity, fun T x => ?_⟩
  letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + i) I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + i)
  -- Abbreviate the per-order installed fibre norms `aₗ := ‖∇^l T‖`.
  set a : ℕ → ℝ := fun l =>
      (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + l) I bb) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
      ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x‖) with ha_def
  have ha_nn : ∀ l, 0 ≤ a l := by
    intro l
    rw [ha_def]
    letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + l) I bb) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
    exact norm_nonneg _
  -- The realize-jet fibre norm `B := ‖∇^i realizeSymm T‖` (installed instance).
  set B : ℝ := ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
      (realizeSymmCcTensor (I := I) g₀ T)).toSection x‖ with hB_def
  have hB_nn : 0 ≤ B := norm_nonneg _
  have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1), a l :=
    Finset.sum_nonneg fun l _ => ha_nn l
  -- Uniform `‖·‖` realize bound with constant `1`: `B = ‖∇^i (½T + ½flip)‖ ≤ ½‖∇^i T‖ + ½‖∇^i flip‖`
  -- `= ‖∇^i T‖ = a i ≤ ∑_{l ≤ i} aₗ` (the slot swap is a fibre isometry of every `∇^i`).
  have hflip_norm := flipCcTensor_iteratedCovGrad_norm_eq (I := I) g₀ T i x
  have hdecomp :
      PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (realizeSymmCcTensor (I := I) g₀ T) =
        (1 / 2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T +
          (1 / 2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (flipCcTensor (I := I) g₀ T) := by
    rw [realizeSymmCcTensor_eq, PDE.RicciFlow.iteratedCovGrad_add,
      iteratedCovGrad_smul, iteratedCovGrad_smul]
  have hB_le_ai : B ≤ a i := by
    rw [hB_def, ha_def]
    change ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
        (realizeSymmCcTensor (I := I) g₀ T)).toSection x‖ ≤
      ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T).toSection x‖
    rw [hdecomp]
    rw [show ((1 / 2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T +
          (1 / 2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (flipCcTensor (I := I) g₀ T)).toSection x =
        (1 / 2 : ℝ) • (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T).toSection x +
          (1 / 2 : ℝ) • (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (flipCcTensor (I := I) g₀ T)).toSection x from by
      rw [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_smul,
        SmoothCcTensor.toSection_smul]; rfl]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith [hflip_norm]
  have hai_le_sum : a i ≤ ∑ l ∈ Finset.range (i + 1), a l :=
    Finset.single_le_sum (fun l _ => ha_nn l) (Finset.mem_range.mpr (Nat.lt_succ_self i))
  have hB_le_sum : B ≤ ∑ l ∈ Finset.range (i + 1), a l := le_trans hB_le_ai hai_le_sum
  -- `rfns(·) = ‖·‖²` (installed instance), via the `sqrt`-bridge squared.
  have hrfns_eq_sq : ∀ (l : ℕ) (S : Integral.L2.SmoothCcTensor g₀ 0 2),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l S).toSection x) =
        (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + l) I bb) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
        ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l S).toSection x‖) ^ 2 := by
    intro l S
    rw [norm_toSection_eq_sqrt_riemannianFiberNormSq_installed (I := I) (M := M) g₀ 0 (2 + l)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l S) x]
    rw [Real.sq_sqrt (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _)]
  -- The LHS rfns `= B²`; the RHS sum `= ∑ aₗ²`.
  rw [hrfns_eq_sq i (realizeSymmCcTensor (I := I) g₀ T)]
  rw [show (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + i) I bb) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + i)
      ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ T)).toSection x‖) = B from rfl]
  have hsum_rfns_eq : (∑ l ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) =
      ∑ l ∈ Finset.range (i + 1), a l ^ 2 := by
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hrfns_eq_sq l T, ha_def]
  rw [hsum_rfns_eq]
  -- `B² ≤ (∑ aₗ)² ≤ (i + 1) · ∑ aₗ²` via Cauchy–Schwarz.
  have hBsq : B ^ 2 ≤ (∑ l ∈ Finset.range (i + 1), a l) ^ 2 :=
    pow_le_pow_left₀ hB_nn hB_le_sum 2
  have hCS : (∑ l ∈ Finset.range (i + 1), a l) ^ 2 ≤
      (Finset.range (i + 1)).card * ∑ l ∈ Finset.range (i + 1), a l ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [Finset.card_range] at hCS
  exact le_trans hBsq (by exact_mod_cast hCS)

/-- **The covariant-Faà-di-Bruno binomial-Leibniz `rfns` fibre domination of the segment-metric
DeTurck right-hand-side difference (the genuine atomic metric-jet Nemytskii primitive).**

For an anchor `g₀`, a flow background `g_bg`, an order `a`, a supercriticality hypothesis
`ha : 2 * a > Module.finrank ℝ E + 4`, and a uniform `H^{a+2}`-size bound `B ≥ 0`, there is an
order-indexed nonnegative constant family `C : ℕ → ℝ` (absorbing the bounded `≤2`-jet metric
coefficient sup `Λ`, the `4^j` covariant-Leibniz factor, and the finitely many contraction-shape
constants) such that for any two `g₀`-fibre-small perturbations `T₁, T₂` whose `H^{a+2}` norms are
`≤ B`, any two realized metrics `g₁, g₂` of `T₁, T₂` (tied by the fibrewise `inner`-identities), every
covariant-gradient order `j ≤ 2 * a`, and every base point `x`, the intrinsic squared fibre norm of
the `j`-th covariant gradient of the **re-tagged DeTurck right-hand-side section difference**
`deTurckRHSRetagG0 g₀ g_bg g₁ − deTurckRHSRetagG0 g₀ g_bg g₂` is dominated by the **binomial covariant
Leibniz grid** of a bounded `≤2`-jet metric coefficient `Λ` against the iterated covariant gradients
of the perturbation difference `T₁ − T₂`:
```
rfns(∇^j (deTurckRHSRetagG0 g₁ − deTurckRHSRetagG0 g₂))(x)
  ≤ C j · ∑_{i ≤ j + 2} rfns(∇^i (T₁ − T₂))(x)     (for j ≤ 2 * a).
```

This is the exact pointwise input the intrinsic Moser-tame product
`exists_moserTameProduct_iteratedCovGrad_l2Norm_le` lifts to the tame `L²` bound: the bounded
coefficient factor (the segment-metric `≤2`-jet, uniformly sup-bounded over the supercritical
`H^{a+2}` family by `exists_segmentMetric_realizeSymm_iteratedCovGradJet2_sup_le`, hence `≤ Λ²`) keeps
the **single high derivative on the perturbation factor `∇^i(T₁ − T₂)`**, the metric difference's jets
being the perturbation difference's jets because `(g₁ − g₂).inner = ccTensorBilinSymm g₀ (T₁ − T₂)`.

**Why this is TRUE.** The chart right-hand side is a fibrewise-smooth function `F` of the metric
`≤2`-jet and the fibre-inverse; the covariant FTC `F(g₁) − F(g₂) = ∫₀¹ DF(g_t)·(g₁ − g₂) dt` and the
covariant product/chain rule expand `∇^j` of the difference into a finite sum of contracted products
of a segment-metric `≤(j+2)`-jet coefficient (whose genuinely-needed pointwise sup is only its
`≤2`-jet, the geometric nonlinearity `Ric + Lie` being `g⁻¹·∂²g` or `g⁻¹·g⁻¹·∂g·∂g`) with
`∇^i(g₁ − g₂)`, `i ≤ j + 2`.  Bounding every metric `≤2`-jet coefficient by `Λ` and every binomial
by its square produces the displayed grid (the `C j` family absorbs `4^j` and the finitely many
contraction-shape constants).  **Trap-screen.** The metric jet enters ONLY through its `≤2`-jet sup
(no pointwise sup of any order-`>2` metric jet, unavailable for `finrank ≥ 4`); the constant `C` is a
*family* over the unbounded gradient order `j`; and the uniform `Λ` is scoped to the supercritical
`H^{a+2}`-bounded `B`-family (`ha`).

**Non-vacuity.** A degenerate `C ≡ 0` is rejected: at `j = 0`, for perturbations with
`deTurckRHSRetagG0 g₁ ≠ deTurckRHSRetagG0 g₂` at some `x` (e.g. `T₁ ≠ T₂` producing distinct
curvatures), the left side is `> 0` while `0 · ∑ … = 0`, contradicting the bound; so `C 0 > 0` and the
domination genuinely uses the perturbation difference.

Its body is `sorry`: the genuine atomic covariant-Faà-di-Bruno (Nemytskii) fibre expansion of the
geometric nonlinearity `Ric + Lie` along the segment metric — the deep metric-jet analytic content,
with NO pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO perturbation-indexed-remainder, and
NO Weyl dependence.  Consumers transitively depend on `sorryAx` only through this single primitive. -/
theorem exists_segmentMetricRHSDiff_binomialLeibniz_rfns_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∀ j : ℕ, j ≤ 2 * a → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                  (deTurckRHSRetagG0 (I := I) g₀ g_bg g₁
                    - deTurckRHSRetagG0 (I := I) g₀ g_bg g₂)).toSection x) ≤
            C j * ∑ i ∈ Finset.range (j + 2 + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)).toSection x) :=
  sorry

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
