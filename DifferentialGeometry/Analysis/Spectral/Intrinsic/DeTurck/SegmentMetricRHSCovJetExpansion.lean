import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRHSSectionRetag
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedCovGradJetGeneralOrder
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizeSymmIteratedCovGradFiberNormBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricRicciDiffOperatorExpansion
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MetricDifferenceFdBTermTree
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricCurvatureDifferenceOpDecomposition

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

* The headline **per-order covariant Faà-di-Bruno Moser-tame `L²` domination** of the retagged DeTurck
  right-hand-side section difference, `exists_segmentMetricRHSDiff_faaDiBruno_moserTame_l2Norm_le`, is
  **proven by composition** here: the second-order Ricci–DeTurck right-hand side `F(g) = -2 • Ric(g) +
  𝓛_{W(g, g_bg)} g` is split additively into its two genuine `SmoothCcTensor` summands — the curvature
  summand `ricciNeg2CcSection` and the Lie-derivative summand `lieDerivCcSection` — via the proven
  section identity `deTurckRHSSection_eq_ricciNeg2_add_lieDeriv`; the `j`-th covariant gradient of the
  retagged difference splits additively (`iteratedCovGrad_add`) and the `L²`-seminorm triangle
  inequality reduces the headline bound to the sum of the two **per-field** primitives, with combined
  per-order constant.
* The per-field **`L²` dominations** `exists_ricciNeg2Diff_faaDiBruno_moserTame_l2Norm_le` and
  `exists_lieDerivDiff_faaDiBruno_moserTame_l2Norm_le`, and the per-field **pointwise two-product `rfns`
  dominations** `ricciNeg2Diff_covFdB_pointwise_twoProduct_rfns_le` and
  `lieDerivDiff_covFdB_pointwise_twoProduct_rfns_le`, are all **proven by composition**: the `L²`
  dominations from the pointwise two-products via the Hamilton/Moser pointwise-to-`L²` lift
  `tensorL2Norm_le_of_pointwise_twoProduct_rfns_bound` and the realize-jet `L²` control; and each
  pointwise two-product, in turn, from the **covariant Faà-di-Bruno difference/cross split** of the
  corresponding summand difference (the two genuine atomic leaves below).
* The two genuine atomic leaves are the **covariant Faà-di-Bruno difference/cross splits**
  of each summand difference: the curvature half `ricciNeg2Diff_covFdB_section_split` and the Lie half
  `lieDerivDiff_covFdB_section_split`.  Each provides a uniform difference-arm constant `Cd` and, per
  perturbation, the structural identity `∇^j(summand-diff) = Adiff + Cross` splitting the `j`-th
  covariant gradient of one geometric nonlinearity (`Ric`, resp. `𝓛_{deTurckVF} g`) into a
  **difference-arm piece** `Adiff` — the high derivative on the difference factor
  `w = realizeSymm (T₁ − T₂)`, `rfns(Adiff) ≤ Cd · ∑_{i ≤ j+2} rfns(∇^i w)` (the metric-built `≤2`-jet
  coefficient folded into `Cd` by the identity-level covariant Faà-di-Bruno collection over the
  segment) — and a **fixed-pair cross piece** `Cross` — the Faà-di-Bruno `i = 0` term's unbounded top coefficient jet `∇^{j+2}g_t`
  kept on the fixed pair `T₁, T₂` against the difference's `C⁰` mass,
  `rfns(Cross) ≤ (1/2)·(∑_{i ≤ j+2}(rfns(∇^i T₁) + rfns(∇^i T₂)))·‖(T₁ − T₂).toHs a‖²`.  Their
  trap-screened design: NO pointwise sup of any order-`>2` metric jet appears (the false-embedding
  lesson — the covariant-FdB `i = 0` term's pointwise-unbounded `∇^{j+2}g_t` rides in the cross piece on
  the fixed pair against the difference's `C⁰` factor, never claimed pointwise); the difference-arm
  constant is uniform over the supercritical `H^{a+2}`-bounded `B`-family (`ha`); and the cross
  coefficient `1/2` is the deep normalisation residual that, after the squared-fibre-norm subadditivity
  factor `2`, yields the coefficient-`1` cross arm the pointwise-to-`L²` lift consumes.  Each split is
  *coupled* (the identity ties the two arm bounds), rejecting both the `Adiff = 0` witness (cross bound
  false for `j ≥ 1`) and the `Cross = 0` witness (difference-arm bound false for `j ∈ (a, 2a]`); both
  pieces carry genuine content.  They carry **no** spectral-nonlinearity, perturbation-indexed-remainder,
  or Weyl dependence.
* The reduction shape — that the section the headline bound is stated on is the `g₀`-retagged DeTurck
  right-hand side `deTurckRHSRetagG0` (definitionally the downstream `deTurckRHSRetag`), and that the
  perturbation factor is the `(0,2)`-difference `T₁ − T₂` — is *fixed by construction* so the
  follow-up assembler (which uniformises the per-order constant and extends the jet-sum range) plugs
  it into the order-`a` chart-RHS tower directly.

The `L²` engine each per-field domination is the natural output of is the proven (sorry-free) intrinsic
Moser-tame product `exists_moserTameProduct_iteratedCovGrad_l2Norm_le`
(`Analysis/Sobolev/MoserTameProduct.lean`), fed by the proven order-`≤2` segment-metric jet sup
`exists_segmentMetric_realizeSymm_iteratedCovGradJet2_sup_le` (the bounded `Λ`-arm coefficient sup)
and the proven `C⁰` Sobolev embedding `tensorPouSobolevHilbert_embedding_Ck` (the `Λ₀`-arm `C⁰`
control on the difference factor).  The two covariant Faà-di-Bruno difference/cross split leaves
`ricciNeg2Diff_covFdB_section_split` and `lieDerivDiff_covFdB_section_split` are now themselves **proven
by composition** over the order-zero linear/cross section splits; consumers transitively depend on
`sorryAx` only through the three genuine Core-II deep posits the splits descend into — the curvature
difference-arm and Cross per-order jet bounds `ricciLinearSection_iteratedCovGrad_diffArm_rfns_le` /
`ricciCrossSection_iteratedCovGrad_cross_rfns_le`, and the Lie order-zero linear/cross split
`lieDerivDiff_order0_linearCross_split`.

An earlier `DiffBilinOp`-contraction *structural-split* layer beneath each leaf (factoring the
difference arm `Adiff` through an undifferentiated metric-contraction `Φ.op 0 2 w` of a differentiated
bilinear contraction operator family plus the binomial covariant-Leibniz engine grid) was **refuted**
and removed: at the consumer's differentiation order `p = 0` the `DiffBilinOp` jet envelope
`DiffBilinOp.rfns_op_le` collapses to the value-order sum `kappa · rfns(w)` (window
`range (0 + 1) = {0}`), so the `Φ.op 0 2 w` arm cannot carry the difference's principal `∇^{j+2}w`
content, and a supercritical localized bump violates the resulting cross bound at the bump centre, for
every `j`.  The two leaves are therefore re-architected directly onto the **satisfiable order-zero
linear/cross section split** of each summand difference, on which the single high derivative is
collected onto whichever factor carries it:

* the curvature half over the order-zero section split `ricciNeg2RetagG0_sub_eq_linear_add_cross`
  (`SegmentMetricCurvatureDifferenceOpDecomposition.lean`, which exhibits the *concrete* smooth
  linear-in-difference section `linearSection` and quadratic-in-difference Cross section `crossSection`),
  plus the two per-order jet-bound posits `ricciLinearSection_iteratedCovGrad_diffArm_rfns_le` (the
  difference arm carries `∇^{j+2}w`) and `ricciCrossSection_iteratedCovGrad_cross_rfns_le` (the fixed-pair
  Cross);
* the Lie half over the order-zero linear/cross split posit `lieDerivDiff_order0_linearCross_split`,
  which posits the genuine existence of the linear/cross decomposition of the Lie-summand difference
  together with the per-order difference-arm and fixed-pair Cross jet bounds (the value-level Lie split
  `lieDerivRetagG0_sub_eq_linear_add_cross` is, unlike the curvature half, genuinely absent on disk).

These posits are the genuine Core-II deep leaves: each carries the difference arm up to `∇^{j+2}w` (so a
zero difference-arm constant or a dropped difference arm falsifies it — non-vacuous), and none carries any
value-bounded `Φ.op 0 2 w` shape, NO pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, and NO Weyl
dependence. -/

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
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ### The per-order covariant jet bounds of the order-zero linear/cross section split

The genuine Core-II deep leaves on which the two per-field covariant-Faà-di-Bruno difference/cross
splits stand.  Each summand difference `F g₁ − F g₂` decomposes at order zero into a
**linear-in-difference** section and a **quadratic-in-difference Cross** section
(`ricciNeg2RetagG0_sub_eq_linear_add_cross` for the curvature half — over the concrete
`linearSection` / `crossSection` of `SegmentMetricCurvatureDifferenceOpDecomposition.lean`; the posited
order-zero split `lieDerivDiff_order0_linearCross_split` for the Lie half, the value-level split being
genuinely absent on disk).  The deep content is the per-order covariant-jet behaviour of the two parts:
the linear part's `j`-th covariant gradient carries the single high derivative on the **difference
factor** `w := realizeSymmCcTensor g₀ (T₁ − T₂)` up to order `j + 2` (the difference-arm grid bound,
with the metric-built `≤2`-jet coefficient folded into a family-uniform constant `Cd`), while the Cross
part's `j`-th covariant gradient is the Faà-di-Bruno `i = 0` term's unbounded top coefficient jet
`∇^{j+2}g_t` kept on the **fixed pair** `T₁, T₂` against the difference's order-`a` chart-Sobolev `C⁰`
mass `‖(T₁ − T₂).toHs a‖²`.  No jet of order `> 2` is ever taken pointwise; the difference arm carries
`∇^{j+2}w` (so a zero difference-arm constant, or a dropped difference arm, falsifies the bound — the
posits are non-vacuous), and neither bound is a value-bounded `Φ.op 0 2 w` shape. -/

/-- **(POSIT — the curvature difference-arm covariant-jet bound.)**  The intrinsic squared fibre norm
of the order-`j` covariant gradient of the concrete linear-in-difference curvature section
`linearSection g₀ g₁ g₂` is dominated by the order-`≤ j + 2` covariant jets of the difference factor
`w := realizeSymmCcTensor g₀ (T₁ − T₂)`, with a nonnegative constant `Cd` **uniform** over the
supercritical `H^{a+2}`-bounded perturbation family:
```
rfns(∇^j linearSection)(x) ≤ Cd · ∑_{i ≤ j+2} rfns(∇^i w)(x).
```

This is the difference arm of the curvature half: the single high derivative lands on the difference
factor `w` (`linearSection` is the linear-in-difference part, whose covariant jets are realize-controlled
by the perturbation difference's jets — the realization gains no derivatives,
`exists_riemannianFiberNormSq_iteratedCovGrad_realizeSymm_le_jetSum`), the metric-built `≤2`-jet
coefficient folded into `Cd` by the binomial covariant-Leibniz `rfns` grid over the window `j + 2`,
ball-uniform by the order-`≤2` segment-metric jet sup.  It is **not** `T₁`/`w` restated: it carries the
difference arm up to `∇^{j+2}w`, and a zero `Cd` falsifies it whenever the linear part is genuinely
present.  NO pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO Weyl dependence.  Its body is
`sorry`: the genuine deep covariant-Leibniz difference-arm content. -/
theorem ricciLinearSection_iteratedCovGrad_diffArm_rfns_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (j : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                  (linearSection (I := I) g₀ g₁ g₂)).toSection x) ≤
            Cd * ∑ i ∈ Finset.range (j + 2 + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                    (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x) :=
  sorry

/-- **(POSIT — the curvature fixed-pair Cross covariant-jet bound.)**  The intrinsic squared fibre norm
of the order-`j` covariant gradient of the concrete quadratic-in-difference curvature Cross section
`crossSection g₀ g₁ g₂` is dominated by the order-`≤ j + 2` **fixed-pair** jet sum against the
difference's order-`a` chart-Sobolev `C⁰` mass:
```
rfns(∇^j crossSection)(x)
  ≤ (1/2) · (∑_{i ≤ j+2} (rfns(∇^i T₁)(x) + rfns(∇^i T₂)(x))) · ‖(T₁ − T₂).toHs a‖².
```

This is the Cross arm of the curvature half: the covariant Faà-di-Bruno `i = 0` term's unbounded top
coefficient jet `∇^{j+2}g_t` (`L²` mass of order `j + 2 ∈ (a + 2, 2a + 2]`, which an `H^{a+2}` ball
cannot bound) is kept on the **fixed pair** `T₁, T₂` against the difference's `C⁰` mass, which the
supercritical Sobolev embedding (`ha`) bounds by `‖(T₁ − T₂).toHs a‖`.  The cross coefficient `1/2` is
the deep normalisation residual that, after the squared-fibre-norm subadditivity factor `2`, yields the
coefficient-`1` cross arm the pointwise-to-`L²` lift consumes.  Non-vacuous: the Cross section genuinely
vanishes to second order (`crossSection_self_toModel`), so it is the genuine quadratic remainder, and
both fixed-pair endpoints are carried.  NO pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO
Weyl dependence.  Its body is `sorry`: the genuine deep fixed-pair top-jet content. -/
theorem ricciCrossSection_iteratedCovGrad_cross_rfns_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (j : ℕ) :
    ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
      (g₁ g₂ : SmoothRiemannianMetric I M),
      (∀ (x : M) (v w : TangentSpace I x),
        g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
      (∀ (x : M) (v w : TangentSpace I x),
        g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
      ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
      ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
      ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                (crossSection (I := I) g₀ g₁ g₂)).toSection x) ≤
          (1 / 2 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
            * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 :=
  sorry

/-- **(POSIT — the order-zero linear/cross split of the Lie-summand difference, with per-order jet
bounds.)**  The genuine Core-II deep leaf of the Lie half.  The `g₀`-retagged Lie-summand difference
`lieDerivRetagG0 g₀ g_bg g₁ − lieDerivRetagG0 g₀ g_bg g₂` decomposes at order zero into a
**linear-in-difference** section `L` and a **quadratic-in-difference Cross** section `C` (genuine smooth
`SmoothCcTensor g₀ 0 2`s), whose per-order covariant jets satisfy the difference-arm grid bound
(carrying the difference factor `w := realizeSymmCcTensor g₀ (T₁ − T₂)` up to `∇^{j+2}w`, with a
family-uniform constant `Cd`) and the fixed-pair Cross bound:
```
lieDerivRetagG0 g₁ − lieDerivRetagG0 g₂ = L + C,
rfns(∇^j L)(x) ≤ Cd · ∑_{i ≤ j+2} rfns(∇^i w)(x),
rfns(∇^j C)(x) ≤ (1/2) · (∑_{i ≤ j+2} (rfns(∇^i T₁)(x) + rfns(∇^i T₂)(x))) · ‖(T₁ − T₂).toHs a‖².
```

The Lie field `𝓛_{W(g)} g` has the **same intrinsic order-`≤2` structure** as the curvature half (the
deTurck vector field `W = g⁻¹ · (Γ(g) − Γ(g_bg))` is a `g⁻¹·∂g`-type field, and one further metric
derivative produces the Lie deformation), so its segment difference admits the identical order-zero
linear/cross split — the `j = 0` chart witness being the structural difference identity
`chartLieDeTurckComp_sub_eq` (`ChartLieDerivStructuralDifference.lean`), which exhibits the
`Lie(g₁) − Lie(g₂)` chart component as a difference of products of metric `≤2`-jets, each carrying a
single Gram/vector-field-component difference factor.  Unlike the curvature half, the value-level split
`lieDerivRetagG0_sub_eq_linear_add_cross` is genuinely absent on disk, so this node posits its existence
together with the per-order jet bounds.  Non-vacuous and coupled: the difference arm carries `∇^{j+2}w`
(a zero `Cd` falsifies it), and the Cross genuinely vanishes when `g₁ = g₂` (the connection difference,
hence the Lie difference's quadratic part, is zero).  NO value-bounded `Φ.op 0 2 w` shape, NO
pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO Weyl dependence.  Its body is `sorry`: the
genuine deep covariant-gauge-jet content. -/
theorem lieDerivDiff_order0_linearCross_split
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∃ L C : Integral.L2.SmoothCcTensor g₀ 0 2,
          lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂ = L + C ∧
          (∀ (j : ℕ) (x : M),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j L).toSection x) ≤
              Cd * ∑ i ∈ Finset.range (j + 2 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x)) ∧
          (∀ (j : ℕ) (x : M),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j C).toSection x) ≤
              (1 / 2 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                  (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2) :=
  sorry

/-- **The covariant Faà-di-Bruno difference/cross split of the Ricci-curvature summand difference
(the deep covariant-curvature-jet structural posit).**

For an anchor `g₀`, an order `a`, a supercriticality hypothesis `ha`, a uniform `H^{a+2}`-size bound
`B ≥ 0`, and a covariant-gradient order `j`, then for any two `g₀`-fibre-small perturbations
`T₁, T₂` with `H^{a+2}` norms `≤ B` and any two realized metrics `g₁, g₂` of `T₁, T₂`, the `j`-th
covariant gradient of the `g₀`-retagged curvature-summand difference
`ricciNeg2RetagG0 g₀ g₁ − ricciNeg2RetagG0 g₀ g₂` splits as a **difference-arm piece** `Adiff` plus a
**fixed-pair cross piece** `Cross`:
```
∇^j (ricciNeg2RetagG0 g₁ − ricciNeg2RetagG0 g₂) = Adiff + Cross,
rfns(Adiff)(x)  ≤ Cd · ∑_{i ≤ j+2} rfns(∇^i w)(x),
rfns(Cross)(x) ≤ (1/2) · (∑_{i ≤ j+2} (rfns(∇^i T₁)(x) + rfns(∇^i T₂)(x))) · ‖(T₁ − T₂).toHs a‖²,
```
with `w := realizeSymmCcTensor g₀ (T₁ − T₂)` and a nonnegative difference-arm constant `Cd`.

This is the **covariant Faà-di-Bruno expansion** of the *sealed* curvature nonlinearity `-2 • Ric(g)`
(the trace of the Levi-Civita curvature operator, `RicciConnection.lean`), differenced along the
segment metric `g_t = g₂ + t·(g₁ − g₂)`, collected by where the single high derivative lands.  The
**difference-arm** piece carries it on the difference factor `w` (the metric-built `≤2`-jet coefficient
folded into `Cd` via the binomial covariant-Leibniz `rfns` grid of the contraction `DiffBilinOp`); the
**cross** piece carries the Faà-di-Bruno `i = 0` term's unbounded top coefficient jet `∇^{j+2}g_t`
(`L²` mass of order `j + 2 ∈ (a + 2, 2a + 2]`, which an `H^{a+2}` ball cannot bound — interpolation
only goes down) on the *fixed pair* `T₁, T₂` in `L²` against the difference's `C⁰` mass, which the
supercritical Sobolev embedding (`ha : 2 * a > dim M + 4`) bounds by `‖(T₁ − T₂).toHs a‖`.  No jet of
order `> 2` is ever taken pointwise; the top jet rides on the fixed pair, never ball-controlled in
isolation.  The cross coefficient is normalised to `1/2` — the genuine top-jet contraction-shape
constant times the supercritical-embedding constant times the segment-metric-jet constant, folded into
the deep coefficient analysis — so that after the squared-fibre-norm subadditivity factor `2` it yields
the coefficient-`1` cross arm the two-product consumer below records.

**Non-vacuity.**  The two arm bounds are *coupled* by the structural identity
`∇^j(summand-diff) = Adiff + Cross`, and the coupling rejects both degenerate witnesses.  With
`Adiff = 0`, `Cross = ∇^j(summand-diff)` would have to satisfy the *cross* bound
`rfns ≤ (1/2)(∑(rfns ∇^i T₁ + rfns ∇^i T₂)) · ‖(T₁ − T₂).toHs a‖²`, FALSE for `j ≥ 1` (the
difference-arm content `∑ rfns(∇^i w)` is genuinely present and is *not* dominated by the fixed-pair ·
`C⁰` cross arm — exactly the known-false *pointwise* form without a difference arm).  With `Cross = 0`,
`Adiff = ∇^j(summand-diff)` would have to satisfy the *difference-arm* bound `rfns ≤ Cd · ∑ rfns(∇^i w)`,
FALSE for `j ∈ (a, 2a]` (the top coefficient jet `∇^{j+2}g_t` content is genuinely
`(∑ fixed-pair) · C⁰`-order and is *not* difference-arm controlled).  Both pieces carry genuine
content; neither arm constant is vacuous.

It is **proven by composition** (TRANSIT) over the *concrete* order-zero linear/cross section split
`ricciNeg2RetagG0_sub_eq_linear_add_cross` (`SegmentMetricCurvatureDifferenceOpDecomposition.lean`),
which exhibits the sealed curvature-section difference `ricciNeg2RetagG0 g₀ g₁ − ricciNeg2RetagG0 g₀ g₂`
as the sum of the concrete smooth linear-in-difference section `linearSection g₀ g₁ g₂` and the concrete
smooth quadratic-in-difference Cross section `crossSection g₀ g₁ g₂` (the latter assembled through the M2
connection-difference operator field `connDiffField` as an operator-trace Cross bilinear form).  Pushing
`∇^j` through the split (`iteratedCovGrad_add`) sets `Adiff := ∇^j linearSection` and
`Cross := ∇^j crossSection`, and the two arm bounds are the two per-order jet-bound posits applied at
order `j`.

The genuine deep content has descended into two named posits: the difference-arm grid bound
`ricciLinearSection_iteratedCovGrad_diffArm_rfns_le` (the binomial covariant-Leibniz `rfns` grid of the
linear part `∇^j linearSection`, the single high derivative on the difference factor `w :=
realizeSymmCcTensor g₀ (T₁ − T₂)`, the metric-built `≤2`-jet coefficient folded into the family-uniform
`Cd` over the window `j + 2`) and the fixed-pair Cross bound
`ricciCrossSection_iteratedCovGrad_cross_rfns_le` (the Faà-di-Bruno `i = 0` term's unbounded top
coefficient jet `∇^{j+2}g_t` kept on the fixed pair against the difference's `C⁰` mass).  Consumers
transitively depend on `sorryAx` only through those two posits; this leaf carries NO value-bounded
`Φ.op 0 2 w` shape, NO pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, and NO Weyl dependence. -/
theorem ricciNeg2Diff_covFdB_section_split
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (j : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∃ Adiff Cross : Integral.L2.SmoothCcTensor g₀ 0 (2 + j),
          PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
              (ricciNeg2RetagG0 (I := I) g₀ g₁ - ricciNeg2RetagG0 (I := I) g₀ g₂)
            = Adiff + Cross ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x (Adiff.toSection x) ≤
              Cd * ∑ i ∈ Finset.range (j + 2 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x (Cross.toSection x) ≤
              (1 / 2 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                  (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2) :=
  by
  classical
  obtain ⟨Cd, hCd_nn, hAdiff⟩ :=
    ricciLinearSection_iteratedCovGrad_diffArm_rfns_le (I := I) g₀ a ha B hB j
  have hCross := ricciCrossSection_iteratedCovGrad_cross_rfns_le (I := I) g₀ a ha B hB j
  refine ⟨Cd, hCd_nn, fun T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ => ?_⟩
  refine ⟨PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (linearSection (I := I) g₀ g₁ g₂),
    PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (crossSection (I := I) g₀ g₁ g₂), ?_,
    hAdiff T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂,
    hCross T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂⟩
  rw [ricciNeg2RetagG0_sub_eq_linear_add_cross (I := I) g₀ g₁ g₂,
    PDE.RicciFlow.iteratedCovGrad_add]

/-- **The pointwise covariant-Faà-di-Bruno two-product domination of the Ricci-curvature summand
difference (the deep covariant-curvature-jet posit).**

For an anchor `g₀`, an order `a`, a supercriticality hypothesis `ha`, a uniform `H^{a+2}`-size bound
`B ≥ 0`, and a covariant-gradient order `j`, there is a nonnegative coefficient sup `Λ` such that for
any two `g₀`-fibre-small perturbations `T₁, T₂` with `H^{a+2}` norms `≤ B`, any two realized metrics
`g₁, g₂` of `T₁, T₂`, and every base point `x`, the squared intrinsic fibre norm
(`riemannianFiberNormSq`, `rfns`) of the `j`-th covariant gradient of the `g₀`-retagged
curvature-summand difference `ricciNeg2RetagG0 g₀ g₁ − ricciNeg2RetagG0 g₀ g₂` is dominated
**pointwise** by the Hamilton/Moser **two-product**
```
rfns(∇^j (ricciNeg2RetagG0 g₁ − ricciNeg2RetagG0 g₂))(x)
  ≤ Λ² · ∑_{i ≤ j+2} rfns(∇^i w)(x)
    + (∑_{i ≤ j+2} (rfns(∇^i T₁)(x) + rfns(∇^i T₂)(x))) · ‖(T₁ − T₂).toHs a‖²,
```
with `w := realizeSymmCcTensor g₀ (T₁ − T₂)`.

This is the **covariant Faà-di-Bruno expansion** of the *sealed* curvature nonlinearity `-2 • Ric(g)`
(the trace `tr(W ↦ riemannOp (LeviCivita g) x W v w)` of the Levi-Civita curvature operator,
`RicciConnection.lean`), differenced along the segment metric `g_t = g₂ + t·(g₁ − g₂)`: the covariant
FTC `Ric(g₁) − Ric(g₂) = ∫₀¹ DRic(g_t)·(g₁ − g₂) dt` and the covariant product/chain rule expand
`∇^j` of the difference into a finite sum of contracted products of a segment-metric-jet coefficient
with a covariant jet of the metric difference `g₁ − g₂` (whose `inner` is the realized form
`ccTensorBilinSymm g₀ (T₁ − T₂)`, so each `∇^i(g₁ − g₂)` is fibre-controlled by `∇^{≤ i} w`).  In the
**regular** product the coefficient's genuinely-needed pointwise sup is only its `≤2`-jet (`Λ`,
ball-uniform over the supercritical `H^{a+2}` family by the order-`≤2` segment-metric jet sup
`exists_segmentMetric_realizeSymm_iteratedCovGradJet2_sup_le`), the single high derivative landing on
the difference factor `w`; in the **top-jet** product the FdB `i = 0` term's unbounded top coefficient
jet `∇^{j+2}g_t` (`L²` mass of order `j + 2 ∈ (a + 2, 2a + 2]`, which an `H^{a+2}` ball cannot bound —
interpolation only goes down) is kept on the *fixed pair* endpoints `T₁, T₂` in `L²` against the
difference's `C⁰` mass, which the supercritical Sobolev embedding (`ha : 2 * a > dim M + 4`, i.e.
`a > dim M / 2`, the sharp `H^a ↪ C⁰` threshold) bounds by `‖(T₁ − T₂).toHs a‖`.  No jet of order `> 2`
is ever taken pointwise; the top jet rides in `L²` on the fixed pair, never ball-controlled in
isolation.

**Non-vacuity.**  Neither product discards its perturbation argument: the regular product carries the
difference factor `w` (its order-`0` term `rfns(w)(x) = 0` iff `T₁ = T₂` at `x`) and the top-jet
product carries **both** endpoints `T₁, T₂` (its order-`0` term `rfns(T₁)(x) + rfns(T₂)(x)`); a
witness with `Λ = 0` and the `‖(T₁ − T₂).toHs a‖`-coefficient effectively `0` fails whenever
`Ric(g₁) ≠ Ric(g₂)` on a positive-measure set (there `rfns(Ric-diff)(x) > 0`, the right side `0`).
`Λ` is the genuine ball-uniform `≤2`-jet coefficient sup, `‖(T₁ − T₂).toHs a‖` the genuine difference
`C⁰` mass.

It is **proven by composition** over the structural covariant Faà-di-Bruno split
`ricciNeg2Diff_covFdB_section_split`: that split provides a uniform difference-arm constant `Cd` and,
per perturbation, the structural identity `∇^j(Ric-diff) = Adiff + Cross` with the difference-arm grid
bound `rfns(Adiff) ≤ Cd · ∑ rfns(∇^i w)` and the cross-piece fixed-pair bound
`rfns(Cross) ≤ (1/2)·(∑ fixed-pair)·‖(T₁ − T₂).toHs a‖²`.  The two-product follows by the
squared-fibre-norm subadditivity `riemannianFiberNormSq_add_le` (factor `2`) over the identity, with
the coefficient `Λ = √(2 Cd)` (`Λ² = 2 Cd` absorbing the difference-arm constant and the factor `2`)
and the cross-piece `1/2` cancelling the same factor `2` into the coefficient-`1` cross arm.  Consumers
transitively depend on `sorryAx` only through the structural split posit, which carries the genuine deep
covariant-curvature-jet content — the covariant Faà-di-Bruno expansion of the sealed Ricci
nonlinearity, with NO pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, and NO Weyl dependence. -/
theorem ricciNeg2Diff_covFdB_pointwise_twoProduct_rfns_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (j : ℕ) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                  (ricciNeg2RetagG0 (I := I) g₀ g₁
                    - ricciNeg2RetagG0 (I := I) g₀ g₂)).toSection x) ≤
            Λ ^ 2 * ∑ i ∈ Finset.range (j + 2 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x)
              + (∑ i ∈ Finset.range (j + 2 + 1),
                  (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 := by
  classical
  -- The covariant Faà-di-Bruno difference/cross split of the curvature-summand difference: a uniform
  -- difference-arm constant `Cd` and, per perturbation, the structural identity `∇^j(Ric-diff) =
  -- Adiff + Cross` with the difference-arm grid bound and the cross-piece fixed-pair bound.
  obtain ⟨Cd, hCd_nn, hsplit⟩ :=
    ricciNeg2Diff_covFdB_section_split (I := I) g₀ a ha B hB j
  -- The two-product coefficient `Λ = √(2 Cd)`: the squared-fibre-norm subadditivity factor `2` folds
  -- the difference-arm constant `Cd` into `Λ² = 2 Cd`, and the cross-piece `1/2` cancels the same
  -- factor `2` into the coefficient-`1` cross arm.
  refine ⟨Real.sqrt (2 * Cd), Real.sqrt_nonneg _,
    fun T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ x => ?_⟩
  obtain ⟨Adiff, Cross, heq, hAdiff, hCross⟩ := hsplit T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂
  -- The squared-fibre-norm subadditivity over the structural identity `∇^j(Ric-diff) = Adiff + Cross`.
  have hsplit_norm :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
              (ricciNeg2RetagG0 (I := I) g₀ g₁
                - ricciNeg2RetagG0 (I := I) g₀ g₂)).toSection x) ≤
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x (Adiff.toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x (Cross.toSection x) := by
    rw [heq, Integral.L2.SmoothCcTensor.toSection_add]
    exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + j) x
      (Adiff.toSection x) (Cross.toSection x)
  -- `Λ² = (√(2 Cd))² = 2 Cd`: the subadditivity factor `2` folds the difference-arm constant `Cd`
  -- into the coefficient, and the cross-piece `1/2` cancels the same factor `2`.
  rw [show Real.sqrt (2 * Cd) ^ 2 = 2 * Cd from Real.sq_sqrt (by positivity)]
  have hA := hAdiff x
  have hC := hCross x
  nlinarith [hsplit_norm, hA, hC]

/-- **The per-field covariant-Faà-di-Bruno Moser-tame `L²` domination of the segment-metric
*Ricci-curvature* summand difference (the curvature half of the geometric nonlinearity, stated at the
`L²`-consumable level).**

The Ricci half of the second-order Ricci–DeTurck right-hand side, `-2 • Ric(g)`, is a fibrewise-smooth
function of the metric `≤2`-jet `(g, ∇g, ∇²g)` and the fibre-inverse `g⁻¹` (schematically
`Ric(g) = g⁻¹ · ∂²g + g⁻¹ · g⁻¹ · ∂g · ∂g`, the `g⁻¹` Neumann factors carrying intrinsic order `0`),
of **intrinsic order capped at `2`**.  For an anchor `g₀`, an order `a`, a supercriticality hypothesis
`ha`, and a uniform `H^{a+2}`-size bound `B ≥ 0`, there is an order-indexed nonnegative constant family
`C` such that for any two `g₀`-fibre-small perturbations `T₁, T₂` with `H^{a+2}` norms `≤ B`, any two
realized metrics `g₁, g₂` of `T₁, T₂`, and every order `j ≤ 2 * a`, the metric `L²` (semi)norm of the
`j`-th covariant gradient of the `g₀`-retagged curvature-summand difference
`ricciNeg2RetagG0 g₀ g₁ − ricciNeg2RetagG0 g₀ g₂` is dominated by the **Hamilton/Moser-tame sum**
(a difference-redistribution part plus a fixed-pair cross term)
```
‖∇^j (ricciNeg2RetagG0 g₁ − ricciNeg2RetagG0 g₂)‖_{L²}
  ≤ C j · ( ‖(T₁ − T₂).toHs a‖ + ∑_{i ≤ j + 2} ‖∇^i (T₁ − T₂)‖_{L²} )
    + C j · ( ∑_{i ≤ j + 2} (‖∇^i T₁‖_{L²} + ‖∇^i T₂‖_{L²}) ) · ‖(T₁ − T₂).toHs a‖   (for j ≤ 2 * a).
```

This is the covariant Faà-di-Bruno expansion of the curvature nonlinearity, lifted to `L²` by the
intrinsic Moser tame product `exists_moserTameProduct_iteratedCovGrad_l2Norm_le`: the covariant FTC
`Ric(g₁) − Ric(g₂) = ∫₀¹ DRic(g_t)·(g₁ − g₂) dt` along the segment `g_t = g₂ + t·(g₁ − g₂)` and the
covariant product/chain rule expand `∇^j` of the difference into a finite sum of contracted products
of a segment-metric `≤(j+2)`-jet coefficient (a `DRic(g_t)`-polynomial in the `≤(j+2)`-jets of `g_t`
and the bounded fibre-inverses) with an iterated covariant gradient `∇^i(g₁ − g₂)`, `i ≤ j + 2`, of the
metric difference.  The coefficient's genuinely-needed pointwise sup is only its `≤2`-jet (supplied by
the proven order-`≤2` segment-metric jet sup `exists_segmentMetric_realizeSymm_iteratedCovGradJet2_sup_le`,
the bounded `Λ`-arm); the **single high derivative** lands on the perturbation factor `∇^i(g₁ − g₂)` in
`L²`, while the **top redistributed coefficient derivative** (the FdB `i = 0` term's `∇^{j+2}g_t`
factor) is kept in `L²` against the difference factor's `C⁰`/`L^∞` factor, which the supercritical `C⁰`
Sobolev embedding folds into the order-`a` chart-Sobolev term `‖(T₁ − T₂).toHs a‖`.  Since
`(g₁ − g₂).inner = ccTensorBilinSymm g₀ (T₁ − T₂)`, each `∇^i(g₁ − g₂)` is `L²`-controlled by the
`≤ i`-order covariant gradients of `T₁ − T₂` (the realization gains no derivatives,
`exists_riemannianFiberNormSq_iteratedCovGrad_realizeSymm_le_jetSum`).

**Why this is `L²`, with a Hamilton-tame cross term — and why a plain ball-bound is FALSE.**  The
FdB `i = 0` term `[∇^{j+2}g_t]·(g₁ − g₂)` carries the **top coefficient jet** `∇^{j+2}g_t`, whose
`L²` mass has order `j + 2`.  For `j ∈ (a, 2a]` this is order `j + 2 ∈ (a + 2, 2a + 2]`, which an
`H^{a+2}` ball **cannot** bound (interpolation only goes down; a high-frequency `T₂⁽ᵏ⁾` in the ball
has `‖∇^{a+3}T₂⁽ᵏ⁾‖_{L²} → ∞`).  So the older "its mass `B`-controlled, `j + 2 ≤ 2a + 2`" reading is
FALSE — it conflated the gradient-order *range* with `H^{a+2}`-ball *control*.  The honest bound is
the standard **Hamilton/Moser tame product**: the difference-redistribution part
`C j · (‖(T₁ − T₂).toHs a‖ + ∑_{i ≤ j+2} ‖∇^i(T₁ − T₂)‖)` plus a **cross term**
`C j · (∑_{i ≤ j+2} (‖∇^i T₁‖ + ‖∇^i T₂‖)) · ‖(T₁ − T₂).toHs a‖`, in which the unbounded top jet
rides on the **fixed-pair** `L²` norms `∑(‖∇^i T₁‖ + ‖∇^i T₂‖)` (finite for each fixed `T₁, T₂`)
against the difference's `C⁰`/`toHs a` factor `‖(T₁ − T₂).toHs a‖`.  The cross-term coefficient is
ball-bounded **only at the terminal absorption** (`exists_iteratedCovGrad_l2Norm_le_toHs` through the
`H^{a+2}`-`B`-ball, order budget `i ≤ 2a + 2 ≤ 2(a + 2)`), where it collapses into the Lipschitz
constant — that deferral is the whole point.  **No jet of order `> 2` is ever taken pointwise.**

**Non-vacuity.**  A degenerate `C ≡ 0` is rejected: at `j = 0`, for perturbations with
`Ric(g₁) ≠ Ric(g₂)` on a positive-measure set, the left side is `> 0` while `0 · (…) = 0`,
contradicting the bound; so `C 0 > 0` and the domination genuinely uses the perturbation difference.
The cross term's `∑(‖∇^i T₁‖ + ‖∇^i T₂‖)` genuinely uses **both** endpoints, so it is not vacuous.

Its body is `sorry`: the curvature half of the genuine atomic covariant-Faà-di-Bruno (Nemytskii) `L²`
expansion — the deep metric-jet analytic content of the Ricci nonlinearity, with NO pointwise-`C^{>2}`-jet
claim, NO spectral-nonlinearity, and NO Weyl dependence. -/
theorem exists_ricciNeg2Diff_faaDiBruno_moserTame_l2Norm_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
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
        ∀ j : ℕ, j ≤ 2 * a →
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
              (ricciNeg2RetagG0 (I := I) g₀ g₁
                - ricciNeg2RetagG0 (I := I) g₀ g₂)‖ ≤
            C j * (‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖
                + ∑ i ∈ Finset.range (j + 2 + 1),
                    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)‖)
              + C j * (∑ i ∈ Finset.range (j + 2 + 1),
                    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖
                      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖))
                  * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ := by
  classical
  -- The deep covariant-curvature-jet posit: a per-order coefficient sup `Λ j` with the pointwise
  -- Hamilton/Moser two-product domination of `∇^j(Ric-diff)`.
  choose Λ hΛ_nn hΛ using
    fun j => ricciNeg2Diff_covFdB_pointwise_twoProduct_rfns_le (I := I) g₀ a ha B hB j
  -- The per-order realize-difference covariant `L²`-jet constant: `‖∇^i realizeSymm S‖ ≤ Cr i · ∑_{l≤i}
  -- ‖∇^l S‖` (the realization gains no derivatives).
  choose Cr hCr_nn hCr using
    fun i => realizeSymm_iteratedCovGrad_l2Norm_le_jetSum (I := I) g₀ i
  -- The combined per-order constant: `Λ j · (∑_{i ≤ j+2} Cr i)` (folding the realize-jet constant on
  -- the difference arm) plus `1` (dominating the cross-term coefficient `1`).
  refine ⟨fun j => Λ j * (∑ i ∈ Finset.range (j + 2 + 1), Cr i) + 1, fun j => ?_, ?_⟩
  · have : 0 ≤ Λ j * ∑ i ∈ Finset.range (j + 2 + 1), Cr i :=
      mul_nonneg (hΛ_nn j) (Finset.sum_nonneg fun i _ => hCr_nn i)
    linarith
  intro T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ j hj
  set D₀ : ℝ := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖
    with hD₀_def
  have hD₀_nn : 0 ≤ D₀ := norm_nonneg _
  -- Abbreviate the difference-jet `L²` sum and the cross-coefficient endpoint-jet sum.
  set diffSum : ℝ := ∑ i ∈ Finset.range (j + 2 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)‖ with hdiffSum_def
  have hdiffSum_nn : 0 ≤ diffSum :=
    Finset.sum_nonneg fun i _ => norm_nonneg _
  set crossSum : ℝ := ∑ i ∈ Finset.range (j + 2 + 1),
      (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖
        + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖) with hcrossSum_def
  have hcrossSum_nn : 0 ≤ crossSum :=
    Finset.sum_nonneg fun i _ => add_nonneg (norm_nonneg _) (norm_nonneg _)
  -- Apply the two-product pointwise-to-`L²` lift to the deep posit's pointwise bound, with the
  -- difference factor `w = realizeSymm (T₁ − T₂)` on the regular arm (coefficient `Λ j`) and the
  -- fixed-pair endpoints `T₁, T₂` on the cross arm (coefficient `D₀ = ‖(T₁ − T₂).toHs a‖`).
  have hlift :
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
          (ricciNeg2RetagG0 (I := I) g₀ g₁ - ricciNeg2RetagG0 (I := I) g₀ g₂)‖
        ≤ Λ j * ∑ i ∈ Finset.range (j + 2 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖
          + D₀ * ∑ i ∈ Finset.range (j + 2 + 1),
              (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖
                + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖) := by
    refine tensorL2Norm_le_of_pointwise_twoProduct_rfns_bound (I := I) (M := M) g₀ (j + 2 + 1)
      (fun i => 2 + i) (fun i => 2 + i)
      (fun i => PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
        (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))
      (fun i => PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁)
      (fun i => PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
        (ricciNeg2RetagG0 (I := I) g₀ g₁ - ricciNeg2RetagG0 (I := I) g₀ g₂))
      (Λ j) D₀ (hΛ_nn j) hD₀_nn (fun x => ?_)
    rw [hD₀_def]
    exact hΛ j T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ x
  -- The realize-difference covariant `L²`-jet bound on the regular arm: each `‖∇^i realizeSymm
  -- (T₁ − T₂)‖ ≤ Cr i · ∑_{l ≤ i} ‖∇^l (T₁ − T₂)‖ ≤ Cr i · diffSum` (since `i ≤ j + 2`).
  have hrealize_termwise : ∀ i ∈ Finset.range (j + 2 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ≤ Cr i * diffSum := by
    intro i hi
    have hi' : i ≤ j + 2 := by rw [Finset.mem_range] at hi; omega
    -- The realize bound is stated in `tensorL2Norm … .toFun`; convert to `‖·‖`.
    have hbound := hCr i (T₁ - T₂)
    rw [← Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))] at hbound
    refine hbound.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCr_nn i)
    -- `∑_{l ≤ i} ‖∇^l (T₁ − T₂)‖ ≤ ∑_{l ≤ j+2} ‖∇^l (T₁ − T₂)‖ = diffSum`.
    rw [hdiffSum_def]
    have hsubset : Finset.range (i + 1) ⊆ Finset.range (j + 2 + 1) :=
      Finset.range_subset_range.mpr (by omega)
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun l _ _ => norm_nonneg _))
    exact Finset.sum_congr rfl fun l _ =>
      (Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l (T₁ - T₂)))
  have hrealize_sum :
      ∑ i ∈ Finset.range (j + 2 + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖
        ≤ (∑ i ∈ Finset.range (j + 2 + 1), Cr i) * diffSum := by
    refine le_trans (Finset.sum_le_sum hrealize_termwise) ?_
    rw [Finset.sum_mul]
  -- Chain: `‖∇^j(Ric-diff)‖ ≤ Λj·(Σ Cr i)·diffSum + D₀·crossSum`, then match the target shape.
  have hCr_sum_nn : 0 ≤ ∑ i ∈ Finset.range (j + 2 + 1), Cr i :=
    Finset.sum_nonneg fun i _ => hCr_nn i
  calc ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
          (ricciNeg2RetagG0 (I := I) g₀ g₁ - ricciNeg2RetagG0 (I := I) g₀ g₂)‖
      ≤ Λ j * ∑ i ∈ Finset.range (j + 2 + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
              (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖
          + D₀ * crossSum := by rw [hcrossSum_def]; exact hlift
    _ ≤ Λ j * ((∑ i ∈ Finset.range (j + 2 + 1), Cr i) * diffSum) + D₀ * crossSum :=
        add_le_add (mul_le_mul_of_nonneg_left hrealize_sum (hΛ_nn j)) (le_refl _)
    _ ≤ (Λ j * (∑ i ∈ Finset.range (j + 2 + 1), Cr i) + 1) * (D₀ + diffSum)
          + (Λ j * (∑ i ∈ Finset.range (j + 2 + 1), Cr i) + 1) * crossSum * D₀ := by
        set C : ℝ := Λ j * (∑ i ∈ Finset.range (j + 2 + 1), Cr i) with hC_def
        have hC_nn : 0 ≤ C := mul_nonneg (hΛ_nn j) hCr_sum_nn
        have h1 : Λ j * ((∑ i ∈ Finset.range (j + 2 + 1), Cr i) * diffSum) = C * diffSum := by
          rw [hC_def]; ring
        rw [h1]
        have he1 : C * diffSum ≤ (C + 1) * (D₀ + diffSum) := by
          have : (C + 1) * (D₀ + diffSum) = C * diffSum + (C * D₀ + (D₀ + diffSum)) := by ring
          rw [this]
          have : 0 ≤ C * D₀ + (D₀ + diffSum) := by positivity
          linarith
        have he2 : D₀ * crossSum ≤ (C + 1) * crossSum * D₀ := by
          have hCS_nn : 0 ≤ crossSum := hcrossSum_nn
          have : (C + 1) * crossSum * D₀ = D₀ * crossSum + (C * crossSum * D₀) := by ring
          rw [this]
          have : 0 ≤ C * crossSum * D₀ := by positivity
          linarith
        linarith [he1, he2]

/-- **The covariant Faà-di-Bruno difference/cross split of the Lie-derivative summand difference
(the deep covariant-gauge-jet structural posit).**

The Lie/`deTurckVF`-gauge analogue of `ricciNeg2Diff_covFdB_section_split`.  For an anchor `g₀`, a
flow background `g_bg`, an order `a`, a supercriticality hypothesis `ha`, and a uniform `H^{a+2}`-size
bound `B ≥ 0`, then for any two `g₀`-fibre-small perturbations `T₁, T₂` with `H^{a+2}` norms `≤ B` and
any two realized metrics `g₁, g₂` of `T₁, T₂`, the `j`-th covariant gradient of the `g₀`-retagged
Lie-summand difference `lieDerivRetagG0 g₀ g_bg g₁ − lieDerivRetagG0 g₀ g_bg g₂` splits as a
**difference-arm piece** `Adiff` plus a **fixed-pair cross piece** `Cross`:
```
∇^j (lieDerivRetagG0 g₁ − lieDerivRetagG0 g₂) = Adiff + Cross,
rfns(Adiff)(x)  ≤ Cd · ∑_{i ≤ j+2} rfns(∇^i w)(x),
rfns(Cross)(x) ≤ (1/2) · (∑_{i ≤ j+2} (rfns(∇^i T₁)(x) + rfns(∇^i T₂)(x))) · ‖(T₁ − T₂).toHs a‖²,
```
with `w := realizeSymmCcTensor g₀ (T₁ − T₂)` and a nonnegative difference-arm constant `Cd`.

This is the **covariant Faà-di-Bruno expansion** of the *sealed* Lie/`deTurckVF` nonlinearity
`𝓛_{W(g, g_bg)} g` (the gauge summand `deTurckRHSSection g_bg g − ricciNeg2CcSection g`), differenced
along the segment metric `g_t = g₂ + t·(g₁ − g₂)`, collected by where the single high derivative lands.
The Lie field `𝓛_{W(g)} g` has the **same intrinsic order-`≤2` structure** as the curvature half (the
deTurck vector field `W = g⁻¹ · (Γ(g) − Γ(g_bg))` is a `g⁻¹·∂g`-type field, and one further metric
derivative produces the Lie deformation), so its segment difference admits the identical
difference/cross split: the **difference-arm** piece carries the high derivative on the difference
factor `w` (the metric-built `≤2`-jet coefficient folded into `Cd` via the binomial covariant-Leibniz
`rfns` grid of the contraction `DiffBilinOp`); the **cross** piece carries the Faà-di-Bruno `i = 0`
term's unbounded top coefficient jet `∇^{j+2}g_t` on the *fixed pair* `T₁, T₂` against the difference's
`C⁰` mass (bounded by `‖(T₁ − T₂).toHs a‖` through the supercritical embedding).  The `j = 0` witness of
exactly this two-piece structure is the chart-level structural difference identity
`chartLieDeTurckComp_sub_eq`.  No jet of order `> 2` is ever taken pointwise; the cross coefficient is
normalised to `1/2` so that after the squared-fibre-norm subadditivity factor `2` it yields the
coefficient-`1` cross arm the two-product consumer below records.

**Non-vacuity.**  As for the curvature half, the two arm bounds are *coupled* by the structural identity
`∇^j(summand-diff) = Adiff + Cross`, rejecting both `Adiff = 0` (the cross bound would be false for
`j ≥ 1`, the difference-arm content `∑ rfns(∇^i w)` genuinely present) and `Cross = 0` (the
difference-arm bound would be false for `j ∈ (a, 2a]`, the top-jet content genuinely
`(∑ fixed-pair) · C⁰`-order).  Both pieces carry genuine content; neither arm constant is vacuous.

It is **proven by composition** (TRANSIT) over the single order-zero linear/cross split posit
`lieDerivDiff_order0_linearCross_split`, which posits the genuine order-zero decomposition
`lieDerivRetagG0 g₁ − lieDerivRetagG0 g₂ = L + C` into a linear-in-difference section `L` and a
quadratic-in-difference Cross section `C` (genuine smooth `SmoothCcTensor`s) together with the per-order
difference-arm grid bound on `∇^j L` (carrying the difference factor `w := realizeSymmCcTensor g₀
(T₁ − T₂)` up to `∇^{j+2}w`, with a family-uniform `Cd`) and the fixed-pair Cross bound on `∇^j C`.
Pushing `∇^j` through the split (`iteratedCovGrad_add`) sets `Adiff := ∇^j L` and `Cross := ∇^j C`, and
the two arm bounds are the posit's all-order bounds at order `j`.

Unlike the curvature half (where the value-level split `ricciNeg2RetagG0_sub_eq_linear_add_cross` and the
concrete `linearSection` / `crossSection` exist on disk), the value-level Lie split
`lieDerivRetagG0_sub_eq_linear_add_cross` is genuinely absent, so the order-zero split and its per-order
jet bounds are bundled into the single posit `lieDerivDiff_order0_linearCross_split` (the genuine deep
covariant-gauge-jet content — the `j = 0` chart witness being the structural difference identity
`chartLieDeTurckComp_sub_eq`, `ChartLieDerivStructuralDifference.lean`).  Consumers transitively depend
on `sorryAx` only through that posit; this leaf carries NO value-bounded `Φ.op 0 2 w` shape, NO
pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, and NO Weyl dependence. -/
theorem lieDerivDiff_covFdB_section_split
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (j : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∃ Adiff Cross : Integral.L2.SmoothCcTensor g₀ 0 (2 + j),
          PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
              (lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂)
            = Adiff + Cross ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x (Adiff.toSection x) ≤
              Cd * ∑ i ∈ Finset.range (j + 2 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x (Cross.toSection x) ≤
              (1 / 2 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                  (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2) :=
  by
  classical
  obtain ⟨Cd, hCd_nn, hbody⟩ :=
    lieDerivDiff_order0_linearCross_split (I := I) g₀ g_bg a ha B hB
  refine ⟨Cd, hCd_nn, fun T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ => ?_⟩
  obtain ⟨L, C, hsplit, hL, hC⟩ := hbody T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂
  refine ⟨PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j L,
    PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j C, ?_, hL j, hC j⟩
  rw [hsplit, PDE.RicciFlow.iteratedCovGrad_add]

/-- **The pointwise covariant-Faà-di-Bruno two-product domination of the Lie-derivative summand
difference (the deep covariant-gauge-jet posit).**

For an anchor `g₀`, a flow background `g_bg`, an order `a`, a supercriticality hypothesis `ha`, a
uniform `H^{a+2}`-size bound `B ≥ 0`, and a covariant-gradient order `j`, there is a nonnegative
coefficient sup `Λ` such that for any two `g₀`-fibre-small perturbations `T₁, T₂` with `H^{a+2}` norms
`≤ B`, any two realized metrics `g₁, g₂` of `T₁, T₂`, and every base point `x`, the squared intrinsic
fibre norm (`riemannianFiberNormSq`, `rfns`) of the `j`-th covariant gradient of the `g₀`-retagged
Lie-summand difference `lieDerivRetagG0 g₀ g_bg g₁ − lieDerivRetagG0 g₀ g_bg g₂` is dominated
**pointwise** by the Hamilton/Moser **two-product**
```
rfns(∇^j (lieDerivRetagG0 g₁ − lieDerivRetagG0 g₂))(x)
  ≤ Λ² · ∑_{i ≤ j+2} rfns(∇^i w)(x)
    + (∑_{i ≤ j+2} (rfns(∇^i T₁)(x) + rfns(∇^i T₂)(x))) · ‖(T₁ − T₂).toHs a‖²,
```
with `w := realizeSymmCcTensor g₀ (T₁ − T₂)`.

This is the **covariant Faà-di-Bruno expansion** of the *sealed* Lie/`deTurckVF` nonlinearity
`𝓛_{W(g, g_bg)} g` (the `deTurckVF`-vector-field Lie deformation of the metric, the gauge summand
`deTurckRHSSection g_bg g − ricciNeg2CcSection g` of the Ricci–DeTurck right-hand side,
`DeTurckRHSSection.lean`), differenced along the segment metric `g_t = g₂ + t·(g₁ − g₂)`: the
covariant FTC `Lie(g₁) − Lie(g₂) = ∫₀¹ DLie(g_t)·(g₁ − g₂) dt` and the covariant product/chain rule
expand `∇^j` of the difference into a finite sum of contracted products of a segment-metric-jet
coefficient with a covariant jet of the metric difference `g₁ − g₂` (whose `inner` is the realized
form `ccTensorBilinSymm g₀ (T₁ − T₂)`, so each `∇^i(g₁ − g₂)` is fibre-controlled by `∇^{≤ i} w`).
The Lie field `𝓛_{W(g)} g` has the **same intrinsic order-`≤2` structure** as the curvature half: it
is `g⁻¹ · ∂g · ∂g + g⁻¹ · ∂²g` (the deTurck vector field `W = g⁻¹ · (Γ(g) − Γ(g_bg))` is a
`g⁻¹·∂g`-type field, and one further metric derivative produces the Lie deformation), the `g⁻¹`
Neumann factors carrying intrinsic order `0`.  The `j = 0` witness of exactly this two-product
structure is the chart-level structural difference identity `chartLieDeTurckComp_sub_eq`
(`DeTurckCoefficients/ChartLieDerivStructuralDifference.lean`), which exhibits the `Lie(g₁) − Lie(g₂)`
chart component as a difference of products of metric `≤2`-jets, splitting into a difference factor
(the `g₁ − g₂` jets) and a fixed-endpoint coefficient factor.  In the **regular** product the
coefficient's genuinely-needed pointwise sup is only its `≤2`-jet (`Λ`, ball-uniform over the
supercritical `H^{a+2}` family by the order-`≤2` segment-metric jet sup
`exists_segmentMetric_realizeSymm_iteratedCovGradJet2_sup_le`), the single high derivative landing on
the difference factor `w`; in the **top-jet** product the FdB `i = 0` term's unbounded top coefficient
jet `∇^{j+2}g_t` (`L²` mass of order `j + 2 ∈ (a + 2, 2a + 2]`, which an `H^{a+2}` ball cannot bound —
interpolation only goes down) is kept on the *fixed pair* endpoints `T₁, T₂` in `L²` against the
difference's `C⁰` mass, which the supercritical Sobolev embedding (`ha : 2 * a > dim M + 4`, i.e.
`a > dim M / 2`, the sharp `H^a ↪ C⁰` threshold) bounds by `‖(T₁ − T₂).toHs a‖`.  No jet of order `> 2`
is ever taken pointwise; the top jet rides in `L²` on the fixed pair, never ball-controlled in
isolation.

**Non-vacuity.**  Neither product discards its perturbation argument: the regular product carries the
difference factor `w` (its order-`0` term `rfns(w)(x) = 0` iff `T₁ = T₂` at `x`) and the top-jet
product carries **both** endpoints `T₁, T₂` (its order-`0` term `rfns(T₁)(x) + rfns(T₂)(x)`); a
witness with `Λ = 0` and the `‖(T₁ − T₂).toHs a‖`-coefficient effectively `0` fails whenever
`𝓛_{W(g₁)} g₁ ≠ 𝓛_{W(g₂)} g₂` on a positive-measure set (there `rfns(Lie-diff)(x) > 0`, the right side
`0`).  `Λ` is the genuine ball-uniform `≤2`-jet coefficient sup, `‖(T₁ − T₂).toHs a‖` the genuine
difference `C⁰` mass.

It is **proven by composition** over the structural covariant Faà-di-Bruno split
`lieDerivDiff_covFdB_section_split` (the same assembly as the curvature half): that split provides a
uniform difference-arm constant `Cd` and, per perturbation, the structural identity
`∇^j(Lie-diff) = Adiff + Cross` with the difference-arm grid bound `rfns(Adiff) ≤ Cd · ∑ rfns(∇^i w)`
and the cross-piece fixed-pair bound `rfns(Cross) ≤ (1/2)·(∑ fixed-pair)·‖(T₁ − T₂).toHs a‖²`.  The
two-product follows by the squared-fibre-norm subadditivity `riemannianFiberNormSq_add_le` (factor `2`)
over the identity, with the coefficient `Λ = √(2 Cd)` and the cross-piece `1/2` cancelling the factor
`2` into the coefficient-`1` cross arm.  Consumers transitively depend on `sorryAx` only through the
structural split posit, which carries the genuine deep covariant-gauge-jet content — the covariant
Faà-di-Bruno expansion of the sealed Lie/`deTurckVF` nonlinearity, with NO pointwise-`C^{>2}`-jet
claim, NO spectral-nonlinearity, and NO Weyl dependence. -/
theorem lieDerivDiff_covFdB_pointwise_twoProduct_rfns_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (j : ℕ) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                  (lieDerivRetagG0 (I := I) g₀ g_bg g₁
                    - lieDerivRetagG0 (I := I) g₀ g_bg g₂)).toSection x) ≤
            Λ ^ 2 * ∑ i ∈ Finset.range (j + 2 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x)
              + (∑ i ∈ Finset.range (j + 2 + 1),
                  (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 := by
  classical
  -- The covariant Faà-di-Bruno difference/cross split of the Lie-summand difference: a uniform
  -- difference-arm constant `Cd` and, per perturbation, the structural identity `∇^j(Lie-diff) =
  -- Adiff + Cross` with the difference-arm grid bound and the cross-piece fixed-pair bound.
  obtain ⟨Cd, hCd_nn, hsplit⟩ :=
    lieDerivDiff_covFdB_section_split (I := I) g₀ g_bg a ha B hB j
  -- The two-product coefficient `Λ = √(2 Cd)`: the squared-fibre-norm subadditivity factor `2` folds
  -- the difference-arm constant `Cd` into `Λ² = 2 Cd`, and the cross-piece `1/2` cancels the same
  -- factor `2` into the coefficient-`1` cross arm.
  refine ⟨Real.sqrt (2 * Cd), Real.sqrt_nonneg _,
    fun T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ x => ?_⟩
  obtain ⟨Adiff, Cross, heq, hAdiff, hCross⟩ := hsplit T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂
  -- The squared-fibre-norm subadditivity over the structural identity `∇^j(Lie-diff) = Adiff + Cross`.
  have hsplit_norm :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
              (lieDerivRetagG0 (I := I) g₀ g_bg g₁
                - lieDerivRetagG0 (I := I) g₀ g_bg g₂)).toSection x) ≤
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x (Adiff.toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x (Cross.toSection x) := by
    rw [heq, Integral.L2.SmoothCcTensor.toSection_add]
    exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + j) x
      (Adiff.toSection x) (Cross.toSection x)
  -- `Λ² = (√(2 Cd))² = 2 Cd`: the subadditivity factor `2` folds the difference-arm constant `Cd`
  -- into the coefficient, and the cross-piece `1/2` cancels the same factor `2`.
  rw [show Real.sqrt (2 * Cd) ^ 2 = 2 * Cd from Real.sq_sqrt (by positivity)]
  have hA := hAdiff x
  have hC := hCross x
  nlinarith [hsplit_norm, hA, hC]

/-- **The per-field covariant-Faà-di-Bruno Moser-tame `L²` domination of the segment-metric
*Lie-derivative* summand difference (the gauge half of the geometric nonlinearity, stated at the
`L²`-consumable level).**

The Lie half of the second-order Ricci–DeTurck right-hand side, `𝓛_{W(g, g_bg)} g` with `W = deTurckVF`
the metric-`g`-trace of the connection difference, is a fibrewise-smooth function of the metric `≤2`-jet
`(g, ∇g, ∇²g)` and the fibre-inverse (schematically `𝓛_{W(g)} g = g⁻¹ · ∂g · ∂g + g⁻¹ · ∂²g`, the `g⁻¹`
Neumann factors carrying intrinsic order `0`), of **intrinsic order capped at `2`**.  For an anchor
`g₀`, a flow background `g_bg`, an order `a`, a supercriticality hypothesis `ha`, and a uniform
`H^{a+2}`-size bound `B ≥ 0`, there is an order-indexed nonnegative constant family `C` such that for
any two `g₀`-fibre-small perturbations `T₁, T₂` with `H^{a+2}` norms `≤ B`, any two realized metrics
`g₁, g₂` of `T₁, T₂`, and every order `j ≤ 2 * a`, the metric `L²` (semi)norm of the `j`-th covariant
gradient of the `g₀`-retagged Lie-summand difference
`lieDerivRetagG0 g₀ g_bg g₁ − lieDerivRetagG0 g₀ g_bg g₂` is dominated by the **Hamilton/Moser-tame
sum** (a difference-redistribution part plus a fixed-pair cross term)
```
‖∇^j (lieDerivRetagG0 g₁ − lieDerivRetagG0 g₂)‖_{L²}
  ≤ C j · ( ‖(T₁ − T₂).toHs a‖ + ∑_{i ≤ j + 2} ‖∇^i (T₁ − T₂)‖_{L²} )
    + C j · ( ∑_{i ≤ j + 2} (‖∇^i T₁‖_{L²} + ‖∇^i T₂‖_{L²}) ) · ‖(T₁ − T₂).toHs a‖   (for j ≤ 2 * a).
```

This is the covariant Faà-di-Bruno expansion of the Lie/`deTurckVF` nonlinearity, lifted to `L²` by the
intrinsic Moser tame product (same Hamilton-tame structure as the curvature half).  The top coefficient
derivative (the FdB `i = 0` term's `∇^{j+2}g_t` factor) has `L²` mass of order `j + 2 ∈ (a + 2, 2a + 2]`
for `j ∈ (a, 2a]`, which an `H^{a+2}` ball **cannot** bound (interpolation only goes down).  So the bound
is NOT the plain difference-redistribution form: that unbounded top jet is carried by the **cross term**,
riding on the **fixed-pair** `L²` norms `∑(‖∇^i T₁‖ + ‖∇^i T₂‖)` (finite for each fixed `T₁, T₂`) against
the difference's `C⁰`/`L^∞` factor `‖(T₁ − T₂).toHs a‖`; the cross-term coefficient is ball-bounded only
at the terminal absorption.  **No jet of order `> 2` is ever taken pointwise.**  Since
`(g₁ − g₂).inner = ccTensorBilinSymm g₀ (T₁ − T₂)`, the metric-difference jets are the
perturbation-difference jets.

**Non-vacuity.**  A degenerate `C ≡ 0` is rejected: at `j = 0`, for perturbations with
`𝓛_{W(g₁)} g₁ ≠ 𝓛_{W(g₂)} g₂` on a positive-measure set, the left side is `> 0` while `0 · (…) = 0`,
contradicting the bound; so `C 0 > 0` and the domination genuinely uses the perturbation difference.
The cross term's `∑(‖∇^i T₁‖ + ‖∇^i T₂‖)` genuinely uses **both** endpoints, so it is not vacuous.

Its body is `sorry`: the gauge half of the genuine atomic covariant-Faà-di-Bruno (Nemytskii) `L²`
expansion — the deep metric-jet analytic content of the Lie/`deTurckVF` nonlinearity, with NO
pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, and NO Weyl dependence. -/
theorem exists_lieDerivDiff_faaDiBruno_moserTame_l2Norm_le
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
        ∀ j : ℕ, j ≤ 2 * a →
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
              (lieDerivRetagG0 (I := I) g₀ g_bg g₁
                - lieDerivRetagG0 (I := I) g₀ g_bg g₂)‖ ≤
            C j * (‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖
                + ∑ i ∈ Finset.range (j + 2 + 1),
                    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)‖)
              + C j * (∑ i ∈ Finset.range (j + 2 + 1),
                    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖
                      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖))
                  * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ := by
  classical
  -- The deep covariant-gauge-jet posit: a per-order coefficient sup `Λ j` with the pointwise
  -- Hamilton/Moser two-product domination of `∇^j(Lie-diff)`.
  choose Λ hΛ_nn hΛ using
    fun j => lieDerivDiff_covFdB_pointwise_twoProduct_rfns_le (I := I) g₀ g_bg a ha B hB j
  -- The per-order realize-difference covariant `L²`-jet constant: `‖∇^i realizeSymm S‖ ≤ Cr i · ∑_{l≤i}
  -- ‖∇^l S‖` (the realization gains no derivatives).
  choose Cr hCr_nn hCr using
    fun i => realizeSymm_iteratedCovGrad_l2Norm_le_jetSum (I := I) g₀ i
  -- The combined per-order constant: `Λ j · (∑_{i ≤ j+2} Cr i)` (folding the realize-jet constant on
  -- the difference arm) plus `1` (dominating the cross-term coefficient `1`).
  refine ⟨fun j => Λ j * (∑ i ∈ Finset.range (j + 2 + 1), Cr i) + 1, fun j => ?_, ?_⟩
  · have : 0 ≤ Λ j * ∑ i ∈ Finset.range (j + 2 + 1), Cr i :=
      mul_nonneg (hΛ_nn j) (Finset.sum_nonneg fun i _ => hCr_nn i)
    linarith
  intro T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ j hj
  set D₀ : ℝ := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖
    with hD₀_def
  have hD₀_nn : 0 ≤ D₀ := norm_nonneg _
  -- Abbreviate the difference-jet `L²` sum and the cross-coefficient endpoint-jet sum.
  set diffSum : ℝ := ∑ i ∈ Finset.range (j + 2 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)‖ with hdiffSum_def
  have hdiffSum_nn : 0 ≤ diffSum :=
    Finset.sum_nonneg fun i _ => norm_nonneg _
  set crossSum : ℝ := ∑ i ∈ Finset.range (j + 2 + 1),
      (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖
        + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖) with hcrossSum_def
  have hcrossSum_nn : 0 ≤ crossSum :=
    Finset.sum_nonneg fun i _ => add_nonneg (norm_nonneg _) (norm_nonneg _)
  -- Apply the two-product pointwise-to-`L²` lift to the deep posit's pointwise bound, with the
  -- difference factor `w = realizeSymm (T₁ − T₂)` on the regular arm (coefficient `Λ j`) and the
  -- fixed-pair endpoints `T₁, T₂` on the cross arm (coefficient `D₀ = ‖(T₁ − T₂).toHs a‖`).
  have hlift :
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
          (lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂)‖
        ≤ Λ j * ∑ i ∈ Finset.range (j + 2 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖
          + D₀ * ∑ i ∈ Finset.range (j + 2 + 1),
              (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖
                + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖) := by
    refine tensorL2Norm_le_of_pointwise_twoProduct_rfns_bound (I := I) (M := M) g₀ (j + 2 + 1)
      (fun i => 2 + i) (fun i => 2 + i)
      (fun i => PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
        (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))
      (fun i => PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁)
      (fun i => PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
        (lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂))
      (Λ j) D₀ (hΛ_nn j) hD₀_nn (fun x => ?_)
    rw [hD₀_def]
    exact hΛ j T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ x
  -- The realize-difference covariant `L²`-jet bound on the regular arm: each `‖∇^i realizeSymm
  -- (T₁ − T₂)‖ ≤ Cr i · ∑_{l ≤ i} ‖∇^l (T₁ − T₂)‖ ≤ Cr i · diffSum` (since `i ≤ j + 2`).
  have hrealize_termwise : ∀ i ∈ Finset.range (j + 2 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ≤ Cr i * diffSum := by
    intro i hi
    have hi' : i ≤ j + 2 := by rw [Finset.mem_range] at hi; omega
    -- The realize bound is stated in `tensorL2Norm … .toFun`; convert to `‖·‖`.
    have hbound := hCr i (T₁ - T₂)
    rw [← Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))] at hbound
    refine hbound.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCr_nn i)
    -- `∑_{l ≤ i} ‖∇^l (T₁ − T₂)‖ ≤ ∑_{l ≤ j+2} ‖∇^l (T₁ − T₂)‖ = diffSum`.
    rw [hdiffSum_def]
    have hsubset : Finset.range (i + 1) ⊆ Finset.range (j + 2 + 1) :=
      Finset.range_subset_range.mpr (by omega)
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun l _ _ => norm_nonneg _))
    exact Finset.sum_congr rfl fun l _ =>
      (Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l (T₁ - T₂)))
  have hrealize_sum :
      ∑ i ∈ Finset.range (j + 2 + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖
        ≤ (∑ i ∈ Finset.range (j + 2 + 1), Cr i) * diffSum := by
    refine le_trans (Finset.sum_le_sum hrealize_termwise) ?_
    rw [Finset.sum_mul]
  -- Chain: `‖∇^j(Lie-diff)‖ ≤ Λj·(Σ Cr i)·diffSum + D₀·crossSum`, then match the target shape.
  have hCr_sum_nn : 0 ≤ ∑ i ∈ Finset.range (j + 2 + 1), Cr i :=
    Finset.sum_nonneg fun i _ => hCr_nn i
  calc ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
          (lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂)‖
      ≤ Λ j * ∑ i ∈ Finset.range (j + 2 + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
              (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖
          + D₀ * crossSum := by rw [hcrossSum_def]; exact hlift
    _ ≤ Λ j * ((∑ i ∈ Finset.range (j + 2 + 1), Cr i) * diffSum) + D₀ * crossSum :=
        add_le_add (mul_le_mul_of_nonneg_left hrealize_sum (hΛ_nn j)) (le_refl _)
    _ ≤ (Λ j * (∑ i ∈ Finset.range (j + 2 + 1), Cr i) + 1) * (D₀ + diffSum)
          + (Λ j * (∑ i ∈ Finset.range (j + 2 + 1), Cr i) + 1) * crossSum * D₀ := by
        set C : ℝ := Λ j * (∑ i ∈ Finset.range (j + 2 + 1), Cr i) with hC_def
        have hC_nn : 0 ≤ C := mul_nonneg (hΛ_nn j) hCr_sum_nn
        have h1 : Λ j * ((∑ i ∈ Finset.range (j + 2 + 1), Cr i) * diffSum) = C * diffSum := by
          rw [hC_def]; ring
        rw [h1]
        have he1 : C * diffSum ≤ (C + 1) * (D₀ + diffSum) := by
          have : (C + 1) * (D₀ + diffSum) = C * diffSum + (C * D₀ + (D₀ + diffSum)) := by ring
          rw [this]
          have : 0 ≤ C * D₀ + (D₀ + diffSum) := by positivity
          linarith
        have he2 : D₀ * crossSum ≤ (C + 1) * crossSum * D₀ := by
          have hCS_nn : 0 ≤ crossSum := hcrossSum_nn
          have : (C + 1) * crossSum * D₀ = D₀ * crossSum + (C * crossSum * D₀) := by ring
          rw [this]
          have : 0 ≤ C * crossSum * D₀ := by positivity
          linarith
        linarith [he1, he2]

/-- **The per-order covariant-Faà-di-Bruno Moser-tame `L²` domination of the segment-metric
DeTurck right-hand-side difference (the genuine atomic metric-jet Nemytskii primitive, stated at the
`L²`-consumable level).**

For an anchor `g₀`, a flow background `g_bg`, an order `a`, a supercriticality hypothesis
`ha : 2 * a > Module.finrank ℝ E + 4`, and a uniform `H^{a+2}`-size bound `B ≥ 0`, there is an
order-indexed nonnegative constant family `C : ℕ → ℝ` (absorbing the bounded `≤2`-jet metric
coefficient sup `Λ`, the segment-metric `L²`-jet mass, the `C⁰`-embedding constant, the binomial
covariant-Leibniz factors, and the finitely many contraction-shape constants) such that for any two
`g₀`-fibre-small perturbations `T₁, T₂` whose `H^{a+2}` norms are `≤ B`, any two realized metrics
`g₁, g₂` of `T₁, T₂` (tied by the fibrewise `inner`-identities), and every covariant-gradient order
`j ≤ 2 * a`, the metric `L²` (semi)norm of the `j`-th covariant gradient of the **re-tagged DeTurck
right-hand-side section difference** `deTurckRHSRetagG0 g₀ g_bg g₁ − deTurckRHSRetagG0 g₀ g_bg g₂` is
dominated by the **Hamilton/Moser-tame sum** — an order-`a` chart-Sobolev `C⁰`-redistribution
term against the iterated covariant `L²`-gradients of the perturbation difference `T₁ − T₂`, plus a
fixed-pair cross term carrying the unbounded top coefficient jet:
```
‖∇^j (deTurckRHSRetagG0 g₁ − deTurckRHSRetagG0 g₂)‖_{L²}
  ≤ C j · ( ‖(T₁ − T₂).toHs a‖ + ∑_{i ≤ j + 2} ‖∇^i (T₁ − T₂)‖_{L²} )
    + C j · ( ∑_{i ≤ j + 2} (‖∇^i T₁‖_{L²} + ‖∇^i T₂‖_{L²}) ) · ‖(T₁ − T₂).toHs a‖   (for j ≤ 2 * a).
```

This is the genuine **covariant Faà-di-Bruno expansion** of the *non-linear* summand `Ric + Lie` of
the second-order Ricci–DeTurck right-hand side, lifted to `L²` by the intrinsic Moser tame product
`exists_moserTameProduct_iteratedCovGrad_l2Norm_le`.  The chart right-hand side is a fibrewise-smooth
function `F` of the metric `≤2`-jet `(g, ∇g, ∇²g)` and the fibre-inverse; the covariant FTC
`F(g₁) − F(g₂) = ∫₀¹ DF(g_t)·(g₁ − g₂) dt` along the **segment metric** `g_t = g₂ + t·(g₁ − g₂)` and
the covariant product/chain rule expand `∇^j` of the difference into a finite sum of contracted
products of a segment-metric `≤(j+2)`-jet coefficient (a `DF(g_t)`-polynomial in the `≤(j+2)`-jets of
`g_t` and the bounded fibre-inverses) with an iterated covariant gradient `∇^i(g₁ − g₂)`, `i ≤ j + 2`,
of the metric difference.  In every Moser-tame term the **intrinsic order of the geometric
nonlinearity `Ric + Lie` is capped at `2`** (it is `g⁻¹·∂²g` or `g⁻¹·g⁻¹·∂g·∂g`; the `g⁻¹` Neumann
factors carry intrinsic order `0`), so the coefficient's genuinely-needed pointwise sup is only its
`≤2`-jet, supplied by the proven order-`≤2` segment-metric jet sup
`exists_segmentMetric_realizeSymm_iteratedCovGradJet2_sup_le` (the bounded `Λ`-arm); the **single high
derivative** lands on the perturbation factor `∇^i(g₁ − g₂)` in `L²` (the `Λ`-arm of the Moser-tame
product), while the **top redistributed coefficient derivative** is kept in `L²` against the
difference factor's `C⁰`/`L^∞` factor (the `Λ₀`-arm), which the supercritical `C⁰` Sobolev embedding
`tensorPouSobolevHilbert_embedding_Ck` folds into the order-`a` chart-Sobolev term `‖(T₁ − T₂).toHs
a‖`.  Since the fibrewise `inner`-difference makes `(g₁ − g₂).inner = ccTensorBilinSymm g₀ (T₁ − T₂)`
the realized bilinear form of `T₁ − T₂`, each `∇^i(g₁ − g₂)` is `L²`-controlled by the `≤ i`-order
covariant gradients of `T₁ − T₂` (the realization gains no derivatives,
`exists_riemannianFiberNormSq_iteratedCovGrad_realizeSymm_le_jetSum`).

**Why this is TRUE — and why a plain ball-bound is FALSE, requiring a Hamilton-tame cross term.**
An earlier *pointwise* `rfns` form (no `C⁰`-redistribution slot) is FALSE for `j ≥ 1`; but so is the
naive `L²` difference-only form `Cf j · (‖(T₁ − T₂).toHs a‖ + ∑_{i ≤ j+2} ‖∇^i(T₁ − T₂)‖)` for
`j ∈ (a, 2a]`.  The covariant-FdB `i = 0` term `[∇^{j+2}g_t]·(g₁ − g₂)` carries the **top coefficient
jet** `∇^{j+2}g_t`, whose `L²` mass has order `j + 2 ∈ (a + 2, 2a + 2]`.  An `H^{a+2}` ball **cannot**
bound such an `H^{a+3+}` jet (interpolation only goes down): take a high-frequency `T₂⁽ᵏ⁾` in the ball
with `‖∇^{a+3}T₂⁽ᵏ⁾‖_{L²} → ∞` and `T₁ := T₂⁽ᵏ⁾ + εU`; then `(1/ε)·`LHS at `j = 2a` blows up along
`k` while `(1/ε)·`(difference-only RHS) stays fixed — a counterexample.  The honest bound is the
standard **Hamilton/Moser tame product**: the difference-redistribution part plus the **cross term**
`C j · (∑_{i ≤ j+2} (‖∇^i T₁‖ + ‖∇^i T₂‖)) · ‖(T₁ − T₂).toHs a‖`, in which that very `i = 0` term is
`‖[∇^{j+2}g_t]·(g₁ − g₂)‖_{L²} ≤ ‖∇^{j+2}g_t‖_{L²}·‖g₁ − g₂‖_{C⁰}` with the unbounded top jet kept in
`L²` on the **fixed pair** `T₁, T₂` (finite for each fixed pair) and the difference's `C⁰`/`L^∞`
factor in `‖(T₁ − T₂).toHs a‖`.  The cross-term coefficient `∑(‖∇^i T₁‖ + ‖∇^i T₂‖)` is ball-bounded
**only at the terminal absorption** (`exists_iteratedCovGrad_l2Norm_le_toHs` through the
`H^{a+2}`-`B`-ball, order budget `i ≤ 2a + 2 ≤ 2(a + 2)`), where it collapses into the Lipschitz
constant exactly as the difference-redistribution term does — that deferral is the whole point.  No
jet of order `> 2` is ever taken pointwise.

**Trap-screen.** The metric jet enters pointwise ONLY through its `≤2`-jet sup (no pointwise sup of
any order-`>2` metric jet, unavailable for `finrank ≥ 4` — the false-embedding lesson); the unbounded
top jet rides in `L²` on the fixed pair inside the cross term, never ball-bounded in isolation; the
constant `C` is a *family* over the unbounded gradient order `j`; and the uniform `Λ`/`Λ₀`/`L²`-jet
budget is scoped to the supercritical `H^{a+2}`-bounded `B`-family (`ha`) only at the terminal absorption.

**Non-vacuity.** A degenerate `C ≡ 0` is rejected: at `j = 0`, for perturbations with
`deTurckRHSRetagG0 g₁ ≠ deTurckRHSRetagG0 g₂` on a positive-measure set (e.g. `T₁ ≠ T₂` producing
distinct curvatures), the left side is `> 0` while `0 · (… ) = 0`, contradicting the bound; so
`C 0 > 0` and the domination genuinely uses the perturbation difference.

It is **proven by composition** (TRANSIT glue) of the two **per-field** covariant-Faà-di-Bruno
Moser-tame `L²` primitives — the curvature-summand difference bound
`exists_ricciNeg2Diff_faaDiBruno_moserTame_l2Norm_le` and the Lie-summand difference bound
`exists_lieDerivDiff_faaDiBruno_moserTame_l2Norm_le` — over the additive `Ric + Lie` split of the
re-tagged DeTurck right-hand-side section `deTurckRHSRetagG0_eq_ricciNeg2_add_lieDeriv` (the section is
the sum of its genuine `SmoothCcTensor` curvature and Lie summands).  Since the section difference
`deTurckRHSRetagG0 g₁ − deTurckRHSRetagG0 g₂` splits as `(ricciNeg2RetagG0 g₁ − ricciNeg2RetagG0 g₂) +
(lieDerivRetagG0 g₁ − lieDerivRetagG0 g₂)`, the additivity of the iterated covariant gradient
(`iteratedCovGrad_add`) and the `L²`-seminorm triangle inequality reduce the bound to the sum of the two
per-field bounds, with combined per-order constant `Cric j + Clie j`.  The genuine deep metric-jet
analytic content — the covariant Faà-di-Bruno (Nemytskii) `L²` expansion of each geometric nonlinearity,
with NO pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO perturbation-indexed-remainder, and
NO Weyl dependence — lives in the two per-field primitives.  Consumers transitively depend on `sorryAx`
only through those two atomic per-field covariant-Faà-di-Bruno Moser-tame `L²` primitives. -/
theorem exists_segmentMetricRHSDiff_faaDiBruno_moserTame_l2Norm_le
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
        ∀ j : ℕ, j ≤ 2 * a →
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
              (deTurckRHSRetagG0 (I := I) g₀ g_bg g₁
                - deTurckRHSRetagG0 (I := I) g₀ g_bg g₂)‖ ≤
            C j * (‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖
                + ∑ i ∈ Finset.range (j + 2 + 1),
                    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)‖)
              + C j * (∑ i ∈ Finset.range (j + 2 + 1),
                    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖
                      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖))
                  * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ := by
  classical
  -- The two per-field covariant-Faà-di-Bruno Moser-tame `L²` primitives (curvature and Lie halves).
  obtain ⟨Cric, hCric_nn, hCric⟩ :=
    exists_ricciNeg2Diff_faaDiBruno_moserTame_l2Norm_le (I := I) g₀ a ha B hB
  obtain ⟨Clie, hClie_nn, hClie⟩ :=
    exists_lieDerivDiff_faaDiBruno_moserTame_l2Norm_le (I := I) g₀ g_bg a ha B hB
  -- The combined per-order constant.
  refine ⟨fun j => Cric j + Clie j, fun j => add_nonneg (hCric_nn j) (hClie_nn j), ?_⟩
  intro T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ j hj
  -- Abbreviate the common difference-redistribution sum and the fixed-pair cross factor.
  set R : ℝ := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖
      + ∑ i ∈ Finset.range (j + 2 + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (T₁ - T₂)‖ with hR_def
  have hR_nn : 0 ≤ R := by
    rw [hR_def]
    exact add_nonneg (norm_nonneg _)
      (Finset.sum_nonneg fun i _ => norm_nonneg _)
  -- The retagged additive split of each section, hence of the difference.
  have hsplit :
      deTurckRHSRetagG0 (I := I) g₀ g_bg g₁ - deTurckRHSRetagG0 (I := I) g₀ g_bg g₂ =
        (ricciNeg2RetagG0 (I := I) g₀ g₁ - ricciNeg2RetagG0 (I := I) g₀ g₂) +
          (lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂) := by
    rw [deTurckRHSRetagG0_eq_ricciNeg2_add_lieDeriv (I := I) g₀ g_bg g₁,
      deTurckRHSRetagG0_eq_ricciNeg2_add_lieDeriv (I := I) g₀ g_bg g₂]
    abel
  -- The `j`-th covariant gradient of the difference splits additively.
  rw [hsplit, PDE.RicciFlow.iteratedCovGrad_add]
  -- The two per-field child bounds, specialized to this `j ≤ 2a`.
  have hric := hCric T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ j hj
  have hlie := hClie T₁ T₂ g₁ g₂ hg₁ hg₂ hsize₁ hsize₂ j hj
  rw [← hR_def] at hric hlie
  -- Triangle inequality on the `L²` seminorm, then the two child bounds and the constant split.
  calc ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
          (ricciNeg2RetagG0 (I := I) g₀ g₁ - ricciNeg2RetagG0 (I := I) g₀ g₂) +
        PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
          (lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂)‖
      ≤ ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
            (ricciNeg2RetagG0 (I := I) g₀ g₁ - ricciNeg2RetagG0 (I := I) g₀ g₂)‖ +
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
            (lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂)‖ :=
        norm_add_le _ _
    _ ≤ (Cric j * R + Cric j * (∑ i ∈ Finset.range (j + 2 + 1),
              (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖
                + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖))
            * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖)
          + (Clie j * R + Clie j * (∑ i ∈ Finset.range (j + 2 + 1),
              (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖
                + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖))
            * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖) :=
        add_le_add hric hlie
    _ = (Cric j + Clie j) * R + (Cric j + Clie j) * (∑ i ∈ Finset.range (j + 2 + 1),
              (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖
                + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖))
            * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ := by
        ring

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
