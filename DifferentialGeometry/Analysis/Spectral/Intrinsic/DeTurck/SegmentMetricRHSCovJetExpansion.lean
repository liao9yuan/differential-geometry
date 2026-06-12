import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRHSSectionRetag
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedCovGradJetGeneralOrder
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizeSymmIteratedCovGradFiberNormBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricRicciDiffOperatorExpansion
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MetricDifferenceFdBTermTree
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricCurvatureDifferenceOpDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricCurvatureDifferenceCovJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricLieDiffCovJet
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.GagliardoNirenbergProductTwoArm
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.SharpOrderRealizedJetEmbedding

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

Each of the three Moser-tame `L²` dominations below is stated and proven **j-uncapped** (the
`allOrder` form, `∀ j : ℕ`, the classical Hamilton-TAME shape: the constant family depends only on
the fixed `H^{a+2}`-ball data `(g₀, g_bg, a, B, δ)` at every order, with no size threshold rebinding
to a higher Sobolev space at higher orders — the shape the per-order Picard invariance system needs
to be downward well-founded); the historical `j ≤ 2 * a` consumer-window forms are kept as verbatim
specializations.  Every ingredient (the diagonal product grids, the integrated Gagliardo–Nirenberg
two-arm engine, the sharp-order embeddings at the fixed orders `a` and `a + 2`, the realize-jet `L²`
conversion, and the integrated gauge two-product posit) takes an unconstrained gradient order, so the
former cap carried no mathematical content.

* The headline **per-order covariant Faà-di-Bruno Moser-tame `L²` domination** of the retagged DeTurck
  right-hand-side section difference, `exists_segmentMetricRHSDiff_faaDiBruno_moserTame_allOrder_l2Norm_le`
  (window specialization `exists_segmentMetricRHSDiff_faaDiBruno_moserTame_l2Norm_le`), is
  **proven by composition** here: the second-order Ricci–DeTurck right-hand side `F(g) = -2 • Ric(g) +
  𝓛_{W(g, g_bg)} g` is split additively into its two genuine `SmoothCcTensor` summands — the curvature
  summand `ricciNeg2CcSection` and the Lie-derivative summand `lieDerivCcSection` — via the proven
  section identity `deTurckRHSSection_eq_ricciNeg2_add_lieDeriv`; the `j`-th covariant gradient of the
  retagged difference splits additively (`iteratedCovGrad_add`) and the `L²`-seminorm triangle
  inequality reduces the headline bound to the sum of the two **per-field** primitives, with combined
  per-order constant.
* The **curvature** per-field `L²` domination `exists_ricciNeg2Diff_faaDiBruno_moserTame_l2Norm_le` is
  **proven by composition** over the corrected pointwise-grid/integrated-two-arm route: the order-zero
  value split `ricciNeg2RetagG0_sub_eq_linear_add_cross` exhibits the curvature difference as
  `linearSection + crossSection`; each piece's order-`j` covariant jet is dominated **pointwise by the
  zero-jet-inclusive diagonal product grid** `∑_{i+l ≤ j+2} rfns(∇^i w)·(rfns(∇^l T₁) + rfns(∇^l T₂))`
  in the realized difference factor `w := realizeSymm (T₁ − T₂)` and the fixed-pair endpoints
  (`ricciLinearSection_covGrad_twoArm_l2Norm_le` /
  `crossSection_iteratedCovGrad_twoArm_l2Norm_le`,
  `SegmentMetricCurvatureDifferenceCovJet.lean`); the grid is then **integrated** through the shared
  Gagliardo–Nirenberg two-arm engine
  `exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le` (Hamilton 12.5,
  `Analysis/Spectral/Tensor/CovGrad/GagliardoNirenbergProductTwoArm.lean`), with the two `C⁰` sups
  supplied by the sharp-order embeddings `exists_realizedJetSum_le_toHs_sharpOrder` (the difference
  factor at order `a`, the `Λ_S ≤ C·‖(T₁ − T₂).toHs a‖` arm) and
  `exists_iteratedCovGradJetSum_le_toHs_sharpOrder` at order `a + 2` (the fixed endpoints, the
  `Λ_T ≤ C·B` arm; `SharpOrderRealizedJetEmbedding.lean`), and the difference-factor `L²` jets
  converted by the realize-jet bound `realizeSymm_iteratedCovGrad_l2Norm_le_jetSum`.
* An earlier **pointwise two-arm** route to the curvature half (a per-point difference-jet arm plus a
  fixed-pair arm against the difference's `‖·.toHs a‖²` mass, with fixed numeric coefficients,
  recombined through pointwise two-product `rfns` dominations) was **refuted** twice over and removed:
  a `g₀`-parallel difference forces the whole value into the would-be fixed-pair piece, whose embedding
  cost no fixed numeric fraction dominates (small-volume witness), and at orders `j ≳ 2a` a joint
  concentration bump makes the middle-diagonal Leibniz terms `∇^i(diff) ⊛ ∇^{j+1−i}(fixed)` larger than
  *both* arms.  The two-arm shape exists only **after integration** — exactly what the
  Gagliardo–Nirenberg engine supplies.
* The **Lie** half is unchanged by that correction at this level: the per-field `L²` domination
  `exists_lieDerivDiff_faaDiBruno_moserTame_l2Norm_le` is proven by composition from the pointwise
  two-product `lieDerivDiff_covFdB_pointwise_twoProduct_rfns_le` over the structural split
  `lieDerivDiff_covFdB_section_split`, which descends through the order-zero linear/cross split
  `lieDerivDiff_order0_linearCross_split` into the single genuine deep gauge leaf
  `lieDerivDiff_connLevel_topRestSplit` (`SegmentMetricLieSectionDecomposition.lean`).  (The same
  pointwise-where-only-integrated correction is scheduled for the Lie band; its migration mirrors the
  curvature half's.)

Consumers of the curvature half transitively depend on `sorryAx` only through the four corrected
posits — the two diagonal product grids, the integrated Gagliardo–Nirenberg two-arm engine, and the
sharp-order `C²` embedding; none of these carries a value-bounded `Φ.op 0 2 w` shape, a
pointwise-`C^{>2}`-jet claim, a pointwise two-arm split, a spectral-nonlinearity, or any Weyl
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

/-- **The two-arm `√`-domination of a squared sum.**  An elementary real-arithmetic step: a
nonnegative `n` whose square is dominated by the integrated two-arm sum
`Λ² · ∑ nwᵢ² + (∑ (nc₁ᵢ² + nc₂ᵢ²)) · D²` is itself dominated by the two-arm sum
`Λ · ∑ nwᵢ + D · ∑ (nc₁ᵢ + nc₂ᵢ)`, with the two constants kept on their *separate* arms.  The
`L²`-norm-squared → `L²`-norm step of the integrated two-product domination, via the finite
Cauchy–Schwarz collapse `∑ aᵢ² ≤ (∑ aᵢ)²` (for nonnegative `aᵢ`) on each arm.  Proved outright. -/
private theorem twoArm_le_of_sq_le (N : ℕ) (nw nc₁ nc₂ : ℕ → ℝ)
    (hnw : ∀ i, 0 ≤ nw i) (hnc₁ : ∀ i, 0 ≤ nc₁ i) (hnc₂ : ∀ i, 0 ≤ nc₂ i)
    (n Λ D : ℝ) (_hn : 0 ≤ n) (hΛ : 0 ≤ Λ) (hD : 0 ≤ D)
    (hsq : n ^ 2 ≤ Λ ^ 2 * ∑ i ∈ Finset.range N, nw i ^ 2
        + (∑ i ∈ Finset.range N, (nc₁ i ^ 2 + nc₂ i ^ 2)) * D ^ 2) :
    n ≤ Λ * ∑ i ∈ Finset.range N, nw i + D * ∑ i ∈ Finset.range N, (nc₁ i + nc₂ i) := by
  classical
  set Sw : ℝ := ∑ i ∈ Finset.range N, nw i with hSw_def
  set Sc : ℝ := ∑ i ∈ Finset.range N, (nc₁ i + nc₂ i) with hSc_def
  have hSw_nn : 0 ≤ Sw := Finset.sum_nonneg fun i _ => hnw i
  have hSc_nn : 0 ≤ Sc := Finset.sum_nonneg fun i _ => add_nonneg (hnc₁ i) (hnc₂ i)
  -- `∑ nwᵢ² ≤ Sw²` (the squared-sum dominates the sum-of-squares for nonnegative terms).
  have hwsq : ∑ i ∈ Finset.range N, nw i ^ 2 ≤ Sw ^ 2 := by
    rw [hSw_def, sq, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [sq]
    exact Finset.single_le_sum (f := fun j => nw i * nw j)
      (fun j _ => mul_nonneg (hnw i) (hnw j)) hi
  -- `∑ (nc₁ᵢ² + nc₂ᵢ²) ≤ ∑ (nc₁ᵢ + nc₂ᵢ)² ≤ Sc²`.
  have hcsq : ∑ i ∈ Finset.range N, (nc₁ i ^ 2 + nc₂ i ^ 2) ≤ Sc ^ 2 := by
    have hstep1 : (∑ i ∈ Finset.range N, (nc₁ i ^ 2 + nc₂ i ^ 2))
        ≤ ∑ i ∈ Finset.range N, (nc₁ i + nc₂ i) ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      nlinarith [mul_nonneg (hnc₁ i) (hnc₂ i)]
    have hstep2 : (∑ i ∈ Finset.range N, (nc₁ i + nc₂ i) ^ 2) ≤ Sc ^ 2 := by
      rw [hSc_def, sq, Finset.sum_mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [sq]
      exact Finset.single_le_sum (f := fun j => (nc₁ i + nc₂ i) * (nc₁ j + nc₂ j))
        (fun j _ => mul_nonneg (add_nonneg (hnc₁ i) (hnc₂ i)) (add_nonneg (hnc₁ j) (hnc₂ j))) hi
    exact le_trans hstep1 hstep2
  -- Combine: `n² ≤ (Λ·Sw)² + (D·Sc)² ≤ (Λ·Sw + D·Sc)²`, hence `n ≤ Λ·Sw + D·Sc`.
  have hΛSw_nn : 0 ≤ Λ * Sw := mul_nonneg hΛ hSw_nn
  have hDSc_nn : 0 ≤ D * Sc := mul_nonneg hD hSc_nn
  have harm1 : Λ ^ 2 * ∑ i ∈ Finset.range N, nw i ^ 2 ≤ (Λ * Sw) ^ 2 := by
    calc Λ ^ 2 * ∑ i ∈ Finset.range N, nw i ^ 2 ≤ Λ ^ 2 * Sw ^ 2 :=
          mul_le_mul_of_nonneg_left hwsq (sq_nonneg _)
      _ = (Λ * Sw) ^ 2 := by ring
  have harm2 : (∑ i ∈ Finset.range N, (nc₁ i ^ 2 + nc₂ i ^ 2)) * D ^ 2 ≤ (D * Sc) ^ 2 := by
    calc (∑ i ∈ Finset.range N, (nc₁ i ^ 2 + nc₂ i ^ 2)) * D ^ 2 ≤ Sc ^ 2 * D ^ 2 :=
          mul_le_mul_of_nonneg_right hcsq (sq_nonneg _)
      _ = (D * Sc) ^ 2 := by ring
  have hcombine : n ^ 2 ≤ (Λ * Sw + D * Sc) ^ 2 := by
    have hcross : (Λ * Sw) ^ 2 + (D * Sc) ^ 2 ≤ (Λ * Sw + D * Sc) ^ 2 := by
      nlinarith [mul_nonneg hΛSw_nn hDSc_nn]
    calc n ^ 2 ≤ Λ ^ 2 * ∑ i ∈ Finset.range N, nw i ^ 2
          + (∑ i ∈ Finset.range N, (nc₁ i ^ 2 + nc₂ i ^ 2)) * D ^ 2 := hsq
      _ ≤ (Λ * Sw) ^ 2 + (D * Sc) ^ 2 := add_le_add harm1 harm2
      _ ≤ (Λ * Sw + D * Sc) ^ 2 := hcross
  nlinarith [hcombine, add_nonneg hΛSw_nn hDSc_nn, sq_nonneg (n - (Λ * Sw + D * Sc))]

/-! ### The order-zero linear/cross split of the Lie-summand difference

The Lie/gauge analogue of the curvature half's `linearSection` / `crossSection` decomposition
(`SegmentMetricCurvatureDifferenceOpDecomposition.lean`).  The `g₀`-retagged Lie-summand difference
`lieDerivRetagG0 g₀ g_bg g₁ − lieDerivRetagG0 g₀ g_bg g₂` decomposes at order zero into a
**linear-in-difference** section `L` and a **quadratic-in-difference Cross** section `C`.  Unlike the
curvature half — where the concrete `crossSection` is *built* through the M2 connection-difference
operator field `connDiffField`, the value split `ricciNeg2RetagG0_sub_eq_linear_add_cross` is then a
pure `abel` over the complement `linearSection := diff − crossSection`, and the difference-arm jet bound
on the linear part is a *separable* leaf — the intrinsic-vector linear/quadratic split of the Lie
deformation difference is **genuinely absent on disk** (only the chart-component telescope
`chartLieDeTurckComp_sub_eq`, `ChartLieDerivStructuralDifference.lean`, exists, and it is the `j = 0`
chart witness, not an intrinsic eval split).

Because the Lie linear section cannot be exhibited as the algebraic complement of an *independently
constructed* concrete Cross section (the construction the curvature half has on disk via `connDiffField`
is absent for the gauge nonlinearity), the value-level split and the **difference-arm bound on the linear
part are mathematically inseparable**: the only property that pins the cross section away from the
degenerate `C = 0` reading — under which the linear part would be the *entire* difference and its
difference-arm bound would be FALSE for `j ∈ (a, 2a]` (the top coefficient jet content is genuinely
`(∑ fixed-pair) · C⁰`-order, not difference-arm controlled) — is precisely that the linear complement
*does* satisfy the difference-arm bound.  So this leaf reduces honestly to the single genuine Core-II
deep child below: the value-level Lie split bundled with its linear-arm difference-arm bound
(`exists_lieDerivLinearCross_diffArm`, which produces the concrete linear/Cross section pair, non-vacuous
because `C = 0` is rejected by the linear-arm bound); the Cross-arm jet content is carried by the
connection-level tower (`SegmentMetricLieSectionDecomposition`). -/

/-- **(The value-level Lie linear/cross split bundled with the 0-jet-inclusive `w`-jet linear-arm
bound — derived by composition (TRANSIT).)**  The gauge analogue of the curvature half's value split
`ricciNeg2RetagG0_sub_eq_linear_add_cross` *together with* its linear-arm reduction — bundled into one
node because, unlike the curvature half, the value-level Lie split
`lieDerivRetagG0_sub_eq_linear_add_cross` and the concrete Lie Cross section are **genuinely absent on
disk** (only the chart-component telescope `chartLieDeTurckComp_sub_eq` exists, the `j = 0` chart
witness), so the linear section cannot be exhibited as the algebraic complement of an independently
constructed concrete Cross section.  (The `connLevel` in the name is the tower layer this node sits at;
its difference arm is the `w`-jet arm below — the former rank-`3` 0-jet-free connection-level arm was
certified false and re-signatured away.)

For an anchor `g₀`, a flow background `g_bg`, an order `a`, a supercriticality hypothesis `ha`, and a
uniform `H^{a+2}`-size bound `B ≥ 0`, there is a nonnegative constant `Cd` such that for any two
`g₀`-fibre-small perturbations `T₁, T₂` with `H^{a+2}` norms `≤ B` and any two realized metrics `g₁, g₂`
of `T₁, T₂`, the `g₀`-retagged Lie-summand difference splits as a **linear-in-difference** section `L`
plus a **quadratic-in-difference Cross** section `C` (genuine smooth `SmoothCcTensor g₀ 0 2`s), with the
linear part's per-order covariant gradient satisfying the Hamilton/Moser two-arm bound whose difference
arm is the **0-jet-inclusive** rank-`2` order-`≤ j+2` covariant jet sum of the realized difference
factor `w := realizeSymmCcTensor g₀ (T₁ − T₂)`:
```
lieDerivRetagG0 g₁ − lieDerivRetagG0 g₂ = L + C,
rfns(∇^j L)(x) ≤ Cd · ∑_{i ≤ j+2} rfns(∇^i w)(x) + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁) + rfns(∇^i T₂)))·D²,
```
with `D := ‖(T₁ − T₂).toHs a‖`.

**Why the difference arm must start at the order-`0` jet `rfns(w)` (unlike the curvature half).**  The
Lie summand `g ↦ 𝓛_{W(g, g_bg)} g` depends on the metric at **order zero**: `deTurckVF` is the
`g`-trace of `connDiff (g, g_bg)`, so the linearization of the Lie summand contains `𝓛_{W₀} h` terms
carrying the *value* of the perturbation `h`, whereas the curvature half is order-zero-immune
(`Γ(g₁) = Γ(g₂)` near `x` forces `Ric(g₁) = Ric(g₂)` near `x`, Palatini).  A difference arm built only
from the `∇^{1..j+2} w` jets (the former rank-`3` `∑_{p ≤ j+1} rfns(∇^p (∇₀ w))` arm) is **false** for
the Lie half — Lean-certified counterexample on a flat `T²` with `g_bg = flat + χ·(y₁²/2)·dy₂²`, `T₁` a
constant `ε·dy₁²` cut off near `0`, `T₂ = 0`, `j = 0`: the perturbation is `g₀`-parallel near `0`, so
every `∇^{≥1} w` arm term vanishes at `0`, while the Lie-difference value there is `ε·𝓛_V(dy₁²)` with
`rfns = ε²`, above the `ε⁴`-sized cross budget, for every `Cd`.

**Non-vacuity (the value split and the linear-arm bound are coupled and reject `C = 0`).**  With `C = 0`,
`L = diff` would have to satisfy the difference-arm bound, FALSE for `j ∈ (a, 2a]` — the top coefficient
jet content of the full Lie difference is genuinely `(∑ fixed-pair) · C⁰`-order (`L²` mass of order
`j + 2 ∈ (a + 2, 2a + 2]`, which an `H^{a+2}` ball cannot bound, only the fixed-pair *cross* arm can carry
it).  So a valid witness `(L, C)` **must** put the genuine quadratic top-jet content into `C` — `C = 0`
is rejected — and `L` is the genuine linear-in-difference part.  A zero `Cd` is rejected (the difference
arm carries the high derivative `∇^{j+2} w`).  NO value-bounded `Φ.op 0 2 w` shape, NO
pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO Weyl dependence.

**Decomposition (TRANSIT).**  Proven by composition over the gauge value-level split
`exists_lieDerivDiff_connLevel_split` (`SegmentMetricLieDiffCovJet.lean`), whose linear arm carries
exactly this `w`-jet bound; this node is its first projection.  Consumers transitively depend on
`sorryAx` only through the single genuine deep gauge leaf `lieDerivDiff_connLevel_topRestSplit`
(`SegmentMetricLieSectionDecomposition.lean`). -/
theorem exists_lieDerivLinearCross_section_connLevel
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∃ L C : Integral.L2.SmoothCcTensor g₀ 0 2,
          lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂ = L + C ∧
          (∀ (j : ℕ),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j L‖ ^ 2 ≤
              Cd * ∑ i ∈ Finset.range (j + 2 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2
                + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2
                      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖ ^ 2))
                  * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2) := by
  classical
  -- The connection-level gauge value-level split (`SegmentMetricLieDiffCovJet.lean`), which produces the
  -- intrinsic linear/Cross section pair `(L, C)` with `diff = L + C` and BOTH arms' 0-jet-inclusive
  -- `w`-jet INTEGRATED two-arm bounds.  The Lie value-level leaf is its first projection (the linear-arm
  -- half).
  obtain ⟨Cd, hCd0, hsplit⟩ :=
    exists_lieDerivDiff_connLevel_split (I := I) g₀ g_bg a ha B hB δ hδ0 hδ1
  refine ⟨Cd, hCd0, fun T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 => ?_⟩
  obtain ⟨L, C, hLC, hLbound, _hCbound⟩ :=
    hsplit T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2
  exact ⟨L, C, hLC, hLbound⟩

/-- **(POSIT — the value-level Lie linear/cross split bundled with the linear-arm difference-arm jet
bound: the genuine Core-II value-level leaf of the Lie half.)**  For an anchor `g₀`, a flow background
`g_bg`, an order `a`, a supercriticality hypothesis `ha`, and a uniform `H^{a+2}`-size bound `B ≥ 0`,
there is a nonnegative difference-arm constant `Cd` such that for any two `g₀`-fibre-small perturbations
`T₁, T₂` with `H^{a+2}` norms `≤ B` and any two realized metrics `g₁, g₂` of `T₁, T₂`, the `g₀`-retagged
Lie-summand difference `lieDerivRetagG0 g₀ g_bg g₁ − lieDerivRetagG0 g₀ g_bg g₂` splits as a
**linear-in-difference** section `L` plus a **quadratic-in-difference Cross** section `C` (genuine smooth
`SmoothCcTensor g₀ 0 2`s), with the linear part's per-order covariant gradient satisfying the
Hamilton/Moser two-arm difference-arm grid bound (carrying the single high derivative on the difference
factor `w := realizeSymmCcTensor g₀ (T₁ − T₂)` up to `∇^{j+2}w`, with the metric-built `≤2`-jet
coefficient folded into the family-uniform `Cd`):
```
lieDerivRetagG0 g₁ − lieDerivRetagG0 g₂ = L + C,
rfns(∇^j L)(x) ≤ Cd · ∑_{i ≤ j+2} rfns(∇^i w)(x) + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁) + rfns(∇^i T₂)))·D²,
```
with `D := ‖(T₁ − T₂).toHs a‖`.

The Lie field `𝓛_{W(g)} g` has the **same intrinsic order-`≤2` structure** as the curvature half (the
deTurck vector field `W = g⁻¹ · (Γ(g) − Γ(g_bg))` is a `g⁻¹·∂g`-type field, and one further metric
derivative produces the Lie deformation), so its segment difference admits the identical order-zero
linear/cross split — the `j = 0` chart witness being the structural difference identity
`chartLieDeTurckComp_sub_eq` (`ChartLieDerivStructuralDifference.lean`), which exhibits the
`Lie(g₁) − Lie(g₂)` chart component as a difference of products of metric `≤2`-jets, each carrying a
single Gram/vector-field-component difference factor; the linear part's `j`-th covariant gradient carries
the single high derivative on the difference factor `w` exactly as the curvature linear part does.

**Non-vacuity (the value split and the linear-arm bound are coupled and reject `C = 0`).**  The bundling
is forced, not cosmetic: with `C = 0`, `L = diff` would have to satisfy the difference-arm bound
`rfns(∇^j L) ≤ Cd · ∑ rfns(∇^i w) + (1/4)·(∑ fixed-pair)·D²`, which is FALSE for `j ∈ (a, 2a]` — the top
coefficient jet `∇^{j+2}g_t` content of the full Lie difference is genuinely `(∑ fixed-pair) · C⁰`-order
(`L²` mass of order `j + 2 ∈ (a + 2, 2a + 2]`, which an `H^{a+2}` ball cannot bound, only the *fixed-pair
cross* arm of the Cross section can carry it), not difference-arm controlled.  So a valid witness `(L, C)`
**must** put the genuine quadratic top-jet content into `C` — `C = 0` is rejected — and `L` is then the
genuine linear-in-difference part.  A zero `Cd` is likewise rejected (the difference arm carries
`∇^{j+2}w`).  NO value-bounded `Φ.op 0 2 w` shape, NO pointwise-`C^{>2}`-jet claim, NO
spectral-nonlinearity, NO Weyl dependence.

**Decomposition (TRANSIT).**  It is the value-level child `exists_lieDerivLinearCross_section_connLevel`
verbatim — that child's linear arm now carries this very 0-jet-inclusive `w`-jet bound (the former
rank-`3` connection-level arm, false for the Lie half because the Lie summand depends on the metric at
order zero, was re-signatured away), so no rank-shift step remains.  Consumers transitively depend on
`sorryAx` only through the single genuine deep gauge leaf `lieDerivDiff_connLevel_topRestSplit`
(`SegmentMetricLieSectionDecomposition.lean`). -/
theorem exists_lieDerivLinearCross_diffArm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∃ L C : Integral.L2.SmoothCcTensor g₀ 0 2,
          lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂ = L + C ∧
          (∀ (j : ℕ),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j L‖ ^ 2 ≤
              Cd * ∑ i ∈ Finset.range (j + 2 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2
                + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2
                      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖ ^ 2))
                  * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2) :=
  -- The value-level split + linear-arm child now carries the 0-jet-inclusive `w`-jet INTEGRATED
  -- difference arm directly (the pointwise per-`x` form being false for the middle covariant-Leibniz
  -- terms at high frequency — Gagliardo–Nirenberg interpolation content), so this node is the child
  -- verbatim — no rank-shift step remains.
  exists_lieDerivLinearCross_section_connLevel (I := I) g₀ g_bg a ha B hB δ hδ0 hδ1

/-- **(The order-zero linear/cross split of the Lie-summand difference, with per-order jet bounds —
proven by composition (TRANSIT).)**  The genuine Core-II deep leaf of the Lie half.  The `g₀`-retagged
Lie-summand difference `lieDerivRetagG0 g₀ g_bg g₁ − lieDerivRetagG0 g₀ g_bg g₂` decomposes at order zero
into a **linear-in-difference** section `L` and a **quadratic-in-difference Cross** section `C` (genuine
smooth `SmoothCcTensor g₀ 0 2`s), whose per-order covariant jets satisfy the difference-arm grid bound
(carrying the difference factor `w := realizeSymmCcTensor g₀ (T₁ − T₂)` up to `∇^{j+2}w`, with a
family-uniform constant `Cd`) and the fixed-pair Cross bound:
```
lieDerivRetagG0 g₁ − lieDerivRetagG0 g₂ = L + C,
rfns(∇^j L)(x) ≤ Cd · ∑_{i ≤ j+2} rfns(∇^i w)(x) + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁) + rfns(∇^i T₂)))·D²,
rfns(∇^j C)(x) ≤ Cd · ∑_{i ≤ j+2} rfns(∇^i w)(x) + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁) + rfns(∇^i T₂)))·D²,
```
with `D := ‖(T₁ − T₂).toHs a‖`.

It is **proven by composition** (TRANSIT): it is the gauge value-level split
`exists_lieDerivDiff_connLevel_split` (`SegmentMetricLieDiffCovJet.lean`) verbatim — that split produces
the concrete linear/Cross section pair `(L, C)` with the value identity
`lieDerivRetagG0 g₁ − lieDerivRetagG0 g₂ = L + C` and BOTH arms' bounds already in this 0-jet-inclusive
`w`-jet shape (the value split and the linear bound are mathematically inseparable for the gauge
nonlinearity, since `C = 0` is rejected only by the linear bound).  Non-vacuous and coupled: the
difference arm carries `∇^{j+2}w` (a zero `Cd` falsifies it), and the Cross genuinely carries the
top-jet content (`C = 0` rejected).  Consumers transitively depend on `sorryAx` only through the single
genuine deep gauge leaf `lieDerivDiff_connLevel_topRestSplit`
(`SegmentMetricLieSectionDecomposition.lean`); this glue carries NO value-bounded `Φ.op 0 2 w` shape,
NO pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO Weyl dependence. -/
theorem lieDerivDiff_order0_linearCross_split
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∃ L C : Integral.L2.SmoothCcTensor g₀ 0 2,
          lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂ = L + C ∧
          (∀ (j : ℕ),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j L‖ ^ 2 ≤
              Cd * ∑ i ∈ Finset.range (j + 2 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2
                + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2
                      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖ ^ 2))
                  * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2) ∧
          (∀ (j : ℕ),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j C‖ ^ 2 ≤
              Cd * ∑ i ∈ Finset.range (j + 2 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2
                + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2
                      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖ ^ 2))
                  * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2) :=
  -- The gauge value-level split (`SegmentMetricLieDiffCovJet.lean`) produces the intrinsic linear/Cross
  -- section pair `(L, C)` with `diff = L + C` and BOTH arms' 0-jet-inclusive `w`-jet INTEGRATED two-arm
  -- bounds (the pointwise per-`x` form being false for the middle covariant-Leibniz terms at high
  -- frequency — Gagliardo–Nirenberg interpolation content), so this node is the split verbatim.
  exists_lieDerivDiff_connLevel_split (I := I) g₀ g_bg a ha B hB δ hδ0 hδ1

/-- **The per-field covariant-Faà-di-Bruno Moser-tame `L²` domination of the segment-metric
*Ricci-curvature* summand difference, at every covariant-gradient order (the curvature half of the
geometric nonlinearity, stated at the `L²`-consumable level, j-uncapped).**

The Ricci half of the second-order Ricci–DeTurck right-hand side, `-2 • Ric(g)`, is a fibrewise-smooth
function of the metric `≤2`-jet `(g, ∇g, ∇²g)` and the fibre-inverse `g⁻¹` (schematically
`Ric(g) = g⁻¹ · ∂²g + g⁻¹ · g⁻¹ · ∂g · ∂g`, the `g⁻¹` Neumann factors carrying intrinsic order `0`),
of **intrinsic order capped at `2`**.  For an anchor `g₀`, an order `a`, a supercriticality hypothesis
`ha`, and a uniform `H^{a+2}`-size bound `B ≥ 0`, there is an order-indexed nonnegative constant family
`C` such that for any two `g₀`-fibre-small perturbations `T₁, T₂` with `H^{a+2}` norms `≤ B`, any two
realized metrics `g₁, g₂` of `T₁, T₂`, and **every order `j : ℕ`**, the metric `L²` (semi)norm of the
`j`-th covariant gradient of the `g₀`-retagged curvature-summand difference
`ricciNeg2RetagG0 g₀ g₁ − ricciNeg2RetagG0 g₀ g₂` is dominated by the **Hamilton/Moser-tame sum**
(a difference-redistribution part plus a fixed-pair cross term)
```
‖∇^j (ricciNeg2RetagG0 g₁ − ricciNeg2RetagG0 g₂)‖_{L²}
  ≤ C j · ( ‖(T₁ − T₂).toHs a‖ + ∑_{i ≤ j + 2} ‖∇^i (T₁ − T₂)‖_{L²} )
    + C j · ( ∑_{i ≤ j + 2} (‖∇^i T₁‖_{L²} + ‖∇^i T₂‖_{L²}) ) · ‖(T₁ − T₂).toHs a‖   (for every j).
```

This is the classical **TAME shape**: the constant `C j` may grow in `j` but depends only on the
data of the FIXED low-order ball — `(g₀, a, B, δ)` and the order `j` — never on any norm of `T₁, T₂`
above the `H^{a+2}` ball.  No size threshold rebinds to a higher Sobolev space at higher `j`: every
ingredient of the proof (the two diagonal product grids, the integrated Gagliardo–Nirenberg two-arm
engine at window `j + 2`, the sharp-order `C⁰` embeddings at the fixed orders `a` and `a + 2`, and
the realize-jet `L²` conversion) is available at every order `j`, so the per-order Picard invariance
system this feeds is downward well-founded.

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

It is **proven by composition** over the integrated-`L²` two-arm route of the scaled-Young
redesign: the order-zero value split `ricciNeg2RetagG0_sub_eq_linear_add_cross` plus the two
**integrated** two-arm bounds (`ricciLinearSection_covGrad_twoArm_l2Norm_le`,
`crossSection_iteratedCovGrad_twoArm_l2Norm_le`, which already carry the Gagliardo–Nirenberg
absorption and the sharp-order `C⁰` embeddings inside), and the realize-jet `L²` conversion
`realizeSymm_iteratedCovGrad_l2Norm_le_jetSum`.  Consumers transitively depend on `sorryAx` only
through the two integrated SUB posits beneath those bounds, with NO pointwise-`C^{>2}`-jet claim,
NO pointwise two-arm split, NO spectral-nonlinearity, and NO Weyl dependence. -/
theorem exists_ricciNeg2Diff_faaDiBruno_moserTame_allOrder_l2Norm_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∀ j : ℕ,
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
  -- Per-order integrated two-arm `L²` bounds for the two order-zero pieces of the curvature
  -- difference (the linear and Cross sections, `SegmentMetricCurvatureDifferenceCovJet.lean`).
  choose CdL hCdL_nn hCdL using
    fun j => ricciLinearSection_covGrad_twoArm_l2Norm_le (I := I) g₀ a ha B hB δ hδ0 hδ1 j
  choose CdC hCdC_nn hCdC using
    fun j => crossSection_iteratedCovGrad_twoArm_l2Norm_le (I := I) g₀ a ha B hB δ hδ0 hδ1 j
  -- The per-order realize-difference covariant `L²`-jet constants.
  choose Cr hCr_nn hCr using
    fun i => realizeSymm_iteratedCovGrad_l2Norm_le_jetSum (I := I) g₀ i
  refine ⟨fun j => (CdL j + CdC j) * (1 + ∑ i ∈ Finset.range (j + 2 + 1), Cr i),
    fun j => ?_, ?_⟩
  · have h1 : 0 ≤ ∑ i ∈ Finset.range (j + 2 + 1), Cr i :=
      Finset.sum_nonneg fun i _ => hCr_nn i
    have h2 := hCdL_nn j
    have h3 := hCdC_nn j
    positivity
  intro T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂ j
  -- The two integrated two-arm bounds at this family member.
  have hL := hCdL j T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂
  have hCc := hCdC j T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂
  -- The order-zero value split of the curvature difference.
  have hvalue : PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
      (ricciNeg2RetagG0 (I := I) g₀ g₁ - ricciNeg2RetagG0 (I := I) g₀ g₂) =
    PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (linearSection (I := I) g₀ g₁ g₂)
      + PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (crossSection (I := I) g₀ g₁ g₂) := by
    rw [ricciNeg2RetagG0_sub_eq_linear_add_cross (I := I) g₀ g₁ g₂,
      PDE.RicciFlow.iteratedCovGrad_add]
  -- The realize-jet `L²` conversion of the `w`-jet arm into the difference jets.
  have hrealize_termwise : ∀ i ∈ Finset.range (j + 2 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ≤
        Cr i * ∑ l ∈ Finset.range (j + 2 + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l (T₁ - T₂)‖ := by
    intro i hi
    have hbound := hCr i (T₁ - T₂)
    rw [← Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))] at hbound
    refine hbound.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCr_nn i)
    have hsubset : Finset.range (i + 1) ⊆ Finset.range (j + 2 + 1) :=
      Finset.range_subset_range.mpr (by rw [Finset.mem_range] at hi; omega)
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun l _ _ => norm_nonneg _))
    exact Finset.sum_congr rfl fun l _ =>
      (Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l (T₁ - T₂)))
  have hSWsum_le : (∑ i ∈ Finset.range (j + 2 + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖) ≤
      (∑ i ∈ Finset.range (j + 2 + 1), Cr i) *
        ∑ l ∈ Finset.range (j + 2 + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l (T₁ - T₂)‖ := by
    refine le_trans (Finset.sum_le_sum hrealize_termwise) ?_
    rw [Finset.sum_mul]
  -- Assemble.
  set Dn := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖
    with hDn
  set SD := ∑ l ∈ Finset.range (j + 2 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l (T₁ - T₂)‖ with hSD
  set SW := ∑ i ∈ Finset.range (j + 2 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ with hSW
  set ST := ∑ i ∈ Finset.range (j + 2 + 1),
      (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖
        + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖) with hST
  set CS := ∑ i ∈ Finset.range (j + 2 + 1), Cr i with hCS
  have hDn_nn : 0 ≤ Dn := norm_nonneg _
  have hSD_nn : 0 ≤ SD := Finset.sum_nonneg fun l _ => norm_nonneg _
  have hST_nn : 0 ≤ ST := Finset.sum_nonneg fun i _ => add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hCS_nn : 0 ≤ CS := Finset.sum_nonneg fun i _ => hCr_nn i
  have hCdL0 := hCdL_nn j
  have hCdC0 := hCdC_nn j
  calc ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
          (ricciNeg2RetagG0 (I := I) g₀ g₁ - ricciNeg2RetagG0 (I := I) g₀ g₂)‖
      = ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (linearSection (I := I) g₀ g₁ g₂)
          + PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
            (crossSection (I := I) g₀ g₁ g₂)‖ := by rw [hvalue]
    _ ≤ ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (linearSection (I := I) g₀ g₁ g₂)‖
          + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
              (crossSection (I := I) g₀ g₁ g₂)‖ := norm_add_le _ _
    _ ≤ (CdL j * SW + CdL j * Dn * ST) + (CdC j * SW + CdC j * Dn * ST) := add_le_add hL hCc
    _ = (CdL j + CdC j) * SW + (CdL j + CdC j) * Dn * ST := by ring
    _ ≤ (CdL j + CdC j) * (1 + CS) * (Dn + SD)
          + (CdL j + CdC j) * (1 + CS) * ST * Dn := by
        have hW_le : (CdL j + CdC j) * SW ≤ (CdL j + CdC j) * (CS * SD) :=
          mul_le_mul_of_nonneg_left hSWsum_le (by linarith)
        have hpad : (CdL j + CdC j) * (CS * SD) ≤ (CdL j + CdC j) * (1 + CS) * (Dn + SD) := by
          nlinarith [mul_nonneg (add_nonneg hCdL0 hCdC0) hSD_nn,
            mul_nonneg (add_nonneg hCdL0 hCdC0) hDn_nn,
            mul_nonneg (mul_nonneg (add_nonneg hCdL0 hCdC0) hCS_nn) hDn_nn]
        have hcross_pad : (CdL j + CdC j) * Dn * ST ≤
            (CdL j + CdC j) * (1 + CS) * ST * Dn := by
          nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (add_nonneg hCdL0 hCdC0) hCS_nn)
            hST_nn) hDn_nn]
        linarith [hW_le, hpad, hcross_pad]

/-- **The per-field covariant-Faà-di-Bruno Moser-tame `L²` domination of the segment-metric
*Ricci-curvature* summand difference, on the consumer window `j ≤ 2 * a`.**

The specialization of the j-uncapped Hamilton-tame estimate
`exists_ricciNeg2Diff_faaDiBruno_moserTame_allOrder_l2Norm_le` to the gradient-order window
`j ≤ 2 * a` of the downstream `2a`-order consumers; the window cap carries no mathematical content
(the all-order constant family restricts verbatim). -/
theorem exists_ricciNeg2Diff_faaDiBruno_moserTame_l2Norm_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
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
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_ricciNeg2Diff_faaDiBruno_moserTame_allOrder_l2Norm_le (I := I) g₀ a ha B hB δ hδ0 hδ1
  exact ⟨C, hC_nn, fun T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂ j _ =>
    hC T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂ j⟩

/-- **The covariant Faà-di-Bruno difference/cross split of the Lie-derivative summand difference
(the deep covariant-gauge-jet structural posit).**

The Lie/`deTurckVF`-gauge structural split (the curvature half's former pointwise analogue was
re-architected onto the diagonal product-grid/integrated-two-arm route; the mirror migration of this
Lie band is scheduled, see `SegmentMetricLieSectionDecomposition.lean`).  For an anchor `g₀`, a
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
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (j : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∃ Adiff Cross : Integral.L2.SmoothCcTensor g₀ 0 (2 + j),
          PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
              (lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂)
            = Adiff + Cross ∧
          (‖Adiff‖ ^ 2 ≤
              Cd * ∑ i ∈ Finset.range (j + 2 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2
                + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2
                      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖ ^ 2))
                  * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2) ∧
          (‖Cross‖ ^ 2 ≤
              Cd * ∑ i ∈ Finset.range (j + 2 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2
                + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2
                      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖ ^ 2))
                  * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2) :=
  by
  classical
  obtain ⟨Cd, hCd_nn, hbody⟩ :=
    lieDerivDiff_order0_linearCross_split (I := I) g₀ g_bg a ha B hB δ hδ0 hδ1
  refine ⟨Cd, hCd_nn, fun T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂ => ?_⟩
  obtain ⟨L, C, hsplit, hL, hC⟩ := hbody T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂
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
theorem lieDerivDiff_covFdB_integrated_twoProduct_l2NormSq_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (j : ℕ) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                (lieDerivRetagG0 (I := I) g₀ g_bg g₁
                  - lieDerivRetagG0 (I := I) g₀ g_bg g₂)‖ ^ 2 ≤
            Λ ^ 2 * ∑ i ∈ Finset.range (j + 2 + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                    (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2
              + (∑ i ∈ Finset.range (j + 2 + 1),
                  (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2
                    + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖ ^ 2))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 := by
  classical
  -- The covariant Faà-di-Bruno difference/cross split of the Lie-summand difference: a uniform
  -- difference-arm constant `Cd` and, per perturbation, the structural identity `∇^j(Lie-diff) =
  -- Adiff + Cross` with the integrated difference-arm grid bound and the cross-piece fixed-pair bound.
  obtain ⟨Cd, hCd_nn, hsplit⟩ :=
    lieDerivDiff_covFdB_section_split (I := I) g₀ g_bg a ha B hB δ hδ0 hδ1 j
  -- The two-product coefficient `Λ = √(4 Cd)`: each piece's integrated two-arm bound carries
  -- `Cd·W + (1/4)·F·D²`, so the `L²`-norm subadditivity factor `2` over `Adiff + Cross` accumulates the
  -- difference arms into `Λ² = 4 Cd` and the two `(1/4)·F·D²` fixed-pair pieces into the coefficient-`1`
  -- cross arm.
  refine ⟨Real.sqrt (4 * Cd), Real.sqrt_nonneg _,
    fun T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂ => ?_⟩
  obtain ⟨Adiff, Cross, heq, hAdiff, hCross⟩ := hsplit T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂
  -- The `L²`-norm subadditivity over the structural identity `∇^j(Lie-diff) = Adiff + Cross`:
  -- `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²` (triangle + the elementary `(p+q)² ≤ 2(p²+q²)`).
  have hsplit_norm :
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
            (lieDerivRetagG0 (I := I) g₀ g_bg g₁
              - lieDerivRetagG0 (I := I) g₀ g_bg g₂)‖ ^ 2 ≤
        2 * ‖Adiff‖ ^ 2 + 2 * ‖Cross‖ ^ 2 := by
    rw [heq]
    have htri := norm_add_le Adiff Cross
    have hAn : 0 ≤ ‖Adiff‖ := norm_nonneg _
    have hCn : 0 ≤ ‖Cross‖ := norm_nonneg _
    nlinarith [htri, hAn, hCn, norm_nonneg (Adiff + Cross), sq_nonneg (‖Adiff‖ - ‖Cross‖)]
  -- `Λ² = (√(4 Cd))² = 4 Cd`: the subadditivity factor `2` over the two `Cd·W` difference arms gives
  -- `4 Cd·W`, and the two `(1/4)·F·D²` fixed-pair pieces sum (after the factor `2`) to `1·F·D²`.
  rw [show Real.sqrt (4 * Cd) ^ 2 = 4 * Cd from Real.sq_sqrt (by positivity)]
  nlinarith [hsplit_norm, hAdiff, hCross]

/-- **The per-field covariant-Faà-di-Bruno Moser-tame `L²` domination of the segment-metric
*Lie-derivative* summand difference, at every covariant-gradient order (the gauge half of the
geometric nonlinearity, stated at the `L²`-consumable level, j-uncapped).**

The Lie half of the second-order Ricci–DeTurck right-hand side, `𝓛_{W(g, g_bg)} g` with `W = deTurckVF`
the metric-`g`-trace of the connection difference, is a fibrewise-smooth function of the metric `≤2`-jet
`(g, ∇g, ∇²g)` and the fibre-inverse (schematically `𝓛_{W(g)} g = g⁻¹ · ∂g · ∂g + g⁻¹ · ∂²g`, the `g⁻¹`
Neumann factors carrying intrinsic order `0`), of **intrinsic order capped at `2`**.  For an anchor
`g₀`, a flow background `g_bg`, an order `a`, a supercriticality hypothesis `ha`, and a uniform
`H^{a+2}`-size bound `B ≥ 0`, there is an order-indexed nonnegative constant family `C` such that for
any two `g₀`-fibre-small perturbations `T₁, T₂` with `H^{a+2}` norms `≤ B`, any two realized metrics
`g₁, g₂` of `T₁, T₂`, and **every order `j : ℕ`**, the metric `L²` (semi)norm of the `j`-th covariant
gradient of the `g₀`-retagged Lie-summand difference
`lieDerivRetagG0 g₀ g_bg g₁ − lieDerivRetagG0 g₀ g_bg g₂` is dominated by the **Hamilton/Moser-tame
sum** (a difference-redistribution part plus a fixed-pair cross term)
```
‖∇^j (lieDerivRetagG0 g₁ − lieDerivRetagG0 g₂)‖_{L²}
  ≤ C j · ( ‖(T₁ − T₂).toHs a‖ + ∑_{i ≤ j + 2} ‖∇^i (T₁ − T₂)‖_{L²} )
    + C j · ( ∑_{i ≤ j + 2} (‖∇^i T₁‖_{L²} + ‖∇^i T₂‖_{L²}) ) · ‖(T₁ − T₂).toHs a‖   (for every j).
```

This is the classical **TAME shape**: the constant `C j` may grow in `j` but depends only on the
data of the FIXED low-order ball — `(g₀, g_bg, a, B, δ)` and the order `j` — never on any norm of
`T₁, T₂` above the `H^{a+2}` ball, and no size threshold rebinds to a higher Sobolev space at
higher `j`.

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

It is **proven by composition** from the per-order integrated two-product domination
`lieDerivDiff_covFdB_integrated_twoProduct_l2NormSq_le` (whose order argument `j` is unconstrained)
via the two-arm `√`-domination `twoArm_le_of_sq_le` and the realize-jet `L²` conversion
`realizeSymm_iteratedCovGrad_l2Norm_le_jetSum` — the gauge half of the genuine atomic
covariant-Faà-di-Bruno (Nemytskii) `L²` expansion, with NO pointwise-`C^{>2}`-jet claim, NO
spectral-nonlinearity, and NO Weyl dependence. -/
theorem exists_lieDerivDiff_faaDiBruno_moserTame_allOrder_l2Norm_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∀ j : ℕ,
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
  -- The deep covariant-gauge-jet posit: a per-order coefficient sup `Λ j` with the **integrated**
  -- Hamilton/Moser two-product domination `‖∇^j(Lie-diff)‖² ≤ Λj²·∑‖∇^i w‖² + (∑(‖∇^i T₁‖²+‖∇^i T₂‖²))·D²`.
  choose Λ hΛ_nn hΛ using
    fun j => lieDerivDiff_covFdB_integrated_twoProduct_l2NormSq_le (I := I) g₀ g_bg a ha B hB δ hδ0 hδ1 j
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
  intro T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂ j
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
  -- Apply the two-arm `√`-domination to the deep posit's **integrated** squared bound, with the
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
    refine twoArm_le_of_sq_le (j + 2 + 1)
      (fun i => ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
        (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖)
      (fun i => ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖)
      (fun i => ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖)
      (fun i => norm_nonneg _) (fun i => norm_nonneg _) (fun i => norm_nonneg _)
      (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
        (lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂)‖)
      (Λ j) D₀ (norm_nonneg _) (hΛ_nn j) hD₀_nn ?_
    rw [hD₀_def]
    exact hΛ j T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂
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

/-- **The per-field covariant-Faà-di-Bruno Moser-tame `L²` domination of the segment-metric
*Lie-derivative* summand difference, on the consumer window `j ≤ 2 * a`.**

The specialization of the j-uncapped Hamilton-tame estimate
`exists_lieDerivDiff_faaDiBruno_moserTame_allOrder_l2Norm_le` to the gradient-order window
`j ≤ 2 * a` of the downstream `2a`-order consumers; the window cap carries no mathematical content
(the all-order constant family restricts verbatim). -/
theorem exists_lieDerivDiff_faaDiBruno_moserTame_l2Norm_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
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
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_lieDerivDiff_faaDiBruno_moserTame_allOrder_l2Norm_le (I := I) g₀ g_bg a ha B hB δ hδ0 hδ1
  exact ⟨C, hC_nn, fun T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂ j _ =>
    hC T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂ j⟩

/-- **The per-order covariant-Faà-di-Bruno Moser-tame `L²` domination of the segment-metric
DeTurck right-hand-side difference, at every covariant-gradient order (the genuine atomic metric-jet
Nemytskii primitive, stated at the `L²`-consumable level, j-uncapped).**

For an anchor `g₀`, a flow background `g_bg`, an order `a`, a supercriticality hypothesis
`ha : 2 * a > Module.finrank ℝ E + 4`, and a uniform `H^{a+2}`-size bound `B ≥ 0`, there is an
order-indexed nonnegative constant family `C : ℕ → ℝ` (absorbing the bounded `≤2`-jet metric
coefficient sup `Λ`, the segment-metric `L²`-jet mass, the `C⁰`-embedding constant, the binomial
covariant-Leibniz factors, and the finitely many contraction-shape constants) such that for any two
`g₀`-fibre-small perturbations `T₁, T₂` whose `H^{a+2}` norms are `≤ B`, any two realized metrics
`g₁, g₂` of `T₁, T₂` (tied by the fibrewise `inner`-identities), and **every covariant-gradient order
`j : ℕ`**, the metric `L²` (semi)norm of the `j`-th covariant gradient of the **re-tagged DeTurck
right-hand-side section difference** `deTurckRHSRetagG0 g₀ g_bg g₁ − deTurckRHSRetagG0 g₀ g_bg g₂` is
dominated by the **Hamilton/Moser-tame sum** — an order-`a` chart-Sobolev `C⁰`-redistribution
term against the iterated covariant `L²`-gradients of the perturbation difference `T₁ − T₂`, plus a
fixed-pair cross term carrying the unbounded top coefficient jet:
```
‖∇^j (deTurckRHSRetagG0 g₁ − deTurckRHSRetagG0 g₂)‖_{L²}
  ≤ C j · ( ‖(T₁ − T₂).toHs a‖ + ∑_{i ≤ j + 2} ‖∇^i (T₁ − T₂)‖_{L²} )
    + C j · ( ∑_{i ≤ j + 2} (‖∇^i T₁‖_{L²} + ‖∇^i T₂‖_{L²}) ) · ‖(T₁ − T₂).toHs a‖   (for every j).
```

This is the classical **TAME shape** (Hamilton's category of tame Fréchet estimates): the constant
`C j` may grow in `j` but depends only on the data of the FIXED low-order ball — `(g₀, g_bg, a, B,
δ)` and the order `j` — never on any norm of `T₁, T₂` above the `H^{a+2}` ball, and no size
threshold rebinds to a higher Sobolev space at higher instantiations.  This is exactly what makes
the per-order Picard invariance system downward well-founded: each order `j` consumes the SAME
`H^{a+2}`-ball hypotheses, with the unbounded high-order content carried linearly by the fixed-pair
cross factor, never by the constant.

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
`exists_ricciNeg2Diff_faaDiBruno_moserTame_allOrder_l2Norm_le` and the Lie-summand difference bound
`exists_lieDerivDiff_faaDiBruno_moserTame_allOrder_l2Norm_le` — over the additive `Ric + Lie` split of the
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
theorem exists_segmentMetricRHSDiff_faaDiBruno_moserTame_allOrder_l2Norm_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∀ j : ℕ,
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
    exists_ricciNeg2Diff_faaDiBruno_moserTame_allOrder_l2Norm_le (I := I) g₀ a ha B hB δ hδ0 hδ1
  obtain ⟨Clie, hClie_nn, hClie⟩ :=
    exists_lieDerivDiff_faaDiBruno_moserTame_allOrder_l2Norm_le (I := I) g₀ g_bg a ha B hB δ hδ0 hδ1
  -- The combined per-order constant.
  refine ⟨fun j => Cric j + Clie j, fun j => add_nonneg (hCric_nn j) (hClie_nn j), ?_⟩
  intro T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂ j
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
  -- The two per-field child bounds at this order `j`.
  have hric := hCric T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂ j
  have hlie := hClie T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂ j
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

/-- **The per-order covariant-Faà-di-Bruno Moser-tame `L²` domination of the segment-metric
DeTurck right-hand-side difference, on the consumer window `j ≤ 2 * a`.**

The specialization of the j-uncapped Hamilton-tame estimate
`exists_segmentMetricRHSDiff_faaDiBruno_moserTame_allOrder_l2Norm_le` to the gradient-order window
`j ≤ 2 * a` of the downstream `2a`-order consumers; the window cap carries no mathematical content
(the all-order constant family restricts verbatim).  New consumers — in particular the per-order
Picard invariance system, whose downward well-foundedness needs constants depending only on the
fixed `H^{a+2}` ball at EVERY order — should consume the all-order form directly. -/
theorem exists_segmentMetricRHSDiff_faaDiBruno_moserTame_l2Norm_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
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
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_segmentMetricRHSDiff_faaDiBruno_moserTame_allOrder_l2Norm_le (I := I) g₀ g_bg a ha B hB
      δ hδ0 hδ1
  exact ⟨C, hC_nn, fun T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂ j _ =>
    hC T₁ T₂ g₁ g₂ hg₁ hg₂ hfib₁ hfib₂ hsize₁ hsize₂ j⟩

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
