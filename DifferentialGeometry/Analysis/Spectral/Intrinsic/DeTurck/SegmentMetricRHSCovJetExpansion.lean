import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedCovGradJetGeneralOrder
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHSSection
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricRicciDiffOperatorExpansion
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MetricDifferenceFdBTermTree

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
* The two genuine atomic posits are the **per-field covariant-Faà-di-Bruno Moser-tame `L²`
  dominations** of each summand difference: the curvature half
  `exists_ricciNeg2Diff_faaDiBruno_moserTame_l2Norm_le` and the Lie half
  `exists_lieDerivDiff_faaDiBruno_moserTame_l2Norm_le`.  Each is the per-field Nemytskii `L²` estimate
  of one geometric nonlinearity (`Ric`, resp. `𝓛_{deTurckVF} g`), which on a manifold of dimension
  `≥ 4` cannot be reduced to a pointwise `C^{>2}`-jet of the metric (the metric pointwise `C^{>2}`-jet
  does not exist there).  Each is stated **at the `L²`-consumable level**, NOT pointwise: the `j`-th
  covariant gradient's metric `L²` norm is dominated, with a per-order family constant, by the sum of
  an order-`a` chart-Sobolev `C⁰`-redistribution term `‖(T₁ − T₂).toHs a‖` (carrying, through the
  supercritical embedding, the `L^∞` factor on the order-`0` difference that the unbounded top
  coefficient jet multiplies in `L²`) and the order-`≤ j+2` covariant `L²`-jets of the perturbation
  difference `T₁ − T₂` (carrying the high derivative on the difference factor).  Their trap-screened
  design: NO pointwise sup of any order-`>2` metric jet appears (the false-embedding lesson — an
  earlier *pointwise* `rfns` form of these dominations, lacking the `C⁰`-redistribution slot, is FALSE
  for `j ≥ 1` because the covariant-FdB `i = 0` term carries a pointwise-unbounded `∇^{j+2}g_t`
  coefficient over the `H^{a+2}` family; the `L²`-level statement keeps that jet in `L²` against the
  difference's `C⁰` factor, never claiming it pointwise); the per-order constant is a *family* over
  the unbounded gradient order; and the uniform redistribution/jet budget is scoped to the
  supercritical `H^{a+2}`-bounded `B`-family (`ha`).  They carry **no** spectral-nonlinearity,
  perturbation-indexed-remainder, or Weyl dependence.
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
control on the difference factor); consumers transitively depend on `sorryAx` only through the two
posited per-field covariant-Faà-di-Bruno Moser-tame `L²` dominations. -/

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

/-! ### The additive `Ric + Lie` split of the DeTurck right-hand-side section

The genuine first decomposition of the second-order Ricci–DeTurck right-hand side `F(g) =
deTurckRicciRHS g_bg g = -2 • Ric(g) + 𝓛_{W(g, g_bg)} g` into its two *separate* geometric
nonlinearities — the **Ricci-curvature** summand `-2 • Ric(g)` and the **Lie-derivative-of-metric**
summand `𝓛_{W(g, g_bg)} g`.  Both are promoted to genuine smooth compactly-supported `(0,2)`-tensor
sections (`SmoothCcTensor g 0 2`), so the section difference `F(g₁) − F(g₂)` splits additively as
`-2 • (Ric(g₁) − Ric(g₂)) + (Lie(g₁) − Lie(g₂))`.  This is the additive bridge over which the
target's per-order covariant `L²` bound reduces to the two **per-field** covariant-Faà-di-Bruno
`L²` primitives (each a separately-reusable Nemytskii estimate).  Each per-field primitive's bound
is the **Hamilton/Moser tame product** shape: a difference-redistribution part plus a *cross term*
carrying the unbounded top coefficient jet `∇^{j+2}g_t` (order `j + 2 ∈ (a + 2, 2a + 2]`, NOT
controlled by an `H^{a+2}` ball) in `L²` against the difference's `C⁰`/`toHs a` factor — finite on
each fixed `(T₁, T₂)`, ball-bounded only at the terminal absorption (`exists_iteratedCovGrad_l2Norm_le_toHs`
through the `H^{a+2}`-`B`-ball, where the cross-term coefficient collapses into the Lipschitz
constant).  An `H^{a+2}` ball cannot bound an `H^{a+3+}` jet; the cross term is exactly the device
that keeps the bound TRUE while never claiming the top jet pointwise or ball-controlled in isolation. -/

/-- The model `(0,2)`-multilinear value of the **Ricci-tensor** bilinear form `-2 • Ric(g) x`
(the curvature summand of the Ricci–DeTurck right-hand side), via `bilinFormToModel`. -/
private def ricciNeg2ModelFun (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x :=
  Tensor0SSpace.ofModel
    (bilinFormToModel (TangentSpace I x)
      ((-2 : ℝ) • ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x))

private theorem ricciNeg2ModelFun_toModel_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel (ricciNeg2ModelFun (I := I) g x) v =
      ((-2 : ℝ) • ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x)
        (v 0) (v 1) := by
  unfold ricciNeg2ModelFun
  rw [Tensor0SSpace.toModel_ofModel]
  exact bilinFormToModel_apply (TangentSpace I x)
    ((-2 : ℝ) • ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x) v

/-- **The `-2 • Ric(g)` curvature summand is a smooth covariant `(0,2)`-tensor field.**  Its chart
component smoothness is the Ricci chart-component smoothness `chartRicci_affine_in_d2g` scaled by
`-2`. -/
def ricciNeg2Field (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => ricciNeg2ModelFun (I := I) g x, by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b _).mpr
      fun σ x₀ => ?_
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M =>
          (-2 : ℝ) • ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x
            (chartFrameVec (I := I) x₀ (σ 0) x)
            (chartFrameVec (I := I) x₀ (σ 1) x))
        (chartAt H x₀).source :=
      (contMDiffOn_const (c := (-2 : ℝ))).smul
        (chartRicci_affine_in_d2g (I := I)
          (smoothRiemannianMetricToInfty (I := I) g) x₀ (σ 0) (σ 1))
    have hx₀_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
    have hx₀_base : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have h_src_nhd : (chartAt H x₀).source ∈ 𝓝 x₀ :=
      (chartAt H x₀).open_source.mem_nhds hx₀_src
    refine ((hcomp x₀ hx₀_src).contMDiffAt h_src_nhd).congr_of_eventuallyEq ?_
    have h_base_nhd :
        (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 x₀ :=
      (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx₀_base
    filter_upwards [h_base_nhd] with x hx
    rw [continuousMultilinearMap_basis_repr]
    change Tensor0SSpace.toModel (ricciNeg2ModelFun (I := I) g x)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [ricciNeg2ModelFun_toModel_apply]
    simp only [ContinuousLinearMap.smul_apply]
    rfl⟩

/-- The `-2 • Ric(g)` curvature summand as a smooth mixed `(0,2)`-tensor section. -/
def ricciNeg2MixedSection (g : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (ricciNeg2Field (I := I) g)

/-- **The `-2 • Ric(g)` curvature summand as a `SmoothCcTensor g 0 2`.** -/
def ricciNeg2CcSection (g : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 0 2 where
  toSection := ricciNeg2MixedSection (I := I) g
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- **The `𝓛_{W(g, g_bg)} g` Lie-derivative summand as a `SmoothCcTensor g 0 2`.**  Defined as the
algebraic complement `deTurckRHSSection g_bg g − ricciNeg2CcSection g`, so the additive `Ric + Lie`
split `deTurckRHSSection g_bg g = ricciNeg2CcSection g + lieDerivCcSection g_bg g` holds by
construction; its underlying field is `𝓛_{W(g, g_bg)} g` (the deTurck-vector-field Lie deformation),
since `deTurckRHSSection`'s field is `-2 • Ric(g) + 𝓛_{W} g`. -/
def lieDerivCcSection (g_bg g : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 0 2 :=
  deTurckRHSSection (I := I) g_bg g - ricciNeg2CcSection (I := I) g

/-- **The additive `Ric + Lie` split of the DeTurck right-hand-side section.**  The Ricci–DeTurck
right-hand-side section is the sum of its curvature summand `-2 • Ric(g)` and its Lie-derivative
summand `𝓛_{W(g, g_bg)} g` (both genuine `SmoothCcTensor`s). -/
theorem deTurckRHSSection_eq_ricciNeg2_add_lieDeriv (g_bg g : SmoothRiemannianMetric I M) :
    deTurckRHSSection (I := I) g_bg g =
      ricciNeg2CcSection (I := I) g + lieDerivCcSection (I := I) g_bg g := by
  rw [lieDerivCcSection]; abel

/-- **The `g₀`-re-tagged `-2 • Ric(g₁)` curvature summand.**  The curvature summand
`ricciNeg2CcSection g₁` re-tagged from the `g₁` type tag to the `g₀` type tag (a pure type-level
parameter change; the underlying section is unchanged). -/
def ricciNeg2RetagG0 (g₀ g₁ : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 2 :=
  { toSection := (ricciNeg2CcSection (I := I) g₁).toSection
    hasCompactSupport := (ricciNeg2CcSection (I := I) g₁).hasCompactSupport }

/-- **The `g₀`-re-tagged `𝓛_{W(g₁, g_bg)} g₁` Lie-derivative summand.**  The Lie-derivative summand
`lieDerivCcSection g_bg g₁` re-tagged from the `g₁` type tag to the `g₀` type tag. -/
def lieDerivRetagG0 (g₀ g_bg g₁ : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 2 :=
  { toSection := (lieDerivCcSection (I := I) g_bg g₁).toSection
    hasCompactSupport := (lieDerivCcSection (I := I) g_bg g₁).hasCompactSupport }

/-- **The retagged additive `Ric + Lie` split.**  The `g₀`-retagged DeTurck right-hand-side section
splits additively into its `g₀`-retagged curvature and Lie-derivative summands. -/
theorem deTurckRHSRetagG0_eq_ricciNeg2_add_lieDeriv
    (g₀ g_bg g₁ : SmoothRiemannianMetric I M) :
    deTurckRHSRetagG0 (I := I) g₀ g_bg g₁ =
      ricciNeg2RetagG0 (I := I) g₀ g₁ + lieDerivRetagG0 (I := I) g₀ g_bg g₁ := by
  refine Integral.L2.SmoothCcTensor.ext ?_
  have h := congrArg Integral.L2.SmoothCcTensor.toSection
    (deTurckRHSSection_eq_ricciNeg2_add_lieDeriv (I := I) g_bg g₁)
  rw [Integral.L2.SmoothCcTensor.toSection_add] at h
  exact h

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

Its body is `sorry`: the genuine deep covariant-curvature-jet content — the covariant Faà-di-Bruno
expansion of the sealed Ricci nonlinearity, with NO pointwise-`C^{>2}`-jet claim, NO
spectral-nonlinearity, and NO Weyl dependence. -/
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
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 :=
  sorry

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
                  * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ :=
  sorry

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
