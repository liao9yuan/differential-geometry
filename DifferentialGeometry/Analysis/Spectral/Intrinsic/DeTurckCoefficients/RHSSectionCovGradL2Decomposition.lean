import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNormReverseOrderZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHSSection
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieSummandLipschitz
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqLeRawComponents
import DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition

/-!
# The covariant `L²`-jet decomposition bound of the realized Ricci–DeTurck RHS section

For a fibre-small smooth perturbation `T` (so that the realized metric
`g_bg + h_sym T = tensorSectionRealizeMetric g_bg T` is a genuine Riemannian metric), the
*genuine geometric Ricci–DeTurck right-hand side* `deTurckRHSSection g_bg (g_bg + h_sym T)`
is a smooth `(0,2)`-tensor section.  Its underlying smooth section, **reanchored** to the
background metric `g_bg` (the metric parameter of a `SmoothCcTensor` is a phantom type
parameter that touches no data field, so reanchoring is a pure rewrap), is the object whose
iterated `g_bg`-covariant gradients `∇^j` the strong-existence assembly differentiates and
takes `L²` norms of.

This file builds the **covariant `L²`-jet Nemytskii decomposition bound** for that section:
on the fibre-small regime the order-`≤ N` covariant `L²` jets of the realized-RHS *difference*
`R̃ T − R̃ T'` are bounded by a fixed multiple of the order-`≤ N + 2` covariant `L²` jets of the
perturbation difference `T − T'`.  The two extra covariant orders are the second-order
quasilinearity of the Ricci–DeTurck right-hand side (the DeTurck vector field `W(g)` carries
`∂g`, so `𝓛_{W(g)} g` carries `∂²g`, and `Ric(g)` carries `∂²g`).

## Mathematical content

`deTurckRicciRHS g_bg g = -2 · Ric(g) + 𝓛_{W(g, g_bg)} g`.  Expanding the iterated covariant
gradient `∇^k` of this section by the covariant Leibniz / Faà-di-Bruno rule produces a finite
sum of products of (chart-Christoffel / DeTurck-coefficient) jet factors of `g = g_bg + h_sym T`
with covariant jets of the perturbation `h_sym T`.  On the fibre-small regime
(`g` uniformly close to `g_bg`) all the Christoffel / inverse-Gram / DeTurck-coefficient
building blocks are uniformly bounded — exactly the `R`-ball uniform regime of
`exists_chartLieDeTurckComp_lipschitz_on_compact` — so the leading coefficient is a single
fibre-small constant `Λ`.  The genuine pointwise differential-geometry input is therefore the
**covariant-Leibniz pointwise domination**

```
‖∇^k (R̃ T − R̃ T')(x)‖² ≤ Λ² · ∑_{i ≤ k + 2} ‖∇^i (T − T')(x)‖²   (∀ x),
```

with `Λ` uniform on the fibre-small ball.  Given that pointwise bound, the global covariant
`L²`-jet inequality is assembled here outright by the finite-sum pointwise-to-`L²` packaging
`tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum`, summed over the jet window — no further
analytic content.

## The consumer

The bound is the analytic core wrapped (cutoff · realize plumbing, and the linear `−Δ_∇ T`
summand) by the strong-existence node `deTurckRemainderOfSection_iteratedCovGrad_l2Norm_lipschitz`
@ `ShortTime/DeTurckRicciStrongExistence.lean`, which feeds the geometric Nemytskii `L²`
Lipschitz `deTurckRicciNsec_diff_oneMinusConnLapIter_l2_lipschitz`.

## Main results

* `deTurckRHSReanchor` — the `g_bg`-reanchored realized-RHS smooth section
  `deTurckRHSSection g_bg (g_bg + h_sym T)`, as a `SmoothCcTensor g_bg 0 2`.
* `deTurckRHSSection_iteratedCovGrad_pointwise_leibniz_domination` (posited TRUE pointwise
  primitive) — the fibre-small covariant-Leibniz pointwise domination of `∇^k (R̃ T − R̃ T')`
  by the order-`≤ k + 2` jets of `T − T'`.
* `deTurckRHSSection_iteratedCovGrad_chartComponent_decomposition` — the headline covariant
  `L²`-jet decomposition bound, assembled from the pointwise primitive.
-/

noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **The `g_bg`-reanchored realized Ricci–DeTurck RHS section.**

For a fibre-small smooth perturbation `T` (`ccTensorBilinSymm T` is `g_bg`-fibre small with
constant `δ < 1`, so `g_bg + h_sym T = tensorSectionRealizeMetric g_bg T` is a genuine metric),
this is the underlying smooth section of `deTurckRHSSection g_bg (g_bg + h_sym T)`, repackaged as
a `SmoothCcTensor g_bg 0 2`.

The metric parameter of `SmoothCcTensor` touches no data field (it is a phantom type parameter,
see `Integral.L2.SmoothCcTensor`), so this rewrap is the section the strong-existence assembly
differentiates with the *background* connection `∇ = ∇^{g_bg}` (the anchor of
`iteratedCovGrad g_bg`).  This matches verbatim the `toSection`/`hasCompactSupport` fields the
`deTurckRemainderOfSection` construction extracts. -/
def deTurckRHSReanchor (g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g_bg 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ) :
    SmoothCcTensor g_bg 0 2 where
  toSection :=
    (deTurckRHSSection (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ)).toSection
  hasCompactSupport :=
    (deTurckRHSSection (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ)).hasCompactSupport

omit [BoundarylessManifold I M] in
/-- The reanchored realized-RHS section carries exactly the section of
`deTurckRHSSection g_bg (g_bg + h_sym T)`. -/
@[simp] theorem deTurckRHSReanchor_toSection (g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g_bg 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ) :
    (deTurckRHSReanchor (I := I) g_bg T hδ_lt hδ).toSection =
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ)).toSection := rfl

/-- **Per-chart covariant Faà-di-Bruno / Leibniz raw-component domination (the genuine
pointwise differential-geometry primitive, localised to one chart of the finite atlas).**

For the *fixed* reanchored realized-RHS difference `S = R̃ T − R̃ T'` and the *fixed*
perturbation difference `Sdiff = T − T'`, a fixed chart base point `α` of the chart atlas
and a covariant order `k`, there is a single constant `Λ ≥ 0` such that, on the closed
support of the chart-atlas partition-of-unity weight at `α`, the sum of squares of the raw
chart-`α`-frame components of the order-`k` covariant gradient `∇^k S` is dominated by `Λ²`
times the order-`≤ k + 2` covariant fibre-norm jets of `Sdiff`:
```
∑_{Idx,Jdx} (tensorChartComponentRaw g_bg 0 (2+k) (∇^k S) α Idx Jdx b)²
  ≤ Λ² · ∑_{i ≤ k+2} ‖∇^i Sdiff(b)‖² .
```

This is the **covariant Faà-di-Bruno expansion** of `∇^k` applied to
`deTurckRicciRHS g_bg g = −2 Ric(g) + 𝓛_{W(g,g_bg)} g`, read in the chart `α`: the chart
component of `∇^k S` is the covariant Leibniz polynomial in the chart Christoffel symbols of
the background metric `g_bg` (uniformly bounded on the compact closed POU support, since
`g_bg` is fixed and smooth) and the Fréchet jets `∂^{≤k}` of the chart components of `S`.  On
the fibre-small regime, those chart-component jets of `S = R̃ T − R̃ T'` are dominated by the
order-`≤ k + 2` chart jets of the metric difference `g₁ − g₂ = h_sym(T − T')` — the second-order
quasilinearity `+2` — through the Christoffel / inverse-Gram / DeTurck-coefficient perturbation
atoms (`exists_chartChristoffel_lipschitz_on_compact`, `exists_chartLieDeTurckComp_lipschitz_on_compact`,
`exists_chartRicciTensor_lipschitz_on_compact`), and the chart jets of `h_sym(T − T')` are in
turn dominated by the intrinsic covariant fibre-norm jets `‖∇^i Sdiff‖`, `i ≤ k + 2`, through
the chart↔covariant fibre-norm bridge (`iteratedFDeriv_rawPull_le_iteratedCovGrad_fibreNorm_uniform`).

The hypotheses constrain only the separate fibre-smallness of `T, T'`; the conclusion is a
pointwise chart-component domination, structurally distinct from any `L²` / spectral
conclusion of the consumers — no packaging. -/
private theorem deTurckRHSReanchor_iteratedCovGrad_rawComponentSq_domination_on_pouTsupport
    (g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g_bg 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ)
    (hδ' : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T') δ)
    (k : ℕ) (α : M) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ b : M,
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        (∑ Idx : Fin 0 → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin (2 + k) → Fin (Module.finrank ℝ E),
            (tensorChartComponentRaw (I := I) (M := M) g_bg 0 (2 + k)
              (iteratedCovGrad (I := I) g_bg 0 2 k
                (deTurckRHSReanchor (I := I) g_bg T hδ_lt hδ -
                  deTurckRHSReanchor (I := I) g_bg T' hδ_lt hδ')) α Idx Jdx b) ^ 2) ≤
          Λ ^ 2 * ∑ i ∈ Finset.range (k + 3),
            riemannianFiberNormSq (I := I) (M := M) g_bg 0 (2 + i) b
              ((iteratedCovGrad (I := I) g_bg 0 2 i (T - T')).toSection b) :=
  sorry

/-- **The fibre-small covariant-Leibniz pointwise domination of the realized Ricci–DeTurck
RHS difference (the genuine pointwise differential-geometry primitive).**

Fix the background metric `g_bg`, two fibre-small perturbations `T, T'` (each `ccTensorBilinSymm`
is `g_bg`-fibre small with a common constant `δ < 1`, so both realized metrics
`g₁ = g_bg + h_sym T`, `g₂ = g_bg + h_sym T'` are genuine), and an order `k`.  There is a
single constant `Λ ≥ 0` — uniform over the fibre-small ball — such that the pointwise
Riemannian fibre-norm-squared of the order-`k` covariant gradient of the *reanchored realized-RHS
difference* `R̃ T − R̃ T'` is dominated by `Λ²` times the order-`≤ k + 2` covariant jets of the
perturbation difference `T − T'`:
```
‖∇^k (R̃ T − R̃ T')(x)‖² ≤ Λ² · ∑_{i ≤ k + 2} ‖∇^i (T − T')(x)‖²   (∀ x).
```

This is the **covariant Faà-di-Bruno / Leibniz expansion** of `∇^k` of
`deTurckRicciRHS g_bg g = -2 Ric(g) + 𝓛_{W(g,g_bg)} g`: each summand carries the top
derivative on the metric-perturbation factor `h_sym(T − T')` (in fibre norm) while the
chart-Christoffel / inverse-Gram / DeTurck-coefficient jet factors of the fibre-small metrics
stay uniformly bounded by `Λ` — exactly the `R`-ball uniform regime of the Christoffel /
DeTurck-coefficient perturbation atoms (`exists_chartChristoffel_lipschitz_on_compact`,
`exists_chartLieDeTurckComp_lipschitz_on_compact`).  The `+2` order budget is the second-order
quasilinearity of the right-hand side (`W(g)` carries `∂g`, so `𝓛_{W(g)} g` carries `∂²g`).

It is assembled here from the **per-chart raw-component domination**
`deTurckRHSReanchor_iteratedCovGrad_rawComponentSq_domination_on_pouTsupport` (the genuine
covariant Faà-di-Bruno content) via the reverse fibre-norm/raw-component bridge
`riemannianFiberNormSq_le_raw_components_on_pouTsupport` and a maximum over the finite chart
atlas `chartAtlasPOU_finset` (every base point lies in the closed POU support of some atlas
chart).

The hypotheses constrain only the *separate* perturbations `T, T'` (their fibre smallness); the
conclusion is a pointwise covariant fibre-norm domination, structurally distinct from any
`L²` / spectral conclusion of the consumers — no packaging. -/
theorem deTurckRHSSection_iteratedCovGrad_pointwise_leibniz_domination
    (g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g_bg 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ)
    (hδ' : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T') δ)
    (k : ℕ) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g_bg 0 (2 + k) x
            ((iteratedCovGrad (I := I) g_bg 0 2 k
              (deTurckRHSReanchor (I := I) g_bg T hδ_lt hδ -
                deTurckRHSReanchor (I := I) g_bg T' hδ_lt hδ')).toSection x) ≤
          Λ ^ 2 * ∑ i ∈ Finset.range (k + 3),
            riemannianFiberNormSq (I := I) (M := M) g_bg 0 (2 + i) x
              ((iteratedCovGrad (I := I) g_bg 0 2 i (T - T')).toSection x) := by
  classical
  set S : SmoothCcTensor g_bg 0 2 :=
    deTurckRHSReanchor (I := I) g_bg T hδ_lt hδ -
      deTurckRHSReanchor (I := I) g_bg T' hδ_lt hδ' with hS_def
  set Sk : SmoothCcTensor g_bg 0 (2 + k) :=
    iteratedCovGrad (I := I) g_bg 0 2 k S with hSk_def
  set R : M → ℝ := fun b => ∑ i ∈ Finset.range (k + 3),
    riemannianFiberNormSq (I := I) (M := M) g_bg 0 (2 + i) b
      ((iteratedCovGrad (I := I) g_bg 0 2 i (T - T')).toSection b) with hR_def
  have hR_nn : ∀ b : M, 0 ≤ R b := by
    intro b
    refine Finset.sum_nonneg (fun i _ => ?_)
    exact riemannianFiberNormSq_nonneg (I := I) (M := M) g_bg 0 (2 + i) b _
  -- Per chart `α` of the finite atlas: the reverse fibre-norm bridge composed with the
  -- posited per-chart covariant-Leibniz raw-component domination produces a single constant
  -- `Kα` with `‖∇^k S(b)‖² ≤ Kα · R b` on the closed POU support of `α`.
  have hperChart : ∀ α : M, ∃ Kα : ℝ, 0 ≤ Kα ∧
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        riemannianFiberNormSq (I := I) (M := M) g_bg 0 (2 + k) b (Sk.toSection b) ≤
          Kα * R b := by
    intro α
    obtain ⟨C, hC_nn, hC⟩ :=
      riemannianFiberNormSq_le_raw_components_on_pouTsupport
        (I := I) (M := M) g_bg 0 (2 + k) α
    obtain ⟨Λ, hΛ_nn, hΛ⟩ :=
      deTurckRHSReanchor_iteratedCovGrad_rawComponentSq_domination_on_pouTsupport
        (I := I) (M := M) g_bg T T' hδ_lt hδ hδ' k α
    refine ⟨C * Λ ^ 2, mul_nonneg hC_nn (sq_nonneg _), ?_⟩
    intro b hb
    have h1 := hC Sk hb
    have h2 := hΛ b hb
    calc riemannianFiberNormSq (I := I) (M := M) g_bg 0 (2 + k) b (Sk.toSection b)
        ≤ C * (∑ Idx : Fin 0 → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin (2 + k) → Fin (Module.finrank ℝ E),
                (tensorChartComponentRaw (I := I) (M := M) g_bg 0 (2 + k)
                  Sk α Idx Jdx b) ^ 2) := h1
      _ ≤ C * (Λ ^ 2 * R b) := by
          refine mul_le_mul_of_nonneg_left ?_ hC_nn
          simpa only [hSk_def, hS_def, hR_def] using h2
      _ = (C * Λ ^ 2) * R b := by ring
  -- Glue over the finite chart atlas: the maximum of the per-chart constants is a single
  -- global constant; each base point lies in the closed POU support of some atlas chart.
  choose! Kα hKα_nn hKα using hperChart
  set Ksum : ℝ := ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Kα α with hKsum_def
  have hKsum_nn : 0 ≤ Ksum := Finset.sum_nonneg (fun α _ => hKα_nn α)
  refine ⟨Real.sqrt Ksum, Real.sqrt_nonneg _, ?_⟩
  intro x
  obtain ⟨α, hα_pos⟩ := (chartAtlasPOU I M).exists_pos_of_mem (Set.mem_univ x)
  have hα_finset : α ∈ chartAtlasPOU_finset (I := I) (M := M) := by
    rw [chartAtlasPOU_finset_mem]
    exact ⟨x, Function.mem_support.mpr (ne_of_gt hα_pos)⟩
  have hx_tsupport : x ∈ tsupport (fun y : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) :=
    subset_tsupport _ (Function.mem_support.mpr (ne_of_gt hα_pos))
  have hsqrt : Real.sqrt Ksum ^ 2 = Ksum := Real.sq_sqrt hKsum_nn
  rw [hsqrt]
  have hKα_le : Kα α ≤ Ksum := by
    rw [hKsum_def]
    exact Finset.single_le_sum (fun β _ => hKα_nn β) hα_finset
  calc riemannianFiberNormSq (I := I) (M := M) g_bg 0 (2 + k) x (Sk.toSection x)
      ≤ Kα α * R x := hKα α hx_tsupport
    _ ≤ Ksum * R x := mul_le_mul_of_nonneg_right hKα_le (hR_nn x)

/-- **The covariant `L²`-jet decomposition bound of the realized Ricci–DeTurck RHS section
(headline).**

For a background metric `g_bg`, two fibre-small smooth perturbations `T, T'` (each
`ccTensorBilinSymm` is `g_bg`-fibre small with a common constant `δ < 1`, so both realized
metrics `g_bg + h_sym T`, `g_bg + h_sym T'` are genuine) and any order `N`, the order-`≤ N`
covariant `L²` jets of the reanchored realized-RHS difference
`R̃ T − R̃ T' = deTurckRHSReanchor g_bg T − deTurckRHSReanchor g_bg T'` are bounded by a fixed
multiple of the order-`≤ N + 2` covariant `L²` jets of the perturbation difference `T − T'`:
```
∑_{j ≤ N} ‖∇^j (R̃ T − R̃ T')‖_{L²} ≤ C · ∑_{i ≤ N + 2} ‖∇^i (T − T')‖_{L²} .
```

This is the genuine higher-order covariant Faà-di-Bruno / Nemytskii decomposition bound for the
second-order quasilinear Ricci–DeTurck right-hand side.  Each covariant order `j ≤ N` is
controlled by the fibre-small covariant-Leibniz pointwise domination
`deTurckRHSSection_iteratedCovGrad_pointwise_leibniz_domination` lifted to `L²` by the finite-sum
pointwise-to-`L²` packaging `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum`; the per-order
bounds are summed over the window `j ∈ range (N + 1)` and the resulting per-order `+2`-windows
are absorbed into the single window `i ∈ range (N + 3)` (monotonicity of the jet sum in non-negative
terms).  The `+2` order budget is the second-order quasilinearity.

The hypotheses constrain only `T, T'`; the conclusion is a covariant-jet `L²` inequality,
structurally distinct from the spectral conclusion of the node it serves — no packaging. -/
theorem deTurckRHSSection_iteratedCovGrad_chartComponent_decomposition
    (g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g_bg 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ)
    (hδ' : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T') δ)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∑ j ∈ Finset.range (N + 1),
          ‖iteratedCovGrad (I := I) g_bg 0 2 j
            (deTurckRHSReanchor (I := I) g_bg T hδ_lt hδ -
              deTurckRHSReanchor (I := I) g_bg T' hδ_lt hδ')‖ ≤
        C * ∑ i ∈ Finset.range (N + 3),
          ‖iteratedCovGrad (I := I) g_bg 0 2 i (T - T')‖ := by
  classical
  set RHSdiff : SmoothCcTensor g_bg 0 2 :=
    deTurckRHSReanchor (I := I) g_bg T hδ_lt hδ -
      deTurckRHSReanchor (I := I) g_bg T' hδ_lt hδ' with hRHSdiff_def
  set Tdiff : SmoothCcTensor g_bg 0 2 := T - T' with hTdiff_def
  -- Per-order: each covariant `L²` jet of the RHS difference is bounded by the order-`≤ j + 2`
  -- jets of the perturbation difference, via the pointwise Leibniz domination + the
  -- pointwise-to-`L²` packaging.
  have hper : ∀ j ∈ Finset.range (N + 1), ∃ Cj : ℝ, 0 ≤ Cj ∧
      ‖iteratedCovGrad (I := I) g_bg 0 2 j RHSdiff‖ ≤
        Cj * ∑ i ∈ Finset.range (N + 3),
          ‖iteratedCovGrad (I := I) g_bg 0 2 i Tdiff‖ := by
    intro j hj
    have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    obtain ⟨Λ, hΛ_nn, hΛ⟩ :=
      deTurckRHSSection_iteratedCovGrad_pointwise_leibniz_domination
        (I := I) (M := M) g_bg T T' hδ_lt hδ hδ' j
    -- Pointwise: the fibre-norm-squared of `∇^j RHSdiff` is dominated by `Λ²` times the order-`≤ j + 2`
    -- jets of `Tdiff`.  Package this into the `L²` bound on the single tensor `∇^j RHSdiff`.
    have hpack :
        ‖iteratedCovGrad (I := I) g_bg 0 2 j RHSdiff‖ ≤
          Λ * ∑ i ∈ Finset.range (j + 3),
            ‖iteratedCovGrad (I := I) g_bg 0 2 i Tdiff‖ := by
      have h :=
        tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g_bg
          (c := 2 + j) (N := j + 3)
          (v := fun i => 2 + i)
          (T := fun i => iteratedCovGrad (I := I) g_bg 0 2 i Tdiff)
          (Curv := iteratedCovGrad (I := I) g_bg 0 2 j RHSdiff)
          (C := Λ) hΛ_nn ?_
      · simpa using h
      · intro x
        exact hΛ x
    -- Drop the per-order `+2` window into the global `N + 3` window (all terms non-negative).
    have hwindow : ∑ i ∈ Finset.range (j + 3),
          ‖iteratedCovGrad (I := I) g_bg 0 2 i Tdiff‖ ≤
        ∑ i ∈ Finset.range (N + 3),
          ‖iteratedCovGrad (I := I) g_bg 0 2 i Tdiff‖ := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => norm_nonneg _)
      exact Finset.range_mono (by omega : j + 3 ≤ N + 3)
    refine ⟨Λ, hΛ_nn, le_trans hpack ?_⟩
    exact mul_le_mul_of_nonneg_left hwindow hΛ_nn
  -- Sum the per-order constants over the finite window `j ∈ range (N + 1)`.
  choose! Cj hCj_nn hCj using hper
  refine ⟨∑ j ∈ Finset.range (N + 1), Cj j,
    Finset.sum_nonneg (fun j hj => hCj_nn j hj), ?_⟩
  calc ∑ j ∈ Finset.range (N + 1),
          ‖iteratedCovGrad (I := I) g_bg 0 2 j RHSdiff‖
      ≤ ∑ j ∈ Finset.range (N + 1),
          Cj j * ∑ i ∈ Finset.range (N + 3),
            ‖iteratedCovGrad (I := I) g_bg 0 2 i Tdiff‖ :=
        Finset.sum_le_sum (fun j hj => hCj j hj)
    _ = (∑ j ∈ Finset.range (N + 1), Cj j) *
          ∑ i ∈ Finset.range (N + 3),
            ‖iteratedCovGrad (I := I) g_bg 0 2 i Tdiff‖ := by
        rw [Finset.sum_mul]

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
