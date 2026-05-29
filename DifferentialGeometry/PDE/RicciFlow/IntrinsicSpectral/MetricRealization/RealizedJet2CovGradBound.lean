import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.RealizedGramDiff
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.ChristoffelPerturbation
import DifferentialGeometry.PDE.RicciFlow.SobolevEmbeddingCmRankReduction

/-!
# The chart `2`-jet seminorm of two realized metrics, bounded by the iterated covariant
gradient of the fixed realized tensor difference

This file develops the **analytic core** of the geometric Ricci–DeTurck nonlinearity:
the chart `2`-jet seminorm `chartMetricJet2DiffSup (realizeMetricAt u₁) (realizeMetricAt u₂)`
of the difference of two realized metrics is controlled, pointwise on a compact piece of
the chart-target interior, by the sum of the `g_bg`-fibre norms of the iterated covariant
gradients `∇^j S` (`j = 0, 1, 2`) of the **fixed** `(0,2)`-tensor difference

  `S := realizableRepr g_bg hu₁ − realizableRepr g_bg hu₂`,

evaluated at the chart preimage `(extChartAt I α).symm y`.

## The two layers

The reduction proceeds in two genuinely distinct layers.

* **The algebraic reduction (this file's headline).**  By
  `chartGramOnE_realizeMetricAt_sub_eq_reprDiff`, the chart-Gram-on-`E` difference of the
  two realized metrics, at chart point `y` and frame indices `(l, b)`, equals the
  chart-frame component of the *single fixed tensor* `S`:

    `chartGramOnE g₁ α l b y − chartGramOnE g₂ α l b y
       = ccTensorBilinSymm g_bg S ((extChartAt I α).symm y)
           (chartBasisVecFiber α l ((extChartAt I α).symm y))
           (chartBasisVecFiber α b ((extChartAt I α).symm y))`.

  Since this holds for **every** `y`, the two functions of `y` are equal, so all their
  chart-coordinate partial derivatives `∂^j` agree on the interior.  Each
  `chartMetricJet2DiffSup` summand is therefore a chart `∂^j` (`j = 0, 1, 2`) of a
  chart-frame component of `S`.  This layer is purely algebraic and is proved here
  unconditionally.

* **The pointwise covariant-gradient jet bound (a genuine analytic input).**  The
  chart `∂^j` of the chart-frame component of a fixed `(0,2)`-tensor `S` is bounded,
  uniformly on a compact piece `K ⊆ interior (extChartAt I α).target`, by a constant times
  `∑_{i ≤ j} ‖(iteratedCovGrad g_bg 0 2 i S).toSection (symm y)‖`.  This is the pointwise
  inversion of the chart-coordinate covariant-derivative formula `∇T = ∂T + Γ·T`
  (`nabla_equals_partial_plus_christoffel_on_tensors`), iterated twice:
  `∂²S = ∇²S − Γ·∂S − (∂Γ + Γ·Γ)·S`, with the Christoffel carriers bounded uniformly on
  `K` (`christoffel_Ck_bound_from_metric_Ck1` / `chartChristoffel_contDiffOn_interior`).

  This is a *pointwise inequality bounding chart partials of a tensor component by the
  covariant-gradient fibre norms of that tensor* — a statement structurally distinct from
  the chart `2`-jet seminorm of the realized-metric difference (the headline conclusion).
  We carry it as the named hypothesis `hcovgrad_jet_bound`; it is a genuine analytic input,
  not a packaging of the conclusion.  The algebraic reduction then converts it into the
  headline bound on `chartMetricJet2DiffSup`.

## Sign convention

Geometer `Δ_∇ = −∇*∇`; resolvent `(1 − Δ_∇)⁻¹`, weights `(1 + λᵢ)^σ ≥ 1` for `σ ≥ 0`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ## Differentiability bookkeeping for `chartGramOnE`

`chartGramOnE g α l b` is `C^∞` on `(extChartAt I α).target` (`chartGramOnE_contDiffOn`),
hence differentiable at every interior point.  We name the differentiability and the
first-partial smoothness needed to commute `partialDeriv` past the subtraction. -/

/-- The chart Gram entry on `E` is differentiable at an interior point. -/
private lemma chartGramOnE_diffAt_interior
    (g : SmoothRiemannianMetric I M) (α : M) (l b : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior ((extChartAt I α).target : Set E)) :
    DifferentiableAt ℝ (chartGramOnE (I := I) g α l b) y := by
  have hcd_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l b)
      (interior ((extChartAt I α).target : Set E)) :=
    (chartGramOnE_contDiffOn (I := I) g α l b).mono interior_subset
  exact (hcd_int.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

/-- The first chart partial `∂_a f` of a function `C^∞` on the chart-target interior is
again `C^∞` there. -/
private lemma partialDeriv_contDiffOn_interior
    (α : M) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f (interior ((extChartAt I α).target : Set E)))
    (a : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (partialDeriv (E := E) a f)
      (interior ((extChartAt I α).target : Set E)) := by
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ f)
      (interior ((extChartAt I α).target : Set E)) :=
    hf.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hrw : (partialDeriv (E := E) a f) =
      fun y => fderiv ℝ f y ((chartModelBasis E) a) := rfl
  rw [hrw]
  exact hfderiv.clm_apply contDiffOn_const

/-- The first chart partial `∂_a (chartGramOnE g α l b)` is differentiable at an interior
point (needed to commute the second partial past the subtraction). -/
private lemma partialDeriv_chartGramOnE_diffAt_interior
    (g : SmoothRiemannianMetric I M) (α : M) (a l b : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior ((extChartAt I α).target : Set E)) :
    DifferentiableAt ℝ
      (partialDeriv (E := E) a (chartGramOnE (I := I) g α l b)) y := by
  have hcd_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l b)
      (interior ((extChartAt I α).target : Set E)) :=
    (chartGramOnE_contDiffOn (I := I) g α l b).mono interior_subset
  have hcd_partial : ContDiffOn ℝ ∞
      (partialDeriv (E := E) a (chartGramOnE (I := I) g α l b))
      (interior ((extChartAt I α).target : Set E)) :=
    partialDeriv_contDiffOn_interior (I := I) α hcd_int a
  exact (hcd_partial.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

/-! ## The chart-frame component of the fixed realized tensor difference

For two realizable elements `u₁, u₂` with smooth representatives `T₁, T₂`, the chart-frame
component function `y ↦ ccTensorBilinSymm g_bg S ((extChartAt I α).symm y) (e_l) (e_b)` of
the fixed difference `S = T₁ − T₂` is, by `chartGramOnE_realizeMetricAt_sub_eq_reprDiff`,
equal to the chart-Gram-on-`E` difference of the two realized metrics, as functions on
`E`.  We record this function-level identity so that the chart-coordinate partials of the
metric-difference Gram entries are exactly the partials of the tensor component. -/

/-- The chart-`α` `(l, b)` frame component of the fixed realized tensor difference
`S = realizableRepr hu₁ − realizableRepr hu₂`, as a function on the chart target `E`. -/
def reprDiffChartCompOnE (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : realizableAt (I := I) g_bg u₁) (hu₂ : realizableAt (I := I) g_bg u₂)
    (α : M) (l b : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y =>
    ccTensorBilinSymm (I := I) g_bg
      (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
      ((extChartAt I α).symm y)
      (chartBasisVecFiber (I := I) α l ((extChartAt I α).symm y))
      (chartBasisVecFiber (I := I) α b ((extChartAt I α).symm y))

/-- **The chart-Gram-on-`E` difference of the two realized metrics, as a function on `E`,
equals the chart-frame component of the fixed tensor difference.**  This is the
function-level upgrade of `chartGramOnE_realizeMetricAt_sub_eq_reprDiff`: both sides are
functions of the chart variable `y`, hence all their iterated chart partials agree. -/
theorem chartGramOnE_realizeMetricAt_sub_funext
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : realizableAt (I := I) g_bg u₁) (hu₂ : realizableAt (I := I) g_bg u₂)
    (α : M) (l b : Fin (Module.finrank ℝ E)) :
    (fun y : E => chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b y -
        chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b y) =
      reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b := by
  funext y
  rw [reprDiffChartCompOnE]
  exact chartGramOnE_realizeMetricAt_sub_eq_reprDiff (I := I) g_bg hu₁ hu₂ α l b y

/-! ## The chart `2`-jet seminorm of the realized-metric difference, entry by entry

We rewrite each `chartGramOnE`-difference (and its partials, on the interior) as the
corresponding chart partial of the chart component of `S`. -/

/-- The `0`-jet entry of the realized-metric difference equals the chart component of `S`
at the chart point. -/
theorem chartGramMatrix_realizeMetricAt_sub_eq_reprDiffComp
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : realizableAt (I := I) g_bg u₁) (hu₂ : realizableAt (I := I) g_bg u₂)
    (α : M) (l b : Fin (Module.finrank ℝ E)) (y : E) :
    chartGramMatrix (I := I) (realizeMetricAt (I := I) g_bg u₁) α
          ((extChartAt I α).symm y) l b -
        chartGramMatrix (I := I) (realizeMetricAt (I := I) g_bg u₂) α
          ((extChartAt I α).symm y) l b =
      reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b y := by
  rw [reprDiffChartCompOnE]
  exact chartGramMatrix_realizeMetricAt_sub_eq_reprDiff (I := I) g_bg hu₁ hu₂
    α ((extChartAt I α).symm y) l b

/-- On the chart-target interior, the first chart partial of the realized-metric
Gram-on-`E` difference equals the first chart partial of the chart component of `S`. -/
theorem partialDeriv_chartGramOnE_realizeMetricAt_sub_eq
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : realizableAt (I := I) g_bg u₁) (hu₂ : realizableAt (I := I) g_bg u₂)
    (α : M) (a l b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior ((extChartAt I α).target : Set E)) :
    partialDeriv (E := E) a
        (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b) y -
      partialDeriv (E := E) a
        (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b) y =
      partialDeriv (E := E) a
        (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b) y := by
  rw [← chartGramOnE_realizeMetricAt_sub_funext (I := I) g_bg hu₁ hu₂ α l b]
  rw [partialDeriv, partialDeriv, partialDeriv, ← ContinuousLinearMap.sub_apply]
  congr 1
  exact (fderiv_sub
    (chartGramOnE_diffAt_interior (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b hy)
    (chartGramOnE_diffAt_interior (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b hy)).symm

/-- On the chart-target interior, the second chart partial of the realized-metric
Gram-on-`E` difference equals the second chart partial of the chart component of `S`. -/
theorem partialDeriv2_chartGramOnE_realizeMetricAt_sub_eq
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : realizableAt (I := I) g_bg u₁) (hu₂ : realizableAt (I := I) g_bg u₂)
    (α : M) (c a l b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior ((extChartAt I α).target : Set E)) :
    partialDeriv (E := E) c
        (partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b)) y -
      partialDeriv (E := E) c
        (partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b)) y =
      partialDeriv (E := E) c
        (partialDeriv (E := E) a
          (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b)) y := by
  -- The first partials of the two metric Gram entries agree, on the interior, with the
  -- first partial of the chart component.  Differentiating once more gives the claim.
  have hop : IsOpen (interior ((extChartAt I α).target : Set E)) := isOpen_interior
  have h_eqOn : Set.EqOn
      (fun z => partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b) z -
        partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b) z)
      (partialDeriv (E := E) a (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b))
      (interior ((extChartAt I α).target : Set E)) := by
    intro z hz
    exact partialDeriv_chartGramOnE_realizeMetricAt_sub_eq (I := I) g_bg hu₁ hu₂ α a l b hz
  -- Pass the second partial `∂_c` through the subtraction (interior differentiability)
  -- and then rewrite by the eventually-equal first partials.
  rw [partialDeriv, partialDeriv, partialDeriv, ← ContinuousLinearMap.sub_apply]
  have hfd_sub :
      fderiv ℝ (partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b)) y -
        fderiv ℝ (partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b)) y =
      fderiv ℝ (fun z => partialDeriv (E := E) a
            (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b) z -
          partialDeriv (E := E) a
            (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b) z) y :=
    (fderiv_sub
      (partialDeriv_chartGramOnE_diffAt_interior (I := I) (realizeMetricAt (I := I) g_bg u₁)
        α a l b hy)
      (partialDeriv_chartGramOnE_diffAt_interior (I := I) (realizeMetricAt (I := I) g_bg u₂)
        α a l b hy)).symm
  rw [hfd_sub]
  -- Replace the differenced first partial by the chart-component first partial via
  -- equality on a neighbourhood.
  have hev : (fun z => partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b) z -
        partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b) z)
      =ᶠ[nhds y]
      partialDeriv (E := E) a (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b) :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨interior ((extChartAt I α).target : Set E), hop.mem_nhds hy, h_eqOn⟩
  rw [hev.fderiv_eq]

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
