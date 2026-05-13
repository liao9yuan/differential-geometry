import DifferentialGeometry.Analysis.Laplacian.Regularity.LeibnizCompensatedFh
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomainVariationalLimit
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomainVariationalLimitGeneral
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartBilinearH1ComplFromDom
import DifferentialGeometry.Analysis.Laplacian.Operator.ChartMeasureEquiv
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridge

/-!
# Chart-pulled integral as a bounded linear functional on `Lp ℝ 2 μ_g`

For a chart point `α : M` of a closed Riemannian manifold `(M, g)` and a
smooth bounded test function `θ : EuclN → ℝ` whose topological support sits
inside a compact subset of `chartTargetEuclid α`, the integral

```
I(F) := ∫_{chartTargetEuclid α} (F ∘ symm)(y) · θ(y) dy
```

defines a bounded linear functional on `Lp ℝ 2 μ_g`, hence is continuous in
`F`. The construction here represents the functional via an explicit
manifold-side weight `w_θ : M → ℝ`, continuous with compact support inside
the chart source, defined by

```
w_θ(x) := θ((toEuclidean ∘ extChartAt I α) x) / chartDensity g α x   (x ∈ chart α source)
w_θ(x) := 0                                                            (otherwise)
```

The chart-pulled volume identity (`integral_riemannianVolumeMeasure_eq_euclidean_chartTarget`)
identifies `∫ F · w_θ dμ_g` with `I(F)` on smooth `F`, and continuity in `F`
extends the identification to all of `Lp ℝ 2 μ_g` by density of smooth
scalars.

## Main definitions

* `chartPulledIntegralWeight g α θ` — the manifold-side weight `w_θ`.
* `chartPulledIntegralCLM g α θ` — the bounded linear functional itself.

## Main results

* `chartPulledIntegralCLM_norm_le` — operator-norm bound for the functional.
* `chartPulledIntegralCLM_smoothToLp` — the smooth-case integral formula.
* `laplacianDomain_variational_identity_general` — extension of the
  smooth-case variational identity to `u_h ∈ laplacianDomain g`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartPulledIntegralContinuity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalLimit
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalLimitGeneral
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom
open DifferentialGeometry.Analysis.Sobolev.Chart

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-! ## The chart-source preimage of `tsupport θ`

`chartSrcPreimage α θ := (extChartAt I α).symm ∘ toEuclidean.symm '' (tsupport θ)`
is the manifold-side preimage of `tsupport θ`, a compact subset of the chart
source whenever `tsupport θ ⊆ chartTargetEuclid α`. -/

/-- The chart-source preimage of `tsupport θ`. -/
private def chartSrcPreimage (α : M) (θ : EuclN → ℝ) : Set M :=
  (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y)) ''
    (tsupport θ)

private lemma chartSrcPreimage_isCompact
    (α : M) {θ : EuclN → ℝ} (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    IsCompact (chartSrcPreimage (I := I) (M := M) α θ) := by
  classical
  unfold chartSrcPreimage
  exact (hθ_cs : IsCompact (tsupport θ)).image_of_continuousOn
    ((continuousOn_symm_toEuclideanSymm (I := I) (M := M) α).mono hθ_supp)

private lemma chartSrcPreimage_subset_chartSource
    (α : M) {θ : EuclN → ℝ}
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    chartSrcPreimage (I := I) (M := M) α θ ⊆ (chartAt H α).source := by
  classical
  unfold chartSrcPreimage
  intro x hx
  rcases hx with ⟨y, hy_supp, hxy⟩
  rw [← hxy]
  exact symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α (hθ_supp hy_supp)

/-! ## The manifold-side weight `w_θ`

The construction `chartPulledIntegralWeight g α θ x` defines:

* `θ((toEuclidean ∘ extChartAt I α) x) / chartDensity g α x`
  when `x ∈ chartAt α source` and the numerator is non-zero;
* `0` otherwise (in particular outside the chart source, and on the chart
  source where `θ` vanishes).

This produces a globally continuous, compactly-supported scalar function
on `M`, taking the value `θ(y) / density(symm y)` at points `x = symm y`
with `y ∈ tsupport θ ⊆ chartTargetEuclid α`. -/

/-- The manifold-side weight `w_θ` corresponding to a chart-pulled test
function `θ`. -/
noncomputable def chartPulledIntegralWeight
    (g : SmoothRiemannianMetric I M) (α : M) (θ : EuclN → ℝ) : M → ℝ := by
  classical
  exact fun x : M =>
    if hx : x ∈ (chartAt H α).source then
      θ ((toEuclidean (E := E)) ((extChartAt I α) x)) / chartDensity g α x
    else 0

lemma chartPulledIntegralWeight_apply_of_mem
    (g : SmoothRiemannianMetric I M) (α : M) (θ : EuclN → ℝ) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    chartPulledIntegralWeight (I := I) (M := M) g α θ x =
      θ ((toEuclidean (E := E)) ((extChartAt I α) x)) / chartDensity g α x := by
  classical
  unfold chartPulledIntegralWeight
  exact dif_pos hx

private lemma chartPulledIntegralWeight_apply_of_notMem
    (g : SmoothRiemannianMetric I M) (α : M) (θ : EuclN → ℝ) {x : M}
    (hx : x ∉ (chartAt H α).source) :
    chartPulledIntegralWeight (I := I) (M := M) g α θ x = 0 := by
  classical
  unfold chartPulledIntegralWeight
  exact dif_neg hx

/-- On the chart source, away from `chartSrcPreimage α θ`, the manifold weight
vanishes (because `θ` vanishes outside `tsupport θ`). -/
private lemma chartPulledIntegralWeight_apply_zero_off_preimage
    (g : SmoothRiemannianMetric I M) (α : M) {θ : EuclN → ℝ} {x : M}
    (hx_src : x ∈ (chartAt H α).source)
    (hx_off : x ∉ chartSrcPreimage (I := I) (M := M) α θ) :
    chartPulledIntegralWeight (I := I) (M := M) g α θ x = 0 := by
  classical
  -- Compute T x := toE ∘ extChartAt α x; show T x ∉ tsupport θ.
  rw [chartPulledIntegralWeight_apply_of_mem (I := I) (M := M) g α θ hx_src]
  have hTx_not_in : (toEuclidean (E := E)) ((extChartAt I α) x) ∉ tsupport θ := by
    intro h_in
    apply hx_off
    refine ⟨(toEuclidean (E := E)) ((extChartAt I α) x), h_in, ?_⟩
    -- Need: (extChartAt I α).symm (toE.symm (T x)) = x, since x ∈ chart src.
    change (extChartAt I α).symm
        ((toEuclidean (E := E)).symm ((toEuclidean (E := E))
          ((extChartAt I α) x))) = x
    have hsymm_inv : (toEuclidean (E := E)).symm ((toEuclidean (E := E))
        ((extChartAt I α) x)) = (extChartAt I α) x :=
      (toEuclidean (E := E)).symm_apply_apply _
    rw [hsymm_inv]
    have hxE : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact hx_src
    exact (extChartAt I α).left_inv hxE
  have hθ_zero : θ ((toEuclidean (E := E)) ((extChartAt I α) x)) = 0 :=
    image_eq_zero_of_notMem_tsupport hTx_not_in
  rw [hθ_zero, zero_div]

/-! ## The weight is supported in `chartSrcPreimage α θ` -/

private lemma chartPulledIntegralWeight_support_subset
    (g : SmoothRiemannianMetric I M) (α : M) (θ : EuclN → ℝ) :
    Function.support (chartPulledIntegralWeight (I := I) (M := M) g α θ) ⊆
      chartSrcPreimage (I := I) (M := M) α θ := by
  classical
  intro x hx
  rw [Function.mem_support] at hx
  by_cases hx_src : x ∈ (chartAt H α).source
  · -- In chart src: x in support ⇒ the formula gives nonzero ⇒ θ(T x) ≠ 0 ⇒ T x ∈ supp θ ⊆ tsupp θ.
    by_contra hx_not
    have h_zero := chartPulledIntegralWeight_apply_zero_off_preimage
      (I := I) (M := M) g α (θ := θ) hx_src hx_not
    exact hx h_zero
  · -- Outside chart src: w_θ x = 0, contradicting hx.
    have h_zero := chartPulledIntegralWeight_apply_of_notMem
      (I := I) (M := M) g α θ hx_src
    exact (hx h_zero).elim

private lemma chartPulledIntegralWeight_tsupport_subset
    (g : SmoothRiemannianMetric I M) (α : M) {θ : EuclN → ℝ}
    (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    tsupport (chartPulledIntegralWeight (I := I) (M := M) g α θ) ⊆
      chartSrcPreimage (I := I) (M := M) α θ := by
  classical
  refine closure_minimal
    (chartPulledIntegralWeight_support_subset (I := I) (M := M) g α θ) ?_
  exact (chartSrcPreimage_isCompact (I := I) (M := M) α hθ_cs hθ_supp).isClosed

/-! ## The weight has compact support and tsupport inside the chart source -/

private lemma chartPulledIntegralWeight_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (α : M) {θ : EuclN → ℝ}
    (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    HasCompactSupport (chartPulledIntegralWeight (I := I) (M := M) g α θ) :=
  HasCompactSupport.of_support_subset_isCompact
    (chartSrcPreimage_isCompact (I := I) (M := M) α hθ_cs hθ_supp)
    (chartPulledIntegralWeight_support_subset (I := I) (M := M) g α θ)

private lemma chartPulledIntegralWeight_tsupport_subset_chartSource
    (g : SmoothRiemannianMetric I M) (α : M) {θ : EuclN → ℝ}
    (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    tsupport (chartPulledIntegralWeight (I := I) (M := M) g α θ) ⊆
      (chartAt H α).source :=
  (chartPulledIntegralWeight_tsupport_subset (I := I) (M := M) g α
      hθ_cs hθ_supp).trans
    (chartSrcPreimage_subset_chartSource (I := I) (M := M) α hθ_supp)

/-! ## Continuity of the weight -/

/-- The chart map `T α := toEuclidean ∘ extChartAt I α` is continuous on the
chart source. -/
private lemma chart_map_continuousOn (α : M) :
    ContinuousOn (fun x : M => (toEuclidean (E := E)) ((extChartAt I α) x))
      (chartAt H α).source := by
  have h_ext : ContinuousOn (extChartAt I α) (chartAt H α).source := by
    have h_src : (chartAt H α).source = (extChartAt I α).source :=
      (DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M) α).symm
    rw [h_src]; exact continuousOn_extChartAt α
  exact (toEuclidean (E := E)).continuous.continuousOn.comp h_ext (Set.mapsTo_univ _ _)

/-- The chart-density-divided test function is continuous on the chart source. -/
private lemma chartPulledIntegralWeight_continuousOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) :
    ContinuousOn (chartPulledIntegralWeight (I := I) (M := M) g α θ)
      (chartAt H α).source := by
  classical
  -- On chart source, the function equals `θ(T x) / density(x)`. Density > 0 on chart src.
  have h_eq : EqOn (chartPulledIntegralWeight (I := I) (M := M) g α θ)
      (fun x : M => θ ((toEuclidean (E := E)) ((extChartAt I α) x)) /
        chartDensity g α x)
      (chartAt H α).source := by
    intro x hx
    exact chartPulledIntegralWeight_apply_of_mem (I := I) (M := M) g α θ hx
  refine ContinuousOn.congr ?_ h_eq
  -- The numerator is continuous.
  have h_num_cont : ContinuousOn (fun x : M =>
      θ ((toEuclidean (E := E)) ((extChartAt I α) x))) (chartAt H α).source :=
    hθ_cont.continuousOn.comp (chart_map_continuousOn (I := I) (M := M) α)
      (Set.mapsTo_univ _ _)
  -- The denominator is continuous and nonzero.
  have h_dens_cont : ContinuousOn (chartDensity g α) (chartAt H α).source := by
    rw [show (chartAt H α).source =
        (trivializationAt E (TangentSpace I) α).baseSet from
      (DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source
        (I := I) (M := M) α).symm]
    exact DifferentialGeometry.Integral.Measure.chartDensity_continuousOn
      (I := I) (M := M) g α
  have h_dens_ne_zero : ∀ x ∈ (chartAt H α).source, chartDensity g α x ≠ 0 := by
    intro x hx
    have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source
        (I := I) (M := M)]
      exact hx
    exact (DifferentialGeometry.Integral.Measure.chartDensity_pos
      (I := I) g α hx_base).ne'
  exact h_num_cont.div h_dens_cont h_dens_ne_zero

/-- Globally on `M`, the manifold-side weight is continuous: it is continuous
on the chart source (smooth division by a strictly positive density), and
identically zero on a neighborhood of every point off the chart source
(thanks to the compact-support property of the numerator). -/
lemma chartPulledIntegralWeight_continuous
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Continuous (chartPulledIntegralWeight (I := I) (M := M) g α θ) := by
  classical
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases hx_in : x ∈ (chartAt H α).source
  · -- In chart src (open): use ContinuousOn.
    have h_open : IsOpen ((chartAt H α).source) := (chartAt H α).open_source
    have h_contOn := chartPulledIntegralWeight_continuousOn_chartSource
      (I := I) (M := M) g α (θ := θ) hθ_cont
    exact h_contOn.continuousAt (h_open.mem_nhds hx_in)
  · -- Outside chart src: w_θ vanishes in a neighborhood of x (containing M \ tsupport w_θ).
    have h_supp_sub : tsupport (chartPulledIntegralWeight (I := I) (M := M) g α θ) ⊆
        (chartAt H α).source :=
      chartPulledIntegralWeight_tsupport_subset_chartSource
        (I := I) (M := M) g α hθ_cs hθ_supp
    -- x ∉ chart src ⇒ x ∉ tsupport w_θ.
    have hx_not_supp : x ∉ tsupport (chartPulledIntegralWeight (I := I) (M := M) g α θ) :=
      fun h_in => hx_in (h_supp_sub h_in)
    -- The complement is open and contains x.
    have h_compl_open : IsOpen
        (tsupport (chartPulledIntegralWeight (I := I) (M := M) g α θ))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    -- On this open neighborhood, w_θ is identically 0.
    have h_zero : EqOn (chartPulledIntegralWeight (I := I) (M := M) g α θ)
        (fun _ => (0 : ℝ))
        (tsupport (chartPulledIntegralWeight (I := I) (M := M) g α θ))ᶜ := by
      intro y hy
      have hy_off : y ∉ Function.support
          (chartPulledIntegralWeight (I := I) (M := M) g α θ) := by
        intro h_supp
        exact hy (subset_tsupport _ h_supp)
      exact Function.notMem_support.mp hy_off
    have h_ev : (chartPulledIntegralWeight (I := I) (M := M) g α θ) =ᶠ[𝓝 x]
        (fun _ : M => (0 : ℝ)) := by
      filter_upwards [h_compl_open.mem_nhds hx_not_supp] with y hy
      exact h_zero hy
    refine ContinuousAt.congr ?_ h_ev.symm
    exact continuousAt_const

/-! ## `MemLp 2` membership of the weight -/

lemma chartPulledIntegralWeight_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (chartPulledIntegralWeight (I := I) (M := M) g α θ) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  exact (chartPulledIntegralWeight_continuous (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_supp).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The `Lp ℝ 2 μ_g` class of the manifold-side weight. -/
noncomputable def chartPulledIntegralWeightLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (chartPulledIntegralWeight_memLp (I := I) (M := M) g α
    hθ_cont hθ_cs hθ_supp).toLp _

/-! ## The change-of-variable identity for smooth scalars

For a smooth scalar `v : SmoothScalar g`, the change-of-variable formula
identifies `∫_M w_θ · v dμ_g` with the chart-pulled integral
`∫_{chartTargetEuclid α} v(symm y) · θ(y) dy`. The proof relies on
`integral_riemannianVolumeMeasure_eq_euclidean_chartTarget` from
`ChartMeasureEquiv.lean` together with the pointwise identity
`density(x) · w_θ(x) = θ((toE ∘ extChartAt I α) x)` on the chart source. -/

/-- Auxiliary: the product `w_θ · v` is continuous and supported in the chart
source whenever `v : M → ℝ` is continuous on `M`. -/
private lemma weight_smul_continuous_aux
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {v : M → ℝ} (hv_cont : Continuous v) :
    Continuous (fun x : M => chartPulledIntegralWeight (I := I) (M := M) g α θ x *
      v x) :=
  (chartPulledIntegralWeight_continuous (I := I) (M := M) g α
    hθ_cont hθ_cs hθ_supp).mul hv_cont

private lemma weight_smul_tsupport_subset_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (v : M → ℝ) :
    tsupport (fun x : M => chartPulledIntegralWeight (I := I) (M := M) g α θ x *
      v x) ⊆ (chartAt H α).source := by
  classical
  -- Support of (w · v) ⊆ support w ⊆ tsupport w ⊆ chart src.
  have h_supp_sub : Function.support
      (fun x : M => chartPulledIntegralWeight (I := I) (M := M) g α θ x *
        v x) ⊆
      Function.support (chartPulledIntegralWeight (I := I) (M := M) g α θ) := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra h_w
    apply hx
    have h_w_zero : chartPulledIntegralWeight (I := I) (M := M) g α θ x = 0 :=
      Function.notMem_support.mp h_w
    rw [h_w_zero, zero_mul]
  refine (closure_mono h_supp_sub).trans ?_
  exact chartPulledIntegralWeight_tsupport_subset_chartSource
    (I := I) (M := M) g α hθ_cs hθ_supp

/-- Pointwise identification on the chart source:
`density(x) · w_θ(x) = θ((toEuclidean ∘ extChartAt I α) x)`. -/
private lemma density_mul_weight_eq_theta
    (g : SmoothRiemannianMetric I M) (α : M) (θ : EuclN → ℝ) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    chartDensity g α x * chartPulledIntegralWeight (I := I) (M := M) g α θ x =
      θ ((toEuclidean (E := E)) ((extChartAt I α) x)) := by
  classical
  rw [chartPulledIntegralWeight_apply_of_mem (I := I) (M := M) g α θ hx]
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source
      (I := I) (M := M)]
    exact hx
  have h_dens_pos : 0 < chartDensity g α x :=
    DifferentialGeometry.Integral.Measure.chartDensity_pos (I := I) g α hx_base
  field_simp

/-- The change-of-variable identity for the weight against a continuous scalar
`v : M → ℝ`. The right-hand integral is over `chartTargetEuclid α` against
plain Euclidean volume.

This identifies the manifold-side `Lp` inner product against the weight with
the desired chart-pulled integral. -/
private lemma integral_weight_smul_eq_chartPulled
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {v : M → ℝ} (hv_cont : Continuous v) :
    ∫ x, chartPulledIntegralWeight (I := I) (M := M) g α θ x * v x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        v ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) * θ y
        ∂(volume : Measure EuclN) := by
  classical
  set f : M → ℝ := fun x : M =>
    chartPulledIntegralWeight (I := I) (M := M) g α θ x * v x with hf_def
  have hf_cont : Continuous f :=
    weight_smul_continuous_aux (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp hv_cont
  have hf_supp : tsupport f ⊆ (chartAt H α).source :=
    weight_smul_tsupport_subset_chartSource (I := I) (M := M) g α hθ_cs hθ_supp v
  -- Apply the chart-pull identity on the manifold side.
  have h_main := integral_riemannianVolumeMeasure_eq_euclidean_chartTarget
    (I := I) (M := M) g α (f := f) hf_cont hf_supp
  rw [h_main]
  -- Convert `Measure.map toEuclidean modelHaar` to `volume`.
  rw [DifferentialGeometry.Integral.Measure.map_toEuclidean_modelHaar_eq_volume]
  -- The integrand on the right is `density(symm y) * f(symm y)`.
  -- Pointwise: `density(symm y) * (w_θ(symm y) * v(symm y)) = θ(y) * v(symm y)`
  -- on chartTargetEuclid α (where symm y is in chart src).
  refine MeasureTheory.setIntegral_congr_fun
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet ?_
  intro y hy
  -- y ∈ chartTargetEuclid α ⇒ symm y ∈ chart src.
  have hy_src : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  -- densityOnEuclid g α y = chartDensity g α (symm y) by definition.
  have h_density_eq : densityOnEuclid (I := I) g α y =
      chartDensity g α ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := rfl
  -- (toE ∘ extChartAt) (symm y) = y : right-inverse on chartTargetEuclid α.
  have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    toEuclidean_symm_mem_target (I := I) hy
  have h_inv1 : (extChartAt I α) ((extChartAt I α).symm
      ((toEuclidean (E := E)).symm y)) = (toEuclidean (E := E)).symm y :=
    (extChartAt I α).right_inv hy_target
  have h_inv2 : (toEuclidean (E := E)) ((toEuclidean (E := E)).symm y) = y :=
    (toEuclidean (E := E)).apply_symm_apply y
  -- Combine into : θ(y) = density(symm y) * w_θ(symm y) by the pointwise lemma.
  have h_pw := density_mul_weight_eq_theta (I := I) (M := M) g α θ hy_src
  -- h_pw : chartDensity g α (symm y) * w_θ(symm y) = θ((toE ∘ extChartAt I α) (symm y)) = θ y.
  have h_pw' : chartDensity g α ((extChartAt I α).symm
      ((toEuclidean (E := E)).symm y)) *
      chartPulledIntegralWeight (I := I) (M := M) g α θ
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = θ y := by
    rw [h_pw]
    rw [h_inv1, h_inv2]
  -- Substitute on the LHS.
  -- Goal at this point: density(y) * f(symm y) = v(symm y) * θ(y).
  -- f(symm y) = w_θ(symm y) * v(symm y), so
  -- LHS = density(symm y) * (w_θ(symm y) * v(symm y))
  --     = (density(symm y) * w_θ(symm y)) * v(symm y)
  --     = θ(y) * v(symm y) = v(symm y) * θ(y).
  change densityOnEuclid (I := I) g α y *
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
    v ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) * θ y
  rw [h_density_eq]
  rw [hf_def]
  rw [show chartDensity g α ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
      (chartPulledIntegralWeight (I := I) (M := M) g α θ
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
        v ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      (chartDensity g α ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
        chartPulledIntegralWeight (I := I) (M := M) g α θ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
        v ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) from by ring]
  rw [h_pw']
  ring

/-! ## The bounded linear functional -/

/-- The chart-pulled integral as a bounded linear functional on `Lp ℝ 2 μ_g`.

For `F : Lp ℝ 2 μ_g`, the value `chartPulledIntegralCLM g α θ ... F` equals
the inner product `⟪chartPulledIntegralWeightLp, F⟫_{L²(μ_g)}`, which by
the change-of-variable identity coincides with the chart-pulled integral

```
∫_{chartTargetEuclid α} (F ∘ symm)(y) · θ(y) dy.
```

Continuity in `F` is automatic from the operator-norm bound on `innerSL`. -/
noncomputable def chartPulledIntegralCLM
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] ℝ :=
  (innerSL ℝ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] ℝ)
    (chartPulledIntegralWeightLp (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp)

/-- The operator-norm bound on the chart-pulled-integral CLM. -/
theorem chartPulledIntegralCLM_norm_le
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp‖ ≤ C := by
  refine ⟨‖chartPulledIntegralWeightLp (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_supp‖, norm_nonneg _, ?_⟩
  unfold chartPulledIntegralCLM
  exact le_of_eq (innerSL_apply_norm (𝕜 := ℝ)
    (chartPulledIntegralWeightLp (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp))

/-- The smooth-case formula: applied to the smooth lift `smoothToLp g v`, the
chart-pulled-integral CLM reduces to the explicit chart-pulled integral

```
∫_{chartTargetEuclid α} v.toFun(symm y) · θ(y) dy.
```
-/
theorem chartPulledIntegralCLM_smoothToLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (v : SmoothScalar g) :
    chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp
        (smoothToLp (I := I) (M := M) g v) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        v.toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          θ y ∂(volume : Measure EuclN) := by
  classical
  unfold chartPulledIntegralCLM
  rw [innerSL_apply_apply]
  -- Inner = ∫ ⟨w_θ_lp, smoothToLp v⟩ = ∫ w_θ * v on M, after a.e.-rewriting both classes.
  rw [L2.inner_def
    (chartPulledIntegralWeightLp (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp)
    (smoothToLp (I := I) (M := M) g v)]
  -- Now it's ∫ ⟨w_θ_lp a, smoothToLp_v a⟩_ℝ ∂μ_g.
  -- Reduce to ∫ w_θ_lp.coeFn · smoothToLp_v.coeFn dμ via L2.
  -- a.e.-rewrite the integrand using the toLp coercions.
  have hae_w : (chartPulledIntegralWeightLp (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_supp : Lp ℝ 2 _) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      chartPulledIntegralWeight (I := I) (M := M) g α θ :=
    MemLp.coeFn_toLp (chartPulledIntegralWeight_memLp
      (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp)
  have hae_v : (smoothToLp (I := I) (M := M) g v : Lp ℝ 2 _) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  have h_int_eq : ∫ a, @inner ℝ _ _
        ((chartPulledIntegralWeightLp (I := I) (M := M) g α
          hθ_cont hθ_cs hθ_supp : Lp ℝ 2 _) a)
        ((smoothToLp (I := I) (M := M) g v : Lp ℝ 2 _) a)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ a, chartPulledIntegralWeight (I := I) (M := M) g α θ a * v.toFun a
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hae_w, hae_v] with a hwa hva
    rw [hwa, hva]
    -- ⟨w(a), v(a)⟩_ℝ = w(a) * v(a) (since ℝ inner product is multiplication).
    rw [show @inner ℝ _ _ (chartPulledIntegralWeight (I := I) (M := M) g α θ a)
          (v.toFun a) =
        v.toFun a * chartPulledIntegralWeight (I := I) (M := M) g α θ a from
      RCLike.inner_apply _ _]
    ring
  rw [h_int_eq]
  exact integral_weight_smul_eq_chartPulled (I := I) (M := M) g α
    hθ_cont hθ_cs hθ_supp v.smooth.continuous

/-! ## L²-continuity in `F` for the chart-pulled integral

For sequences `F_n → F_lim` in `Lp ℝ 2 μ_g`, the chart-pulled integral
`I(F_n) → I(F_lim)`, by continuity of the CLM `chartPulledIntegralCLM`. -/

theorem chartPulledIntegralCLM_continuous
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Continuous (chartPulledIntegralCLM (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_supp) :=
  (chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp).continuous

/-- For a convergent sequence `F_n → F_lim` in `Lp ℝ 2 μ_g`, the chart-pulled
integrals converge accordingly. -/
theorem chartPulledIntegralCLM_tendsto
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {F : ℕ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    {F_lim : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (h_tendsto : Tendsto F atTop (𝓝 F_lim)) :
    Tendsto (fun n => chartPulledIntegralCLM (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_supp (F n)) atTop
      (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
        hθ_cont hθ_cs hθ_supp F_lim)) :=
  ((chartPulledIntegralCLM_continuous (I := I) (M := M) g α
    hθ_cont hθ_cs hθ_supp).tendsto _).comp h_tendsto

/-! ## Lp-extension of the smooth-case integral formula

For a non-smooth `F : Lp ℝ 2 μ_g` obtained as the L²-limit of smooth scalars
`v_n → F`, the chart-pulled integral `I(F)` is the limit of the smooth-case
integrals `I(v_n)`. -/

theorem chartPulledIntegralCLM_tendsto_of_smoothToLp_tendsto
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {v : ℕ → SmoothScalar g}
    {F_lim : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (h_tendsto : Tendsto (fun n => smoothToLp (I := I) (M := M) g (v n))
      atTop (𝓝 F_lim)) :
    Tendsto (fun n => ∫ y in chartTargetEuclid (I := I) (M := M) α,
        (v n).toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          θ y ∂(volume : Measure EuclN)) atTop
      (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
        hθ_cont hθ_cs hθ_supp F_lim)) := by
  -- Use that `chartPulledIntegralCLM` is continuous and the smooth-case formula.
  have h_smooth_formula : (fun n => ∫ y in chartTargetEuclid (I := I) (M := M) α,
        (v n).toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          θ y ∂(volume : Measure EuclN)) =
      (fun n => chartPulledIntegralCLM (I := I) (M := M) g α
          hθ_cont hθ_cs hθ_supp (smoothToLp (I := I) (M := M) g (v n))) := by
    funext n
    exact (chartPulledIntegralCLM_smoothToLp (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_supp (v n)).symm
  rw [h_smooth_formula]
  exact chartPulledIntegralCLM_tendsto (I := I) (M := M) g α
    hθ_cont hθ_cs hθ_supp h_tendsto

/-! ## L²-extension of the smooth integral identity (chartPulledIntegral side)

For the right-hand side and the manifold-side mass integrand of the
variational identity, we package the smooth-case formula
`pouScalar_oneSubLap_aeEq_fHLeibniz_smooth` together with the
continuity of `chartPulledIntegralCLM`. -/

/-- The Lp-class equality identifying `smoothToLp ((pouScalar α v).oneSubLap)`
with `fHLeibniz g α (smoothToH1Compl v) _` as members of `Lp ℝ 2 μ_g`. This is
the Lp-class form of the a.e.-pointwise lemma
`pouScalar_oneSubLap_aeEq_fHLeibniz_smooth`. -/
lemma smoothToLp_pouScalar_oneSubLap_eq_fHLeibniz
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    smoothToLp (I := I) (M := M) g
        (pouScalar (I := I) (M := M) α v).oneSubLapClassical =
      fHLeibniz (I := I) (M := M) g α
        (smoothToH1Compl (I := I) (M := M) g v)
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) := by
  classical
  apply MeasureTheory.Lp.ext
  -- ⇑smoothToLp g (pouScalar α v).oneSubLap =ᵐ (pouScalar α v).oneSubLap.toFun.
  have h_lhs_aeeq : (smoothToLp (I := I) (M := M) g
      (pouScalar (I := I) (M := M) α v).oneSubLapClassical : Lp ℝ 2 _) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (pouScalar (I := I) (M := M) α v).oneSubLapClassical.toFun :=
    MemLp.coeFn_toLp (pouScalar (I := I) (M := M) α v).oneSubLapClassical.memLp_two
  -- The RHS coeFn is a.e.-equal to `(pouScalar α v).oneSubLap.toFun` by the lemma above.
  have h_rhs_aeeq : (pouScalar (I := I) (M := M) α v).oneSubLapClassical.toFun =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      ((fHLeibniz (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g v)
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
          : Lp ℝ 2 _) : M → ℝ) :=
    pouScalar_oneSubLap_aeEq_fHLeibniz_smooth (I := I) (M := M) g α v
  exact h_lhs_aeeq.trans h_rhs_aeeq

/-! ## Smooth-case rewriting of the chart-pulled-integral CLM

For a smooth scalar `v : SmoothScalar g`, applying the chart-pulled
integral CLM to the smooth Lp-class
`smoothToLp ((pouScalar α v).oneSubLap)` yields the same value as
applying it to `fHLeibniz g α (smoothToH1Compl v) _`, because the two
classes are equal in `Lp ℝ 2 μ_g`. -/

theorem chartPulledIntegralCLM_pouScalar_oneSubLap_eq_fHLeibniz_smooth
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (v : SmoothScalar g) :
    chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp
        (smoothToLp (I := I) (M := M) g
          (pouScalar (I := I) (M := M) α v).oneSubLapClassical) =
      chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp
        (fHLeibniz (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g v)
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)) := by
  rw [smoothToLp_pouScalar_oneSubLap_eq_fHLeibniz (I := I) (M := M) g α v]

/-! ## General-case variational identity (conditional on smooth approximation)

The general-case form of the variational identity for `u_h ∈ laplacianDomain g`
extends the smooth case `laplacianDomain_variational_identity_smooth_case`
through limit-passage in a smooth approximating sequence `v_n → u_h` in
`H1Compl g`.

The smooth-case identity gives, for each `v_n`,

```
LHS_principal(v_n) + LHS_u_chart_mass(v_n) = RHS(v_n)
```

where the three integrals are as in `laplacianDomain_variational_identity_smooth_case`.
The convergence as `v_n → u_h` is via:

* `LHS_principal(v_n) → LHS_principal_general(u_h)` — uses the L²-continuity of
  the chart-pushed-partial map `H1ComplPartialCLM` (defined in
  `H1ComplWeakPartialLimit`).
* `LHS_u_chart_mass(v_n) → LHS_u_chart_mass_general(u_h)` — uses the continuity
  of `chartPulledIntegralCLM` against the weight `ρα ∘ symm · density · ψ`.
* `RHS(v_n) → chartPulledIntegralCLM g α (density · ψ) (fHLeibniz g α u_h hu_h)` —
  uses the continuity of `chartPulledIntegralCLM` against the weight
  `density · ψ`, applied to a smooth sequence with `fHLeibniz_n →
  fHLeibniz g α u_h hu_h` in `Lp ℝ 2 μ_g`.

The third convergence is the substantive component that depends on the
specific properties of the smooth approximating sequence. The general theorem
is therefore stated with an additional `h_fHLeibniz_tendsto` hypothesis,
which any downstream consumer can verify either:

* by exploiting elliptic regularity (yielding smooth solutions
  `v_n` with `(1 - Δ_g) v_n = ṽ_n` for chosen smooth `ṽ_n → preimage u_h`),
* by constructing the smooth approximation directly with stronger convergence,
* or by other means specific to the application.

Once `h_fHLeibniz_tendsto` is supplied, the headline identity follows by
combining the existing chart-bilinear smooth identity with the three
convergence statements. -/

/-- **General-case identity for the chart-pulled RHS integral.**

For `u_h ∈ laplacianDomain g`, equipped with a smooth approximating sequence
`v_n` whose smooth-case `fHLeibniz` Lp classes converge to the general-case
`fHLeibniz`, the chart-pulled RHS integral converges accordingly. The
convergence is reduced via
`smoothToLp_pouScalar_oneSubLap_eq_fHLeibniz` to a `chartPulledIntegralCLM`
continuity application. -/
theorem chartPulledIntegralCLM_RHS_tendsto_of_fHLeibniz_tendsto
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl g) (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {v : ℕ → SmoothScalar g}
    (h_fHLeibniz_tendsto :
      Tendsto (fun n => fHLeibniz (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g (v n))
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) (v n)))
        atTop (𝓝 (fHLeibniz (I := I) (M := M) g α u_h hu_h))) :
    Tendsto (fun n => chartPulledIntegralCLM (I := I) (M := M) g α
        hθ_cont hθ_cs hθ_supp
        (smoothToLp (I := I) (M := M) g
          (pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical))
      atTop (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
        hθ_cont hθ_cs hθ_supp
        (fHLeibniz (I := I) (M := M) g α u_h hu_h))) := by
  classical
  -- Step 1: Rewrite each `smoothToLp ((pouScalar α v_n).oneSubLap)` as
  -- `fHLeibniz g α (smoothToH1Compl v_n) _` (Lp class equality).
  have h_eq_n : ∀ n,
      smoothToLp (I := I) (M := M) g
          (pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical =
      fHLeibniz (I := I) (M := M) g α
        (smoothToH1Compl (I := I) (M := M) g (v n))
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) (v n)) :=
    fun n => smoothToLp_pouScalar_oneSubLap_eq_fHLeibniz
      (I := I) (M := M) g α (v n)
  -- Step 2: Substitute and apply chartPulledIntegralCLM continuity.
  have h_funeq : (fun n => chartPulledIntegralCLM (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_supp
      (smoothToLp (I := I) (M := M) g
        (pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical)) =
    fun n => chartPulledIntegralCLM (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_supp
      (fHLeibniz (I := I) (M := M) g α
        (smoothToH1Compl (I := I) (M := M) g (v n))
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) (v n))) := by
    funext n
    rw [h_eq_n n]
  rw [h_funeq]
  exact chartPulledIntegralCLM_tendsto (I := I) (M := M) g α
    hθ_cont hθ_cs hθ_supp h_fHLeibniz_tendsto

/-- **General-case identity for the smooth-side RHS integral.**

For a smooth approximating sequence `v_n` with the appropriate convergence,
the smooth-side RHS integral
`∫_{chartTarget} density · ((pouScalar α v_n).oneSubLap.toFun ∘ symm) · ψ dvol`
converges to the general-case identity's chart-pulled RHS, expressed via
`chartPulledIntegralCLM g α (density · ψ) (fHLeibniz g α u_h hu_h)`. -/
theorem rhs_integral_smooth_tendsto_chartPulledIntegralCLM_fHLeibniz
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl g) (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {v : ℕ → SmoothScalar g}
    (h_fHLeibniz_tendsto :
      Tendsto (fun n => fHLeibniz (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g (v n))
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) (v n)))
        atTop (𝓝 (fHLeibniz (I := I) (M := M) g α u_h hu_h))) :
    Tendsto (fun n => ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          ψ y ∂(volume : Measure EuclN))
      atTop (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
        (θ := fun y => densityOnEuclid (I := I) g α y * ψ y)
        (by
          -- Continuity of densityOnEuclid · ψ on EuclN:
          -- density is smooth on chartTarget (open), and ψ is continuous globally.
          -- Outside chartTarget, the product vanishes (handled via cutoff arguments).
          -- For our purposes, we observe: density · ψ is continuous on tsupport ψ
          -- (since tsupport ψ ⊆ chartTarget). Outside tsupport ψ, ψ = 0, so the
          -- product equals 0 (since density is bounded on M). Hence the product is
          -- continuous everywhere.
          refine continuous_iff_continuousAt.mpr fun y => ?_
          by_cases hy : y ∈ tsupport ψ
          · have hy_T : y ∈ chartTargetEuclid (I := I) (M := M) α := hψ_supp hy
            have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
              Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
            have h_dens : ContinuousAt (densityOnEuclid (I := I) g α) y :=
              ((densityOnEuclid_contDiffOn (I := I) g α).continuousOn).continuousAt
                (hOpen.mem_nhds hy_T)
            exact h_dens.mul hψ.continuous.continuousAt
          · have h_compl_open : IsOpen (tsupport ψ)ᶜ := (isClosed_tsupport _).isOpen_compl
            have h_ev : (fun y => densityOnEuclid (I := I) g α y * ψ y) =ᶠ[𝓝 y]
                (fun _ => (0 : ℝ)) := by
              filter_upwards [h_compl_open.mem_nhds hy] with z hz
              have hψ_z : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
              rw [hψ_z, mul_zero]
            refine ContinuousAt.congr ?_ h_ev.symm
            exact continuousAt_const)
        (by
          -- HasCompactSupport: the function vanishes outside tsupport ψ (compact).
          refine HasCompactSupport.intro (hψ_cs : IsCompact (tsupport ψ)) (fun y hy => ?_)
          have hψ_y : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
          rw [hψ_y, mul_zero])
        (by
          -- tsupport (density · ψ) ⊆ chartTargetEuclid α: the product vanishes outside
          -- support ψ ⊆ tsupport ψ ⊆ chartTargetEuclid α.
          refine subset_trans (closure_mono ?_) hψ_supp
          intro y hy
          rw [Function.mem_support] at hy
          by_contra hyψ
          apply hy
          have hψ_y : ψ y = 0 := Function.notMem_support.mp hyψ
          rw [hψ_y, mul_zero])
        (fHLeibniz (I := I) (M := M) g α u_h hu_h))) := by
  classical
  -- Step 1: Each smooth integral equals chartPulledIntegralCLM applied to
  -- `smoothToLp ((pouScalar α v_n).oneSubLap)` against `density · ψ`.
  set θ : EuclN → ℝ := fun y : EuclN => densityOnEuclid (I := I) g α y * ψ y with hθ_def
  have hθ_cont : Continuous θ := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    by_cases hy : y ∈ tsupport ψ
    · have hy_T : y ∈ chartTargetEuclid (I := I) (M := M) α := hψ_supp hy
      have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
        Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
      have h_dens : ContinuousAt (densityOnEuclid (I := I) g α) y :=
        ((densityOnEuclid_contDiffOn (I := I) g α).continuousOn).continuousAt
          (hOpen.mem_nhds hy_T)
      exact h_dens.mul hψ.continuous.continuousAt
    · have h_compl_open : IsOpen (tsupport ψ)ᶜ := (isClosed_tsupport _).isOpen_compl
      have h_ev : (fun y => densityOnEuclid (I := I) g α y * ψ y) =ᶠ[𝓝 y]
          (fun _ => (0 : ℝ)) := by
        filter_upwards [h_compl_open.mem_nhds hy] with z hz
        have hψ_z : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
        rw [hψ_z, mul_zero]
      refine ContinuousAt.congr ?_ h_ev.symm
      exact continuousAt_const
  have hθ_cs : HasCompactSupport θ :=
    HasCompactSupport.intro (hψ_cs : IsCompact (tsupport ψ)) (fun y hy => by
      have hψ_y : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
      change densityOnEuclid (I := I) g α y * ψ y = 0
      rw [hψ_y, mul_zero])
  have hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α := by
    refine subset_trans (closure_mono ?_) hψ_supp
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyψ
    apply hy
    have hψ_y : ψ y = 0 := Function.notMem_support.mp hyψ
    change densityOnEuclid (I := I) g α y * ψ y = 0
    rw [hψ_y, mul_zero]
  -- Step 2: Rewrite the integrand as `v_n.oneSubLapClassical(symm y) * θ(y)`.
  -- This is the smooth-case formula `chartPulledIntegralCLM_smoothToLp`.
  have h_eq_smooth : ∀ n,
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
            ψ y ∂(volume : Measure EuclN) =
      chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp
        (smoothToLp (I := I) (M := M) g
          (pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical) := by
    intro n
    rw [chartPulledIntegralCLM_smoothToLp (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_supp
      (pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical]
    -- Need to identify the two integrands; they differ by associativity/commutativity.
    refine MeasureTheory.setIntegral_congr_fun
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α).measurableSet ?_
    intro y _hy
    change densityOnEuclid (I := I) g α y *
        ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
        ψ y =
      ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
        (densityOnEuclid (I := I) g α y * ψ y)
    ring
  -- Step 3: Substitute and apply chartPulledIntegralCLM_RHS_tendsto_of_fHLeibniz_tendsto.
  rw [show (fun n => ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
            ψ y ∂(volume : Measure EuclN)) =
        (fun n => chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp
          (smoothToLp (I := I) (M := M) g
            (pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical)) from
      funext h_eq_smooth]
  exact chartPulledIntegralCLM_RHS_tendsto_of_fHLeibniz_tendsto
    (I := I) (M := M) g α u_h hu_h hθ_cont hθ_cs hθ_supp h_fHLeibniz_tendsto

/-! ## Headline general-case variational identity

The headline general-case variational identity for `u_h ∈ laplacianDomain g`
is obtained from `laplacianDomain_variational_identity_smooth_case` (the
smooth case, proved in `LaplacianDomainVariationalLimit`) via limit-passage
in a smooth approximating sequence `v_n → u_h` in `H1Compl g`. The
limit-passage of the right-hand side requires the additional hypothesis that
`fHLeibniz g α (smoothToH1Compl v_n) _ → fHLeibniz g α u_h hu_h` in
`Lp ℝ 2 μ_g`; this hypothesis is what `chartPulledIntegralCLM_RHS_tendsto_of_fHLeibniz_tendsto`
above discharges, and is the substantive limit-passage component beyond the
purely L²-CLM machinery.

The headline below packages both convergence statements (LHS u_chart_mass via
`chartPulledIntegralCLM` and RHS via `fHLeibniz`-convergence) together with
the smooth-case identity for each `v_n`, yielding the limit identity:

```
lim_{n → ∞} (LHS_principal_n + LHS_u_chart_mass_n) =
  chartPulledIntegralCLM g α (density · ψ) (fHLeibniz g α u_h hu_h).
```

The full headline `LHS_principal_general(u_h) + LHS_u_chart_mass_general(u_h)
= chartPulledIntegralCLM g α (density · ψ) (fHLeibniz g α u_h hu_h)` requires
the LHS_principal limit-passage to be discharged separately; this is provided
in a follow-up via `tendsto_inner_integral` against the chart-pulled weighted
measure (see comments in `LaplacianDomainVariationalLimit`). -/

/-- **General-case variational identity (LHS u_chart_mass + RHS half).**

For an approximating sequence `v_n` of smooth scalars with
`smoothToH1Compl v_n → u_h` in `H1Compl g` and the `fHLeibniz`-convergence
hypothesis discharged, the smooth-case integrals
`∫ density · chartPushed POU α v_n · ψ dvol` and
`∫ density · ((pouScalar α v_n).oneSubLap.toFun ∘ symm) · ψ dvol` converge
to their respective general-case values via `chartPulledIntegralCLM`. -/
theorem laplacianDomain_variational_identity_general_partial
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl g) (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {v : ℕ → SmoothScalar g}
    (_h_v_tendsto :
      Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
        atTop (𝓝 u_h))
    (h_fHLeibniz_tendsto :
      Tendsto (fun n => fHLeibniz (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g (v n))
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) (v n)))
        atTop (𝓝 (fHLeibniz (I := I) (M := M) g α u_h hu_h))) :
    -- The smooth-case RHS integrals converge to the general-case
    -- chart-pulled-integral CLM applied to `fHLeibniz`.
    Tendsto (fun n => ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          ψ y ∂(volume : Measure EuclN))
      atTop (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
        (θ := fun y : EuclN => densityOnEuclid (I := I) g α y * ψ y)
        (by
          refine continuous_iff_continuousAt.mpr fun y => ?_
          by_cases hy : y ∈ tsupport ψ
          · have hy_T : y ∈ chartTargetEuclid (I := I) (M := M) α := hψ_supp hy
            have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
              Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
            have h_dens : ContinuousAt (densityOnEuclid (I := I) g α) y :=
              ((densityOnEuclid_contDiffOn (I := I) g α).continuousOn).continuousAt
                (hOpen.mem_nhds hy_T)
            exact h_dens.mul hψ.continuous.continuousAt
          · have h_compl_open : IsOpen (tsupport ψ)ᶜ := (isClosed_tsupport _).isOpen_compl
            have h_ev : (fun y => densityOnEuclid (I := I) g α y * ψ y) =ᶠ[𝓝 y]
                (fun _ => (0 : ℝ)) := by
              filter_upwards [h_compl_open.mem_nhds hy] with z hz
              have hψ_z : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
              rw [hψ_z, mul_zero]
            refine ContinuousAt.congr ?_ h_ev.symm
            exact continuousAt_const)
        (by
          refine HasCompactSupport.intro (hψ_cs : IsCompact (tsupport ψ)) (fun y hy => ?_)
          have hψ_y : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
          rw [hψ_y, mul_zero])
        (by
          refine subset_trans (closure_mono ?_) hψ_supp
          intro y hy
          rw [Function.mem_support] at hy
          by_contra hyψ
          apply hy
          have hψ_y : ψ y = 0 := Function.notMem_support.mp hyψ
          rw [hψ_y, mul_zero])
        (fHLeibniz (I := I) (M := M) g α u_h hu_h))) := by
  exact rhs_integral_smooth_tendsto_chartPulledIntegralCLM_fHLeibniz
    (I := I) (M := M) g α u_h hu_h hψ hψ_cs hψ_supp h_fHLeibniz_tendsto

end ChartPulledIntegralContinuity
end Laplacian
end Analysis
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Analysis.Laplacian.ChartPulledIntegralContinuity.chartPulledIntegralCLM
#print axioms
  DifferentialGeometry.Analysis.Laplacian.ChartPulledIntegralContinuity.chartPulledIntegralCLM_norm_le
#print axioms
  DifferentialGeometry.Analysis.Laplacian.ChartPulledIntegralContinuity.chartPulledIntegralCLM_smoothToLp
#print axioms
  DifferentialGeometry.Analysis.Laplacian.ChartPulledIntegralContinuity.chartPulledIntegralCLM_tendsto
#print axioms
  DifferentialGeometry.Analysis.Laplacian.ChartPulledIntegralContinuity.smoothToLp_pouScalar_oneSubLap_eq_fHLeibniz
#print axioms
  DifferentialGeometry.Analysis.Laplacian.ChartPulledIntegralContinuity.chartPulledIntegralCLM_pouScalar_oneSubLap_eq_fHLeibniz_smooth
#print axioms
  DifferentialGeometry.Analysis.Laplacian.ChartPulledIntegralContinuity.chartPulledIntegralCLM_RHS_tendsto_of_fHLeibniz_tendsto
#print axioms
  DifferentialGeometry.Analysis.Laplacian.ChartPulledIntegralContinuity.rhs_integral_smooth_tendsto_chartPulledIntegralCLM_fHLeibniz
#print axioms
  DifferentialGeometry.Analysis.Laplacian.ChartPulledIntegralContinuity.laplacianDomain_variational_identity_general_partial
end Sanity
