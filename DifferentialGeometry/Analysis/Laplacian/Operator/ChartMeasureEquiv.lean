import DifferentialGeometry.Analysis.Laplacian.MetricExtension
import DifferentialGeometry.Integral.DivergenceTheorem.Closed
import DifferentialGeometry.Integral.Measure.Family
import DifferentialGeometry.Integral.Measure.ChartDensity
import DifferentialGeometry.Integral.Measure.Invariance
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Chart-pulled equivalence between the Riemannian volume measure and Lebesgue
with the chart density

For a smooth Riemannian metric `g` on a smooth manifold `M` and a chart point
`α : M`, this file packages the existing chart-local measure infrastructure
into clean public Bochner integral identities of the form

```
∫_M f x dμ_g(x)
  = ∫ y in (extChartAt I α).target,
      chartDensity g α (symm y) * f (symm y) ∂modelHaar
```

valid for any continuous `f : M → ℝ` whose topological support lies inside
`(chartAt H α).source`.

The identity is the Bochner-integral form of the chart-pulled equivalence
between `riemannianVolumeMeasure g` and the canonical Haar measure on the
model space `E`, weighted by the chart-local volume density.

Two parallel forms are delivered:

* a *model-space form* using `modelHaar : Measure E` and
  `(extChartAt I α).target ⊆ E`, which is the form that the
  chart-local measure infrastructure naturally produces;
* an *Euclidean form* using the Haar measure on
  `EuclideanSpace ℝ (Fin (Module.finrank ℝ E))`, accessed as the pushforward
  `Measure.map toEuclidean modelHaar` to keep the statement free of any
  external scaling constant; the integration set is `chartTargetEuclid α`,
  the inverse-chart composition is `(extChartAt I α).symm ∘ toEuclidean.symm`,
  and the volume density is `densityOnEuclid g α` (both reused from
  `MetricExtension.lean`).

## Setting

Throughout we work in the boundaryless closed-manifold setting with
`[I.Boundaryless]`, `[T2Space M]`, `[SigmaCompactSpace M]`, `[CompactSpace M]`.
The model fibre is a finite-dimensional real inner-product space `E`.

## Main results

* `integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget`: model-space form
  of the chart-pulled identity, expressed against `modelHaar` over
  `(extChartAt I α).target`.
* `integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_indicator`: same
  identity with the integration domain folded into a `Set.indicator` factor,
  i.e., the integral runs over all of `E` with an explicit indicator.
* `integral_riemannianVolumeMeasure_eq_euclidean_chartTarget`: the
  `EuclideanSpace`-form of the identity, against
  `Measure.map toEuclidean modelHaar`. The integrand uses `densityOnEuclid` and
  the chart-target image `chartTargetEuclid α` (both from
  `MetricExtension.lean`).
* `integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_indicator`: same
  identity with the integration domain folded into a `Set.indicator` factor,
  matching the form most convenient for downstream chart-based analysis.

The identities reduce the global Bochner integral against the Riemannian
volume measure to a Bochner integral on the model side via the inverse chart
and the chart density, in the form requested by downstream chart-based
analysis (Sobolev embeddings, elliptic-regularity bridges, etc.).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff ENNReal Matrix BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartMeasureEquiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension

/-! ## File-local Borel-space instances on `E` and `M`

Match the convention in surrounding files: install Borel σ-algebras locally
without leaking global instances. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## Model-space form: integral against `modelHaar` on the chart target -/

/-- **Chart-pulled volume identity (model-space form).**

For a continuous scalar function `f : M → ℝ` whose topological support sits
inside the chart source `(chartAt H α).source`, the Bochner integral of `f`
against the canonical Riemannian volume measure equals the Bochner integral
on the chart target `(extChartAt I α).target ⊆ E` of the chart-pulled
density-weighted function

```
y ↦ chartDensity g α ((extChartAt I α).symm y) * f ((extChartAt I α).symm y)
```

against the canonical Haar measure `modelHaar` on `E`. -/
theorem integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y in (extChartAt I α).target,
        chartDensity g α ((extChartAt I α).symm y) *
          f ((extChartAt I α).symm y)
        ∂(modelHaar (E := E)) := by
  classical
  -- Step 1: replace `μ_g` by the chart-local measure at `α`.
  have h_step1 :=
    integral_riemannianVolumeMeasure_eq_chartLocal_of_support_in_chart
      (I := I) (M := M) g α hf_cont hf_supp
  rw [h_step1]
  -- Step 2: unfold the chart-local Bochner integral via `integral_chartLocalMeasure`.
  exact integral_chartLocalMeasure (I := I) (M := M) g α f hf_cont.measurable

/-- **Chart-pulled volume identity (model-space form, indicator variant).**

The same identity as `integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget`,
with the chart-target restriction expressed as a multiplication by
`Set.indicator (extChartAt I α).target 1`. The integrand vanishes off the
chart target so the integral runs over all of `E` against `modelHaar`. -/
theorem integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_indicator
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y,
        chartDensity g α ((extChartAt I α).symm y) *
          f ((extChartAt I α).symm y) *
          Set.indicator (extChartAt I α).target (fun _ => (1 : ℝ)) y
        ∂(modelHaar (E := E)) := by
  classical
  rw [integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget
    (I := I) (M := M) g α hf_cont hf_supp]
  -- Convert the `setIntegral` over `target` to an `integral` over all of `E`
  -- by pre-multiplying with `Set.indicator target 1`.
  have htgt_meas : MeasurableSet (extChartAt I α).target :=
    measurableSet_extChartAt_target (I := I) α
  -- First, rewrite `setIntegral` as `∫ y, target.indicator (fun y' => density(y') * f(y')) y dμ`.
  rw [show
      (∫ y in (extChartAt I α).target,
          chartDensity g α ((extChartAt I α).symm y) *
            f ((extChartAt I α).symm y)
          ∂(modelHaar (E := E))) =
        ∫ y, (extChartAt I α).target.indicator
              (fun y' : E =>
                chartDensity g α ((extChartAt I α).symm y') *
                  f ((extChartAt I α).symm y')) y
            ∂(modelHaar (E := E)) from
        (MeasureTheory.integral_indicator htgt_meas).symm]
  -- Then rewrite `target.indicator (fun y' => density y' * f y') y =
  -- density y * f y * target.indicator 1 y` pointwise.
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (fun y => ?_))
  simp only
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, mul_one]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]

/-! ## Euclidean form: integral against `Measure.map toEuclidean modelHaar`

The Euclidean form transports `modelHaar` along the linear isomorphism
`toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin n)` and stays in the project's
standard Euclidean space coordinates, where `densityOnEuclid` and
`chartTargetEuclid α` (both from `MetricExtension.lean`) are the natural
chart-pulled objects.

By choosing `Measure.map toEuclidean modelHaar` as the reference measure on
`EuclideanSpace`, we avoid introducing any external scaling constant: the
identity is a direct chart-pull-back without further factors. The standard
Lebesgue volume on `EuclideanSpace ℝ (Fin n)` differs from this pushforward
by a positive multiplicative constant (`Measure.addHaarScalarFactor`), which
is the same Haar-uniqueness factor that already appears in the chart-bridge
literature in this codebase. -/

/-- The canonical `MeasurableEquiv` underlying `toEuclidean`, used for
applying `MeasureTheory.integral_map_equiv` below. -/
private def toEuclideanMeasurableEquiv :
    E ≃ᵐ EuclN :=
  (toEuclidean (E := E)).toHomeomorph.toMeasurableEquiv

/-- The canonical `MeasurableEquiv` evaluates as `toEuclidean`. -/
@[simp] private lemma toEuclideanMeasurableEquiv_apply (y : E) :
    toEuclideanMeasurableEquiv (E := E) y = toEuclidean y := rfl

/-- The canonical `MeasurableEquiv`'s symmetric inverse evaluates as
`toEuclidean.symm`. -/
@[simp] private lemma toEuclideanMeasurableEquiv_symm_apply (y : EuclN) :
    (toEuclideanMeasurableEquiv (E := E)).symm y = (toEuclidean (E := E)).symm y := rfl

omit [IsManifold I ∞ M] in
/-- Membership identification: `toEuclidean y ∈ chartTargetEuclid α`
iff `y ∈ (extChartAt I α).target`. -/
private lemma toEuclidean_mem_chartTargetEuclid_iff
    (α : M) (y : E) :
    toEuclidean (E := E) y ∈ chartTargetEuclid (I := I) (M := M) α ↔
      y ∈ (extChartAt I α).target := by
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · rcases hy with ⟨z, hz_target, hz_eq⟩
    have hyz : y = z := ((toEuclidean (E := E)).injective hz_eq).symm
    rw [hyz]; exact hz_target
  · exact ⟨y, hy, rfl⟩

/-- The chart-target image (under `toEuclidean`) is Borel-measurable. -/
private lemma chartTargetEuclid_measurableSet (α : M) :
    MeasurableSet (chartTargetEuclid (I := I) (M := M) α) := by
  have htarget_meas : MeasurableSet (extChartAt I α).target :=
    measurableSet_extChartAt_target (I := I) α
  change MeasurableSet (toEuclidean '' (extChartAt I α).target)
  exact (toEuclideanMeasurableEquiv (E := E)).measurableEmbedding.measurableSet_image.mpr
    htarget_meas

/-- **Chart-pulled volume identity (Euclidean form).**

For a continuous scalar function `f : M → ℝ` whose topological support sits
inside `(chartAt H α).source`, the Bochner integral of `f` against the
canonical Riemannian volume measure equals the Bochner integral on the
chart-target image `chartTargetEuclid α ⊆ EuclideanSpace ℝ (Fin (finrank ℝ E))`
of the chart-pulled density-weighted function

```
y ↦ densityOnEuclid g α y * f ((extChartAt I α).symm (toEuclidean.symm y))
```

against the pushforward measure `Measure.map toEuclidean modelHaar`.

The pushforward `Measure.map toEuclidean modelHaar` is itself an additive Haar
measure on `EuclideanSpace ℝ (Fin (finrank ℝ E))`; using it keeps the identity
free of any external scaling constant. -/
theorem integral_riemannianVolumeMeasure_eq_euclidean_chartTarget
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
            (modelHaar (E := E))) := by
  classical
  -- Step 1: rewrite via the model-space form.
  rw [integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget
    (I := I) (M := M) g α hf_cont hf_supp]
  -- Step 2: rewrite both sides as `integral` over the full space using
  -- `setIntegral_eq_integral_of_indicator` / equivalently `integral_indicator`.
  have htarget_meas : MeasurableSet (extChartAt I α).target :=
    measurableSet_extChartAt_target (I := I) α
  have hctE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  -- LHS as full integral with target.indicator.
  rw [show
      (∫ y in (extChartAt I α).target,
          chartDensity g α ((extChartAt I α).symm y) *
            f ((extChartAt I α).symm y)
          ∂(modelHaar (E := E))) =
        ∫ y, (extChartAt I α).target.indicator
              (fun y' : E =>
                chartDensity g α ((extChartAt I α).symm y') *
                  f ((extChartAt I α).symm y')) y
            ∂(modelHaar (E := E)) from
        (MeasureTheory.integral_indicator htarget_meas).symm]
  -- RHS as full integral with chartTargetEuclid.indicator.
  rw [show
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
              (modelHaar (E := E)))) =
        ∫ y',
            (chartTargetEuclid (I := I) (M := M) α).indicator
              (fun y'' : EuclN =>
                densityOnEuclid (I := I) g α y'' *
                  f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y''))) y'
            ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
                (modelHaar (E := E))) from
        (MeasureTheory.integral_indicator hctE_meas).symm]
  -- Apply `integral_map_equiv` to push the right-hand integral back to `E`.
  rw [show
      (∫ y',
          (chartTargetEuclid (I := I) (M := M) α).indicator
            (fun y'' : EuclN =>
              densityOnEuclid (I := I) g α y'' *
                f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y''))) y'
          ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
              (modelHaar (E := E)))) =
        ∫ y,
          (chartTargetEuclid (I := I) (M := M) α).indicator
            (fun y'' : EuclN =>
              densityOnEuclid (I := I) g α y'' *
                f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y'')))
            (toEuclideanMeasurableEquiv (E := E) y)
          ∂(modelHaar (E := E)) from ?_]
  · -- Now both integrals are over `E` w.r.t. `modelHaar`. Compare integrands.
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun y => ?_))
    simp only
    by_cases hy : y ∈ (extChartAt I α).target
    · -- On `target`: both indicators apply, and the integrands match by
      -- `densityOnEuclid_def` since `toEuclidean.symm (toEuclidean y) = y`.
      have hctE_y : toEuclideanMeasurableEquiv (E := E) y ∈
          chartTargetEuclid (I := I) (M := M) α :=
        (toEuclidean_mem_chartTargetEuclid_iff (I := I) (M := M) α y).mpr hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hctE_y]
      -- Compare values.
      have h_symm_apply :
          (toEuclidean (E := E)).symm (toEuclidean y) = y :=
        (toEuclidean (E := E)).symm_apply_apply y
      change chartDensity g α ((extChartAt I α).symm y) *
          f ((extChartAt I α).symm y) =
        densityOnEuclid (I := I) g α (toEuclidean y) *
          f ((extChartAt I α).symm
            ((toEuclidean (E := E)).symm (toEuclidean y)))
      rw [h_symm_apply]
      -- `densityOnEuclid g α (toEuclidean y) = chartDensity g α (symm y)`.
      change chartDensity g α ((extChartAt I α).symm y) *
          f ((extChartAt I α).symm y) =
        chartDensity g α ((extChartAt I α).symm
            ((toEuclidean (E := E)).symm (toEuclidean y))) *
          f ((extChartAt I α).symm y)
      rw [h_symm_apply]
    · -- Off `target`: both indicators give `0`.
      have hctE_off : toEuclideanMeasurableEquiv (E := E) y ∉
          chartTargetEuclid (I := I) (M := M) α := by
        intro hcontra
        exact hy ((toEuclidean_mem_chartTargetEuclid_iff (I := I) (M := M) α y).mp hcontra)
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hctE_off]
  · -- The `integral_map_equiv` step.
    exact MeasureTheory.integral_map_equiv
      (μ := modelHaar (E := E))
      (e := toEuclideanMeasurableEquiv (E := E))
      (f := fun y'' : EuclN =>
        (chartTargetEuclid (I := I) (M := M) α).indicator
          (fun y''' : EuclN =>
            densityOnEuclid (I := I) g α y''' *
              f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y'''))) y'')

/-- **Chart-pulled volume identity (Euclidean form, indicator variant).**

The same identity as `integral_riemannianVolumeMeasure_eq_euclidean_chartTarget`,
with the chart-target restriction expressed as a multiplication by
`Set.indicator (chartTargetEuclid α) 1`. The integrand vanishes outside the
chart-target image, so the integral runs over all of
`EuclideanSpace ℝ (Fin (finrank ℝ E))`. -/
theorem integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_indicator
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y,
        densityOnEuclid (I := I) g α y *
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          Set.indicator (chartTargetEuclid (I := I) (M := M) α)
            (fun _ => (1 : ℝ)) y
        ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
            (modelHaar (E := E))) := by
  classical
  rw [integral_riemannianVolumeMeasure_eq_euclidean_chartTarget
    (I := I) (M := M) g α hf_cont hf_supp]
  have hctE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  -- Expand the setIntegral as an indicator-form integral.
  rw [show
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
              (modelHaar (E := E)))) =
        ∫ y,
          (chartTargetEuclid (I := I) (M := M) α).indicator
            (fun y' : EuclN =>
              densityOnEuclid (I := I) g α y' *
                f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y'))) y
          ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
              (modelHaar (E := E))) from
        (MeasureTheory.integral_indicator hctE_meas).symm]
  -- Pointwise: `S.indicator (fun y' => g y' * h y') y = (g y * h y) * S.indicator 1 y`.
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (fun y => ?_))
  simp only
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, mul_one]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]

end ChartMeasureEquiv
end Laplacian
end Analysis
end DifferentialGeometry
