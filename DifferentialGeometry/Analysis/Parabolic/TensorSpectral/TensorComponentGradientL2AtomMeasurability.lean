import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorComponentGradientL2RawAtoms
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartComponents
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# `AEStronglyMeasurable` of the per-`α` gradient `L²` atom integrands

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, and a chart base
point `α : M`, the per-`α` partition-of-unity-weighted gradient `L²`
assembly produces three integrand atoms whose `L²` norms are controlled by
the `H¹` seminorm of the underlying smooth compactly-supported tensor
section. This file ships the `AEStronglyMeasurable` companion lemmas needed
to upgrade the existing `eLpNorm` bounds to `MemLp` membership.

## The "raw²"-indicator atom

```
b ↦ (tsupport ρ_α).indicator
      (fun b' => |scalarOnE α (tensorChartComponentRaw g r s S α Idx Jdx)
                    (extChartAt I α b')|) b
```

is `AEStronglyMeasurable` with respect to the Riemannian volume measure.
The argument exploits:

* `tsupport ρ_α` is closed (and compact since `M` is compact), hence
  measurable in the Borel structure on `M`.
* On `tsupport ρ_α ⊆ (chartAt H α).source` (subordination of the
  chart-atlas partition of unity), the chart-pullback
  `scalarOnE α (raw) (extChartAt I α b)` coincides with `raw b`
  (`scalarOnE_extChartAt`).
* The raw chart-frame scalar component `tensorChartComponentRaw` is
  `ContMDiffOn` on `(chartAt H α).source`
  (`tensorChartComponentRaw_contMDiffOn_chart_source`), in particular
  continuous on the closed subset `tsupport ρ_α`.
* `ContinuousOn (|·|)` composes with the chart-source continuity, giving
  a function continuous on the compact set `tsupport ρ_α`.
* `ContinuousOn.aestronglyMeasurable_of_isCompact` then provides the
  restricted `AEStronglyMeasurable` statement, which lifts to the global
  indicator via `aestronglyMeasurable_indicator_iff`.

## Public theorem

* `aestronglyMeasurable_indicator_tsupp_abs_raw` — the raw-component
  indicator atom is `AEStronglyMeasurable` against the Riemannian volume
  measure.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Closed support of the chart-atlas POU weight at `α` is measurable

The compactness of `tsupport ρ_α` is `pouTsupport_isCompact` from
`ChartTensorInnerLowerBound`. We only need the measurability statement
locally, which follows from being closed inside the Borel structure. -/

/-- The closed support of the chart-atlas partition-of-unity weight at `α`
is measurable in the Borel σ-algebra on `M`. -/
private lemma pouTsupport_measurableSet (α : M) :
    MeasurableSet (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
  (isClosed_tsupport _).measurableSet

/-! ## Identification of the chart-pullback raw scalar on `tsupport ρ_α`

On `tsupport ρ_α ⊆ (chartAt H α).source ⊆ (extChartAt I α).source`, the
chart-pullback `scalarOnE α raw (extChartAt I α b)` equals the raw scalar
`raw b`. This is `scalarOnE_extChartAt` applied to the chart-source
inclusion. -/

private lemma scalarOnE_raw_eq_raw_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :
    scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (extChartAt I α b) =
      tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  have hb_chart : b ∈ (chartAt H α).source := hb_base
  have hb_ext : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hb_chart
  exact scalarOnE_extChartAt (I := I) α
    (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hb_ext

/-! ## Continuity of the raw chart-frame scalar component on `tsupport ρ_α`

By `tensorChartComponentRaw_contMDiffOn_chart_source` and the inclusion
`tsupport ρ_α ⊆ (chartAt H α).source`, the raw scalar is `ContinuousOn`
on the closed subset `tsupport ρ_α`. -/

private lemma tensorChartComponentRaw_continuousOn_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) := by
  classical
  have h_on : ContinuousOn
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
      ((chartAt H α).source) :=
    (tensorChartComponentRaw_contMDiffOn_chart_source
      (I := I) (M := M) g r s S α Idx Jdx).continuousOn
  refine h_on.mono ?_
  intro b hb
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  exact hb_base

/-! ## Continuity of the chart-pulled-back raw scalar on `tsupport ρ_α`

Combining the chart-pullback identification with chart-source continuity,
the function `b ↦ scalarOnE α raw (extChartAt I α b)` is `ContinuousOn`
on `tsupport ρ_α` (because it agrees pointwise with `raw` there). -/

private lemma scalarOnE_raw_continuousOn_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M => scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (extChartAt I α b))
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) := by
  classical
  have h_raw_on :=
    tensorChartComponentRaw_continuousOn_pouTsupport
      (I := I) (M := M) g r s α S Idx Jdx
  refine h_raw_on.congr ?_
  intro b hb
  exact scalarOnE_raw_eq_raw_on_pouTsupport
    (I := I) (M := M) g r s α S Idx Jdx hb

/-! ## Continuity of `|scalarOnE α raw (extChartAt I α ·)|` on `tsupport ρ_α` -/

private lemma abs_scalarOnE_raw_continuousOn_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M => |scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (extChartAt I α b)|)
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) := by
  classical
  have h_inner := scalarOnE_raw_continuousOn_pouTsupport
    (I := I) (M := M) g r s α S Idx Jdx
  exact _root_.continuous_abs.comp_continuousOn h_inner

/-! ## Restricted-measure `AEStronglyMeasurable` from chart-source continuity

`ContinuousOn` on the compact closed set `tsupport ρ_α` implies
`AEStronglyMeasurable` of the function against the restricted Riemannian
volume measure on that set. -/

private lemma abs_scalarOnE_raw_aestronglyMeasurable_restrict_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    AEStronglyMeasurable
      (fun b : M => |scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (extChartAt I α b)|)
      ((riemannianVolumeMeasure (I := I) (M := M) g).restrict
        (tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))) := by
  classical
  exact ContinuousOn.aestronglyMeasurable_of_isCompact
    (abs_scalarOnE_raw_continuousOn_pouTsupport
      (I := I) (M := M) g r s α S Idx Jdx)
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_measurableSet (I := I) (M := M) α)

/-! ## Public theorem: `AEStronglyMeasurable` of the raw-indicator atom

The indicator over `tsupport ρ_α` of the chart-pullback of the raw
chart-frame scalar component (in absolute value) is
`AEStronglyMeasurable` with respect to the Riemannian volume measure.

Equality of two `AEStronglyMeasurable` predicates is reduced via
`aestronglyMeasurable_indicator_iff` to `AEStronglyMeasurable` of the
inner function against the restricted measure. The chart-source continuity
of `raw`, together with the pointwise identification of the chart pullback
with `raw` on `tsupport ρ_α`, then provides the required restricted
`AEStronglyMeasurable` statement via
`ContinuousOn.aestronglyMeasurable_of_isCompact`. -/

/-- **`AEStronglyMeasurable` of the per-`α` `raw²`-indicator atom.**
For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart base
point `α : M`, a smooth compactly-supported `H^1` tensor section
`S : SmoothCcTensorH1 g r s`, and a multi-index pair `(Idx, Jdx)`,
the function

```
b ↦ (tsupport ρ_α).indicator
      (fun b' => |scalarOnE α (tensorChartComponentRaw g r s S α Idx Jdx)
                    (extChartAt I α b')|) b
```

is `AEStronglyMeasurable` with respect to `riemannianVolumeMeasure g`. -/
theorem aestronglyMeasurable_indicator_tsupp_abs_raw
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensorH1 g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    AEStronglyMeasurable
      (fun b : M =>
        (tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
          (fun b' : M => |scalarOnE (I := I) α
            (tensorChartComponentRaw (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx)
            (extChartAt I α b')|) b)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  -- Reduce to `AEStronglyMeasurable` of the indicand against the restricted
  -- measure via `aestronglyMeasurable_indicator_iff`.
  set ρSet : Set M := tsupport (fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hρSet_def
  have hρSet_meas : MeasurableSet ρSet :=
    pouTsupport_measurableSet (I := I) (M := M) α
  rw [aestronglyMeasurable_indicator_iff hρSet_meas]
  -- The restricted-measure `AEStronglyMeasurable` follows from the
  -- chart-source `ContinuousOn` via `aestronglyMeasurable_of_isCompact`.
  exact abs_scalarOnE_raw_aestronglyMeasurable_restrict_pouTsupport
    (I := I) (M := M) g r s α S.toCcTensor Idx Jdx

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.aestronglyMeasurable_indicator_tsupp_abs_raw

end Sanity
