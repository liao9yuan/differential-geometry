import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorComponentGradientL2RawAtoms
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartComponents
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SlotCorrectionTrivImageContMDiff
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorComponentGradientL2ChristoffelAtoms
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

## The Christoffel slot-correction atom (per direction)

```
b ↦ ρ_α(b) *
      √( (∑ k : Fin r, ‖triv.continuousLinearMapAt b
                          (chartTensorRSInputSlotCorrection r s g α
                            S.toSection (chartBasisVecFiber α j) b k)‖²)
       + (∑ l : Fin s, ‖triv.continuousLinearMapAt b
                          (chartTensorRSOutputSlotCorrection r s g α
                            S.toSection (chartBasisVecFiber α j) b l)‖²) )
```

is `AEStronglyMeasurable` with respect to the Riemannian volume measure.
The argument is the slot-correction analog of the covariant-derivative
atom proof: replace the chart-source smoothness lemma
`tensorCovDeriv_chartBasis_trivImage_contMDiffOn` with the slot-correction
trivialised-image lemmas
`chartTensorRSInputSlotCorrection_chartBasisVec_trivImage_contMDiffOn_chartSource`
and `chartTensorRSOutputSlotCorrection_chartBasisVec_trivImage_contMDiffOn_chartSource`,
then sum over both slot indices, take Euclidean norms, square, sum, take
the square root, and multiply by the globally smooth POU weight.

## Public theorems

* `aestronglyMeasurable_indicator_tsupp_abs_raw` — the raw-component
  indicator atom is `AEStronglyMeasurable` against the Riemannian volume
  measure.
* `aestronglyMeasurable_pou_mul_sqrt_sum_christoffel_correction` —
  the per-direction Christoffel slot-correction atom integrand is
  `AEStronglyMeasurable` against the Riemannian volume measure.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

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
open DifferentialGeometry.Integral.Connection
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

/-! ## The per-direction trivialisation-projected Christoffel slot-correction
atom integrand

We package the Christoffel slot-correction atom integrand as a private
abbreviation to avoid repeating the unfolded `(input + output)`-sum
expression in every intermediate `ContinuousOn`/`AEStronglyMeasurable`
lemma. The integrand is

```
ρ_α(b) * √( (∑ k, ‖triv.continuousLinearMapAt b (input_k j b)‖²)
          + (∑ l, ‖triv.continuousLinearMapAt b (output_l j b)‖²) )
```

evaluated at the chart-`α` basis direction `j` and chart base point `b`.

The bridge identity equating the trivialisation's `continuousLinearMapAt`
action with the trivialisation `.2`-component on the chart-base set lets
us pull chart-source smoothness from the just-shipped trivialised-image
headlines into chart-source continuity of the integrand. The integrand
vanishes off `tsupport ρ_α` because `ρ_α` does, and `tsupport ρ_α` is
compact (closed in compact `M`), so
`ContinuousOn.aestronglyMeasurable_of_isCompact` lifts the chart-source
continuity to the headline. -/

section ChristoffelAtomMeasurability

variable (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
  (j : Fin (Module.finrank ℝ E))

/-- The per-slot trivialised input-slot factor used inside the
Christoffel atom integrand. -/
private def trivInput
    (T : Π b' : M, TensorRSSpace r s I b') (b : M) (k : Fin r) :
    TensorRSModel r s ℝ E :=
  (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
    (chartTensorRSInputSlotCorrection (I := I) r s g α
      (fun b' => T b') (chartBasisVecFiber (I := I) α j) b k)

/-- The per-slot trivialised output-slot factor used inside the
Christoffel atom integrand. -/
private def trivOutput
    (T : Π b' : M, TensorRSSpace r s I b') (b : M) (l : Fin s) :
    TensorRSModel r s ℝ E :=
  (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
    (chartTensorRSOutputSlotCorrection (I := I) r s g α
      (fun b' => T b') (chartBasisVecFiber (I := I) α j) b l)

/-- The per-direction Christoffel slot-correction atom integrand. -/
private def christoffelAtomIntegrand
    (T : Π b' : M, TensorRSSpace r s I b') (b : M) : ℝ :=
  ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
    Real.sqrt
      ((∑ k : Fin r, ‖trivInput (I := I) g r s α j T b k‖ ^ 2) +
       (∑ l : Fin s, ‖trivOutput (I := I) g r s α j T b l‖ ^ 2))

/-! ## Bridge: `triv.continuousLinearMapAt b X = (triv ⟨b, X⟩).2`
on chart source

Both slot corrections share the same chart-base-set membership argument
(intersection of the underlying `Tensor0SModel r` / `Tensor0SModel s`
tangent-bundle base sets, both equal to the tangent-bundle base set at
`α`) and the same `coe_linearMapAt_of_mem`-driven identification. We
factor this through a generic helper. -/

/-- On the chart-`α` source, the trivialisation-`α` `continuousLinearMapAt ℝ b`
applied to any fibre value `v : TensorRSSpace r s I b` equals the
trivialisation `.2`-component of the corresponding bundled value. -/
private lemma triv_continuousLinearMapAt_eq_triv_snd
    {b : M} (hb : b ∈ (chartAt H α).source) (v : TensorRSSpace r s I b) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b v =
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α ⟨b, v⟩).2 := by
  classical
  -- `b` lies in the `TensorRSModel r s ℝ E`-trivialisation base set (the
  -- intersection of the `Tensor0SModel r` / `Tensor0SModel s` base sets at
  -- `α`, both equal to the tangent-bundle base set at `α`).
  have hbaseRS : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change b ∈ (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet
    refine ⟨?_, ?_⟩
    all_goals
      change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
      exact hb
  have hcoe := (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).coe_linearMapAt_of_mem
    (R := ℝ) hbaseRS
  change ((trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b) v = _
  exact congrFun hcoe _

/-! ## Chart-source continuity of the per-slot trivialised factors -/

variable {g r s α j} in
private lemma trivInput_continuousOn_chartSource (S : SmoothCcTensor g r s)
    (k : Fin r) :
    ContinuousOn (fun b : M => trivInput (I := I) g r s α j S.toSection b k)
      ((chartAt H α).source) := by
  classical
  have h_trivImage :=
    (chartTensorRSInputSlotCorrection_chartBasisVec_trivImage_contMDiffOn_chartSource
      (I := I) (M := M) g r s α
      (fun b' : M => S.toSection b') S.toSection.contMDiff j k).continuousOn
  refine h_trivImage.congr ?_
  intro b hb
  exact triv_continuousLinearMapAt_eq_triv_snd (I := I) (r := r) (s := s)
    (α := α) (b := b) hb
    (chartTensorRSInputSlotCorrection (I := I) r s g α
      (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α j) b k)

variable {g r s α j} in
private lemma trivOutput_continuousOn_chartSource (S : SmoothCcTensor g r s)
    (l : Fin s) :
    ContinuousOn (fun b : M => trivOutput (I := I) g r s α j S.toSection b l)
      ((chartAt H α).source) := by
  classical
  have h_trivImage :=
    (chartTensorRSOutputSlotCorrection_chartBasisVec_trivImage_contMDiffOn_chartSource
      (I := I) (M := M) g r s α
      (fun b' : M => S.toSection b') S.toSection.contMDiff j l).continuousOn
  refine h_trivImage.congr ?_
  intro b hb
  exact triv_continuousLinearMapAt_eq_triv_snd (I := I) (r := r) (s := s)
    (α := α) (b := b) hb
    (chartTensorRSOutputSlotCorrection (I := I) r s g α
      (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α j) b l)

/-! ## Chart-source continuity of the integrand
`b ↦ ρ_α(b) * √(sum)` -/

variable {g r s α j} in
private lemma christoffelAtomIntegrand_continuousOn_chartSource
    (S : SmoothCcTensor g r s) :
    ContinuousOn (christoffelAtomIntegrand (I := I) g r s α j S.toSection)
      ((chartAt H α).source) := by
  classical
  -- POU weight is globally continuous (smooth).
  have h_pou : ContinuousOn
      (fun b : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b)
      ((chartAt H α).source) :=
    ((chartAtlasPOU I M α).contMDiff.continuous).continuousOn
  -- Squared-norm sums of continuous factors are continuous.
  have h_input : ContinuousOn
      (fun b : M => ∑ k : Fin r, ‖trivInput (I := I) g r s α j S.toSection b k‖ ^ 2)
      ((chartAt H α).source) :=
    continuousOn_finset_sum _ (fun k _ =>
      (trivInput_continuousOn_chartSource (I := I) S k).norm.pow 2)
  have h_output : ContinuousOn
      (fun b : M => ∑ l : Fin s, ‖trivOutput (I := I) g r s α j S.toSection b l‖ ^ 2)
      ((chartAt H α).source) :=
    continuousOn_finset_sum _ (fun l _ =>
      (trivOutput_continuousOn_chartSource (I := I) S l).norm.pow 2)
  have h_sumsq := h_input.add h_output
  have h_sqrt := Real.continuous_sqrt.comp_continuousOn h_sumsq
  exact h_pou.mul h_sqrt

/-! ## Chart-source continuity restricts to `tsupport ρ_α` -/

variable {g r s α j} in
private lemma christoffelAtomIntegrand_continuousOn_pouTsupport
    (S : SmoothCcTensor g r s) :
    ContinuousOn (christoffelAtomIntegrand (I := I) g r s α j S.toSection)
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) := by
  classical
  refine (christoffelAtomIntegrand_continuousOn_chartSource (I := I) S).mono ?_
  intro b hb
  exact pouTsupport_subset_baseSet (I := I) (M := M) α hb

/-! ## Vanishing off `tsupport ρ_α` and the indicator identity -/

variable {g r s α j} in
private lemma christoffelAtomIntegrand_zero_outside_pouTsupport
    (T : Π b' : M, TensorRSSpace r s I b') {b : M}
    (hb : b ∉ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :
    christoffelAtomIntegrand (I := I) g r s α j T b = 0 := by
  classical
  have hρ_zero : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b = 0 := by
    by_contra hne
    exact hb (subset_tsupport _ hne)
  simp [christoffelAtomIntegrand, hρ_zero]

variable {g r s α j} in
private lemma christoffelAtomIntegrand_eq_indicator
    (T : Π b' : M, TensorRSSpace r s I b') :
    christoffelAtomIntegrand (I := I) g r s α j T =
      (tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
        (christoffelAtomIntegrand (I := I) g r s α j T) := by
  classical
  funext b
  by_cases hb : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
  · rw [Set.indicator_of_mem hb]
  · rw [Set.indicator_of_notMem hb]
    exact christoffelAtomIntegrand_zero_outside_pouTsupport (I := I) T hb

/-! ## Restricted-measure `AEStronglyMeasurable` for the integrand -/

variable {g r s α j} in
private lemma christoffelAtomIntegrand_aestronglyMeasurable_restrict_pouTsupport
    (S : SmoothCcTensor g r s) :
    AEStronglyMeasurable
      (christoffelAtomIntegrand (I := I) g r s α j S.toSection)
      ((riemannianVolumeMeasure (I := I) (M := M) g).restrict
        (tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))) := by
  classical
  exact ContinuousOn.aestronglyMeasurable_of_isCompact
    (christoffelAtomIntegrand_continuousOn_pouTsupport (I := I) S)
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_measurableSet (I := I) (M := M) α)

end ChristoffelAtomMeasurability

/-! ## Public headline: `AEStronglyMeasurable` of the per-direction
Christoffel slot-correction atom integrand

The chart-frame Christoffel slot-correction atom integrand, written in the
trivialisation-projected form summing both input and output slots,
is `AEStronglyMeasurable` with respect to the Riemannian volume measure on
`(M, g)`. -/

/-- **`AEStronglyMeasurable` of the per-`α` per-direction Christoffel
slot-correction atom integrand.** For a closed Riemannian manifold `(M, g)`,
ranks `(r, s)`, a chart base point `α : M`, a chart-basis direction
`j : Fin (Module.finrank ℝ E)`, and a smooth compactly-supported `H^1`
tensor section `S : SmoothCcTensorH1 g r s`, the function

```
b ↦ ρ_α(b) *
      √( (∑ k : Fin r,
            ‖triv.continuousLinearMapAt b
              (chartTensorRSInputSlotCorrection r s g α
                S.toSection (chartBasisVecFiber α j) b k)‖²)
       + (∑ l : Fin s,
            ‖triv.continuousLinearMapAt b
              (chartTensorRSOutputSlotCorrection r s g α
                S.toSection (chartBasisVecFiber α j) b l)‖²) )
```

is `AEStronglyMeasurable` with respect to `riemannianVolumeMeasure g`. -/
theorem aestronglyMeasurable_pou_mul_sqrt_sum_christoffel_correction
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (S : SmoothCcTensorH1 g r s) :
    AEStronglyMeasurable
      (fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            ((∑ k : Fin r,
                ‖(trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                      ℝ b
                  (chartTensorRSInputSlotCorrection (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α j) b k)‖ ^ 2) +
              (∑ l : Fin s,
                ‖(trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                      ℝ b
                  (chartTensorRSOutputSlotCorrection (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α j) b l)‖ ^ 2)))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  -- The headline integrand is `christoffelAtomIntegrand ... S.toCcTensor.toSection`.
  change AEStronglyMeasurable
    (christoffelAtomIntegrand (I := I) g r s α j S.toCcTensor.toSection)
    (riemannianVolumeMeasure (I := I) (M := M) g)
  -- Replace the integrand by its `tsupport ρ_α`-indicator (they agree
  -- pointwise on `M` because `ρ_α = 0` off the support).
  rw [christoffelAtomIntegrand_eq_indicator (I := I)
    (T := fun b' : M => S.toCcTensor.toSection b')]
  -- `aestronglyMeasurable_indicator_iff` reduces to `AEStronglyMeasurable`
  -- on the restricted measure.
  rw [aestronglyMeasurable_indicator_iff
    (pouTsupport_measurableSet (I := I) (M := M) α)]
  exact christoffelAtomIntegrand_aestronglyMeasurable_restrict_pouTsupport
    (I := I) S.toCcTensor

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.aestronglyMeasurable_indicator_tsupp_abs_raw

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.aestronglyMeasurable_pou_mul_sqrt_sum_christoffel_correction

end Sanity
