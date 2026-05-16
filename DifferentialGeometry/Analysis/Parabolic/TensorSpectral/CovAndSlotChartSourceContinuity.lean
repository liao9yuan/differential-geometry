import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.CovL2BoundFromH1
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SectionNormFromTensorInner
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SlotCorrectionUniformBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TrivProjBridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartGoodSetMeasure
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.PreHilbert
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorComponentGradientL2CovariantAtoms
import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivativeAgreement
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Chart-source continuity for the per-`α` gradient atom integrand

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, and a chart base
point `α : M`, this file delivers the `AEStronglyMeasurable` companion to the
covariant-derivative atom appearing in the per-`α` gradient `L²` assembly.

## The chart-frame covariant-derivative atom

```
b ↦ ρ_α(b) *
      √(∑ k, ‖triv.continuousLinearMapAt b
                (chartTensorRSCovariantDerivative r s g α S.toSection
                  (chartBasisVecFiber α k) b)‖²)
```

is `AEStronglyMeasurable` with respect to the Riemannian volume measure.

## Strategy

The integrand vanishes off `tsupport ρ_α ⊆ (chartAt H α).source`. On the
chart-`α` source, the chart-frame covariant derivative agrees with the
bundled directional covariant derivative `tensorCovDerivAt`, and the
trivialisation-`α` `continuousLinearMapAt`-action sends a fibre value to
the second component of the trivialisation. The latter has chart-source
smoothness via `tensorCovDeriv_chartBasis_trivImage_contMDiffOn`, which
yields chart-source continuity of the `TensorRSModel r s ℝ E`-valued
integrand and therefore of its Euclidean norm sum.

Multiplying by the globally continuous weight `ρ_α` and reducing to the
restricted-measure `AEStronglyMeasurable` via `aestronglyMeasurable_indicator_iff`,
the headline follows from `ContinuousOn.aestronglyMeasurable_of_isCompact`
applied to the compact set `tsupport ρ_α`.

## Public theorem

* `aestronglyMeasurable_pou_mul_sqrt_sum_triv_chart_cov` — the covariant-
  derivative atom integrand is `AEStronglyMeasurable` against the
  Riemannian volume measure.
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
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Chart-source continuity of the trivialisation-projected chart-frame
covariant derivative

The trivialisation-`α` `continuousLinearMapAt ℝ b` applied to the chart-frame
covariant derivative of a smooth tensor section, evaluated at a chart-basis
direction, agrees on the chart-`α` source with the trivialisation `.2`-
component of the bundled covariant-derivative section. The latter has
chart-source smoothness via `tensorCovDeriv_chartBasis_trivImage_contMDiffOn`,
giving chart-source continuity of the projected chart-frame value. -/

/-- On the chart-`α` source, the trivialisation-`α` `continuousLinearMapAt ℝ b`
applied to the chart-frame covariant derivative
`chartTensorRSCovariantDerivative r s g α S.toSection (chartBasisVecFiber α k) b`
equals the trivialisation `.2`-component of the bundled directional covariant
derivative `tensorCovDerivAt g r s S b (chartBasisVecFiber α k b)`. -/
private lemma triv_continuousLinearMapAt_chartTensorRSCovariantDerivative_eq_triv_snd
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb : b ∈ (chartAt H α).source)
    (k : Fin (Module.finrank ℝ E)) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
      (chartTensorRSCovariantDerivative (I := I) r s g α
        (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α k) b) =
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
        ⟨b, tensorCovDerivAt (I := I) (M := M) g r s S b
          (chartBasisVecFiber (I := I) α k b)⟩).2 := by
  classical
  -- Reduce the chart-frame covariant derivative at `b` to `tensorCovDerivAt`
  -- via the existing pointwise bridge.
  have hcov_eq :=
    chartTensorRSCovariantDerivative_eq_tensorCovDerivAt_at
      (I := I) (M := M) g r s α S (chartBasisVecFiber (I := I) α k) hb
  rw [hcov_eq]
  -- The `.2` of the trivialisation equals `linearMapAt R b T` (and hence
  -- `continuousLinearMapAt R b T`) on the chart base set.
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
  -- `continuousLinearMapAt R b T = linearMapAt R b T` (the underlying linear
  -- map). Apply `hcoe` to the tensor argument and extract the value.
  change ((trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b)
      (tensorCovDerivAt (I := I) (M := M) g r s S b
        (chartBasisVecFiber (I := I) α k b)) = _
  exact congrFun hcoe _

/-- On the chart-`α` source, the trivialisation-projected chart-frame
covariant-derivative atom `b ↦ triv.continuousLinearMapAt b
  (chartTensorRSCovariantDerivative ... b)` is continuous as a function
valued in `TensorRSModel r s ℝ E`. -/
private lemma triv_chartTensorRSCovariantDerivative_continuousOn_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (k : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSCovariantDerivative (I := I) r s g α
            (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α k) b))
      ((chartAt H α).source) := by
  classical
  -- Continuity on the chart base set of `b ↦ (triv ⟨b, ∇_eₖ S b⟩).2` follows
  -- from `tensorCovDeriv_chartBasis_trivImage_contMDiffOn.continuousOn`.
  have hbase :
      ContinuousOn
        (fun b : M =>
          (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α
            ⟨b, tensorCovDerivAt (I := I) (M := M) g r s S b
              (chartBasisVecFiber (I := I) α k b)⟩).2)
        (trivializationAt E (TangentSpace I) α).baseSet :=
    (tensorCovDeriv_chartBasis_trivImage_contMDiffOn
      (I := I) (M := M) g r s S α k).continuousOn
  -- Identify chart base set with chart source. (`trivializationAt`'s baseSet
  -- equals `(chartAt H α).source`; this is the standard identification.)
  have hbase_eq :
      (trivializationAt E (TangentSpace I) α).baseSet =
        (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source α
  rw [hbase_eq] at hbase
  -- Use the pointwise identification on chart source.
  refine hbase.congr ?_
  intro b hb_chart
  -- Apply the identification lemma at `b ∈ chart source`.
  exact triv_continuousLinearMapAt_chartTensorRSCovariantDerivative_eq_triv_snd
    (I := I) (M := M) g r s α S hb_chart k

/-! ## Chart-source continuity of the squared-norm sum

The Euclidean square norm sum
`∑ k, ‖triv.continuousLinearMapAt b (chartTensorRSCovariantDerivative ... b)‖²`
is continuous on the chart-`α` source via a finite sum of squared norms of
continuous functions. -/

private lemma norm_sq_sum_triv_chartTensorRSCovariantDerivative_continuousOn_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    ContinuousOn
      (fun b : M =>
        ∑ k : Fin (Module.finrank ℝ E),
          ‖(trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSCovariantDerivative (I := I) r s g α
              (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α k) b)‖
            ^ 2)
      ((chartAt H α).source) := by
  classical
  refine continuousOn_finset_sum _ (fun k _ => ?_)
  -- Continuity of the model-norm of a continuous model-valued function,
  -- squared.
  have h_proj := triv_chartTensorRSCovariantDerivative_continuousOn_chart_source
    (I := I) (M := M) g r s α S k
  have h_norm : ContinuousOn
      (fun b : M =>
        ‖(trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSCovariantDerivative (I := I) r s g α
            (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α k) b)‖)
      ((chartAt H α).source) := h_proj.norm
  exact h_norm.pow 2

/-! ## Chart-source continuity of the integrand `b ↦ ρ_α(b) * √(∑ ‖·‖²)` -/

private lemma pou_mul_sqrt_sum_continuousOn_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    ContinuousOn
      (fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              ‖(trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toSection b')
                  (chartBasisVecFiber (I := I) α k) b)‖ ^ 2))
      ((chartAt H α).source) := by
  classical
  -- `ρ_α` is smooth, hence globally continuous, hence ContinuousOn.
  have h_pou_cont : Continuous
      (fun b : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b) :=
    ((chartAtlasPOU I M α).contMDiff.continuous)
  have h_pou_on : ContinuousOn
      (fun b : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b)
      ((chartAt H α).source) := h_pou_cont.continuousOn
  -- The norm-square sum is ContinuousOn chart source.
  have h_sumsq :=
    norm_sq_sum_triv_chartTensorRSCovariantDerivative_continuousOn_chart_source
      (I := I) (M := M) g r s α S
  -- The square root composition with a continuous function is continuous.
  have h_sqrt : ContinuousOn
      (fun b : M =>
        Real.sqrt
          (∑ k : Fin (Module.finrank ℝ E),
            ‖(trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                  ℝ b
              (chartTensorRSCovariantDerivative (I := I) r s g α
                (fun b' => S.toSection b')
                (chartBasisVecFiber (I := I) α k) b)‖ ^ 2))
      ((chartAt H α).source) :=
    Real.continuous_sqrt.comp_continuousOn h_sumsq
  exact h_pou_on.mul h_sqrt

/-! ## Chart-source continuity of the integrand on `tsupport ρ_α`

The closed support `tsupport ρ_α` is contained in `(chartAt H α).source`,
so the chart-source continuity restricts. -/

private lemma pou_mul_sqrt_sum_continuousOn_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    ContinuousOn
      (fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              ‖(trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toSection b')
                  (chartBasisVecFiber (I := I) α k) b)‖ ^ 2))
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) := by
  classical
  refine (pou_mul_sqrt_sum_continuousOn_chart_source
    (I := I) (M := M) g r s α S).mono ?_
  intro b hb
  -- `tsupport ρ_α ⊆ (trivAt E α).baseSet = (chartAt H α).source`.
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  exact hb_base

/-! ## Vanishing of the integrand off `tsupport ρ_α`

Outside the closed support of `ρ_α`, the `ρ_α`-factor is zero, hence the
integrand is zero. -/

private lemma pou_mul_sqrt_sum_zero_outside_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb : b ∉ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
        Real.sqrt
          (∑ k : Fin (Module.finrank ℝ E),
            ‖(trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                  ℝ b
              (chartTensorRSCovariantDerivative (I := I) r s g α
                (fun b' => S.toSection b')
                (chartBasisVecFiber (I := I) α k) b)‖ ^ 2) = 0 := by
  classical
  have hρ_zero : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b = 0 := by
    by_contra hne
    exact hb (subset_tsupport _ hne)
  rw [hρ_zero, zero_mul]

/-! ## Indicator identity

The integrand equals its indicator over `tsupport ρ_α` because it is
zero off this set. -/

private lemma pou_mul_sqrt_sum_eq_indicator
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    (fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              ‖(trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toSection b')
                  (chartBasisVecFiber (I := I) α k) b)‖ ^ 2)) =
      (tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
        (fun b : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            Real.sqrt
              (∑ k : Fin (Module.finrank ℝ E),
                ‖(trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                      ℝ b
                  (chartTensorRSCovariantDerivative (I := I) r s g α
                    (fun b' => S.toSection b')
                    (chartBasisVecFiber (I := I) α k) b)‖ ^ 2)) := by
  classical
  funext b
  by_cases hb : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
  · -- On the support, indicator coincides with the function value.
    rw [Set.indicator_of_mem hb]
  · -- Off the support, both sides equal zero.
    rw [Set.indicator_of_notMem hb]
    exact pou_mul_sqrt_sum_zero_outside_pouTsupport
      (I := I) (M := M) g r s α S hb

/-! ## Restricted-measure `AEStronglyMeasurable`

`ContinuousOn` on the compact closed set `tsupport ρ_α` lifts to
`AEStronglyMeasurable` on the restricted Riemannian volume measure via
`ContinuousOn.aestronglyMeasurable_of_isCompact`. -/

private lemma pouTsupport_measurableSet (α : M) :
    MeasurableSet (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
  (isClosed_tsupport _).measurableSet

private lemma pou_mul_sqrt_sum_aestronglyMeasurable_restrict_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    AEStronglyMeasurable
      (fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              ‖(trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toSection b')
                  (chartBasisVecFiber (I := I) α k) b)‖ ^ 2))
      ((riemannianVolumeMeasure (I := I) (M := M) g).restrict
        (tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))) := by
  classical
  exact ContinuousOn.aestronglyMeasurable_of_isCompact
    (pou_mul_sqrt_sum_continuousOn_pouTsupport
      (I := I) (M := M) g r s α S)
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_measurableSet (I := I) (M := M) α)

/-! ## Public headline: `AEStronglyMeasurable` of the cov atom integrand

The chart-frame covariant-derivative atom integrand, written in the
trivialisation-projected form
`b ↦ ρ_α(b) * √(∑ k ‖triv.continuousLinearMapAt b (chartTensorRSCovariantDerivative ... b)‖²)`,
is `AEStronglyMeasurable` with respect to the Riemannian volume measure on
`(M, g)`. -/

/-- **`AEStronglyMeasurable` of the per-`α` chart-frame covariant-derivative
atom integrand.** For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`,
a chart base point `α : M`, and a smooth compactly-supported `H^1` tensor
section `S : SmoothCcTensorH1 g r s`, the function

```
b ↦ ρ_α(b) * √(∑ k, ‖triv.continuousLinearMapAt b
                    (chartTensorRSCovariantDerivative r s g α
                      S.toSection (chartBasisVecFiber α k) b)‖²)
```

is `AEStronglyMeasurable` with respect to `riemannianVolumeMeasure g`. -/
theorem aestronglyMeasurable_pou_mul_sqrt_sum_triv_chart_cov
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensorH1 g r s) :
    AEStronglyMeasurable
      (fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              ‖(trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toCcTensor.toSection b')
                  (chartBasisVecFiber (I := I) α k) b)‖ ^ 2))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  -- Replace the integrand by its `tsupport ρ_α`-indicator (they agree
  -- pointwise on `M` because `ρ_α = 0` off the support).
  rw [pou_mul_sqrt_sum_eq_indicator (I := I) (M := M) g r s α S.toCcTensor]
  -- `aestronglyMeasurable_indicator_iff` reduces to `AEStronglyMeasurable`
  -- on the restricted measure.
  rw [aestronglyMeasurable_indicator_iff
    (pouTsupport_measurableSet (I := I) (M := M) α)]
  exact pou_mul_sqrt_sum_aestronglyMeasurable_restrict_pouTsupport
    (I := I) (M := M) g r s α S.toCcTensor

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.aestronglyMeasurable_pou_mul_sqrt_sum_triv_chart_cov

end Sanity
