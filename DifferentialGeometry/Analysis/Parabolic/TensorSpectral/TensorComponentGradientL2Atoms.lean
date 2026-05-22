import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartComponents
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.GoodSetMeasure
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ChristoffelL2BoundFromH1
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ComponentL2BoundUniform
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.CovL2BoundFromH1
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.H1Compl
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.PreHilbert
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SlotChartSourceContMDiff
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SlotUniformBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TrivProj.Bridge
import DifferentialGeometry.Geometry.LocalChartConsistency
import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivativeAgreement
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Per-`α` gradient `L²` atom bounds and measurability companions

Consolidated `L²` bounds (and the `AEStronglyMeasurable` companion lemmas)
for the per-`α` partition-of-unity-weighted gradient atom integrands that
appear in the chart-frame scalar-component gradient `L²` assembly on a
closed Riemannian manifold `(M, g)`. The atoms covered are:

1. **Chart-source continuity for the covariant-derivative atom** —
   `aestronglyMeasurable_pou_mul_sqrt_sum_triv_chart_cov`.
2. **`L²` bound on the covariant-derivative atom sum** —
   `exists_eLpNorm_sq_pou_mul_sum_triv_chart_cov_le_const_mul_h1NormSq`.
3. **`L²` bound on the `raw²`-indicator atom over POU support** —
   `exists_integral_indicator_tsupp_raw_sq_le_const_mul_h1NormSq`.
4. **Unconditional `L²` bound on the Christoffel slot-correction sum** —
   `exists_eLpNorm_sq_pou_mul_sqrt_sum_christoffel_correction_le_const_mul_h1NormSq`.
5. **`AEStronglyMeasurable` of the per-`α` `raw²`-indicator atom** —
   `aestronglyMeasurable_indicator_tsupp_abs_raw`.
6. **`AEStronglyMeasurable` of the per-direction Christoffel slot-correction
   atom integrand** — `aestronglyMeasurable_pou_mul_sqrt_sum_christoffel_correction`.
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

/-! ## Chart-source continuity companion to the covariant-derivative atom -/

section CovariantAtomsChartSource

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ### File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The closed support of the chart-atlas partition-of-unity weight at `α`
is measurable in the Borel σ-algebra on `M`. -/
private lemma pouTsupport_measurableSet (α : M) :
    MeasurableSet (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
  (isClosed_tsupport _).measurableSet

/-! ### Point-only dependence of `chartTensorRSCovariantDerivative` in the
tangent field

The chart-frame `(r, s)`-tensor covariant derivative
`chartTensorRSCovariantDerivative r s g α T X b`, viewed as a function of the
tangent field `X`, depends only on the value of `X` at the basepoint `b`. -/

private lemma chartTensorRSCovariantDerivative_eq_of_eq_at
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X Y : Π b' : M, TangentSpace I b') {b : M} (hb : X b = Y b) :
    chartTensorRSCovariantDerivative (I := I) r s g α T X b =
      chartTensorRSCovariantDerivative (I := I) r s g α T Y b := by
  classical
  rw [chartTensorRSCovariantDerivative_def, chartTensorRSCovariantDerivative_def]
  rw [show tensorRSIntrinsicChartCLM (I := I) r s α T b (X b) =
      tensorRSIntrinsicChartCLM (I := I) r s α T b (Y b) from by rw [hb]]
  have hPara :
      chartLeviCivitaParallelCLM (I := I) g α b X =
        chartLeviCivitaParallelCLM (I := I) g α b Y := by
    unfold chartLeviCivitaParallelCLM
    rw [hb]
  have hInput : ∀ k : Fin r,
      chartTensorRSInputSlotCorrection (I := I) r s g α T X b k =
        chartTensorRSInputSlotCorrection (I := I) r s g α T Y b k := by
    intro k
    unfold chartTensorRSInputSlotCorrection
    rw [hPara]
  have hOutput : ∀ l : Fin s,
      chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l =
        chartTensorRSOutputSlotCorrection (I := I) r s g α T Y b l := by
    intro l
    unfold chartTensorRSOutputSlotCorrection
    rw [hPara]
  rw [Finset.sum_congr rfl (fun k _ => hInput k)]
  rw [Finset.sum_congr rfl (fun l _ => hOutput l)]

/-! ### Pointwise bridge: chart-frame covariant derivative ↔ abstract directional
derivative -/

lemma chartTensorRSCovariantDerivative_eq_tensorCovDerivAt_at
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (X : Π b' : M, TangentSpace I b')
    {b : M} (hb : b ∈ (chartAt H α).source) :
    chartTensorRSCovariantDerivative (I := I) r s g α
        (fun b' => S.toSection b') X b =
      tensorCovDerivAt (I := I) (M := M) g r s S b (X b) := by
  classical
  obtain ⟨Y, hYb⟩ :=
    ContMDiffSection.exists_eq_at (I := I) (F := E) (n := (⊤ : ℕ∞))
      (V := (TangentSpace I : M → Type _)) b (X b)
  have hswap :
      chartTensorRSCovariantDerivative (I := I) r s g α
          (fun b' => S.toSection b') X b =
        chartTensorRSCovariantDerivative (I := I) r s g α
          (fun b' => S.toSection b') Y.toFun b :=
    chartTensorRSCovariantDerivative_eq_of_eq_at
      (I := I) g r s α (fun b' => S.toSection b') X Y.toFun hYb.symm
  rw [hswap]
  have hb_goodSet : b ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α,
        extChartAt_source_eq_chartAt_source (I := I)]
    exact hb
  have hagree :=
    chartTensorRSCovariantDerivative_eq_abstract
      (I := I) (M := M) g r s α S.toSection Y hb_goodSet
  change chartTensorRSCovariantDerivative (I := I) r s g α
      (fun b' => S.toSection b') Y.toFun b =
    TensorRSNabla.tensorRSCovariantDerivative I M r s
      (LeviCivita (I := I) g) (fun b' => S.toSection b') b (X b)
  have hagree' :
      chartTensorRSCovariantDerivative (I := I) r s g α
          (fun b' => S.toSection b') Y.toFun b =
        TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g) (fun b' => S.toSection b') b (Y.toFun b) :=
    hagree
  rw [hagree']
  have hYb' : Y.toFun b = X b := hYb
  rw [hYb']

/-! ### Chart-source continuity of the trivialisation-projected chart-frame
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
  have hcov_eq :=
    chartTensorRSCovariantDerivative_eq_tensorCovDerivAt_at
      (I := I) (M := M) g r s α S (chartBasisVecFiber (I := I) α k) hb
  rw [hcov_eq]
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
  have hbase_eq :
      (trivializationAt E (TangentSpace I) α).baseSet =
        (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source α
  rw [hbase_eq] at hbase
  refine hbase.congr ?_
  intro b hb_chart
  exact triv_continuousLinearMapAt_chartTensorRSCovariantDerivative_eq_triv_snd
    (I := I) (M := M) g r s α S hb_chart k

/-! ### Chart-source continuity of the squared-norm sum -/

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

/-! ### Chart-source continuity of the integrand `b ↦ ρ_α(b) * √(∑ ‖·‖²)` -/

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
  have h_pou_cont : Continuous
      (fun b : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b) :=
    ((chartAtlasPOU I M α).contMDiff.continuous)
  have h_pou_on : ContinuousOn
      (fun b : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b)
      ((chartAt H α).source) := h_pou_cont.continuousOn
  have h_sumsq :=
    norm_sq_sum_triv_chartTensorRSCovariantDerivative_continuousOn_chart_source
      (I := I) (M := M) g r s α S
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
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  exact hb_base

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
  · rw [Set.indicator_of_mem hb]
  · rw [Set.indicator_of_notMem hb]
    exact pou_mul_sqrt_sum_zero_outside_pouTsupport
      (I := I) (M := M) g r s α S hb

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
  rw [pou_mul_sqrt_sum_eq_indicator (I := I) (M := M) g r s α S.toCcTensor]
  rw [aestronglyMeasurable_indicator_iff
    (pouTsupport_measurableSet (I := I) (M := M) α)]
  exact pou_mul_sqrt_sum_aestronglyMeasurable_restrict_pouTsupport
    (I := I) (M := M) g r s α S.toCcTensor

/-! ## `L²` bound on the covariant-derivative atom sum -/

private lemma triv_continuousLinearMapAt_chart_cov_eq_chartRSTwistInv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M} (hb : b ∈ (chartAt H α).source)
    (k : Fin (Module.finrank ℝ E)) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
      (chartTensorRSCovariantDerivative (I := I) r s g α
        (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α k) b) =
      chartRSTwistInv (I := I) (M := M) α b r s
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α k b))) := by
  classical
  have hcov_eq :=
    chartTensorRSCovariantDerivative_eq_tensorCovDerivAt_at
      (I := I) (M := M) g r s α S (chartBasisVecFiber (I := I) α k) hb
  rw [hcov_eq]
  exact triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
    (I := I) (M := M) r s α (b := b) hb
    (tensorCovDerivAt (I := I) (M := M) g r s S b
      (chartBasisVecFiber (I := I) α k b))

private lemma pou_mul_sqrt_sum_triv_chart_cov_eq_pou_mul_sqrt_sum_chartRSTwistInv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (b : M) :
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
        Real.sqrt
          (∑ k : Fin (Module.finrank ℝ E),
            ‖(trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              (chartTensorRSCovariantDerivative (I := I) r s g α
                (fun b' => S.toSection b')
                (chartBasisVecFiber (I := I) α k) b)‖ ^ 2) =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
        Real.sqrt
          (∑ k : Fin (Module.finrank ℝ E),
            ‖chartRSTwistInv (I := I) (M := M) α b r s
                (TensorRSSpace.toModel
                  (tensorCovDerivAt (I := I) (M := M) g r s S b
                    (chartBasisVecFiber (I := I) α k b)))‖ ^ 2) := by
  classical
  by_cases hb : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
  · have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      pouTsupport_subset_baseSet (I := I) (M := M) α hb
    have hb_chart : b ∈ (chartAt H α).source := hb_base
    have hsumeq :
        (∑ k : Fin (Module.finrank ℝ E),
          ‖(trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSCovariantDerivative (I := I) r s g α
              (fun b' => S.toSection b')
              (chartBasisVecFiber (I := I) α k) b)‖ ^ 2) =
          ∑ k : Fin (Module.finrank ℝ E),
            ‖chartRSTwistInv (I := I) (M := M) α b r s
                (TensorRSSpace.toModel
                  (tensorCovDerivAt (I := I) (M := M) g r s S b
                    (chartBasisVecFiber (I := I) α k b)))‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [triv_continuousLinearMapAt_chart_cov_eq_chartRSTwistInv
        (I := I) (M := M) g r s α S hb_chart k]
    rw [hsumeq]
  · have hρ_zero : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b = 0 := by
      by_contra hne
      exact hb (subset_tsupport _ hne)
    rw [hρ_zero]
    ring

/-- **Per-`α` `L²` bound on the covariant-derivative atom sum.** For a closed
Riemannian manifold `(M, g)`, ranks `(r, s)`, and a chart base point `α : M`,
there is a non-negative real constant `C` (depending only on `(g, r, s, α)`)
such that for every smooth compactly-supported `H¹` tensor section
`S : SmoothCcTensorH1 g r s`,

```
eLpNorm
    (fun b ↦ ρ_α(b) *
      √ (∑ k, ‖triv.continuousLinearMapAt b
              (chartTensorRSCovariantDerivative r s g α S.toSection
                (chartBasisVecFiber α k) b)‖²))
    2 (riemannianVolumeMeasure g) ≤
  ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞),
```

where `ρ_α` is the chart-atlas partition-of-unity weight at `α`. The constant
`C` is independent of `S`. The locality hypothesis
`HasLocallyConstantChartAt H M` is accepted in the signature for symmetry with
neighbouring per-`α` atom bounds; the proof itself does not need it. -/
theorem exists_eLpNorm_sq_pou_mul_sum_triv_chart_cov_le_const_mul_h1NormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s),
        eLpNorm
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
            2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C, hC_nn, h_eL⟩ :=
    exists_eLpNorm_chartPou_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm
      (I := I) (M := M) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S
  have h_pt :
      (fun b : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            Real.sqrt
              (∑ k : Fin (Module.finrank ℝ E),
                ‖(trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                      ℝ b
                  (chartTensorRSCovariantDerivative (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α k) b)‖ ^ 2)) =
        (fun b : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            Real.sqrt
              (∑ k : Fin (Module.finrank ℝ E),
                ‖chartRSTwistInv (I := I) (M := M) α b r s
                    (TensorRSSpace.toModel
                      (tensorCovDerivAt (I := I) (M := M) g r s
                        S.toCcTensor b
                        (chartBasisVecFiber (I := I) α k b)))‖ ^ 2)) := by
    funext b
    exact pou_mul_sqrt_sum_triv_chart_cov_eq_pou_mul_sqrt_sum_chartRSTwistInv
      (I := I) (M := M) g r s α S.toCcTensor b
  rw [h_pt]
  exact h_eL S

end CovariantAtomsChartSource

/-! ## `L²` bound on the `raw²`-indicator atom -/

section RawAtoms

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

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

/-- **Pointwise quadratic upper bound on the chart-pullback raw scalar.** -/
private lemma scalarOnE_raw_sq_le_const_mul_tensorInner_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E))
        {b : M}, b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
          (scalarOnE (I := I) α
              (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
              (extChartAt I α b)) ^ 2 ≤
            C * tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b) := by
  classical
  obtain ⟨K, hK_nn, h_norm⟩ :=
    tensorTrivProj_norm_sq_le_const_mul_tensorInner
      (I := I) (M := M) (E := E) g r s α
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  refine ⟨C_proj ^ 2 * K, mul_nonneg (sq_nonneg _) hK_nn, ?_⟩
  intro S Idx Jdx b hb
  rw [scalarOnE_raw_eq_raw_on_pouTsupport (I := I) (M := M) g r s α S Idx Jdx hb]
  unfold tensorChartComponentRaw
  set T : TensorRSModel r s ℝ E :=
    tensorTrivProj (I := I) (M := M) g r s S α b
  set P_IJ : TensorRSModel r s ℝ E →L[ℝ] ℝ :=
    tensorChartComponentProjection (E := E) r s Idx Jdx
  have h_proj_le : ‖P_IJ T‖ ≤ C_proj * ‖T‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right
        (tensorChartComponentProjection_norm_le_uniform (E := E) r s Idx Jdx)
        (norm_nonneg _))
  have h_proj_sq_le : (P_IJ T) ^ 2 ≤ C_proj ^ 2 * ‖T‖ ^ 2 := by
    have h_abs : (P_IJ T) ^ 2 = ‖P_IJ T‖ ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
    rw [h_abs]
    have hsq := mul_self_le_mul_self (norm_nonneg _) h_proj_le
    have h_rhs : (C_proj * ‖T‖) * (C_proj * ‖T‖) = C_proj ^ 2 * ‖T‖ ^ 2 := by
      ring
    have h_lhs : ‖P_IJ T‖ * ‖P_IJ T‖ = ‖P_IJ T‖ ^ 2 := by rw [sq]
    linarith [hsq, h_lhs.symm.le, h_rhs.symm.le, h_lhs.le, h_rhs.le]
  have h_triv_sq_le : ‖T‖ ^ 2 ≤ K *
      tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) := h_norm S b hb
  have hC_proj_sq_nn : 0 ≤ C_proj ^ 2 := sq_nonneg _
  have h_chain_sq : (P_IJ T) ^ 2 ≤
      C_proj ^ 2 *
        (K * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) := by
    have h_mul := mul_le_mul_of_nonneg_left h_triv_sq_le hC_proj_sq_nn
    exact h_proj_sq_le.trans h_mul
  have h_reassoc :
      C_proj ^ 2 *
        (K * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) =
        C_proj ^ 2 * K *
          tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) := by ring
  linarith [h_chain_sq, h_reassoc.le, h_reassoc.symm.le]

private lemma indicator_scalarOnE_raw_sq_le_const_mul_tensorInner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E))
        (b : M),
          ((tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
            (fun b' : M => scalarOnE (I := I) α
              (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
              (extChartAt I α b')) b) ^ 2 ≤
            C * tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b) := by
  classical
  obtain ⟨C, hC_nn, h_pt⟩ :=
    scalarOnE_raw_sq_le_const_mul_tensorInner_on_pouTsupport
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S Idx Jdx b
  set ρSet : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
  set F : M → ℝ := fun b' : M => scalarOnE (I := I) α
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
      (extChartAt I α b')
  by_cases hb : b ∈ ρSet
  · have h_ind_eq : ρSet.indicator F b = F b := Set.indicator_of_mem hb _
    rw [h_ind_eq]
    exact h_pt S Idx Jdx hb
  · have h_ind_eq : ρSet.indicator F b = 0 := Set.indicator_of_notMem hb _
    rw [h_ind_eq]
    have hQ_nn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) :=
      tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
    have h_RHS_nn : 0 ≤ C * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) := mul_nonneg hC_nn hQ_nn
    have hzero_sq : (0 : ℝ) ^ 2 = 0 := by ring
    rw [hzero_sq]
    exact h_RHS_nn

private lemma sq_eLpNorm_two_eq_lintegral_enorm_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top]
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  rw [h2_toReal]
  have h_inner_eq : ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
      ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards with x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

private lemma le_sqrt_of_sq_le {x y : ℝ≥0∞} (h : x ^ 2 ≤ y) :
    x ≤ y ^ ((1 : ℝ) / 2) := by
  have h_xpow : x = (x ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
    norm_num
  conv_lhs => rw [h_xpow]
  exact ENNReal.rpow_le_rpow h (by norm_num)

private lemma sqrt_ofReal_eq_ofReal_sqrt {S : ℝ} (hS : 0 ≤ S) :
    (ENNReal.ofReal S) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (Real.sqrt S) := by
  rw [show S = Real.sqrt S * Real.sqrt S from (Real.mul_self_sqrt hS).symm,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    show (ENNReal.ofReal (Real.sqrt S)) * (ENNReal.ofReal (Real.sqrt S)) =
      (ENNReal.ofReal (Real.sqrt S)) ^ 2 from by ring,
    ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

private lemma eLpNorm_two_le_ofReal_sqrt
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {S : ℝ} (hS : 0 ≤ S)
    (h_sq : (eLpNorm f 2 μ) ^ 2 ≤ ENNReal.ofReal S) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt S) := by
  have h_pow := le_sqrt_of_sq_le h_sq
  rw [sqrt_ofReal_eq_ofReal_sqrt hS] at h_pow
  exact h_pow

private lemma sq_eLpNorm_indicator_raw_le_const_mul_tensorL2Inner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        (eLpNorm (fun b : M =>
            (tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
              (fun b' : M => scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
                (extChartAt I α b')) b) 2
            (riemannianVolumeMeasure (I := I) (M := M) g)) ^ 2 ≤
          ENNReal.ofReal (C *
            tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun) := by
  classical
  obtain ⟨C, hC_nn, h_pt⟩ :=
    indicator_scalarOnE_raw_sq_le_const_mul_tensorInner
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S Idx Jdx
  set f : M → ℝ := fun b : M =>
    (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
      (fun b' : M => scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (extChartAt I α b')) b
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  have h_pt_enn : ∀ b : M,
      (‖f b‖ₑ : ℝ≥0∞) ^ 2 ≤
        ENNReal.ofReal (C * tensorInnerPointwise (I := I) (M := M)
          g r s b (S.toFun b) (S.toFun b)) := by
    intro b
    rw [show (‖f b‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((f b) ^ 2) by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]]
    exact ENNReal.ofReal_le_ofReal (h_pt S Idx Jdx b)
  have h_inner_int := SmoothCcTensor.integrable_inner_cross
    (I := I) (M := M) (g := g) (r := r) (s := s) S S
  have h_C_smul_int :
      Integrable (fun b : M => C *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b)) μ :=
    h_inner_int.const_mul C
  have h_C_smul_nn :
      0 ≤ᵐ[μ] (fun b : M => C * tensorInnerPointwise
        (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) := by
    refine Filter.Eventually.of_forall ?_
    intro b
    exact mul_nonneg hC_nn
      (tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _)
  rw [sq_eLpNorm_two_eq_lintegral_enorm_sq μ f]
  have h_lint_le :
      ∫⁻ b, (‖f b‖ₑ : ℝ≥0∞) ^ 2 ∂μ ≤
        ∫⁻ b, ENNReal.ofReal (C * tensorInnerPointwise
          (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards with b using h_pt_enn b
  have h_lint_eq :
      ∫⁻ b, ENNReal.ofReal (C * tensorInnerPointwise
        (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) ∂μ =
        ENNReal.ofReal (∫ b, C * tensorInnerPointwise
          (I := I) (M := M) g r s b (S.toFun b) (S.toFun b) ∂μ) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      h_C_smul_int h_C_smul_nn).symm
  rw [h_lint_eq] at h_lint_le
  have h_int_const_mul :
      ∫ b, C * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) ∂μ =
        C * tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun := by
    unfold tensorL2Inner
    rw [integral_const_mul]
  rw [h_int_const_mul] at h_lint_le
  exact h_lint_le

private theorem indicator_eLpNorm_raw_le_const_mul_tensorL2Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (fun b : M =>
            (tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
              (fun b' : M => scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
                (extChartAt I α b')) b) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C *
            ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) := by
  classical
  obtain ⟨C, hC_nn, h_sq⟩ :=
    sq_eLpNorm_indicator_raw_le_const_mul_tensorL2Inner
      (I := I) (M := M) (E := E) g r s α
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  intro S Idx Jdx
  have h_inner_nn :
      0 ≤ tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun := by
    unfold tensorL2Inner
    refine integral_nonneg ?_
    intro b
    exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  have h_norm_sq :
      tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun =
        (tensorL2Norm (I := I) (M := M) g r s S.toFun) ^ 2 := by
    unfold tensorL2Norm
    rw [sq, Real.mul_self_sqrt h_inner_nn]
  set S_total : ℝ := C *
    tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun with hS_total_def
  have hS_total_nn : 0 ≤ S_total := mul_nonneg hC_nn h_inner_nn
  have h_eLpNorm_le :=
    eLpNorm_two_le_ofReal_sqrt hS_total_nn (h_sq S Idx Jdx)
  have h_sqrt_factor :
      Real.sqrt S_total = Real.sqrt C *
        tensorL2Norm (I := I) (M := M) g r s S.toFun := by
    rw [hS_total_def, h_norm_sq, Real.sqrt_mul hC_nn,
      show (tensorL2Norm (I := I) (M := M) g r s S.toFun) ^ 2 =
        tensorL2Norm (I := I) (M := M) g r s S.toFun *
          tensorL2Norm (I := I) (M := M) g r s S.toFun from by ring,
      Real.sqrt_mul_self
        (tensorL2Norm_nonneg (I := I) (M := M) g r s S.toFun)]
  rw [h_sqrt_factor,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at h_eLpNorm_le
  exact h_eLpNorm_le

private lemma tensorL2Norm_eq_norm_toCcTensor
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun =
      ‖S.toCcTensor‖ := by
  have h_sq := SmoothCcTensor.norm_sq_eq_inner_self
    (I := I) (M := M) (g := g) (r := r) (s := s) S.toCcTensor
  have h_l2_nn :
      0 ≤ tensorL2Inner (I := I) (M := M) g r s
        S.toCcTensor.toFun S.toCcTensor.toFun := by
    unfold tensorL2Inner
    refine MeasureTheory.integral_nonneg ?_
    intro x
    exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s x _
  have h_norm_nn : 0 ≤ ‖S.toCcTensor‖ := norm_nonneg _
  have h_lhs :
      tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun =
        Real.sqrt (tensorL2Inner (I := I) (M := M) g r s
          S.toCcTensor.toFun S.toCcTensor.toFun) := rfl
  rw [h_lhs]
  have h_rhs :
      ‖S.toCcTensor‖ = Real.sqrt
        (tensorL2Inner (I := I) (M := M) g r s
          S.toCcTensor.toFun S.toCcTensor.toFun) := by
    rw [← Real.sqrt_sq h_norm_nn, h_sq]
  rw [h_rhs]

private lemma coe_nnnorm_eq_ofReal_norm {X : Type*} [SeminormedAddCommGroup X]
    (x : X) :
    (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
  rw [show ((‖x‖₊ : ℝ≥0∞)) = ‖x‖ₑ from (enorm_eq_nnnorm x).symm,
    ← ofReal_norm_eq_enorm x]

private lemma ofReal_tensorL2Norm_le_norm_ennreal
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ENNReal.ofReal
        (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) ≤
      (‖S‖₊ : ℝ≥0∞) := by
  rw [tensorL2Norm_eq_norm_toCcTensor (I := I) (M := M) g r s S]
  have h_l2_le_h1 :
      ‖S.toCcTensor‖ ≤ ‖S‖ :=
    SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S
  rw [coe_nnnorm_eq_ofReal_norm S]
  exact ENNReal.ofReal_le_ofReal h_l2_le_h1

/-- **Per-`α` `L²` bound on the `raw²` chart-component indicator over POU
support.** -/
theorem exists_integral_indicator_tsupp_raw_sq_le_const_mul_h1NormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm
          (fun b : M => (tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
            (fun b' : M =>
              scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx)
                (extChartAt I α b')) b) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C, hC_nn, h_smoothCc⟩ :=
    indicator_eLpNorm_raw_le_const_mul_tensorL2Norm
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S Idx Jdx
  have h_smoothCc' :
      eLpNorm (fun b : M =>
          (tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
            (fun b' : M => scalarOnE (I := I) α
              (tensorChartComponentRaw (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx)
              (extChartAt I α b')) b) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C *
          ENNReal.ofReal
            (tensorL2Norm (I := I) (M := M) g r s
              S.toCcTensor.toFun) :=
    h_smoothCc S.toCcTensor Idx Jdx
  have h_rhs_le :
      ENNReal.ofReal C *
        ENNReal.ofReal
          (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) ≤
        ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) :=
    mul_le_mul_of_nonneg_left
      (ofReal_tensorL2Norm_le_norm_ennreal (I := I) (M := M) g r s S)
      (by exact zero_le _)
  exact h_smoothCc'.trans h_rhs_le

end RawAtoms

/-! ## Unconditional `L²` bound on the Christoffel slot-correction atom sum -/

section ChristoffelAtoms

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma exists_eLpNorm_chartPou_mul_sqrt_slotCorrection_per_direction
    (h_atlas : HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s),
        eLpNorm
            (fun b : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                Real.sqrt
                  ((∑ k : Fin r,
                      ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (chartBasisVecFiber (I := I) α j) b k‖ ^ 2) +
                    (∑ l : Fin s,
                      ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (chartBasisVecFiber (I := I) α j) b l‖ ^ 2)))
            2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨M_F_in, hM_F_in_nn, hM_F_in_le⟩ :=
    chartTensorRSInputSlotCorrection_norm_le_const_on_pouTsupport
      (I := I) (M := M) h_atlas g r s α
  obtain ⟨M_F_out, hM_F_out_nn, hM_F_out_le⟩ :=
    chartTensorRSOutputSlotCorrection_norm_le_const_on_pouTsupport
      (I := I) (M := M) h_atlas g r s α
  set M_F : ℝ := max M_F_in M_F_out with hM_F_def
  have hM_F_nn : 0 ≤ M_F := le_max_of_le_left hM_F_in_nn
  have hM_F_in_le' : M_F_in ≤ M_F := le_max_left _ _
  have hM_F_out_le' : M_F_out ≤ M_F := le_max_right _ _
  have hM_F_input :
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ k : Fin r,
          ‖chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α j) b k‖ ≤
            M_F * ‖S.toSection b‖ := by
    intro S b hb k
    have h_orig :=
      hM_F_in_le (fun b' => S.toSection b') (b := b) hb j k
    have h_factor : M_F_in * ‖S.toSection b‖ ≤ M_F * ‖S.toSection b‖ :=
      mul_le_mul_of_nonneg_right hM_F_in_le' (norm_nonneg _)
    exact h_orig.trans h_factor
  have hM_F_output :
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ l : Fin s,
          ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α j) b l‖ ≤
            M_F * ‖S.toSection b‖ := by
    intro S b hb l
    have h_orig :=
      hM_F_out_le (fun b' => S.toSection b') (b := b) hb j l
    have h_factor : M_F_out * ‖S.toSection b‖ ≤ M_F * ‖S.toSection b‖ :=
      mul_le_mul_of_nonneg_right hM_F_out_le' (norm_nonneg _)
    exact h_orig.trans h_factor
  obtain ⟨K_S, hK_S_nn, hK_S_bound⟩ :=
    norm_section_sq_le_const_mul_tensorInnerPointwise_on_pouTsupport
      (I := I) (M := M) h_atlas g r s α
  exact
    exists_eLpNorm_chartPou_mul_sqrt_chart_christoffel_correction_le_const_mul_h1Norm
      (I := I) (M := M) g r s α (chartBasisVecFiber (I := I) α j)
      hM_F_nn hM_F_input hM_F_output hK_S_nn hK_S_bound

/-- **Unconditional `L²` bound on the partition-of-unity-weighted Christoffel
slot-correction sum.** -/
theorem exists_eLpNorm_sq_pou_mul_sqrt_sum_christoffel_correction_le_const_mul_h1NormSq
    (h_atlas : HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s),
        eLpNorm
            (fun b : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                Real.sqrt
                  ((∑ k : Fin r,
                      ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (chartBasisVecFiber (I := I) α j) b k‖ ^ 2) +
                    (∑ l : Fin s,
                      ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (chartBasisVecFiber (I := I) α j) b l‖ ^ 2)))
            2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) :=
  exists_eLpNorm_chartPou_mul_sqrt_slotCorrection_per_direction
    (I := I) (M := M) h_atlas g r s α j

end ChristoffelAtoms

/-! ## `AEStronglyMeasurable` companions for the `raw²` and Christoffel atoms -/

section AtomMeasurability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The closed support of the chart-atlas partition-of-unity weight at `α`
is measurable in the Borel σ-algebra on `M`. -/
private lemma pouTsupport_measurableSet_meas (α : M) :
    MeasurableSet (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
  (isClosed_tsupport _).measurableSet

/-! ### `AEStronglyMeasurable` of the per-`α` `raw²`-indicator atom -/

private lemma scalarOnE_raw_eq_raw_on_pouTsupport_meas
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
  exact scalarOnE_raw_eq_raw_on_pouTsupport_meas
    (I := I) (M := M) g r s α S Idx Jdx hb

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
    (pouTsupport_measurableSet_meas (I := I) (M := M) α)

/-- **`AEStronglyMeasurable` of the per-`α` `raw²`-indicator atom.** -/
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
  set ρSet : Set M := tsupport (fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hρSet_def
  have hρSet_meas : MeasurableSet ρSet :=
    pouTsupport_measurableSet_meas (I := I) (M := M) α
  rw [aestronglyMeasurable_indicator_iff hρSet_meas]
  exact abs_scalarOnE_raw_aestronglyMeasurable_restrict_pouTsupport
    (I := I) (M := M) g r s α S.toCcTensor Idx Jdx

/-! ### `AEStronglyMeasurable` of the per-direction Christoffel slot-correction
atom integrand -/

section ChristoffelAtomMeasurability

variable (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
  (j : Fin (Module.finrank ℝ E))

private def trivInput
    (T : Π b' : M, TensorRSSpace r s I b') (b : M) (k : Fin r) :
    TensorRSModel r s ℝ E :=
  (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
    (chartTensorRSInputSlotCorrection (I := I) r s g α
      (fun b' => T b') (chartBasisVecFiber (I := I) α j) b k)

private def trivOutput
    (T : Π b' : M, TensorRSSpace r s I b') (b : M) (l : Fin s) :
    TensorRSModel r s ℝ E :=
  (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
    (chartTensorRSOutputSlotCorrection (I := I) r s g α
      (fun b' => T b') (chartBasisVecFiber (I := I) α j) b l)

private def christoffelAtomIntegrand
    (T : Π b' : M, TensorRSSpace r s I b') (b : M) : ℝ :=
  ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
    Real.sqrt
      ((∑ k : Fin r, ‖trivInput (I := I) g r s α j T b k‖ ^ 2) +
       (∑ l : Fin s, ‖trivOutput (I := I) g r s α j T b l‖ ^ 2))

private lemma triv_continuousLinearMapAt_eq_triv_snd
    {b : M} (hb : b ∈ (chartAt H α).source) (v : TensorRSSpace r s I b) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b v =
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α ⟨b, v⟩).2 := by
  classical
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

variable {g r s α j} in
private lemma christoffelAtomIntegrand_continuousOn_chartSource
    (S : SmoothCcTensor g r s) :
    ContinuousOn (christoffelAtomIntegrand (I := I) g r s α j S.toSection)
      ((chartAt H α).source) := by
  classical
  have h_pou : ContinuousOn
      (fun b : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b)
      ((chartAt H α).source) :=
    ((chartAtlasPOU I M α).contMDiff.continuous).continuousOn
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
    (pouTsupport_measurableSet_meas (I := I) (M := M) α)

end ChristoffelAtomMeasurability

/-- **`AEStronglyMeasurable` of the per-`α` per-direction Christoffel
slot-correction atom integrand.** -/
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
  change AEStronglyMeasurable
    (christoffelAtomIntegrand (I := I) g r s α j S.toCcTensor.toSection)
    (riemannianVolumeMeasure (I := I) (M := M) g)
  rw [christoffelAtomIntegrand_eq_indicator (I := I)
    (T := fun b' : M => S.toCcTensor.toSection b')]
  rw [aestronglyMeasurable_indicator_iff
    (pouTsupport_measurableSet_meas (I := I) (M := M) α)]
  exact christoffelAtomIntegrand_aestronglyMeasurable_restrict_pouTsupport
    (I := I) S.toCcTensor

end AtomMeasurability

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.aestronglyMeasurable_pou_mul_sqrt_sum_triv_chart_cov
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_sq_pou_mul_sum_triv_chart_cov_le_const_mul_h1NormSq
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_integral_indicator_tsupp_raw_sq_le_const_mul_h1NormSq
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_sq_pou_mul_sqrt_sum_christoffel_correction_le_const_mul_h1NormSq
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.aestronglyMeasurable_indicator_tsupp_abs_raw
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.aestronglyMeasurable_pou_mul_sqrt_sum_christoffel_correction
end Sanity
