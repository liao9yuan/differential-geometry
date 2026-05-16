import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.CovL2BoundFromH1
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SectionNormFromTensorInner
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SlotCorrectionUniformBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TrivProjBridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartGoodSetMeasure
import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivativeAgreement

/-!
# Per-`α` `L²` bound on the covariant-derivative atom sum over POU support

For a closed Riemannian manifold `(M, g)` modelled on `(E, H, I)`, a chart base
point `α : M`, and ranks `(r, s)`, this file ships a uniform `L²` bound on the
partition-of-unity-weighted Euclidean norm of the sum-over-directions of the
trivialisation-projected chart-frame covariant-derivative atoms

```
Tcov_sum α b :=
  ∑ k, ‖triv.continuousLinearMapAt b
    (chartTensorRSCovariantDerivative r s g α S.toSection
      (chartBasisVecFiber α k) b)‖^2.
```

The headline reads

```
eLpNorm (fun b ↦ ρ_α(b) · √(Tcov_sum α b)) 2 (riemannianVolumeMeasure g)
  ≤ ENNReal.ofReal C · (‖S‖₊ : ℝ≥0∞)
```

for every `S : SmoothCcTensorH1 g r s`, with a non-negative real constant `C`
depending only on `(g, r, s, α)`.

## Strategy

The existing per-`α` conditional bound
`exists_eLpNorm_chartPou_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm`
controls the analogous integrand stated in terms of the *abstract* directional
covariant derivative `tensorCovDerivAt` and the *inverse chart-`(α, b)` twist*
`chartRSTwistInv`. To re-express it in terms of the *chart-frame* covariant
derivative and the *trivialisation-`α` continuousLinearMapAt`-action*, two
pointwise identities are chained:

* `triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel` (from
  `TrivProjBridge.lean`) — on the chart-`α` source, the trivialisation's
  `continuousLinearMapAt ℝ b` action on any fibre element coincides with the
  inverse chart twist of its model image.
* `chartTensorRSCovariantDerivative_eq_abstract` (from
  `Integral.Connection.ChartTensorRSCovariantDerivativeAgreement`) — on the
  chart Levi-Civita good set, the chart-frame covariant derivative of a
  smooth section agrees with the bundled one. Combined with the
  `[I.Boundaryless]` identification
  `chartLeviCivitaGoodSet α = (extChartAt I α).source`
  (`chartLeviCivitaGoodSet_eq_extChartAt_source`), the bridge applies on the
  entire chart-`α` source.

To plug the basis vector field `chartBasisVecFiber α k` — which is only
smooth on the chart-`α` source, not globally — into the agreement (which
takes a globally smooth tangent field), we exploit a structural property of
`chartTensorRSCovariantDerivative`: at a single point `b`, its value depends
on the tangent field `X` only through `X b`. A globally smooth tangent field
`Y` with `Y b = chartBasisVecFiber α k b` exists by
`ContMDiffSection.exists_eq_at`; switching to `Y` makes the agreement
applicable, and the pointwise-in-`X` independence then transfers the result
back to `chartBasisVecFiber α k`.

On the closed support of the chart-atlas partition-of-unity weight at `α`
(`tsupport ρ_α ⊆ (chartAt H α).source`), both bridges apply pointwise,
turning the two integrands into pointwise-equal real numbers. Outside the
support, `ρ_α(b) = 0` annihilates the factor and forces both integrands to
zero. Hence the new integrand equals the existing one identically as a
function on `M`, and the new headline follows from the existing conditional
without changing the constant.

## Public theorem

* `exists_eLpNorm_sq_pou_mul_sum_triv_chart_cov_le_const_mul_h1NormSq` — the
  per-`α` `L²` bound on the partition-of-unity-weighted Euclidean norm of the
  covariant-derivative atom sum, controlled by the `H¹` seminorm of `S`.
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

/-! ## Point-only dependence of `chartTensorRSCovariantDerivative` in the
tangent field

The chart-frame `(r, s)`-tensor covariant derivative
`chartTensorRSCovariantDerivative r s g α T X b`, viewed as a function of the
tangent field `X`, depends only on the value of `X` at the basepoint `b`.
This is immediate from the explicit formula: the intrinsic chart piece
`tensorRSIntrinsicChartCLM r s α T b (X b)` is linear in `X b`, and each
slot-Christoffel correction is built from
`chartLeviCivitaParallelCLM g α b X = (trivFromE α b) ∘ christoffelCorrection
g α b (trivToE α b (X b))`, which again only uses `X b`. -/

private lemma chartTensorRSCovariantDerivative_eq_of_eq_at
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X Y : Π b' : M, TangentSpace I b') {b : M} (hb : X b = Y b) :
    chartTensorRSCovariantDerivative (I := I) r s g α T X b =
      chartTensorRSCovariantDerivative (I := I) r s g α T Y b := by
  classical
  rw [chartTensorRSCovariantDerivative_def, chartTensorRSCovariantDerivative_def]
  -- Intrinsic part depends only on `X b`.
  rw [show tensorRSIntrinsicChartCLM (I := I) r s α T b (X b) =
      tensorRSIntrinsicChartCLM (I := I) r s α T b (Y b) from by rw [hb]]
  -- Slot corrections depend only on `X b` via `chartLeviCivitaParallelCLM`.
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

/-! ## Pointwise bridge: chart-frame covariant derivative ↔ abstract directional
derivative

By combining `chartTensorRSCovariantDerivative_eq_abstract` (chart-frame /
abstract agreement on `chartLeviCivitaGoodSet`) with the `[I.Boundaryless]`
identification `chartLeviCivitaGoodSet α = (extChartAt I α).source` and the
point-only dependence in `X`, we obtain a pointwise bridge that does **not**
require global smoothness of `X`: at any chart-`α` source point, the chart-
frame covariant derivative of a smooth `(r, s)`-tensor section equals the
bundled directional covariant derivative, evaluated at the value `X b`. -/

lemma chartTensorRSCovariantDerivative_eq_tensorCovDerivAt_at
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (X : Π b' : M, TangentSpace I b')
    {b : M} (hb : b ∈ (chartAt H α).source) :
    chartTensorRSCovariantDerivative (I := I) r s g α
        (fun b' => S.toSection b') X b =
      tensorCovDerivAt (I := I) (M := M) g r s S b (X b) := by
  classical
  -- Build a globally smooth tangent field `Y` with `Y b = X b` via the
  -- vector-bundle existence lemma.
  obtain ⟨Y, hYb⟩ :=
    ContMDiffSection.exists_eq_at (I := I) (F := E) (n := (⊤ : ℕ∞))
      (V := (TangentSpace I : M → Type _)) b (X b)
  -- The chart-frame value at `b` only depends on `X b`, so we may switch to
  -- `Y.toFun` without changing the value.
  have hswap :
      chartTensorRSCovariantDerivative (I := I) r s g α
          (fun b' => S.toSection b') X b =
        chartTensorRSCovariantDerivative (I := I) r s g α
          (fun b' => S.toSection b') Y.toFun b :=
    chartTensorRSCovariantDerivative_eq_of_eq_at
      (I := I) g r s α (fun b' => S.toSection b') X Y.toFun hYb.symm
  rw [hswap]
  -- Promote `b ∈ chart source` to `b ∈ chartLeviCivitaGoodSet` via
  -- `[I.Boundaryless]`.
  have hb_goodSet : b ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α,
        extChartAt_source_eq_chartAt_source (I := I)]
    exact hb
  -- Apply the agreement theorem with the smooth `Y`.
  have hagree :=
    chartTensorRSCovariantDerivative_eq_abstract
      (I := I) (M := M) g r s α S.toSection Y hb_goodSet
  -- `S.toSection.toFun = fun b' => S.toSection b'` and
  -- `(fun y => S.toSection y) = S.toSection.toFun` definitionally.
  -- `Y.toFun b = X b` from the construction.
  -- `tensorCovDerivAt g r s S b v` unfolds to
  --   `tensorRSCovariantDerivative I M r s (LeviCivita g) S.toSection b v`.
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
  -- `Y.toFun b = Y b = X b`.
  have hYb' : Y.toFun b = X b := hYb
  rw [hYb']

/-! ## Trivialisation `continuousLinearMapAt` ↔ inverse chart twist

A re-statement of `triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel`
specialised to the value
`chartTensorRSCovariantDerivative r s g α S.toSection (chartBasisVecFiber α k)
 b`, valid on the chart-`α` source. -/

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
  -- Bridge `chartTensorRSCovariantDerivative ↔ tensorCovDerivAt`.
  have hcov_eq :=
    chartTensorRSCovariantDerivative_eq_tensorCovDerivAt_at
      (I := I) (M := M) g r s α S (chartBasisVecFiber (I := I) α k) hb
  rw [hcov_eq]
  -- Bridge `triv.continuousLinearMapAt ↔ chartRSTwistInv ∘ toModel`.
  exact triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
    (I := I) (M := M) r s α (b := b) hb
    (tensorCovDerivAt (I := I) (M := M) g r s S b
      (chartBasisVecFiber (I := I) α k b))

/-! ## Pointwise integrand identity

On the closed support of the chart-`α` partition-of-unity weight, the new
covariant-derivative atom sum `Tcov_sum α b` equals the existing
trivialisation-twist atom sum used in
`exists_eLpNorm_chartPou_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm`.
Outside the support, the `ρ_α`-factor in the integrand vanishes, so the two
factor-weighted integrands coincide globally as functions on `M`. -/

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
  · -- Inside the support: both square-root arguments agree summand-by-
    -- summand by the pointwise bridge.
    have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
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
  · -- Outside the support: `ρ b = 0`, so both sides equal zero.
    have hρ_zero : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b = 0 := by
      by_contra hne
      exact hb (subset_tsupport _ hne)
    rw [hρ_zero]
    ring

/-! ## Headline `L²` bound

The squared `L²(volume)` seminorm of the partition-of-unity-weighted
Euclidean norm of the chart-frame covariant-derivative atom sum is uniformly
bounded by `ENNReal.ofReal C` times the `H¹` seminorm of `S`. -/

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
    (_h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
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
  -- Existing conditional bound: it provides a constant `C` for the
  -- chartRSTwistInv-form integrand.
  obtain ⟨C, hC_nn, h_eL⟩ :=
    exists_eLpNorm_chartPou_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm
      (I := I) (M := M) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S
  -- Pointwise equality of the two integrands, then `eLpNorm_congr`.
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

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_sq_pou_mul_sum_triv_chart_cov_le_const_mul_h1NormSq

end Sanity
