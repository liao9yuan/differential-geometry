import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorComponentGradientEpNormPerAlpha
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorComponentEpNormUniform
import DifferentialGeometry.Geometry.LocalChartConsistency
import Mathlib.Topology.Compactness.LocallyFinite

/-!
# `α`-uniform `L²` bound on the metric self-inner-product square-root of the
gradient of the chart-frame scalar component

For a closed Riemannian manifold `(M, g)` and a smooth compactly-supported
`H¹` tensor section `S : SmoothCcTensorH1 g r s`, this file delivers an
`α`-**uniform** `L²` bound on the metric self-inner-product square-root of
the gradient of the chart-frame scalar component
`u_α := tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx`:

```
eLpNorm (b ↦ √ g.inner b (∇u_α b) (∇u_α b)) 2 (riemannianVolumeMeasure g) ≤
  ENNReal.ofReal C_grad * ‖S‖₊
```

with a single non-negative real constant `C_grad` independent of the chart
base point `α : M`, the multi-index pair `(Idx, Jdx)`, and the section `S`.

## Strategy

The per-`α` headline
`exists_eLpNorm_sqrt_g_inner_gradFun_tensorChartComponentScalar_le_const_mul_h1Norm`
supplies, for each `α : M`, a non-negative constant `C(α)` such that the `L²`
norm of the square-root inner product of the gradient is bounded by
`ENNReal.ofReal C(α) · ‖S‖₊`, uniformly in `(S, Idx, Jdx)`.

To upgrade to an `α`-uniform constant, we exploit two ingredients (mirroring
the construction in `TensorComponentEpNormUniform.lean`):

1. **Compactness + local finiteness**: the chart-atlas partition of unity
   `chartAtlasPOU I M : SmoothPartitionOfUnity M I M univ` is locally
   finite, so on a compact manifold only finitely many index points
   `α : M` have non-empty `support(POU_α)`. The set of "active" centres
   is a `Finset M`.

2. **Vanishing on inactive centres**: when `support(POU_α) = ∅`, the scalar
   component `tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx` is
   identically zero. The gradient of the zero function vanishes everywhere,
   so the square-root inner product is `0`, and its `L²` norm is `0`.

Summing the per-`α` constants `C(α)` over the (finite) active set gives a
single non-negative constant `C_grad` that dominates each `C(α)`.

## Public theorem

* `tensorChartComponentScalar_grad_eLpNorm_le` — the
  headline `α`-uniform `L²` bound on the square-root inner product of the
  gradient of the chart-frame scalar component, for a smooth compactly-
  supported `H¹` tensor section, on a closed Riemannian manifold (assuming
  `[CompactSpace M]` for the finite-cover argument).
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
open DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Vanishing of the gradient self-inner integrand on inactive centres

When `α : M` lies outside the active partition-of-unity finset, the scalar
component `tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx` is
identically zero. Consequently `gradFun g u` vanishes everywhere, and the
metric self-inner integrand is identically zero. -/

/-- When the scalar component is identically zero, the metric self-inner
square-root of its gradient is identically zero. -/
private lemma sqrt_g_inner_gradFun_eq_zero_of_scalar_zero
    (g : SmoothRiemannianMetric I M)
    {u : M → ℝ} (h_u_zero : u = 0) :
    (fun b : M => Real.sqrt
        (g.inner b (gradFun (I := I) g u b)
          (gradFun (I := I) g u b))) = 0 := by
  funext b
  -- `gradFun g u b = 0` because `u` is the zero function.
  have h_ev : u =ᶠ[𝓝 b] (fun _ : M => (0 : ℝ)) := by
    rw [h_u_zero]; rfl
  have h_grad_zero :
      gradFun (I := I) g u b = (0 : TangentSpace I b) :=
    gradFun_eq_zero_of_eventuallyEq_zero (I := I) g h_ev
  rw [h_grad_zero]
  -- `g.inner b 0 0 = 0`.
  have h_map : g.inner b (0 : TangentSpace I b) =
      (0 : TangentSpace I b →L[ℝ] ℝ) := map_zero _
  rw [h_map]
  -- `(0 : T*M_b)(0) = 0`, and `sqrt 0 = 0`.
  change Real.sqrt ((0 : TangentSpace I b →L[ℝ] ℝ) (0 : TangentSpace I b)) =
    (0 : M → ℝ) b
  simp

/-- For an inactive centre `α`, the `eLpNorm` of the gradient self-inner
square-root integrand is `0`. -/
private lemma eLpNorm_sqrt_g_inner_gradFun_eq_zero_of_inactive
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {α : M} (hα : α ∉ chartAtlasPOU_activeFinset I M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    eLpNorm (fun b : M => Real.sqrt
        (g.inner b
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx) b)
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx) b))) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  have h_zero :=
    chartAtlasPOU_eq_zero_of_notMem_activeFinset (I := I) (M := M) hα
  have h_scalar_zero :
      tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx = 0 :=
    tensorChartComponentScalar_eq_zero_of_pou_zero
      (I := I) (M := M) g r s α h_zero S Idx Jdx
  have h_integrand_zero :
      (fun b : M => Real.sqrt
          (g.inner b
            (gradFun (I := I) g
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S α Idx Jdx) b)
            (gradFun (I := I) g
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S α Idx Jdx) b))) = 0 :=
    sqrt_g_inner_gradFun_eq_zero_of_scalar_zero
      (I := I) (M := M) g h_scalar_zero
  rw [h_integrand_zero]
  exact eLpNorm_zero

/-! ## Per-`α` gradient constants and their sum over the active finset

We package the per-`α` gradient constants (one for each `α : M`) and sum
them over the (finite) active set, giving a single non-negative real
constant that dominates each per-`α` gradient constant on the active set. -/

/-- The per-`α` gradient constant from the per-`α` G5 headline. -/
private noncomputable def perAlphaGradConstant
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) : ℝ :=
  Classical.choose
    (exists_eLpNorm_sqrt_g_inner_gradFun_tensorChartComponentScalar_le_const_mul_h1Norm
      (I := I) (M := M) h_atlas g r s α)

/-- The per-`α` gradient constant is non-negative. -/
private lemma perAlphaGradConstant_nonneg
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    0 ≤ perAlphaGradConstant (I := I) (M := M) h_atlas g r s α :=
  (Classical.choose_spec
    (exists_eLpNorm_sqrt_g_inner_gradFun_tensorChartComponentScalar_le_const_mul_h1Norm
      (I := I) (M := M) h_atlas g r s α)).1

/-- The per-`α` gradient headline bound, expressed using
`perAlphaGradConstant`. -/
private lemma perAlphaGradConstant_bound
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensorH1 g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    eLpNorm (fun b : M => Real.sqrt
        (g.inner b
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) b)
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) b))) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ENNReal.ofReal (perAlphaGradConstant (I := I) (M := M) h_atlas g r s α) *
        (‖S‖₊ : ℝ≥0∞) :=
  (Classical.choose_spec
    (exists_eLpNorm_sqrt_g_inner_gradFun_tensorChartComponentScalar_le_const_mul_h1Norm
      (I := I) (M := M) h_atlas g r s α)).2 S Idx Jdx

/-- Sum of the per-`α` gradient constants over the active finset. This is a
single non-negative real, independent of `α` (and of `(S, Idx, Jdx)`), that
dominates each per-`α` gradient constant for `α` in the active finset. -/
private noncomputable def totalActiveGradConstant
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) : ℝ :=
  ∑ α ∈ chartAtlasPOU_activeFinset I M,
    perAlphaGradConstant (I := I) (M := M) h_atlas g r s α

private lemma totalActiveGradConstant_nonneg
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    0 ≤ totalActiveGradConstant (I := I) (M := M) h_atlas g r s := by
  classical
  unfold totalActiveGradConstant
  exact Finset.sum_nonneg (fun α _ =>
    perAlphaGradConstant_nonneg (I := I) (M := M) h_atlas g r s α)

/-- For each active centre `α`, its per-`α` gradient constant is dominated by
the total sum over the active finset. -/
private lemma perAlphaGradConstant_le_totalActiveGradConstant
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {α : M}
    (hα : α ∈ chartAtlasPOU_activeFinset I M) :
    perAlphaGradConstant (I := I) (M := M) h_atlas g r s α ≤
      totalActiveGradConstant (I := I) (M := M) h_atlas g r s := by
  classical
  unfold totalActiveGradConstant
  have h_split :
      ∑ β ∈ chartAtlasPOU_activeFinset I M,
        perAlphaGradConstant (I := I) (M := M) h_atlas g r s β =
        perAlphaGradConstant (I := I) (M := M) h_atlas g r s α +
        ∑ β ∈ (chartAtlasPOU_activeFinset I M).erase α,
          perAlphaGradConstant (I := I) (M := M) h_atlas g r s β := by
    rw [← Finset.sum_erase_add _ _ hα, add_comm]
  rw [h_split]
  have h_rest_nn :
      0 ≤ ∑ β ∈ (chartAtlasPOU_activeFinset I M).erase α,
            perAlphaGradConstant (I := I) (M := M) h_atlas g r s β :=
    Finset.sum_nonneg (fun β _ =>
      perAlphaGradConstant_nonneg (I := I) (M := M) h_atlas g r s β)
  linarith

/-! ## Headline `α`-uniform `L²` bound for the gradient self-inner
square-root integrand -/

/-- **Headline theorem (α-uniform L² bound for the metric self-inner
square-root of the gradient of chart-frame scalar components).** For a
closed Riemannian manifold `(M, g)` with locally constant chart selection
and ranks `(r, s)`, there exists a single non-negative real constant
`C_grad` such that for every smooth compactly-supported `H¹` tensor section
`S : SmoothCcTensorH1 g r s`, every chart base point `α : M`, and every
multi-index pair `(Idx, Jdx)`, the `L²` norm of the metric self-inner
square-root of the gradient of
`tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx` is bounded by
`ENNReal.ofReal C_grad · ‖S‖₊`.

The constant `C_grad` is independent of `α`, `(Idx, Jdx)`, and `S`. -/
theorem tensorChartComponentScalar_grad_eLpNorm_le
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C_grad : ℝ, 0 ≤ C_grad ∧
      ∀ (S : SmoothCcTensorH1 g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (fun b : M => Real.sqrt
            (g.inner b
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) b)
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) b))) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C_grad * (‖S‖₊ : ℝ≥0∞) := by
  classical
  refine ⟨totalActiveGradConstant (I := I) (M := M) h_atlas g r s,
    totalActiveGradConstant_nonneg (I := I) (M := M) h_atlas g r s, ?_⟩
  intro S α Idx Jdx
  -- Split on whether `α` is active.
  by_cases hα : α ∈ chartAtlasPOU_activeFinset I M
  · -- Active: chain through per-`α` bound + `perAlphaGradConstant ≤ total`.
    have h_per :
        eLpNorm (fun b : M => Real.sqrt
            (g.inner b
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) b)
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) b))) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal
              (perAlphaGradConstant (I := I) (M := M) h_atlas g r s α) *
            (‖S‖₊ : ℝ≥0∞) :=
      perAlphaGradConstant_bound (I := I) (M := M) h_atlas g r s α S Idx Jdx
    have h_const_le :
        ENNReal.ofReal
            (perAlphaGradConstant (I := I) (M := M) h_atlas g r s α) ≤
          ENNReal.ofReal
            (totalActiveGradConstant (I := I) (M := M) h_atlas g r s) :=
      ENNReal.ofReal_le_ofReal
        (perAlphaGradConstant_le_totalActiveGradConstant
          (I := I) (M := M) h_atlas g r s hα)
    have h_envelope_le :
        ENNReal.ofReal
              (perAlphaGradConstant (I := I) (M := M) h_atlas g r s α) *
              (‖S‖₊ : ℝ≥0∞) ≤
          ENNReal.ofReal
              (totalActiveGradConstant (I := I) (M := M) h_atlas g r s) *
              (‖S‖₊ : ℝ≥0∞) :=
      mul_le_mul_of_nonneg_right h_const_le (by exact zero_le _)
    exact h_per.trans h_envelope_le
  · -- Inactive: scalar component is identically zero, so the integrand
    -- vanishes and the `eLpNorm` is `0`.
    rw [eLpNorm_sqrt_g_inner_gradFun_eq_zero_of_inactive
      (I := I) (M := M) g r s hα S.toCcTensor Idx Jdx]
    exact zero_le _

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_grad_eLpNorm_le

end Sanity
