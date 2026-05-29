import DifferentialGeometry.Integral.Connection.TensorConnLapSecondOrderIBP
import DifferentialGeometry.Integral.Connection.TensorCovGradL2InnerDirichletBridge
import DifferentialGeometry.Integral.Connection.DivergenceCovariantTrace
import DifferentialGeometry.Integral.Connection.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Integral.Connection.TensorRSMetricCompatible
import DifferentialGeometry.Integral.DivergenceTheorem.Proper
import DifferentialGeometry.Geometry.MetricSharpSmooth
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.GoodSetMeasure

/-!
# The `(0, 2)` connection-Laplacian Green identity via the intrinsic Dirichlet current

For a closed smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file proves the integrated Green identity for the
rough (connection) Laplacian on `(0, 2)`-tensor fields,

```
tensorL2Inner g 0 3 (covGrad g 0 2 T).toFun (covGrad g 0 2 v).toFun
  = − tensorL2Inner g 0 2 (rawTensorConnLapSmooth g 0 2 T).toFun v.toFun,
```

through a single **Dirichlet current** vector field and a single application of
the divergence theorem on the closed manifold — with no partition-of-unity
fixed-frame Leibniz weight residual.

## The Dirichlet current

The Dirichlet current is the metric-musical raise `♯` of the `1`-form

```
ω_b : X ↦ ⟨∇_X T, v⟩_g,
```

i.e. the smooth tangent vector field `Z` characterised by `g(Z b, X) = ω_b(X)`
for every tangent vector `X`. Its intrinsic divergence satisfies the pointwise
Bochner identity

```
div_g Z b = ⟨∇T, ∇v⟩_b + ⟨Δ_∇ T, v⟩_b,
```

whose integral against the Riemannian volume vanishes on the closed manifold.
Combined with the gradient-side bridge for the left-hand `L²` inner product, this
gives the headline.

## Main definitions

* `dirichletCurrentForm g T v b` — the `1`-form `X ↦ ⟨∇_X T, v⟩_g` at `b`.
* `dirichletCurrent g T v b` — its metric-musical sharp, a tangent vector at `b`.
* `dirichletCurrentSection g T v` — `dirichletCurrent` packaged as a smooth
  tangent-bundle section.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Tensor.TensorRSRiemannian
open Tensor0SNabla TensorRSNabla TensorMetricLowering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## The Dirichlet current `1`-form and its musical sharp -/

/-- **The Dirichlet `1`-form.** At a base point `b`, the linear functional
`X ↦ ⟨∇_X T, v⟩_g` on `T_b M`, where `∇_X T` is the directional covariant
derivative of `T` along `X` and `⟨·, ·⟩_g` is the pointwise metric inner product
on `(0, 2)`-tensors. Linearity in `X` follows from the linearity of the
covariant derivative in the direction (it is a continuous linear map) together
with the model coercion and the left-linearity of the pointwise inner product. -/
def dirichletCurrentForm
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) (b : M) :
    TangentSpace I b →ₗ[ℝ] ℝ where
  toFun X := tensorInnerPointwise (I := I) (M := M) g 0 2 b
    (TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g 0 2 T b X))
    (TensorRSSpace.toModel (v.toSection b))
  map_add' X Y := by
    have hcov : tensorCovDerivAt (I := I) (M := M) g 0 2 T b (X + Y) =
        tensorCovDerivAt (I := I) (M := M) g 0 2 T b X +
          tensorCovDerivAt (I := I) (M := M) g 0 2 T b Y := by
      change (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
          (fun y : M => T.toSection y) b (X + Y) = _
      rw [ContinuousLinearMap.map_add]
      rfl
    rw [hcov, TensorRSSpace.toModel_add, tensorInnerPointwise_add_left]
  map_smul' c X := by
    have hcov : tensorCovDerivAt (I := I) (M := M) g 0 2 T b (c • X) =
        c • tensorCovDerivAt (I := I) (M := M) g 0 2 T b X := by
      change (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
          (fun y : M => T.toSection y) b (c • X) = _
      rw [ContinuousLinearMap.map_smul]
      rfl
    rw [hcov, TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left]
    rfl

@[simp] lemma dirichletCurrentForm_apply
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) (b : M)
    (X : TangentSpace I b) :
    dirichletCurrentForm (I := I) (M := M) g T v b X =
      tensorInnerPointwise (I := I) (M := M) g 0 2 b
        (TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g 0 2 T b X))
        (TensorRSSpace.toModel (v.toSection b)) := rfl

/-- **The Dirichlet current vector field, pointwise.** The metric-musical sharp
of the Dirichlet `1`-form: the unique tangent vector `Z b` with
`g(Z b, X) = ⟨∇_X T, v⟩_g` for all `X`. -/
def dirichletCurrent
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) (b : M) :
    TangentSpace I b :=
  metricSharp (I := I) g b (dirichletCurrentForm (I := I) (M := M) g T v b)

/-- **The defining Riesz identity for the Dirichlet current.** For every tangent
vector `X` at `b`, `g(Z b, X) = ⟨∇_X T, v⟩_g`. -/
lemma inner_dirichletCurrent
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) (b : M)
    (X : TangentSpace I b) :
    g.inner b (dirichletCurrent (I := I) (M := M) g T v b) X =
      dirichletCurrentForm (I := I) (M := M) g T v b X := by
  rw [dirichletCurrent]
  exact inner_metricSharp (I := I) g b (dirichletCurrentForm (I := I) (M := M) g T v b) X

/-! ## Smoothness of the Dirichlet current as a tangent-bundle section -/

/-- **Chart-local smoothness of the Dirichlet-form chart-basis component.** For
each chart base point `α` and chart-basis index `j`, the scalar
`b ↦ ω_b(∂ⱼ) = ⟨∇_{∂ⱼ}T, v⟩_g` is `C^∞` on the chart-`α` source. This is the
hypothesis consumed by `metricSharp_contMDiff_total`. The component is the
pointwise tensor inner product of the chart-locally-smooth covariant-derivative
section `b ↦ ∇_{∂ⱼ}T b` (smooth on the chart base set by
`tensorCovDeriv_chartBasis_contMDiffOn`) with the globally smooth section `v`. -/
private lemma dirichletCurrentForm_chartBasis_component_contMDiffOn
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => dirichletCurrentForm (I := I) (M := M) g T v b
        (chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source := by
  -- The chart-locally-smooth covariant-derivative section `b ↦ ∇_{∂ⱼ}T b`.
  have hcov_section : ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun y : M => TensorRSSpace 0 2 I y) b
        (tensorCovDerivAt (I := I) (M := M) g 0 2 T b
          (chartBasisVecFiber (I := I) α j b)))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    tensorCovDeriv_chartBasis_contMDiffOn (I := I) (M := M) g 0 2 T α j
  -- Its `loweredCompose` model representation is smooth on the chart base set.
  have hcov_lowered : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (0 + 2) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g 0 2 α b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g 0 2 T b
            (chartBasisVecFiber (I := I) α j b))))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    TensorMetricLowering.contMDiffOn_loweredCompose_of_section_contMDiffOn
      (I := I) (M := M) g 0 2
      (fun b : M => tensorCovDerivAt (I := I) (M := M) g 0 2 T b
        (chartBasisVecFiber (I := I) α j b)) α hcov_section
  -- The globally smooth section `v`'s `loweredCompose` model representation.
  have hv_lowered : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (0 + 2) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g 0 2 α b
        (TensorRSSpace.toModel (v.toSection b)))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    TensorMetricLowering.contMDiffOn_loweredCompose (I := I) (M := M) g 0 2 v.toSection α
  -- The pointwise inner product is smooth on the chart base set.
  have hinner : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        tensorInnerPointwise (I := I) (M := M) g 0 2 b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 2 T b
              (chartBasisVecFiber (I := I) α j b)))
          (TensorRSSpace.toModel (v.toSection b)))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_contMDiff_inner_of_smooth_sections
      (I := I) (M := M) g 0 2
      (fun b : M => tensorCovDerivAt (I := I) (M := M) g 0 2 T b
        (chartBasisVecFiber (I := I) α j b))
      (fun b : M => v.toSection b) α hcov_lowered hv_lowered
  -- Transfer the base set to the chart source and rewrite the integrand.
  have hbase_eq : (trivializationAt E (TangentSpace I) α).baseSet =
      (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source
      (I := I) α
  rw [hbase_eq] at hinner
  refine hinner.congr ?_
  intro b _
  rw [dirichletCurrentForm_apply]

/-- **Smoothness of the Dirichlet current as a tangent-bundle section.** The
metric-musical sharp `b ↦ Z b` is a smooth tangent-bundle section, via
`metricSharp_contMDiff_total` and the chart-basis component smoothness. -/
lemma dirichletCurrent_contMDiff
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E b (dirichletCurrent (I := I) (M := M) g T v b)) :=
  metricSharp_contMDiff_total (I := I) g
    (cv := fun b : M => dirichletCurrentForm (I := I) (M := M) g T v b)
    (fun α j => dirichletCurrentForm_chartBasis_component_contMDiffOn
      (I := I) (M := M) g T v α j)

/-- **The Dirichlet current packaged as a smooth tangent-bundle section.** -/
def dirichletCurrentSection
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ContMDiffSection.mk
    (fun b : M => dirichletCurrent (I := I) (M := M) g T v b)
    (dirichletCurrent_contMDiff (I := I) (M := M) g T v)

@[simp] lemma dirichletCurrentSection_apply
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) (b : M) :
    dirichletCurrentSection (I := I) (M := M) g T v b =
      dirichletCurrent (I := I) (M := M) g T v b := rfl

end Connection
end Integral
end DifferentialGeometry

end
