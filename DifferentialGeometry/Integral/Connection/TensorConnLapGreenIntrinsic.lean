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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
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

/-! ## The Dirichlet integrand in smooth-orthonormal-frame form (LHS pointwise)

At every base point `b`, the inverse-Gram-weighted Dirichlet integrand
`tensorCovDerivPointwiseInner g 0 2 T v b` equals the diagonal sum over the
smooth orthonormal frame `Bᵢ = smoothOrthoFrame g b i b` (which is
`g_b`-orthonormal at its centre `b`) of the pointwise tensor inner products of
the directional covariant derivatives `∇_{Bᵢ}T`, `∇_{Bᵢ}v`. This is the
right-hand side of the metric-isometry diagonalisation, specialised to the same
smooth frame against which the rough Laplacian is computed. -/

/-- **Dirichlet integrand = smooth-orthonormal-frame diagonal sum.** For every
`b`, with `Bᵢ = smoothOrthoFrame g b i b`,
`tensorCovDerivPointwiseInner g 0 2 T v b = ∑ᵢ ⟨∇_{Bᵢ}T, ∇_{Bᵢ}v⟩_b`. -/
lemma tensorCovDerivPointwiseInner_eq_smoothOrthoFrame_diag_sum
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) (b : M) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v b =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g 0 2 b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 2 T b
              (smoothOrthoFrame (I := I) g b i b)))
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 2 v b
              (smoothOrthoFrame (I := I) g b i b))) := by
  classical
  -- Orthonormality of the smooth frame values at the centre `b`.
  have hB_orth : ∀ i j, g.inner b
      (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b j b) =
      if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g b i j
  -- Build a `Module.Basis` from the orthonormal frame values.
  have hB_li : LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) => smoothOrthoFrame (I := I) g b i b) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner b (smoothOrthoFrame (I := I) g b k b)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g b j b) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs,
        g.inner b (smoothOrthoFrame (I := I) g b k b)
          (c j • smoothOrthoFrame (I := I) g b j b) =
        c j * g.inner b (smoothOrthoFrame (I := I) g b k b)
          (smoothOrthoFrame (I := I) g b j b) := by
      intro j _
      rw [(g.inner b (smoothOrthoFrame (I := I) g b k b)).map_smul
        (c j) (smoothOrthoFrame (I := I) g b j b), smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    have h_pull2 : ∀ j ∈ fs,
        c j * g.inner b (smoothOrthoFrame (I := I) g b k b)
          (smoothOrthoFrame (I := I) g b j b) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [hB_orth k j]
    rw [Finset.sum_congr rfl h_pull2] at h_zero
    rw [Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rw [if_pos rfl, mul_one] at h_zero
      exact h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E := by
    rw [Fintype.card_fin]
  set frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    basisOfLinearIndependentOfCardEqFinrank hB_li hcard with hframe_def
  have hframe_eq : ∀ i, frame i = smoothOrthoFrame (I := I) g b i b := by
    intro i
    rw [hframe_def]
    change (basisOfLinearIndependentOfCardEqFinrank hB_li hcard :
        Fin (Module.finrank ℝ E) → E) i = smoothOrthoFrame (I := I) g b i b
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hframe_orth : ∀ i j,
      g.inner b (frame i) (frame j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [hframe_eq i, hframe_eq j]
    exact hB_orth i j
  rw [tensorCovDerivPointwiseInner_eq_orthoFrame_diag_sum
    (I := I) (M := M) g 0 2 T v b frame hframe_orth]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hframe_eq i]

/-! ## The intrinsic divergence as the chart-basis metric covariant trace

At every base point `b`, the Voss–Weyl divergence of a smooth tangent vector
field `Z` equals the metric trace, in the chart centred at `b` itself, of the
Levi-Civita covariant derivative of `Z`:

```
divergence_g g Z b = ∑_{m,n} G⁻¹_{mn}(b) · g(∇_{∂_m}Z, ∂_n),
```

where `∂_m = chartBasisVecFiber b m` are the coordinate frame vectors of the
chart at `b` and `G⁻¹ = chartInvGramMatrix g b b` is the inverse chart Gram
matrix. This is the genuinely intrinsic (partition-of-unity-free) form: it holds
at every point because every `b` lies in its own chart source — equivalently, in
the chart-`b` Levi-Civita good set. -/

/-- **Divergence equals the chart-basis metric covariant trace (at every point).**
For a smooth tangent vector field `Z` and any base point `b`,
`divergence_g g Z b = ∑_{m,n} G⁻¹_{mn}(b) · g(∇_{∂_m}Z, ∂_n)`, with the chart
centred at `b`. -/
lemma divergence_g_eq_chartBasis_metricTrace
    (g : SmoothRiemannianMetric I M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    divergence_g (I := I) g Z b =
      ∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g b b m n *
          g.inner b
            ((LeviCivita (I := I) g).toFun Z.toFun b
              (chartBasisVecFiber (I := I) b m b))
            (chartBasisVecFiber (I := I) b n b) := by
  classical
  -- `b` lies in its own chart source and Levi-Civita good set.
  have hb_src : b ∈ (chartAt H b).source := mem_chart_source H b
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) b := by
    rw [mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source (I := I) b b]
    exact mem_extChartAt_source (I := I) b
  -- `divergence_g g Z b = localDivergence g b Z b` (Voss–Weyl chart invariance).
  rw [voss_weyl_divergence_formula (I := I) g b Z hb_src]
  rw [localDivergence_eq_coord_covariant_divergence (I := I) g b Z hb_good]
  -- Rewrite the metric trace into the coordinate covariant divergence, then match.
  rw [metricTrace_eq_coord_covariant_divergence (I := I) g b Z hb_good]
  -- Both sides are now chart-`b` coordinate covariant divergences; reconcile the
  -- Christoffel parts, exactly as in `divergence_g_eq_leviCivita_frameTrace`.
  rw [Finset.sum_add_distrib]
  congr 1
  -- LHS Christoffel: `∑ᵢ Zⁱ (∑ₖ Γᵏᵢₖ)`; RHS Christoffel: `∑ₘ (∑ⱼ Γᵐₘⱼ Zʲ)`.
  rw [show (∑ i : Fin (Module.finrank ℝ E),
          chartCoeffOnE (I := I) b Z i (extChartAt I b b) *
            ∑ k : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g b i k k (extChartAt I b b)) =
        ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g b i k k (extChartAt I b b) *
            chartCoeffOnE (I := I) b Z i (extChartAt I b b) from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [chartChristoffel_symm (I := I) g b k i i]

/-! ## Bilinear metric-trace invariance

The chart-basis inverse-Gram trace of a bilinear form equals the plain diagonal
trace over any `g_b`-orthonormal frame. This is the change-of-basis invariance of
the metric trace, applied to the divergence bilinear form
`K(u, w) = g(∇_u Z, w)`. It converts the intrinsic divergence
`∑_{m,n} G⁻¹_{mn} K(∂_m, ∂_n)` into the smooth-orthonormal-frame trace
`∑_i K(B_i, B_i)`, against which the rough Laplacian and the Dirichlet integrand
are both expressed. -/

/-- **Matrix form of the bilinear trace invariance.** For an invertible change of
basis `T`, an invertible Gram matrix `G`, and a bilinear-form matrix `B`,
`∑_{ij} (TᵀGT)⁻¹_{ij} (TᵀBT)_{ij} = ∑_{ij} G⁻¹_{ij} B_{ij}`. The proof writes each
double sum as a Frobenius trace `trace (M Nᵀ)` and cancels the change-of-basis
factors by the cyclic property of the matrix trace. -/
private lemma bilinear_trace_change_of_basis_matrix
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (hT : IsUnit T)
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : IsUnit G)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, (Tᵀ * G * T)⁻¹ i j * (Tᵀ * B * T) i j) =
      ∑ i : Fin n, ∑ j : Fin n, G⁻¹ i j * B i j := by
  classical
  -- The sum `∑_{ij} M_{ij} N_{ij}` is the Frobenius trace `trace (M Nᵀ)`.
  have hsum_eq : ∀ M N : Matrix (Fin n) (Fin n) ℝ,
      ∑ i : Fin n, ∑ j : Fin n, M i j * N i j = Matrix.trace (M * Nᵀ) := by
    intro M N
    rw [Matrix.trace]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [Matrix.transpose_apply]
  rw [hsum_eq, hsum_eq]
  set G' : Matrix (Fin n) (Fin n) ℝ := Tᵀ * G * T with hG'_def
  have hT_unit : IsUnit T := hT
  have hTT_unit : IsUnit Tᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det] at hT ⊢
    simpa [Matrix.det_transpose] using hT
  have hG_unit : IsUnit G := hG
  have hG'_inv : G'⁻¹ = T⁻¹ * G⁻¹ * (Tᵀ)⁻¹ := by
    rw [hG'_def, Matrix.mul_inv_rev, Matrix.mul_inv_rev, mul_assoc]
  rw [hG'_inv]
  set B' : Matrix (Fin n) (Fin n) ℝ := Tᵀ * B * T with hB'_def
  have hB'_trans : B'ᵀ = Tᵀ * Bᵀ * T := by
    rw [hB'_def, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      mul_assoc]
  rw [hB'_trans]
  have hT_inv_T : (Tᵀ)⁻¹ * Tᵀ = 1 := Matrix.nonsing_inv_mul _
    (by simpa [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose] using hT)
  have hT_T_inv : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv _
    (by simpa [Matrix.isUnit_iff_isUnit_det] using hT)
  have hcyc :
      T⁻¹ * G⁻¹ * (Tᵀ)⁻¹ * (Tᵀ * Bᵀ * T) =
        T⁻¹ * G⁻¹ * ((Tᵀ)⁻¹ * Tᵀ) * Bᵀ * T := by
    repeat rw [mul_assoc]
  rw [hcyc, hT_inv_T, mul_one]
  have hreassoc : T⁻¹ * G⁻¹ * Bᵀ * T = T⁻¹ * (G⁻¹ * Bᵀ * T) := by
    rw [mul_assoc T⁻¹ G⁻¹ Bᵀ, mul_assoc T⁻¹ (G⁻¹ * Bᵀ) T]
  rw [hreassoc, Matrix.trace_mul_comm T⁻¹ (G⁻¹ * Bᵀ * T)]
  rw [mul_assoc (G⁻¹ * Bᵀ) T T⁻¹, hT_T_inv, mul_one]

/-- **Bilinear metric-trace invariance on `E`.** For a `g_b`-orthonormal
`Module.Basis` `frame` of `E` and a bundled bilinear form
`K : E →ₗ[ℝ] E →ₗ[ℝ] ℝ`, the plain diagonal trace of `K` over `frame` equals the
inverse-Gram-weighted trace of `K` over the canonical model basis:

```
∑_i K (frame i) (frame i)
  = ∑_{m,n} (gramMatrixAt g b)⁻¹_{mn} · K (e_m) (e_n).
```

The change-of-basis matrix `T m i := (chartModelBasis E).repr (frame i) m`
satisfies `Tᵀ · G · T = 1` by orthonormality (with `G := gramMatrixAt g b`), so
`bilinear_trace_change_of_basis_matrix` applied to the bilinear-form matrix
`B m n := K (e_m) (e_n)` yields the claim. -/
lemma bilinear_metricTrace_invariance
    (g : SmoothRiemannianMetric I M) (b : M)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (horth : ∀ i j, g.inner b (frame i) (frame j) = if i = j then (1 : ℝ) else 0)
    (K : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    (∑ i : Fin (Module.finrank ℝ E), K (frame i) (frame i)) =
      ∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        (gramMatrixAt (I := I) (M := M) g b)⁻¹ m n *
          K ((chartModelBasis E) m) ((chartModelBasis E) n) := by
  classical
  set G : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    gramMatrixAt (I := I) (M := M) g b with hG_def
  -- Change-of-basis matrix `T m i = coordinate of `frame i` along `e_m`.
  set T : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun m i => (chartModelBasis E).repr (frame i) m with hT_def
  -- The bilinear-form matrix `B m n = K e_m e_n`.
  set B : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun m n => K ((chartModelBasis E) m) ((chartModelBasis E) n) with hB_def
  -- Each frame vector expands in the model basis with coordinates `T · i`.
  have hframe_expand : ∀ i : Fin (Module.finrank ℝ E),
      frame i = ∑ m : Fin (Module.finrank ℝ E), T m i • (chartModelBasis E) m := by
    intro i
    conv_lhs => rw [← (chartModelBasis E).sum_repr (frame i)]
  -- Bilinear expansion (bundled `K`): `K (∑ aₘ•eₘ) (∑ cₙ•eₙ) = ∑ₘₙ aₘ cₙ K(eₘ,eₙ)`.
  -- `map_sum` first fires on the OUTER application (second argument), expanding
  -- `∑ cₙ•eₙ`; then on the first argument inside.
  have hK_expand : ∀ (a c' : Fin (Module.finrank ℝ E) → ℝ),
      K (∑ m, a m • (chartModelBasis E) m) (∑ n, c' n • (chartModelBasis E) n) =
        ∑ m, ∑ n, a m * c' n *
          K ((chartModelBasis E) m) ((chartModelBasis E) n) := by
    intro a c'
    rw [map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [map_smul, smul_eq_mul]
    rw [map_sum, LinearMap.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  -- Bilinear expansion of `K (frame i) (frame j)` in the model basis.
  have hK_frame : ∀ i j : Fin (Module.finrank ℝ E),
      K (frame i) (frame j) =
        ∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
          T m i * T n j * B m n := by
    intro i j
    rw [hframe_expand i, hframe_expand j, hK_expand]
  -- The inner product also expands bilinearly; orthonormality ⇒ `Tᵀ G T = 1`.
  have hinner_expand : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b (frame i) (frame j) =
        ∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
          T m i * T n j * G m n := by
    intro i j
    rw [hframe_expand i, hframe_expand j]
    rw [map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    rw [map_sum, ContinuousLinearMap.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
      hG_def, gramMatrixAt_apply]
    ring
  have hTGT : Tᵀ * G * T = 1 := by
    ext i j
    rw [Matrix.one_apply]
    rw [Matrix.mul_apply]
    rw [show (∑ k : Fin (Module.finrank ℝ E), (Tᵀ * G) i k * T k j) =
          g.inner b (frame i) (frame j) from by
      rw [hinner_expand i j]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Matrix.transpose_apply]
      ring]
    rw [horth i j]
  -- `G` and `T` are units.
  have hG_unit : IsUnit G := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, hG_def]
    exact ne_of_gt (gramMatrixAt_posDef (I := I) (M := M) g b).det_pos
  have hT_unit : IsUnit T := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro hdetT
    have hdet1 : (Tᵀ * G * T).det = 1 := by rw [hTGT, Matrix.det_one]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetT] at hdet1
    simp at hdet1
  -- Apply the matrix trace invariance with `Tᵀ * G * T = 1`.
  have hmatrix := bilinear_trace_change_of_basis_matrix (n := Module.finrank ℝ E)
    T hT_unit G hG_unit B
  rw [hTGT, inv_one] at hmatrix
  -- LHS of `hmatrix`: `∑ᵢⱼ (1)ᵢⱼ (Tᵀ B T)ᵢⱼ = ∑ᵢ (Tᵀ B T)ᵢᵢ`.
  rw [show (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) i j *
              (Tᵀ * B * T) i j) =
        ∑ i : Fin (Module.finrank ℝ E), (Tᵀ * B * T) i i from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_eq_single i]
      · rw [Matrix.one_apply_eq, one_mul]
      · intro j _ hji; rw [Matrix.one_apply_ne (Ne.symm hji), zero_mul]
      · intro hi; exact absurd (Finset.mem_univ i) hi] at hmatrix
  -- `(Tᵀ B T) i i = K (frame i) (frame i)`.
  rw [show (∑ i : Fin (Module.finrank ℝ E), (Tᵀ * B * T) i i) =
        ∑ i : Fin (Module.finrank ℝ E), K (frame i) (frame i) from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hK_frame i i]
      rw [Matrix.mul_apply]
      -- Matrix side: `∑ₙ (Tᵀ*B) i n * T n i = ∑ₙ ∑ₘ T m i * B m n * T n i`.
      rw [show (∑ n : Fin (Module.finrank ℝ E), (Tᵀ * B) i n * T n i) =
            ∑ n : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
              T m i * B m n * T n i from by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Matrix.mul_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [Matrix.transpose_apply]]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      refine Finset.sum_congr rfl (fun n _ => ?_)
      ring] at hmatrix
  -- Conclude (the RHS matches `B = K e_m e_n`).
  rw [hmatrix]

/-- At its own centre `b`, the chart-`b` Gram matrix is the canonical model-basis
Gram matrix `gramMatrixAt g b`, because `chartBasisVecFiber b m b = e_m`. -/
lemma chartGramMatrix_self_eq_gramMatrixAt
    (g : SmoothRiemannianMetric I M) (b : M) :
    chartGramMatrix (I := I) g b b = gramMatrixAt (I := I) (M := M) g b := by
  ext m n
  rw [chartGramMatrix_apply, gramMatrixAt_apply,
    chartBasisVecFiber_self (I := I) b m, chartBasisVecFiber_self (I := I) b n]

/-- The divergence bilinear form `K(u, w) = g(∇_u Z, w)` at `b`, bundled as a
genuine bilinear map `E →ₗ[ℝ] E →ₗ[ℝ] ℝ`. The first slot factors through the
Levi-Civita derivative continuous-linear map `(LeviCivita g) Z b`, the inner
product supplying bilinearity. -/
def divergenceBilinearForm
    (g : SmoothRiemannianMetric I M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun u w => g.inner b ((LeviCivita (I := I) g).toFun Z.toFun b u) w)
    (fun u₁ u₂ w => by
      dsimp only
      rw [map_add, map_add]
      rfl)
    (fun c u w => by
      dsimp only
      rw [map_smul, map_smul]
      rfl)
    (fun u w₁ w₂ => by dsimp only; rw [map_add])
    (fun c u w => by dsimp only; rw [map_smul])

@[simp] lemma divergenceBilinearForm_apply
    (g : SmoothRiemannianMetric I M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) (u w : E) :
    divergenceBilinearForm (I := I) (M := M) g Z b u w =
      g.inner b ((LeviCivita (I := I) g).toFun Z.toFun b u) w := rfl

/-- **Divergence equals the smooth-orthonormal-frame metric covariant trace.** For
a smooth tangent vector field `Z` and any base point `b`, with
`Bᵢ = smoothOrthoFrame g b i b`,

```
divergence_g g Z b = ∑_i g(∇_{B_i} Z, B_i).
```

This combines the chart-basis metric-trace form `divergence_g_eq_chartBasis_metricTrace`
with the bilinear metric-trace invariance, transported to the same smooth
orthonormal frame against which the rough Laplacian and the Dirichlet integrand
are expressed. -/
lemma divergence_g_eq_smoothOrthoFrame_metricTrace
    (g : SmoothRiemannianMetric I M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    divergence_g (I := I) g Z b =
      ∑ i : Fin (Module.finrank ℝ E),
        g.inner b
          ((LeviCivita (I := I) g).toFun Z.toFun b
            (smoothOrthoFrame (I := I) g b i b))
          (smoothOrthoFrame (I := I) g b i b) := by
  classical
  -- Build the orthonormal `Module.Basis` from `smoothOrthoFrame g b · b`.
  have hB_orth : ∀ i j, g.inner b
      (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b j b) =
      if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g b i j
  have hB_li : LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) => smoothOrthoFrame (I := I) g b i b) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner b (smoothOrthoFrame (I := I) g b k b)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g b j b) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs,
        g.inner b (smoothOrthoFrame (I := I) g b k b)
          (c j • smoothOrthoFrame (I := I) g b j b) =
        c j * g.inner b (smoothOrthoFrame (I := I) g b k b)
          (smoothOrthoFrame (I := I) g b j b) := by
      intro j _
      rw [(g.inner b (smoothOrthoFrame (I := I) g b k b)).map_smul
        (c j) (smoothOrthoFrame (I := I) g b j b), smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    have h_pull2 : ∀ j ∈ fs,
        c j * g.inner b (smoothOrthoFrame (I := I) g b k b)
          (smoothOrthoFrame (I := I) g b j b) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [hB_orth k j]
    rw [Finset.sum_congr rfl h_pull2] at h_zero
    rw [Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rw [if_pos rfl, mul_one] at h_zero
      exact h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E := by
    rw [Fintype.card_fin]
  set frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    basisOfLinearIndependentOfCardEqFinrank hB_li hcard with hframe_def
  have hframe_eq : ∀ i, frame i = smoothOrthoFrame (I := I) g b i b := by
    intro i
    rw [hframe_def]
    change (basisOfLinearIndependentOfCardEqFinrank hB_li hcard :
        Fin (Module.finrank ℝ E) → E) i = smoothOrthoFrame (I := I) g b i b
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hframe_orth : ∀ i j,
      g.inner b (frame i) (frame j) = if i = j then (1 : ℝ) else 0 := by
    intro i j; rw [hframe_eq i, hframe_eq j]; exact hB_orth i j
  -- Start from the chart-basis metric-trace form.
  rw [divergence_g_eq_chartBasis_metricTrace (I := I) g Z b]
  -- Rewrite the chart-basis data at the centre to the canonical model basis.
  have hrw : ∀ m n : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g b b m n *
          g.inner b
            ((LeviCivita (I := I) g).toFun Z.toFun b
              (chartBasisVecFiber (I := I) b m b))
            (chartBasisVecFiber (I := I) b n b) =
        (gramMatrixAt (I := I) (M := M) g b)⁻¹ m n *
          divergenceBilinearForm (I := I) (M := M) g Z b
            ((chartModelBasis E) m) ((chartModelBasis E) n) := by
    intro m n
    rw [divergenceBilinearForm_apply]
    rw [chartBasisVecFiber_self (I := I) b m, chartBasisVecFiber_self (I := I) b n]
    rw [chartInvGramMatrix, chartGramMatrix_self_eq_gramMatrixAt (I := I) g b]
  rw [Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => hrw m n))]
  -- Apply the bilinear metric-trace invariance, reversed.
  rw [← bilinear_metricTrace_invariance (I := I) (M := M) g b frame hframe_orth
    (divergenceBilinearForm (I := I) (M := M) g Z b)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hframe_eq i, divergenceBilinearForm_apply]

/-! ## The smooth orthonormal frame as a tangent-bundle section -/

/-- The `i`-th smooth orthonormal frame field centred at `α`, packaged as a smooth
tangent-bundle section. -/
def smoothOrthoFrameSection
    (g : SmoothRiemannianMetric I M) (α : M) (i : Fin (Module.finrank ℝ E)) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ContMDiffSection.mk
    (fun b : M => smoothOrthoFrame (I := I) g α i b)
    (smoothOrthoFrame_smooth (I := I) g α i)

@[simp] lemma smoothOrthoFrameSection_apply
    (g : SmoothRiemannianMetric I M) (α : M) (i : Fin (Module.finrank ℝ E)) (b : M) :
    smoothOrthoFrameSection (I := I) (M := M) g α i b =
      smoothOrthoFrame (I := I) g α i b := rfl

/-- The function-coercion of `smoothOrthoFrameSection g α i` is `smoothOrthoFrame g α i`. -/
lemma smoothOrthoFrameSection_coe_eq
    (g : SmoothRiemannianMetric I M) (α : M) (i : Fin (Module.finrank ℝ E)) :
    (fun y : M => (smoothOrthoFrameSection (I := I) (M := M) g α i) y) =
      smoothOrthoFrame (I := I) g α i := rfl

/-- The first directional covariant derivative section of `T.toSection` along a
smooth vector field `B`, evaluated at `b`, is `tensorCovDerivAt g 0 2 T b (B b)`. -/
lemma covDerivAlongVFSection_eq_tensorCovDerivAt
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    covDerivAlongVFSection (I := I) (M := M) g T.toSection B b =
      tensorCovDerivAt (I := I) (M := M) g 0 2 T b (B b) := rfl

/-! ## Conversion of lowered `(0, 0 + 2)` inner products to mixed `(0, 2)` ones -/

/-- The lowered cross term `⟨∇_{B}W, S⟩₀ₛ` equals the mixed inner product
`⟨∇_{B}W, S⟩`. -/
lemma tensorInnerPointwise_0s_loweredCovDeriv_lifted_eq_mixed
    (g : SmoothRiemannianMetric I M)
    (W S : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    tensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g b
        (Tensor0SSpace.toModel
          (loweredCovDerivAt (I := I) (M := M) g 0 2 W b (B b)))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g 0 2 S b)) =
      tensorInnerPointwise (I := I) (M := M) g 0 2 b
        (TensorRSSpace.toModel (covDerivAlongVFSection (I := I) (M := M) g W B b))
        (TensorRSSpace.toModel (S b)) := by
  rw [tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g 0 2
    (covDerivAlongVFSection (I := I) (M := M) g W B) S b]
  congr 1
  rw [toModel_liftedTensorSection, covDerivAlongVFSection_lowered_eq]

/-- The lowered cross term `⟨W, ∇_{B}S⟩₀ₛ` equals the mixed inner product
`⟨W, ∇_{B}S⟩`. -/
lemma tensorInnerPointwise_0s_lifted_loweredCovDeriv_eq_mixed
    (g : SmoothRiemannianMetric I M)
    (W S : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    tensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g b
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g 0 2 W b))
        (Tensor0SSpace.toModel
          (loweredCovDerivAt (I := I) (M := M) g 0 2 S b (B b))) =
      tensorInnerPointwise (I := I) (M := M) g 0 2 b
        (TensorRSSpace.toModel (W b))
        (TensorRSSpace.toModel (covDerivAlongVFSection (I := I) (M := M) g S B b)) := by
  rw [tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g 0 2
    W (covDerivAlongVFSection (I := I) (M := M) g S B) b]
  congr 1
  rw [toModel_liftedTensorSection, covDerivAlongVFSection_lowered_eq]

/-! ## Second-order directional Leibniz in mixed form -/

/-- **Second-order directional Leibniz (mixed form).**
`B⟨∇_{B}T, v⟩ = ⟨∇_{B}(∇_{B}T), v⟩ + ⟨∇_{B}T, ∇_{B}v⟩`. -/
lemma tangentSectionAction_tensorInnerScalar_covDerivAlongVFSection
    (g : SmoothRiemannianMetric I M)
    (T v : SmoothCcTensor g 0 2)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    tangentSectionAction (I := I) B
        (tensorInnerScalar (I := I) (M := M) g 0 2
          (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) v.toSection) b =
      tensorInnerPointwise (I := I) (M := M) g 0 2 b
          (TensorRSSpace.toModel
            (covDerivAlongVFSection (I := I) (M := M) g
              (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) B b))
          (TensorRSSpace.toModel (v.toSection b))
        + tensorInnerPointwise (I := I) (M := M) g 0 2 b
          (TensorRSSpace.toModel
            (covDerivAlongVFSection (I := I) (M := M) g T.toSection B b))
          (TensorRSSpace.toModel
            (covDerivAlongVFSection (I := I) (M := M) g v.toSection B b)) := by
  rw [tangentSectionAction_tensorInnerScalar (I := I) (M := M) g 0 2
    (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) v.toSection B b]
  rw [tensorInnerPointwise_0s_loweredCovDeriv_lifted_eq_mixed (I := I) (M := M) g
    (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) v.toSection B b]
  rw [tensorInnerPointwise_0s_lifted_loweredCovDeriv_eq_mixed (I := I) (M := M) g
    (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) v.toSection B b]

/-! ## Metric-compatibility expansion of the divergence summand -/

/-- The inner product of the Dirichlet current against a smooth vector field `B`
equals the mixed inner-product scalar `⟨∇_{B}T, v⟩`, in `.toFun`-coercion form. -/
lemma dirichletCurrent_inner_eq_tensorInnerScalar
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    (fun y : M => g.inner y
        ((dirichletCurrentSection (I := I) (M := M) g T v).toFun y) (B.toFun y)) =
      tensorInnerScalar (I := I) (M := M) g 0 2
        (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) v.toSection := by
  funext y
  change g.inner y (dirichletCurrent (I := I) (M := M) g T v y) (B y) = _
  rw [inner_dirichletCurrent (I := I) (M := M) g T v y (B y)]
  rw [dirichletCurrentForm_apply, tensorInnerScalar_apply]
  rfl

/-- **Metric-compatibility expansion of the divergence summand.**
`g(∇_{B}Z, B) = B⟨∇_{B}T, v⟩ − ⟨∇_{(∇_{B}B)(b)}T, v⟩`. -/
lemma dirichletCurrent_metricTrace_summand
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    g.inner b
        ((LeviCivita (I := I) g).toFun
          (dirichletCurrentSection (I := I) (M := M) g T v).toFun b (B b))
        (B b) =
      tangentSectionAction (I := I) B
          (tensorInnerScalar (I := I) (M := M) g 0 2
            (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) v.toSection) b
        - tensorInnerPointwise (I := I) (M := M) g 0 2 b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 2 T b
              ((LeviCivita (I := I) g).toFun B.toFun b (B b))))
          (TensorRSSpace.toModel (v.toSection b)) := by
  classical
  have hZ_mdiff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E y
        ((dirichletCurrentSection (I := I) (M := M) g T v).toFun y)) b :=
    ((dirichletCurrentSection (I := I) (M := M) g T v).contMDiff.mdifferentiable
      (by norm_num)).mdifferentiableAt
  have hB_mdiff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E y (B.toFun y)) b :=
    (B.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt
  have hmc := (LeviCivita_isMetricCompatible (I := I) g).apply
    (Y := (dirichletCurrentSection (I := I) (M := M) g T v).toFun)
    (Z := B.toFun) hZ_mdiff hB_mdiff (B b)
  have hfun_eq := dirichletCurrent_inner_eq_tensorInnerScalar (I := I) (M := M) g T v B
  rw [hfun_eq] at hmc
  have hcorr : g.inner b
        ((dirichletCurrentSection (I := I) (M := M) g T v).toFun b)
        ((LeviCivita (I := I) g).toFun B.toFun b (B b)) =
      tensorInnerPointwise (I := I) (M := M) g 0 2 b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g 0 2 T b
            ((LeviCivita (I := I) g).toFun B.toFun b (B b))))
        (TensorRSSpace.toModel (v.toSection b)) := by
    change g.inner b (dirichletCurrent (I := I) (M := M) g T v b)
        ((LeviCivita (I := I) g).toFun B.toFun b (B b)) = _
    rw [inner_dirichletCurrent (I := I) (M := M) g T v b
      ((LeviCivita (I := I) g).toFun B.toFun b (B b))]
    rw [dirichletCurrentForm_apply]
  rw [hcorr] at hmc
  have htan : tangentSectionAction (I := I) B
        (tensorInnerScalar (I := I) (M := M) g 0 2
          (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) v.toSection) b =
      mfderiv I 𝓘(ℝ)
        (tensorInnerScalar (I := I) (M := M) g 0 2
          (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) v.toSection) b (B b) :=
    tangentSectionAction_def (I := I) B _ b
  exact eq_sub_of_add_eq (htan.trans hmc).symm

/-- **Per-direction divergence summand in Bochner form.**
`g(∇_{B}Z, B) = ⟨∇²_{B,B}T, v⟩ + ⟨∇_{B}T, ∇_{B}v⟩`. -/
lemma dirichletCurrent_metricTrace_summand_bochner
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    g.inner b
        ((LeviCivita (I := I) g).toFun
          (dirichletCurrentSection (I := I) (M := M) g T v).toFun b (B b))
        (B b) =
      tensorInnerPointwise (I := I) (M := M) g 0 2 b
          (TensorRSSpace.toModel
            (tensorSecondCovDeriv (I := I) g 0 2
              (fun y : M => B y) (fun y : M => B y) (fun y : M => T.toSection y) b))
          (TensorRSSpace.toModel (v.toSection b))
        + tensorInnerPointwise (I := I) (M := M) g 0 2 b
          (TensorRSSpace.toModel
            (covDerivAlongVFSection (I := I) (M := M) g T.toSection B b))
          (TensorRSSpace.toModel
            (covDerivAlongVFSection (I := I) (M := M) g v.toSection B b)) := by
  classical
  rw [dirichletCurrent_metricTrace_summand (I := I) (M := M) g T v B b]
  rw [tangentSectionAction_tensorInnerScalar_covDerivAlongVFSection (I := I) (M := M) g T v B b]
  have hsecond := covDerivAlong_covDerivAlongVFSection_eq (I := I) (M := M) g T.toSection B b
  have hcorr_eq :
      tensorCovDerivAt (I := I) (M := M) g 0 2 T b
          ((LeviCivita (I := I) g).toFun B.toFun b (B b)) =
        (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
          (fun y : M => T.toSection y) b
          ((LeviCivita (I := I) g).toFun (fun y : M => B y) b (B b)) := rfl
  rw [hsecond]
  rw [TensorRSSpace.toModel_add, tensorInnerPointwise_add_left]
  rw [hcorr_eq]
  ring

/-! ## The pointwise Bochner divergence identity -/

/-- The Hessian frame-trace half: the diagonal frame sum of the second covariant
derivatives paired with `v` is the rough connection Laplacian inner product. -/
lemma dirichletCurrent_hessian_frameTrace_eq
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) (b : M) :
    (∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g 0 2 b
          (TensorRSSpace.toModel
            (tensorSecondCovDeriv (I := I) g 0 2
              (fun y : M => smoothOrthoFrameSection (I := I) (M := M) g b i y)
              (fun y : M => smoothOrthoFrameSection (I := I) (M := M) g b i y)
              (fun y : M => T.toSection y) b))
          (TensorRSSpace.toModel (v.toSection b))) =
      tensorInnerScalar (I := I) (M := M) g 0 2
        (rawTensorConnLapSmooth (I := I) g 0 2 T).toSection v.toSection b := by
  classical
  -- Abbreviate the per-frame second-covariant-derivative model tensors.
  set A : Fin (Module.finrank ℝ E) → TensorRSModel 0 2 ℝ E :=
    fun i => TensorRSSpace.toModel
      (tensorSecondCovDeriv (I := I) g 0 2
        (fun y : M => smoothOrthoFrameSection (I := I) (M := M) g b i y)
        (fun y : M => smoothOrthoFrameSection (I := I) (M := M) g b i y)
        (fun y : M => T.toSection y) b) with hA_def
  -- Pull the finite sum out of the inner product (left argument), via `sum_left`
  -- with unit coefficients.
  have hpull : (∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g 0 2 b (A i)
          (TensorRSSpace.toModel (v.toSection b))) =
      tensorInnerPointwise (I := I) (M := M) g 0 2 b
        (∑ i : Fin (Module.finrank ℝ E), A i)
        (TensorRSSpace.toModel (v.toSection b)) := by
    rw [show (∑ i : Fin (Module.finrank ℝ E), A i) =
          ∑ i : Fin (Module.finrank ℝ E), (1 : ℝ) • A i from by
        refine Finset.sum_congr rfl (fun i _ => ?_); rw [one_smul]]
    rw [tensorInnerPointwise_sum_left (I := I) (M := M) g 0 2 b Finset.univ A
      (fun _ => (1 : ℝ)) (TensorRSSpace.toModel (v.toSection b))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [one_mul]
  rw [hpull, tensorInnerScalar_apply]
  congr 1
  -- `∑ᵢ A i = toModel ((rawTensorConnLapSmooth g 0 2 T).toSection b)`.
  rw [rawTensorConnLapSmooth_toSection_apply, rawTensorConnLap_def]
  -- Push `toModel` through the finite sum on the right via the `toModelL` linear equiv.
  rw [show TensorRSSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E),
          ((tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
              (covApply (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g))
                (smoothOrthoFrame (I := I) g b i) (fun z : M => T.toSection z)) b
              (smoothOrthoFrame (I := I) g b i b) -
            (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
              (fun z : M => T.toSection z) b
              ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g b i) b
                (smoothOrthoFrame (I := I) g b i b)))) =
        ∑ i : Fin (Module.finrank ℝ E),
          TensorRSSpace.toModel
            ((tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
                (covApply (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g))
                  (smoothOrthoFrame (I := I) g b i) (fun z : M => T.toSection z)) b
                (smoothOrthoFrame (I := I) g b i b) -
              (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
                (fun z : M => T.toSection z) b
                ((LeviCivita (I := I) g).toFun
                  (smoothOrthoFrame (I := I) g b i) b
                  (smoothOrthoFrame (I := I) g b i b))) from by
      rw [show (TensorRSSpace.toModel
            (∑ i : Fin (Module.finrank ℝ E),
              ((tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
                  (covApply (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g))
                    (smoothOrthoFrame (I := I) g b i) (fun z : M => T.toSection z)) b
                  (smoothOrthoFrame (I := I) g b i b) -
                (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
                  (fun z : M => T.toSection z) b
                  ((LeviCivita (I := I) g).toFun
                    (smoothOrthoFrame (I := I) g b i) b
                    (smoothOrthoFrame (I := I) g b i b))))) =
          (TensorRSSpace.toModelL (I := I) 0 2 b)
            (∑ i : Fin (Module.finrank ℝ E),
              ((tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
                  (covApply (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g))
                    (smoothOrthoFrame (I := I) g b i) (fun z : M => T.toSection z)) b
                  (smoothOrthoFrame (I := I) g b i b) -
                (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
                  (fun z : M => T.toSection z) b
                  ((LeviCivita (I := I) g).toFun
                    (smoothOrthoFrame (I := I) g b i) b
                    (smoothOrthoFrame (I := I) g b i b)))) from rfl]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rfl]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [hA_def, tensorSecondCovDeriv_def, smoothOrthoFrameSection_coe_eq]

/-- The Dirichlet cross half: the diagonal frame sum of the Dirichlet cross terms
is the inverse-Gram Dirichlet integrand `tensorCovDerivPointwiseInner g 0 2 T v`. -/
lemma dirichletCurrent_dirichlet_frameTrace_eq
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) (b : M) :
    (∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g 0 2 b
          (TensorRSSpace.toModel
            (covDerivAlongVFSection (I := I) (M := M) g T.toSection
              (smoothOrthoFrameSection (I := I) (M := M) g b i) b))
          (TensorRSSpace.toModel
            (covDerivAlongVFSection (I := I) (M := M) g v.toSection
              (smoothOrthoFrameSection (I := I) (M := M) g b i) b))) =
      tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v b := by
  classical
  rw [tensorCovDerivPointwiseInner_eq_smoothOrthoFrame_diag_sum (I := I) (M := M) g T v b]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [covDerivAlongVFSection_eq_tensorCovDerivAt (I := I) (M := M) g T
    (smoothOrthoFrameSection (I := I) (M := M) g b i) b,
    covDerivAlongVFSection_eq_tensorCovDerivAt (I := I) (M := M) g v
    (smoothOrthoFrameSection (I := I) (M := M) g b i) b,
    smoothOrthoFrameSection_apply]

/-- **Pointwise Bochner divergence identity.** For the Dirichlet current `Z` of
`T, v` on a closed Riemannian manifold, at every base point `b`,

```
div_g Z b = ⟨∇T, ∇v⟩_b + ⟨Δ_∇ T, v⟩_b.
```
-/
theorem divergence_g_dirichletCurrent_eq
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) (b : M) :
    divergence_g (I := I) g (dirichletCurrentSection (I := I) (M := M) g T v) b =
      tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v b +
        tensorInnerScalar (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T).toSection v.toSection b := by
  classical
  rw [divergence_g_eq_smoothOrthoFrame_metricTrace (I := I) (M := M) g
    (dirichletCurrentSection (I := I) (M := M) g T v) b]
  -- Convert the bare frame to the section frame, then split each summand.
  rw [show (∑ i : Fin (Module.finrank ℝ E),
          g.inner b
            ((LeviCivita (I := I) g).toFun
              (dirichletCurrentSection (I := I) (M := M) g T v).toFun b
              (smoothOrthoFrame (I := I) g b i b))
            (smoothOrthoFrame (I := I) g b i b)) =
        ∑ i : Fin (Module.finrank ℝ E),
          g.inner b
            ((LeviCivita (I := I) g).toFun
              (dirichletCurrentSection (I := I) (M := M) g T v).toFun b
              ((smoothOrthoFrameSection (I := I) (M := M) g b i) b))
            ((smoothOrthoFrameSection (I := I) (M := M) g b i) b) from rfl]
  rw [Finset.sum_congr rfl (fun i _ =>
    dirichletCurrent_metricTrace_summand_bochner (I := I) (M := M) g T v
      (smoothOrthoFrameSection (I := I) (M := M) g b i) b)]
  rw [Finset.sum_add_distrib]
  rw [dirichletCurrent_hessian_frameTrace_eq (I := I) (M := M) g T v b]
  rw [dirichletCurrent_dirichlet_frameTrace_eq (I := I) (M := M) g T v b]
  rw [add_comm]

end Connection
end Integral
end DifferentialGeometry

end
