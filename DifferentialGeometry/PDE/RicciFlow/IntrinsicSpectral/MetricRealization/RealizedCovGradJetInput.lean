import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.RealizedJet2CovGradBound
import DifferentialGeometry.Integral.Connection.TensorRSChartFiberToModelOpNormUnconditional
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ComponentL2BoundUniform

/-!
# The pointwise covariant-gradient jet input for the chart `2`-jet seminorm bound

This file discharges the analytic input `hcovgrad_jet_bound` of
`chartMetricJet2DiffSup_realizeMetricAt_le_iteratedCovGradJetSum`: on a compact piece
`K ⊆ interior (extChartAt I α).target`, every chart `∂^j` (`j = 0, 1, 2`) of the chart-frame
component function `reprDiffChartCompOnE g_bg hu₁ hu₂ α l b` of the **fixed** tensor
difference `S = realizableRepr hu₁ − realizableRepr hu₂` is bounded by a single constant
times the iterated covariant-gradient jet sum `iteratedCovGradJetSum g_bg S ((symm) y)`.

## The per-component pointwise bound (leaf-2)

The raw chart-frame scalar component `tensorChartComponentRaw g_bg 0 (2 + i) T α Idx Jdx b`
is, by definition, the `(Idx, Jdx)`-projection of the chart-`α` trivialisation fibre
`tensorTrivProj g_bg 0 (2 + i) T α b` of the underlying tensor section `T.toSection b`.
Hence its absolute value is bounded by `‖projection‖ · ‖tensorTrivProj‖`, with the
projection operator norm bounded uniformly by `chartComponentProjectionUniformBound` and the
trivialisation-fibre norm bounded uniformly on the compact `K` by the **unconditional**
op-norm bound `tensorRSChartFiberToModel_opNorm_isBounded_on_compact_unconditional`, against
the `g_bg`-Riemannian fibre norm `‖T.toSection b‖`.  This produces

  `|tensorChartComponentRaw g_bg 0 (2 + i) T α Idx Jdx b| ≤ C · ‖T.toSection b‖`,

uniformly over the compact base set and over all multi-indices.

## Sign convention

Geometer `Δ_∇ = −∇*∇`; resolvent `(1 − Δ_∇)⁻¹`, weights `(1 + λᵢ)^σ ≥ 1` for `σ ≥ 0`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ## Leaf-2: the per-component pointwise bound -/

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Pointwise bound on a single raw chart-frame scalar component.**

For a smooth compactly-supported `(0, s)`-tensor `T`, a chart center `α`, and a compact
base set `K ⊆ (chartAt H α).source`, there is a single constant `C ≥ 0` such that for every
base point `b ∈ K` and all frame multi-indices `Jdx`,

  `|tensorChartComponentRaw g_bg 0 s T α (![] : Fin 0 → _) Jdx b| ≤ C · ‖T.toSection b‖`,

where the fibre norm on the right is the `g_bg`-Riemannian bundle norm.  `C` is independent
of `T`, of `Jdx`, and of `b`. -/
theorem tensorChartComponentRaw_abs_le_riemannianFibreNorm
    (g_bg : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    {K : Set M} (hK : IsCompact K) (hKsub : K ⊆ (chartAt H α).source) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 s
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : SmoothCcTensor g_bg 0 s) (b : M), b ∈ K →
      ∀ (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        |tensorChartComponentRaw (I := I) (M := M) g_bg 0 s T α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx b| ≤
          C * ‖T.toSection b‖ := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 s
  -- Unconditional uniform op-norm bound on the chart-`α` forward trivialisation over `K`.
  obtain ⟨Cop, hCop_pos, hCop_bound⟩ :=
    tensorRSChartFiberToModel_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g_bg 0 s α hK hKsub
  -- The uniform projection operator-norm bound.
  set Cproj : ℝ := chartComponentProjectionUniformBound (E := E) 0 s with hCproj_def
  have hCproj_nn : 0 ≤ Cproj := chartComponentProjectionUniformBound_nonneg (E := E) 0 s
  refine ⟨Cproj * Cop, mul_nonneg hCproj_nn (le_of_lt hCop_pos), ?_⟩
  intro T b hb Jdx
  -- Abbreviate the trivialisation fibre.
  set v : TensorRSModel 0 s ℝ E :=
    tensorTrivProj (I := I) (M := M) g_bg 0 s T α b with hv_def
  -- The raw component is the projection of the trivialisation fibre.
  rw [tensorChartComponentRaw_def]
  -- `|P_IJ v| ≤ ‖P_IJ‖ · ‖v‖ ≤ Cproj · ‖v‖`.
  have h_proj_le :
      |tensorChartComponentProjection (E := E) 0 s
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx v| ≤
        ‖tensorChartComponentProjection (E := E) 0 s
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx‖ * ‖v‖ := by
    have h := (tensorChartComponentProjection (E := E) 0 s
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx).le_opNorm v
    simpa [Real.norm_eq_abs] using h
  have h_proj_norm_le :
      ‖tensorChartComponentProjection (E := E) 0 s
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx‖ ≤ Cproj :=
    tensorChartComponentProjection_norm_le_uniform (E := E) 0 s _ Jdx
  -- `‖v‖ ≤ Cop · ‖T.toSection b‖`.
  have h_v_le : ‖v‖ ≤ Cop * ‖T.toSection b‖ := by
    rw [hv_def]
    exact hCop_bound b hb (T.toSection b)
  -- Chain the bounds.
  calc |tensorChartComponentProjection (E := E) 0 s
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx v|
      ≤ ‖tensorChartComponentProjection (E := E) 0 s
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx‖ * ‖v‖ := h_proj_le
    _ ≤ Cproj * ‖v‖ :=
        mul_le_mul_of_nonneg_right h_proj_norm_le (norm_nonneg _)
    _ ≤ Cproj * (Cop * ‖T.toSection b‖) :=
        mul_le_mul_of_nonneg_left h_v_le hCproj_nn
    _ = Cproj * Cop * ‖T.toSection b‖ := by ring

/-! ## Leaf-3: the dictionary `ccTensorBilin = raw chart-frame component` -/

/-- The rank-`0` chart-frame basis element `chartFrameBasisModel α x 0 (![] : Fin 0 → _)`
is the unit `(0, 0)`-tensor `constOfIsEmpty 1`.  Both are `0`-ary continuous multilinear
maps, hence determined by their (unique, empty-tuple) value, which is the empty product
`1` on either side. -/
lemma chartFrameBasisModel_zero_eq_constOfIsEmpty (α x : M) :
    chartFrameBasisModel (I := I) (M := M) α x 0
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := by
  refine ContinuousMultilinearMap.ext ?_
  intro v
  rw [chartFrameBasisModel_apply]
  simp

/-- **The bilinear-form value of a `(0,2)`-tensor section equals its raw chart-frame
component.**  For a smooth compactly-supported `(0,2)`-tensor `S`, a chart center `α`, a base
point `x` in the chart source, and frame indices `l b`, the extracted bilinear form
`ccTensorBilin g_bg S x` evaluated on the chart-`α`-frame vectors `(e_l, e_b)` equals the
raw chart-frame scalar component `tensorChartComponentRaw g_bg 0 2 S α (![]) ![l, b] x`. -/
theorem ccTensorBilin_chartBasisVecFiber_eq_tensorChartComponentRaw
    (g_bg : SmoothRiemannianMetric I M) (S : SmoothCcTensor g_bg 0 2) (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) (l b : Fin (Module.finrank ℝ E)) :
    ccTensorBilin (I := I) g_bg S x
        (chartBasisVecFiber (I := I) α l x) (chartBasisVecFiber (I := I) α b x) =
      tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 S α
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E)))
        ![l, b] x := by
  classical
  -- Unfold the right-hand side to the chart-frame closed form.
  rw [tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g_bg 0 2 S α hx
    (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b]]
  -- The `(0,0)`-tensor input is the unit `constOfIsEmpty 1`.
  rw [chartFrameBasisModel_zero_eq_constOfIsEmpty (I := I) (M := M) α x]
  -- The left-hand side: `ccTensorBilin = ccTensorModel ![·,·] = ccTensorMultilinear ![·,·]`.
  rw [ccTensorBilin_apply, ccTensorModel, ccTensorMultilinear_apply]
  -- `Tensor0SSpace.toModel` is the identity on the underlying carrier.
  change (Tensor0SBundle.Tensor0SSpace.toModel
      (S.toSection x (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))))
      ![chartBasisVecFiber (I := I) α l x, chartBasisVecFiber (I := I) α b x] =
    (S.toSection x (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
      (fun j : Fin 2 => chartBasisVecFiber (I := I) α (![l, b] j) x)
  rw [Tensor0SBundle.Tensor0SSpace.toModel,
    Tensor0SBundle.tensor0SSpace_continuousLinearEquiv_apply]
  -- The two tuples agree pointwise.
  congr 1
  funext j
  fin_cases j <;> rfl

/-- **The chart-frame component function of the realized tensor difference is the
symmetrized raw chart-frame component of `S`.**  At every chart point `y` whose chart
preimage `(extChartAt I α).symm y` lies in the chart source, `reprDiffChartCompOnE` equals
the symmetrization `½ (raw_{l,b} + raw_{b,l})` of the raw chart-frame components of the
fixed tensor difference `S = realizableRepr hu₁ − realizableRepr hu₂`. -/
theorem reprDiffChartCompOnE_eq_symm_tensorChartComponentRaw
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : realizableAt (I := I) g_bg u₁) (hu₂ : realizableAt (I := I) g_bg u₂)
    (α : M) (l b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : (extChartAt I α).symm y ∈ (chartAt H α).source) :
    reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b y =
      (1 / 2 : ℝ) *
        (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2
            (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂) α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b]
            ((extChartAt I α).symm y) +
          tensorChartComponentRaw (I := I) (M := M) g_bg 0 2
            (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂) α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![b, l]
            ((extChartAt I α).symm y)) := by
  classical
  set S : SmoothCcTensor g_bg 0 2 :=
    realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂ with hS_def
  rw [reprDiffChartCompOnE, ccTensorBilinSymm_apply]
  rw [ccTensorBilin_chartBasisVecFiber_eq_tensorChartComponentRaw (I := I) g_bg S α hy l b,
    ccTensorBilin_chartBasisVecFiber_eq_tensorChartComponentRaw (I := I) g_bg S α hy b l]

/-! ## Leaf-4: coordinate translation between E-side and Euclidean-side partials

The covariant-gradient component formula `tensorChartComponentRaw_covGrad` is stated with the
`EuclideanSpace`-side `euclidPartial` of the chart-pushed raw component.  The target conjuncts
use the `E`-side `partialDeriv`.  The two are interchanged by the chain rule through the
linear isometry `toEuclidean : E ≃ₗᵢ EuclideanSpace ℝ (Fin n)`. -/

/-- **Chain-rule translation of `partialDeriv` to `euclidPartial`.**  For any scalar
`f : E → ℝ` and any direction `a`, the `E`-side partial derivative `partialDeriv a f y` equals
the `EuclideanSpace`-side partial `euclidPartial a (f ∘ toEuclidean.symm) (toEuclidean y)`. -/
theorem partialDeriv_eq_euclidPartial_comp_toEuclidean
    (a : Fin (Module.finrank ℝ E)) (f : E → ℝ) (y : E) :
    partialDeriv (E := E) a f y =
      euclidPartial (E := E) a (f ∘ (toEuclidean (E := E)).symm) (toEuclidean (E := E) y) := by
  rw [euclidPartial_def, partialDeriv]
  -- Chain rule through the linear isometry `toEuclidean.symm`.
  rw [(toEuclidean (E := E)).symm.comp_right_fderiv
    (f := f) (x := toEuclidean (E := E) y)]
  rw [ContinuousLinearMap.comp_apply]
  -- `toEuclidean.symm (single a 1) = chartModelBasis E a`.
  rw [show (toEuclidean (E := E)).symm.toContinuousLinearMap
      (EuclideanSpace.single a (1 : ℝ)) = (chartModelBasis E) a from by
    rw [chartModelBasis_apply]; rfl]
  -- `toEuclidean.symm (toEuclidean y) = y`.
  rw [show (toEuclidean (E := E)).symm (toEuclidean (E := E) y) = y from by simp]

/-- The `E`-side partial derivative function `partialDeriv a f`, pulled back through
`toEuclidean.symm`, equals the `EuclideanSpace`-side partial `euclidPartial a (f ∘
toEuclidean.symm)` (as functions on the Euclidean model space). -/
theorem partialDeriv_comp_toEuclidean_symm_eq_euclidPartial
    (a : Fin (Module.finrank ℝ E)) (f : E → ℝ) :
    (partialDeriv (E := E) a f) ∘ (toEuclidean (E := E)).symm =
      euclidPartial (E := E) a (f ∘ (toEuclidean (E := E)).symm) := by
  funext z
  rw [Function.comp_apply,
    partialDeriv_eq_euclidPartial_comp_toEuclidean (E := E) a f
      ((toEuclidean (E := E)).symm z)]
  rw [show toEuclidean (E := E) ((toEuclidean (E := E)).symm z) = z from by simp]

/-- **Second-order chain-rule translation.**  For any scalar `f : E → ℝ` and directions
`c a`, the iterated `E`-side partial `partialDeriv c (partialDeriv a f) y` equals the iterated
`EuclideanSpace`-side partial `euclidPartial c (euclidPartial a (f ∘ toEuclidean.symm))
(toEuclidean y)`. -/
theorem partialDeriv2_eq_euclidPartial2_comp_toEuclidean
    (c a : Fin (Module.finrank ℝ E)) (f : E → ℝ) (y : E) :
    partialDeriv (E := E) c (partialDeriv (E := E) a f) y =
      euclidPartial (E := E) c
        (euclidPartial (E := E) a (f ∘ (toEuclidean (E := E)).symm))
        (toEuclidean (E := E) y) := by
  rw [partialDeriv_eq_euclidPartial_comp_toEuclidean (E := E) c (partialDeriv (E := E) a f) y]
  rw [partialDeriv_comp_toEuclidean_symm_eq_euclidPartial (E := E) a f]

/-! ## Leaf-4: the chart-pushed realized component as a symmetrized raw chart push -/

/-- On the Euclidean chart target, the `toEuclidean.symm`-pull of the realized-difference
chart-frame component function `reprDiffChartCompOnE g_bg hu₁ hu₂ α l b` equals the
symmetrized chart-push of the raw chart components of `S = realizableRepr hu₁ −
realizableRepr hu₂`. -/
theorem reprDiffChartCompOnE_comp_toEuclidean_symm_eqOn
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : realizableAt (I := I) g_bg u₁) (hu₂ : realizableAt (I := I) g_bg u₂)
    (α : M) (l b : Fin (Module.finrank ℝ E)) :
    Set.EqOn
      (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b ∘ (toEuclidean (E := E)).symm)
      (fun y' => (1 / 2 : ℝ) *
        (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2
              (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂) α
              (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b]) y'
          + chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2
              (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂) α
              (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![b, l]) y'))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  intro y' hy'
  set S : SmoothCcTensor g_bg 0 2 :=
    realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂ with hS_def
  -- `b₀ := symm (toEuclidean.symm y')` lies in the chart source.
  have hb_src : (extChartAt I α).symm ((toEuclidean (E := E)).symm y') ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy'
  -- Beta-reduce the right-hand side lambda.
  simp only []
  -- LHS is the symmetrized raw component at the chart preimage (leaf-3).
  rw [Function.comp_apply,
    reprDiffChartCompOnE_eq_symm_tensorChartComponentRaw (I := I) g_bg hu₁ hu₂ α l b
      (y := (toEuclidean (E := E)).symm y') hb_src]
  -- RHS: `chartPushedRaw` of each raw component at `y'` is the raw component at the preimage.
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy',
    chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy']

/-! ## Leaf-4: the covariant-gradient inversion of the chart-pushed raw component

The chart-component formula `tensorChartComponentRaw_covGrad` reads, in `EuclideanSpace`
coordinates, the raw component of `covGrad S` as `euclidPartial (chart-push of raw comp of S)
+ Christoffel correction`.  Rearranged, the `EuclideanSpace`-side partial of the chart-pushed
raw component of `S` is the raw component of `covGrad S` minus the correction. -/

/-- **First-order covariant-gradient inversion (`s = 2`, `r = 0`).**  For `y' ∈
chartTargetEuclid α`, the `EuclideanSpace`-side partial of the chart-pushed raw `(0,2)`-component
of `S` at indices `![l, b]` in direction `a` equals the raw `(0,3)`-component of `covGrad g_bg
0 2 S` at indices `![a, l, b]` (read at the chart preimage of `y'`), minus the lower-order
Christoffel correction. -/
theorem euclidPartial_chartPushedRaw_eq_covGrad_sub_lowerOrder
    (g_bg : SmoothRiemannianMetric I M) (S : SmoothCcTensor g_bg 0 2) (α : M)
    (a l b : Fin (Module.finrank ℝ E)) {y' : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy' : y' ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) a
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 S α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b])) y' =
      tensorChartComponentRaw (I := I) (M := M) g_bg 0 (2 + 1)
          (covGrad (I := I) (M := M) g_bg 0 2 S) α
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![a, l, b]
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y'))
        - covDerivLowerOrderTerm (I := I) (M := M) g_bg 0 2 S α a
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b] y' := by
  classical
  -- `vecTail ![a, l, b] = ![l, b]` and `![a, l, b] 0 = a`.
  have hJ0 : (![a, l, b] : Fin 3 → Fin (Module.finrank ℝ E)) 0 = a := rfl
  have hJtail : Matrix.vecTail (![a, l, b] : Fin 3 → Fin (Module.finrank ℝ E)) = ![l, b] := by
    funext j; fin_cases j <;> rfl
  -- Apply the chart-component formula at `Jdx := ![a, l, b]`.
  have hform := tensorChartComponentRaw_covGrad (I := I) (M := M) g_bg 0 2 S α
    (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![a, l, b] hy'
  rw [hJ0, hJtail] at hform
  -- `hform : raw(covGrad S) = euclidPartial a (chartPush raw_{![l,b]}) + lowerOrder`.
  -- Rearrange to isolate the euclidPartial term.
  rw [hform]
  ring

/-! ## Leaf-4: differentiability bookkeeping in Euclidean coordinates -/

/-- The chart-push of a raw chart component is differentiable at every point of the
(open) Euclidean chart target. -/
theorem chartPushedRaw_tensorChartComponentRaw_differentiableAt
    (g_bg : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g_bg 0 s) (α : M)
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y' : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy' : y' ∈ chartTargetEuclid (I := I) (M := M) α) :
    DifferentiableAt ℝ
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g_bg 0 s S α
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx)) y' := by
  have hcd := chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M) g_bg 0 s S α
    (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  exact (hcd.contDiffAt (hopen.mem_nhds hy')).differentiableAt (by simp)

/-- For `y` in the chart-target interior, `toEuclidean y` lies in the Euclidean chart target. -/
theorem toEuclidean_mem_chartTargetEuclid_of_mem_interior
    (α : M) {y : E} (hy : y ∈ interior ((extChartAt I α).target : Set E)) :
    toEuclidean (E := E) y ∈ chartTargetEuclid (I := I) (M := M) α :=
  ⟨y, interior_subset hy, rfl⟩

/-! ## Leaf-4: the first chart-coordinate partial of the realized component -/

/-- **The first chart partial of the realized-difference component, as covariant-gradient
components minus Christoffel corrections.**  For `y` in the chart-target interior, the
`E`-side partial `partialDeriv a (reprDiffChartCompOnE g_bg hu₁ hu₂ α l b) y` equals the
symmetrized combination of the raw `(0,3)`-components of `covGrad g_bg 0 2 S` at indices
`![a, l, b]` and `![a, b, l]` (evaluated at the chart preimage) minus the lower-order
Christoffel corrections. -/
theorem partialDeriv_reprDiffChartCompOnE_eq_covGrad_sub_lowerOrder
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : realizableAt (I := I) g_bg u₁) (hu₂ : realizableAt (I := I) g_bg u₂)
    (α : M) (a l b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior ((extChartAt I α).target : Set E)) :
    partialDeriv (E := E) a (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b) y =
      (1 / 2 : ℝ) *
        ((tensorChartComponentRaw (I := I) (M := M) g_bg 0 (2 + 1)
              (covGrad (I := I) (M := M) g_bg 0 2
                (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)) α
              (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![a, l, b]
              ((extChartAt I α).symm y)
            - covDerivLowerOrderTerm (I := I) (M := M) g_bg 0 2
                (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂) α a
                (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b]
                (toEuclidean (E := E) y))
          + (tensorChartComponentRaw (I := I) (M := M) g_bg 0 (2 + 1)
              (covGrad (I := I) (M := M) g_bg 0 2
                (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)) α
              (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![a, b, l]
              ((extChartAt I α).symm y)
            - covDerivLowerOrderTerm (I := I) (M := M) g_bg 0 2
                (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂) α a
                (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![b, l]
                (toEuclidean (E := E) y))) := by
  classical
  set S : SmoothCcTensor g_bg 0 2 :=
    realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂ with hS_def
  set ys : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean (E := E) y with hys_def
  have hys_mem : ys ∈ chartTargetEuclid (I := I) (M := M) α :=
    toEuclidean_mem_chartTargetEuclid_of_mem_interior (I := I) (M := M) α hy
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  -- Abbreviate the two chart-pushed raw components.
  set Flb : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    chartPushedRaw I α
      (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 S α
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b]) with hFlb_def
  set Fbl : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    chartPushedRaw I α
      (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 S α
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![b, l]) with hFbl_def
  -- Step 1: translate the E-side partial to the Euclidean side.
  rw [partialDeriv_eq_euclidPartial_comp_toEuclidean (E := E) a
    (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b) y]
  rw [← hys_def]
  -- Step 2: on a neighbourhood of `ys`, the pulled component equals the symmetrized push.
  have hevt : (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b ∘ (toEuclidean (E := E)).symm)
      =ᶠ[nhds ys] (fun y' => (1 / 2 : ℝ) * (Flb y' + Fbl y')) := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨chartTargetEuclid (I := I) (M := M) α, hopen.mem_nhds hys_mem, ?_⟩
    intro z hz
    have h := reprDiffChartCompOnE_comp_toEuclidean_symm_eqOn (I := I) g_bg hu₁ hu₂ α l b hz
    rw [hFlb_def, hFbl_def]
    exact h
  -- Step 3: differentiate the symmetrized push by linearity.
  rw [euclidPartial_def, hevt.fderiv_eq]
  have hdiff_lb : DifferentiableAt ℝ Flb ys :=
    chartPushedRaw_tensorChartComponentRaw_differentiableAt (I := I) g_bg 2 S α ![l, b] hys_mem
  have hdiff_bl : DifferentiableAt ℝ Fbl ys :=
    chartPushedRaw_tensorChartComponentRaw_differentiableAt (I := I) g_bg 2 S α ![b, l] hys_mem
  rw [show (fun y' => (1 / 2 : ℝ) * (Flb y' + Fbl y')) =
      (1 / 2 : ℝ) • (Flb + Fbl) from by
        funext y'; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]]
  rw [fderiv_const_smul (hdiff_lb.add hdiff_bl),
    fderiv_add hdiff_lb hdiff_bl]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul]
  -- Step 4: convert each fderiv-term back to a euclidPartial and apply the inversion.
  rw [show fderiv ℝ Flb ys (EuclideanSpace.single a 1) = euclidPartial (E := E) a Flb ys from rfl,
    show fderiv ℝ Fbl ys (EuclideanSpace.single a 1) = euclidPartial (E := E) a Fbl ys from rfl]
  rw [hFlb_def, hFbl_def, hys_def,
    euclidPartial_chartPushedRaw_eq_covGrad_sub_lowerOrder (I := I) g_bg S α a l b
      (by rw [← hys_def]; exact hys_mem),
    euclidPartial_chartPushedRaw_eq_covGrad_sub_lowerOrder (I := I) g_bg S α a b l
      (by rw [← hys_def]; exact hys_mem)]
  rw [show (toEuclidean (E := E)).symm ys = y from by rw [hys_def]; simp]

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
