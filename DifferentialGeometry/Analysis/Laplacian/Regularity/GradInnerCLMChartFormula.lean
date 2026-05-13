import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInnerCLM
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartBilinearSmooth
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomainChartData
import DifferentialGeometry.Analysis.Laplacian.MetricExtension
import DifferentialGeometry.Geometry.Gradient
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Chart formula for `gradInnerCLM` (smooth case)

For a closed Riemannian manifold `(M, g)` and a chart point `α : M`, the
pointwise metric inner product of the gradients of two smooth functions `ρα`
and `v` expands in chart coordinates as

```
g(grad ρα, grad v)(x) =
  ∑ i, j, g⁻¹^{ij}(x) · ∂_i (ρα ∘ symm)(φ x) · ∂_j (v ∘ symm)(φ x),
```

where `φ = extChartAt I α`, `symm = (extChartAt I α).symm` and `g⁻¹^{ij}(x)`
is the `(i, j)`-entry of the chart-local inverse Gram matrix at `x`. After
pulling back via `(extChartAt I α).symm ∘ toEuclidean.symm` to a point `y` in
`chartTargetEuclid α`, the formula reads

```
chartPushedRaw I α (gradInnerSmooth g ρα v) y =
  ∑ i, j, invGramOnEuclid g α i j y
    · partialDerivOnEuclid α i ρα y · partialDerivOnEuclid α j v.toFun y,
```

where `partialDerivOnEuclid α i u y := partialDeriv i (scalarOnE α u) (symm_E y)`
denotes the `i`-th chart-coordinate partial of the chart-pulled scalar
`u ∘ (extChartAt I α).symm` evaluated at `(toEuclidean (E := E)).symm y`.

This file packages the smooth-case chart formula in two equivalent forms:

* a pointwise identity on `chartTargetEuclid α`,
* an `ae`-identity between two `Lp ℝ 2` classes on the chart-pulled weighted
  measure restricted to `chartTargetEuclid α`, lifting the pointwise identity
  through the `chartPushedRawLpFromLp` construction.

Both formulations use the smooth-case identification `gradInnerCLM g ρα
(smoothToH1Compl v) = gradInnerSmooth g ρα v` from `GradInnerCLM.lean`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology Function
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerCLMChartFormula

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearSmooth
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Sobolev.Chart

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-! ## Auxiliary helper: the chart-pulled `i`-th partial of a smooth function

Given a smooth function `u : M → ℝ` and a chart point `α : M`, we define the
chart-pulled `i`-th partial as
```
partialDerivOnEuclid α i u y := partialDeriv i (scalarOnE α u) ((toEuclidean (E := E)).symm y).
```
This is a smooth function of `y` on `chartTargetEuclid α`, since
`scalarOnE α u = u ∘ (extChartAt I α).symm` is smooth on `(extChartAt I α).target`
when `u` is smooth on `M`, and `(toEuclidean (E := E)).symm` is a continuous
linear equivalence. -/

/-- The `i`-th chart-pulled partial derivative of a function `u : M → ℝ` at a
point `y ∈ EuclN`, defined as
`partialDeriv i (u ∘ (extChartAt I α).symm) ((toEuclidean (E := E)).symm y)`. -/
def partialDerivOnEuclid (α : M) (i : Fin (Module.finrank ℝ E)) (u : M → ℝ) :
    EuclN → ℝ := fun y =>
  partialDeriv (E := E) i (scalarOnE (I := I) α u) ((toEuclidean (E := E)).symm y)

@[simp] lemma partialDerivOnEuclid_def (α : M) (i : Fin (Module.finrank ℝ E))
    (u : M → ℝ) (y : EuclN) :
    partialDerivOnEuclid (I := I) (M := M) α i u y =
      partialDeriv (E := E) i (scalarOnE (I := I) α u)
        ((toEuclidean (E := E)).symm y) := rfl

/-! ## The pointwise chart formula for `gradInnerSmooth` -/

/-- **Pointwise chart formula** for the smooth pointwise gradient inner
product. For smooth `ρα, u : M → ℝ` and `y ∈ chartTargetEuclid α`, denoting
`x = (extChartAt I α).symm ((toEuclidean (E := E)).symm y)`, the metric inner
product `g(grad ρα x, grad u x)` equals the chart-coordinate sum
`∑ i, j, invGramOnEuclid g α i j y · partialDerivOnEuclid α i ρα y ·
partialDerivOnEuclid α j u y`. -/
theorem gradInner_eq_chart_formula
    (g : SmoothRiemannianMetric I M) (α : M)
    {ρα u : M → ℝ}
    (hρα : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρα) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    g.inner ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (gradFun (I := I) g ρα
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (gradFun (I := I) g u
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        invGramOnEuclid (I := I) g α i j y *
          partialDerivOnEuclid (I := I) (M := M) α i ρα y *
          partialDerivOnEuclid (I := I) (M := M) α j u y := by
  classical
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  -- `x` lies in the chart base set.
  have h_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    toEuclidean_symm_mem_target (I := I) hy
  have hx_source : x ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target h_target
  have hx_chart_src : x ∈ (chartAt H α).source := by
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hx_source
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx_chart_src
  -- The chart map sends `x` into the interior of the chart target.
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target := by
    have h_φx : extChartAt I α x = (toEuclidean (E := E)).symm y := by
      rw [hx_def]; exact (extChartAt I α).right_inv h_target
    rw [h_φx]
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) α h_target
  -- Apply Step 1 of `ChartBilinearSmooth`.
  have h_step1 := gradInner_eq_invGramMatrix_partials_smooth
    (I := I) g α hρα hu hx_base hx_int
  -- Identify `extChartAt I α x = (toEuclidean (E := E)).symm y`.
  have hφx_eq : extChartAt I α x = (toEuclidean (E := E)).symm y := by
    rw [hx_def]; exact (extChartAt I α).right_inv h_target
  -- Identify `chartInvGramMatrix g α x i j = invGramOnEuclid g α i j y`.
  have h_invGram : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g α x i j =
        invGramOnEuclid (I := I) g α i j y := by
    intro i j
    unfold invGramOnEuclid; rfl
  -- Identify partial derivatives.
  have h_partial : ∀ k : Fin (Module.finrank ℝ E),
      ∀ u' : M → ℝ,
        partialDeriv (E := E) k (scalarOnE (I := I) α u') (extChartAt I α x) =
          partialDerivOnEuclid (I := I) (M := M) α k u' y := by
    intro k u'
    rw [hφx_eq]
    rfl
  -- Substitute.
  rw [h_step1]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [h_partial i ρα, h_partial j u, h_invGram i j]

/-! ## Pointwise chart formula for `gradInnerSmooth g ρα v` -/

/-- Pointwise chart formula at a point `y ∈ chartTargetEuclid α` for the
pulled-back gradient inner product `gradInnerSmooth g ρα v` evaluated at
`x_y = (extChartAt I α).symm ((toEuclidean (E := E)).symm y)`. -/
theorem chartPushedRaw_gradInnerSmooth_pointwise
    (g : SmoothRiemannianMetric I M) (α : M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    g.inner ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (gradFun (I := I) g ρα
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (gradFun (I := I) g v.toFun
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        invGramOnEuclid (I := I) g α i j y *
          partialDerivOnEuclid (I := I) (M := M) α i ρα y *
          partialDerivOnEuclid (I := I) (M := M) α j v.toFun y :=
  gradInner_eq_chart_formula (I := I) (M := M) g α ρα.contMDiff v.smooth hy

/-! ## Measurability and continuity of the chart formula RHS

The chart formula RHS is a sum of products of three factors:

* `invGramOnEuclid g α i j y` — smooth (and hence continuous) on
  `chartTargetEuclid α`.
* `partialDerivOnEuclid α i ρα y` — smooth (and hence continuous) on
  `chartTargetEuclid α` for smooth `ρα`.
* `partialDerivOnEuclid α j v.toFun y` — smooth (and hence continuous) on
  `chartTargetEuclid α` for smooth `v.toFun`.

The full sum is therefore continuous on `chartTargetEuclid α`, measurable
everywhere on `EuclN` (by extending continuously or via Borel-measurability),
and in particular AEStronglyMeasurable with respect to the chart-pulled
weighted measure restricted to `chartTargetEuclid α`. -/

/-- Smoothness of `partialDerivOnEuclid α i u` on `chartTargetEuclid α` for
smooth `u`. -/
lemma partialDerivOnEuclid_contDiffOn (α : M) (i : Fin (Module.finrank ℝ E))
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ContDiffOn ℝ ∞ (partialDerivOnEuclid (I := I) (M := M) α i u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- `partialDerivOnEuclid α i u = (partialDeriv i (scalarOnE α u)) ∘ symm_E`.
  -- `scalarOnE α u` is smooth on `(extChartAt I α).target` (by `scalarOnE_contDiffOn`).
  -- Its `i`-th partial is the value at the chart-target point of the fderiv applied to
  -- a fixed basis vector — smooth on the same open set.
  have h_scalar : ContDiffOn ℝ ∞ (scalarOnE (I := I) α u) (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hu
  -- The fderiv of a `ContDiffOn ℝ ∞` function is `ContDiffOn ℝ ∞` on the open subset
  -- — actually, we use `ContDiffOn.fderivWithin`/`ContDiff.fderiv`. Since
  -- `(extChartAt I α).target` is open in `E`, fderiv coincides with fderivWithin on it.
  have h_open_target : IsOpen ((extChartAt I α).target) :=
    isOpen_extChartAt_target (I := I) α
  -- `partialDeriv i u' y = fderiv ℝ u' y ((chartModelBasis E) i)`.
  have h_pd : ContDiffOn ℝ ∞
      (fun y : E => partialDeriv (E := E) i (scalarOnE (I := I) α u) y)
      (extChartAt I α).target := by
    unfold partialDeriv
    -- fderiv of scalarOnE α u is `ContDiffOn ℝ (∞-1) = ContDiffOn ℝ ∞` (since we have `∞`).
    have h_fderiv_smooth :
        ContDiffOn ℝ ∞ (fun y : E => fderiv ℝ (scalarOnE (I := I) α u) y)
          (extChartAt I α).target := by
      have h_le : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        rw [show ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 = ((⊤ : ℕ∞) : WithTop ℕ∞) from by
          simp]
      exact h_scalar.fderiv_of_isOpen h_open_target h_le
    exact h_fderiv_smooth.clm_apply contDiffOn_const
  -- Compose with `(toEuclidean (E := E)).symm`, which is smooth from `EuclN` to `E`.
  have h_symm_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm : EuclN → E) :=
    ContinuousLinearEquiv.contDiff _
  have h_maps : Set.MapsTo ((toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := by
    intro y hy
    exact toEuclidean_symm_mem_target (I := I) hy
  have h_comp : ContDiffOn ℝ ∞
      ((fun y : E => partialDeriv (E := E) i (scalarOnE (I := I) α u) y) ∘
        ((toEuclidean (E := E)).symm))
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_pd.comp h_symm_smooth.contDiffOn h_maps
  exact h_comp

/-- Continuity of `partialDerivOnEuclid α i u` on `chartTargetEuclid α`. -/
lemma partialDerivOnEuclid_continuousOn (α : M) (i : Fin (Module.finrank ℝ E))
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ContinuousOn (partialDerivOnEuclid (I := I) (M := M) α i u)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (partialDerivOnEuclid_contDiffOn (I := I) (M := M) α i hu).continuousOn

/-! ## The chart formula RHS as a function

The sum
```
y ↦ ∑ i j, invGramOnEuclid g α i j y · partialDerivOnEuclid α i ρα y
    · partialDerivOnEuclid α j v.toFun y
```
is the natural chart-side expression of the gradient inner product. We
establish its continuity on `chartTargetEuclid α`. -/

/-- The chart formula RHS for the smooth gradient inner product. -/
def chartFormulaRhsSmooth (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) (u : M → ℝ) : EuclN → ℝ := fun y =>
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    invGramOnEuclid (I := I) g α i j y *
      partialDerivOnEuclid (I := I) (M := M) α i ρα y *
      partialDerivOnEuclid (I := I) (M := M) α j u y

@[simp] lemma chartFormulaRhsSmooth_def (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) (u : M → ℝ) (y : EuclN) :
    chartFormulaRhsSmooth (I := I) (M := M) g α ρα u y =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        invGramOnEuclid (I := I) g α i j y *
          partialDerivOnEuclid (I := I) (M := M) α i ρα y *
          partialDerivOnEuclid (I := I) (M := M) α j u y := rfl

/-- Smoothness of `chartFormulaRhsSmooth g α ρα u` on `chartTargetEuclid α`
for smooth `u`. -/
lemma chartFormulaRhsSmooth_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ContDiffOn ℝ ∞ (chartFormulaRhsSmooth (I := I) (M := M) g α ρα u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold chartFormulaRhsSmooth
  refine ContDiffOn.sum (fun i _ => ?_)
  refine ContDiffOn.sum (fun j _ => ?_)
  refine ContDiffOn.mul ?_ ?_
  · refine ContDiffOn.mul ?_ ?_
    · exact invGramOnEuclid_contDiffOn (I := I) (M := M) g α i j
    · exact partialDerivOnEuclid_contDiffOn (I := I) (M := M) α i ρα.contMDiff
  · exact partialDerivOnEuclid_contDiffOn (I := I) (M := M) α j hu

/-- Continuity of `chartFormulaRhsSmooth g α ρα u` on `chartTargetEuclid α`. -/
lemma chartFormulaRhsSmooth_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ContinuousOn (chartFormulaRhsSmooth (I := I) (M := M) g α ρα u)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (chartFormulaRhsSmooth_contDiffOn (I := I) (M := M) g α ρα hu).continuousOn

/-! ## Pointwise identity: chart-pushed-raw `gradInnerSmooth = chart formula RHS` -/

/-- **Pointwise identity** on `chartTargetEuclid α`: for smooth `v`, the
chart-pushed-raw gradient inner product agrees with the chart-formula RHS. -/
theorem chartPushedRaw_gradInner_eq_rhs_pointwise
    (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw (I := I) α
        (fun x : M => g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g v.toFun x)) y =
      chartFormulaRhsSmooth (I := I) (M := M) g α ρα v.toFun y := by
  classical
  -- Unfold chartPushedRaw on chartTarget: it evaluates the function at the
  -- chart-pulled-back point.
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
  unfold chartFormulaRhsSmooth
  exact chartPushedRaw_gradInnerSmooth_pointwise (I := I) (M := M) g α ρα v hy

/-! ## Measurability of the chart formula RHS

To pass to the Lp class identity, we need the chart formula RHS to be
measurable. By continuity on the open set `chartTargetEuclid α`, the RHS is
Borel-measurable on that set. We extend by `0` outside and show the resulting
function is measurable on all of `EuclN`.

For the `ae` identity on `chartPulledWeightedMeasure.restrict chartTarget`,
we only care about behaviour on `chartTarget`, so this extension is harmless. -/

/-- The chart formula RHS, extended by `0` outside `chartTargetEuclid α`.
The natural conventional extension. -/
noncomputable def chartFormulaRhsSmoothExt (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) (u : M → ℝ) : EuclN → ℝ := by
  classical
  exact fun y =>
    if y ∈ chartTargetEuclid (I := I) (M := M) α then
      chartFormulaRhsSmooth (I := I) (M := M) g α ρα u y
    else 0

lemma chartFormulaRhsSmoothExt_apply_of_mem (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) (u : M → ℝ) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartFormulaRhsSmoothExt (I := I) (M := M) g α ρα u y =
      chartFormulaRhsSmooth (I := I) (M := M) g α ρα u y := by
  classical
  change (if y ∈ chartTargetEuclid (I := I) (M := M) α then
        chartFormulaRhsSmooth (I := I) (M := M) g α ρα u y
      else 0) = _
  rw [if_pos hy]

lemma chartFormulaRhsSmoothExt_apply_of_notMem (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) (u : M → ℝ) {y : EuclN}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    chartFormulaRhsSmoothExt (I := I) (M := M) g α ρα u y = 0 := by
  classical
  change (if y ∈ chartTargetEuclid (I := I) (M := M) α then
        chartFormulaRhsSmooth (I := I) (M := M) g α ρα u y
      else 0) = 0
  rw [if_neg hy]

/-- The extended chart formula RHS is continuous on the open chart target
(by smoothness on it) and vanishes outside, hence it is measurable on
`EuclN`. -/
lemma chartFormulaRhsSmoothExt_measurable
    (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    Measurable (chartFormulaRhsSmoothExt (I := I) (M := M) g α ρα u) := by
  classical
  -- Approach: write the function as the indicator of `chartTargetEuclid`
  -- of a continuous function (on chartTargetEuclid, extended arbitrarily
  -- to `EuclN`). The indicator is measurable on a Borel space because
  -- `chartTargetEuclid α` is open (hence Borel).
  have h_meas_target : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  -- Strategy: extend `chartFormulaRhsSmooth` to a measurable function on EuclN
  -- and combine via Set.indicator. Note:
  -- chartFormulaRhsSmoothExt = Set.indicator chartTargetEuclid
  --   (chartFormulaRhsSmooth ...).
  have h_eq : chartFormulaRhsSmoothExt (I := I) (M := M) g α ρα u =
      Set.indicator (chartTargetEuclid (I := I) (M := M) α)
        (chartFormulaRhsSmooth (I := I) (M := M) g α ρα u) := by
    funext y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [chartFormulaRhsSmoothExt_apply_of_mem (I := I) (M := M) g α ρα u hy]
      rw [Set.indicator_of_mem hy]
    · rw [chartFormulaRhsSmoothExt_apply_of_notMem (I := I) (M := M) g α ρα u hy]
      rw [Set.indicator_of_notMem hy]
  rw [h_eq]
  -- The function `chartFormulaRhsSmooth` is continuous on the open set
  -- `chartTargetEuclid`. The indicator on the open (measurable) set is
  -- measurable because the function is continuous on the set.
  have h_cont_on :
      ContinuousOn (chartFormulaRhsSmooth (I := I) (M := M) g α ρα u)
        (chartTargetEuclid (I := I) (M := M) α) :=
    chartFormulaRhsSmooth_continuousOn (I := I) (M := M) g α ρα hu
  -- A continuous function on an open set is measurable as an indicator
  -- on that set: use `Measurable.indicator` after lifting via piecewise.
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  -- The indicator `s.indicator f` agrees with `s.piecewise f 0` since 0 is constant.
  have h_piecewise_eq :
      Set.indicator (chartTargetEuclid (I := I) (M := M) α)
          (chartFormulaRhsSmooth (I := I) (M := M) g α ρα u) =
        (chartTargetEuclid (I := I) (M := M) α).piecewise
          (chartFormulaRhsSmooth (I := I) (M := M) g α ρα u)
          (fun _ => (0 : ℝ)) := by
    funext y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy, Set.piecewise_eq_of_mem _ _ _ hy]
    · rw [Set.indicator_of_notMem hy, Set.piecewise_eq_of_notMem _ _ _ hy]
  rw [h_piecewise_eq]
  refine ContinuousOn.measurable_piecewise h_cont_on ?_ h_meas_target
  exact continuousOn_const

/-! ## Lp class identity: smooth case

The smooth-case Lp class identity:
```
chartPushedRawLpFromLp g α (gradInnerSmooth g ρα v) =ᵐ chartFormulaRhsSmoothExt g α ρα v.toFun.
```

The proof uses the pointwise identity on `chartTargetEuclid α` and the
identification of `chartPushedRawLpFromLp` with `chartPushedRaw` of the
manifold-side representative.
-/

/-- **Smooth-case Lp class identity** for the chart formula. The
chart-pushed-raw Lp class of `gradInnerSmooth g ρα v` is ae-equal to the
extended chart-formula RHS, where ae is taken against the chart-pulled
weighted measure restricted to `chartTargetEuclid α`. -/
theorem chartPushedRawLpFromLp_gradInnerSmooth_aeEq
    (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α
        (gradInnerSmooth (I := I) (M := M) g ρα v) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartFormulaRhsSmoothExt (I := I) (M := M) g α ρα v.toFun := by
  classical
  -- Step 1: `chartPushedRawLpFromLp_coeFn` gives
  --   ((chartPushedRawLpFromLp _).coeFn) =ᵐ chartPushedRaw I α (gradInnerSmooth ...).coeFn.
  have h_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α
    (gradInnerSmooth (I := I) (M := M) g ρα v)
  -- Step 2: `gradInnerSmooth_coeFn` gives
  --   (gradInnerSmooth g ρα v).coeFn =ᵐ pointwise inner product.
  have h_inner := gradInnerSmooth_coeFn (I := I) (M := M) g ρα v
  -- Step 3: Bridge `chartPushedRaw` of ae-equal functions.
  have h_inner_meas :
      Measurable ((gradInnerSmooth (I := I) (M := M) g ρα v :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
    (Lp.stronglyMeasurable _).measurable
  have h_pointwise_meas : Measurable (fun x : M =>
      g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x)) :=
    (gradInnerSmooth_continuous (I := I) (M := M) g ρα v).measurable
  have h_chartPushedRaw_aeEq :=
    DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData.chartPushedRaw_aeEq_of_aeEq
      (I := I) (M := M) g α h_inner_meas h_pointwise_meas h_inner
  -- Step 4: On `chartTargetEuclid α`, the pointwise identity gives
  --   chartPushedRaw I α (pointwise inner)(y) = chartFormulaRhsSmoothExt α ρα v.toFun y.
  -- The chart-pulled weighted measure restricted to chartTarget is supported
  -- on chartTarget (ae statement), so we only need pointwise agreement on chartTarget.
  have h_meas_target : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  have h_weighted_restrict_ae_chartTarget :
      ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)),
      y ∈ chartTargetEuclid (I := I) (M := M) α := by
    rw [ae_restrict_iff' h_meas_target]
    exact Filter.Eventually.of_forall (fun _ h => h)
  -- Combine all pieces.
  filter_upwards [h_coeFn, h_chartPushedRaw_aeEq, h_weighted_restrict_ae_chartTarget]
    with y hy_coeFn hy_chartPushedRaw hy_target
  -- hy_coeFn : (chartPushedRawLpFromLp ...).coeFn y = chartPushedRaw I α (gradInnerSmooth ...).coeFn y
  -- hy_chartPushedRaw : chartPushedRaw I α (gradInnerSmooth ...).coeFn y = chartPushedRaw I α (pointwise inner) y
  -- hy_target : y ∈ chartTargetEuclid α
  rw [hy_coeFn, hy_chartPushedRaw]
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy_target]
  rw [chartFormulaRhsSmoothExt_apply_of_mem (I := I) (M := M) g α ρα v.toFun hy_target]
  unfold chartFormulaRhsSmooth
  exact chartPushedRaw_gradInnerSmooth_pointwise (I := I) (M := M) g α ρα v hy_target

/-! ## Lp class identity for `gradInnerCLM` on smooth scalars

We restate the smooth-case identity for `gradInnerCLM g ρα (smoothToH1Compl v)`,
using the compatibility `gradInnerCLM_smoothToH1Compl`. -/

/-- **Smooth-case chart formula** for `gradInnerCLM`. For smooth `v` and
`u_h = smoothToH1Compl v`, the chart-pushed-raw Lp class of
`gradInnerCLM g ρα u_h` is ae-equal to the extended chart-formula RHS. -/
theorem chartPushedRawLpFromLp_gradInnerCLM_smoothToH1Compl_aeEq
    (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α
        (gradInnerCLM (I := I) (M := M) g ρα
          (smoothToH1Compl (I := I) (M := M) g v)) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartFormulaRhsSmoothExt (I := I) (M := M) g α ρα v.toFun := by
  classical
  rw [gradInnerCLM_smoothToH1Compl (I := I) (M := M) g ρα v]
  exact chartPushedRawLpFromLp_gradInnerSmooth_aeEq (I := I) (M := M) g α ρα v

/-! ## Summary

The smooth-case chart formula identity says: for smooth `v : SmoothScalar g`
and `ρα : C^∞⟮I, M; ℝ⟯`,

```
((chartPushedRawLpFromLp g α (gradInnerCLM g ρα (smoothToH1Compl v))) : EuclN → ℝ)
  =ᵐ[μ_w.restrict chartTarget]
    fun y =>
      if y ∈ chartTargetEuclid α then
        ∑ i, j, invGramOnEuclid g α i j y
          · partialDerivOnEuclid α i ρα y · partialDerivOnEuclid α j v.toFun y
      else 0.
```

This is the pointwise chart formula `g(grad ρα, grad v)(x) = ∑ g⁻¹^{ij}
∂_i ρα ∂_j v(x)` packaged as a chart-pulled `Lp ℝ 2` ae-identity.

The natural next step is to extend this identity from smooth scalars `v` to
arbitrary `u_h ∈ H1Compl g` via density of smooth scalars in `H1Compl g` and
continuity of both sides. The LHS is a `CLM H1Compl g →L[ℝ] Lp ℝ 2`. The RHS
is a `Lp ℝ 2` class formed as a finite sum of products `(smooth bounded
coefficient on chartTarget) * (j-th chart-side weak partial of u_h)`. To
realize the RHS as a CLM in `u_h`, one needs a chart-side weak partial CLM
without the partition-of-unity weight (the existing `chartPushedWeakPartialLp`
carries a partition-of-unity factor that does not match the smooth-case
identity above without further compensation). Such infrastructure is not
provided here; it would parallel the construction of `chartPushedWeakPartialLp`
in `H1ComplWeakPartialLimit.lean` but replace the `chartPushed`-with-POU
input by the `chartPushedRaw` input. -/

end GradInnerCLMChartFormula
end Laplacian
end Analysis
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Analysis.Laplacian.GradInnerCLMChartFormula.gradInner_eq_chart_formula
#print axioms
  DifferentialGeometry.Analysis.Laplacian.GradInnerCLMChartFormula.chartPushedRawLpFromLp_gradInnerSmooth_aeEq
#print axioms
  DifferentialGeometry.Analysis.Laplacian.GradInnerCLMChartFormula.chartPushedRawLpFromLp_gradInnerCLM_smoothToH1Compl_aeEq
end Sanity
