import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.CovDerivComponentFormula
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.CovDerivChartFormLowerOrder
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.ChartWeakIdentity

/-!
# The chart-coordinate second covariant-derivative component formula

For a smooth, compactly-supported `(r, s)`-tensor section `S` over a closed
Riemannian manifold `(M, g)`, a chart center `α : M`, and a pair of chart
directions `(m, n)`, the chart-coordinate `(Idx, Jdx)`-component of the
covariant derivative along `chartBasisVecFiber α m` pulls back to a scalar
function on the Euclidean chart target

```
covDerivComponentEuclid g r s S α m Idx Jdx :
  chartTargetEuclid α → ℝ
```

whose value at `y` is, by the headline of `CovDerivComponentFormula.lean`,
`∂_m raw_α^{Idx,Jdx}(y) + covDerivLowerOrderTerm(y)`. Differentiating again in
the `n`-th chart-Euclidean direction expresses this function's `n`-th
Euclidean partial derivative as

```
∂_n ∂_m raw_α^{Idx,Jdx}(y)
  + ∑_{(Idx', Jdx')} (∂_n covDerivLowerOrderCoeff)(y) · raw_α^{Idx',Jdx'}(y)
  + ∑_{(Idx', Jdx')} covDerivLowerOrderCoeff(y) · ∂_n raw_α^{Idx',Jdx'}(y)
```

— a finite linear combination of the principal mixed partial `∂_n ∂_m raw`,
first-order partials `∂_n raw_α^p` of raw chart components, and undifferentiated
raw chart components, with coefficients `C^∞` on the Euclidean chart target.

This is the precise chart-coordinate-coefficient formula that lifts pointwise
scalar `H²`-style regularity statements (mixed second partials on chart-pulled
push-forwards) to chart-α coordinate-frame second covariant-derivative
components — the input shape that the downstream elliptic-regularity bootstrap
consumes.

## Main definitions

* `covDerivComponentEuclid g r s S α m Idx Jdx y` — the wrapped raw chart
  component of the `m`-direction chart-coordinate covariant derivative,
  evaluated at the chart-pull-back of `y ∈ chartTargetEuclid α`.
* `covDerivLowerOrderTermEuclid g r s S α m Idx Jdx` — the lower-order term
  `covDerivLowerOrderTerm` viewed as a function on the Euclidean chart target.
* `secondCovDerivLO_gradCoeff g r s α m n Idx Idx' Jdx Jdx'` — the smooth
  coefficient multiplying `∂_n raw_α^{Idx', Jdx'}` in the formula (the
  un-differentiated `covDerivLowerOrderCoeff`).
* `secondCovDerivLO_valueCoeff g r s α m n Idx Idx' Jdx Jdx'` — the smooth
  coefficient multiplying `raw_α^{Idx', Jdx'}` in the formula (the
  `n`-th Euclidean partial of `covDerivLowerOrderCoeff`).

## Main results

* `covDerivComponent_second_eq_iteratedFDeriv_add_lowerOrder` — the headline:
  the `n`-th Euclidean partial of `covDerivComponentEuclid` is the second
  mixed partial `∂_n ∂_m raw_α^{Idx,Jdx}` plus a finite linear combination of
  `∂_n raw_α^{Idx',Jdx'}` and `raw_α^{Idx',Jdx'}` with `C^∞` coefficients.
* `secondCovDerivLO_gradCoeff_contDiffOn`,
  `secondCovDerivLO_valueCoeff_contDiffOn` — the lower-order coefficients are
  `C^∞` on the Euclidean chart target.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators
open Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## A `ContDiffOn`-stability lemma for the Euclidean partial derivative

If `u` is `C^∞` on the open Euclidean chart target, its `n`-th Euclidean
partial derivative is again `C^∞` there: on the open set the Fréchet derivative
coincides with the within-derivative, which is `C^∞` by
`contDiffOn_succ_iff_fderivWithin`, and evaluation at a fixed basis vector is
continuous linear. -/

/-- The `n`-th chart-Euclidean partial derivative of a function `C^∞` on the
Euclidean chart target is again `C^∞` on the Euclidean chart target. -/
private lemma euclidPartial_contDiffOn_chartTarget'
    (α : M) (n : Fin (Module.finrank ℝ E))
    {u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (hu : ContDiffOn ℝ ∞ u (chartTargetEuclid (I := I) (M := M) α)) :
    ContDiffOn ℝ ∞ (euclidPartial (E := E) n u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hfderiv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ u z)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have hsucc : ContDiffOn ℝ ((∞ : WithTop ℕ∞) + 1) u
        (chartTargetEuclid (I := I) (M := M) α) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl]; exact hu
    have hfw : ContDiffOn ℝ ∞ (fderivWithin ℝ u
        (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      ((contDiffOn_succ_iff_fderivWithin hopen.uniqueDiffOn).mp hsucc).2.2
    refine hfw.congr (fun z hz => ?_)
    exact (fderivWithin_of_isOpen (f := u) (𝕜 := ℝ) hopen hz).symm
  have hcomp : ContDiffOn ℝ ∞
      ((fun L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] ℝ =>
          L (EuclideanSpace.single n 1)) ∘ (fun z => fderiv ℝ u z))
      (chartTargetEuclid (I := I) (M := M) α) :=
    (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single n 1)).contDiff.comp_contDiffOn hfderiv
  refine hcomp.congr (fun z _ => ?_)
  rfl

/-! ## The wrapped raw chart component of the first covariant derivative,
viewed as a function on the Euclidean chart target

The headline of `CovDerivComponentFormula.lean` equates the wrapped
`(Idx, Jdx)`-raw chart component of the chart-coordinate covariant derivative
`chartTensorRSCovariantDerivative … (chartBasisVecFiber α m)`, evaluated at
`b := (extChartAt I α).symm (toEuclidean.symm y)`, to
`∂_m raw_α^{Idx,Jdx}(y) + covDerivLowerOrderTerm(y)`. To differentiate this
identity in `y` we record the LHS as an explicit function of `y`. -/

/-- The wrapped `(Idx, Jdx)`-raw chart component of the chart-coordinate
covariant derivative `chartTensorRSCovariantDerivative … (chartBasisVecFiber α
m)`, viewed as a function of `y ∈ EuclideanSpace ℝ (Fin n)` by pulling back
through `(extChartAt I α).symm ∘ toEuclidean.symm`. -/
noncomputable def covDerivComponentEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    tensorChartComponentProjection (E := E) r s Idx Jdx
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
          (chartBasisVecFiber (I := I) α m)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))

/-- Unfolding lemma for `covDerivComponentEuclid`. -/
lemma covDerivComponentEuclid_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    covDerivComponentEuclid (I := I) (M := M) g r s α S m Idx Jdx y =
      tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
            (chartBasisVecFiber (I := I) α m)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) := rfl

/-! ## The first-derivative formula in functional form

The chart-α 1st-derivative headline
`covDerivComponent_eq_euclidPartial_add_lowerOrder` rewritten as an identity
between *functions* on `chartTargetEuclid α`. -/

/-- **The first-derivative formula in functional form.** As functions on
`chartTargetEuclid α`, `covDerivComponentEuclid g r s S α m Idx Jdx` agrees
with `euclidPartial m (chartPushedRaw I α (tensorChartComponentRaw …))
+ covDerivLowerOrderTerm`. -/
lemma covDerivComponentEuclid_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EqOn (covDerivComponentEuclid (I := I) (M := M) g r s α S m Idx Jdx)
      (fun y =>
        euclidPartial (E := E) m
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y
          + covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  rw [covDerivComponentEuclid_def]
  exact covDerivComponent_eq_euclidPartial_add_lowerOrder
    (I := I) (M := M) g r s S α m Idx Jdx hy

/-! ## Smoothness of `covDerivComponentEuclid` on the Euclidean chart target

By `covDerivComponentEuclid_eqOn`, on the open Euclidean chart target the
function `covDerivComponentEuclid` agrees with the sum of a `C^∞` Euclidean
partial of a chart-pushed raw component and a `C^∞` lower-order correction
term. -/

/-- **The wrapped covariant-derivative chart-component is `C^∞` on the
Euclidean chart target.** Equal on that open set to the sum
`euclidPartial m (chartPushedRaw …) + covDerivLowerOrderTerm`, both `C^∞`. -/
theorem covDerivComponentEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (covDerivComponentEuclid (I := I) (M := M) g r s α S m Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- The partial of the chart-pushed raw component is `C^∞`.
  have h1 : ContDiffOn ℝ ∞
      (euclidPartial (E := E) m
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)))
      (chartTargetEuclid (I := I) (M := M) α) :=
    euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M) g r s S α m Idx Jdx
  -- The lower-order term is `C^∞`.
  have h2 : ContDiffOn ℝ ∞
      (covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
    covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M) g r s S α m Idx Jdx
      (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
        (I := I) (M := M) g r s S α Idx' Jdx')
  -- The sum is `C^∞`.
  have hsum := h1.add h2
  -- Transfer back via `covDerivComponentEuclid_eqOn`.
  refine hsum.congr (fun y hy => ?_)
  exact covDerivComponentEuclid_eqOn (I := I) (M := M) g r s α S m Idx Jdx hy

/-! ## The chart-pushed raw component as a chart-target function

For the Leibniz expansion of the lower-order term `LO = ∑ coeff · raw`, we
isolate the raw factor as a function on the Euclidean chart target:
`rawComponentEuclid g r s S α p y := tensorChartComponentRaw … (extChartAt^-1
(toEuclidean^-1 y))`. On the chart target this coincides pointwise with the
chart-pushed raw component `chartPushedRaw I α (tensorChartComponentRaw …) y`,
hence is `C^∞` there. -/

/-- The raw chart-α component `tensorChartComponentRaw g r s S α Idx Jdx` pulled
back to a function on the Euclidean model space through
`(extChartAt I α).symm ∘ toEuclidean.symm`. -/
noncomputable def rawComponentEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))

/-- Unfolding lemma for `rawComponentEuclid`. -/
@[simp] lemma rawComponentEuclid_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    rawComponentEuclid (I := I) (M := M) g r s α S Idx Jdx y =
      tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := rfl

/-- On the Euclidean chart target, `rawComponentEuclid` agrees with the chart-
pushed raw component `chartPushedRaw I α (tensorChartComponentRaw …)`. -/
lemma rawComponentEuclid_eqOn_chartPushed
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EqOn (rawComponentEuclid (I := I) (M := M) g r s α S Idx Jdx)
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  rw [rawComponentEuclid_def]
  exact (chartPushedRaw_apply_of_mem (I := I) (M := M) α
    (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hy).symm

/-- `rawComponentEuclid` is `C^∞` on the Euclidean chart target — it agrees
there with the `C^∞` push-forward `chartPushedRaw I α (tensorChartComponentRaw
…)`. -/
theorem rawComponentEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (rawComponentEuclid (I := I) (M := M) g r s α S Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h := chartPushedRaw_tensorChartComponentRaw_contDiffOn
    (I := I) (M := M) g r s S α Idx Jdx
  refine h.congr (fun y hy => ?_)
  exact rawComponentEuclid_eqOn_chartPushed (I := I) (M := M)
    g r s α S Idx Jdx hy

/-- The Euclidean partial of `rawComponentEuclid` is `C^∞` on the Euclidean
chart target. -/
lemma euclidPartial_rawComponentEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (n : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (euclidPartial (E := E) n
        (rawComponentEuclid (I := I) (M := M) g r s α S Idx Jdx))
      (chartTargetEuclid (I := I) (M := M) α) :=
  euclidPartial_contDiffOn_chartTarget' (I := I) (M := M) α n
    (rawComponentEuclid_contDiffOn (I := I) (M := M) g r s α S Idx Jdx)

/-! ## Equivalence of `euclidPartial` on the chart target

On the open Euclidean chart target, `rawComponentEuclid` and `chartPushedRaw
I α (tensorChartComponentRaw …)` agree pointwise, so their Euclidean partials
agree there too: the Fréchet derivative is local. -/

/-- On the Euclidean chart target, the `n`-th Euclidean partial of
`rawComponentEuclid` equals that of `chartPushedRaw I α (tensorChartComponentRaw
…)`. -/
lemma euclidPartial_rawComponentEuclid_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (n : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EqOn (euclidPartial (E := E) n
        (rawComponentEuclid (I := I) (M := M) g r s α S Idx Jdx))
      (euclidPartial (E := E) n
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  intro y hy
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have heq : EqOn (rawComponentEuclid (I := I) (M := M) g r s α S Idx Jdx)
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))
      (chartTargetEuclid (I := I) (M := M) α) :=
    rawComponentEuclid_eqOn_chartPushed (I := I) (M := M) g r s α S Idx Jdx
  -- Fréchet derivatives of pointwise-equal functions agree on open sets.
  have hfderiv : fderiv ℝ
      (rawComponentEuclid (I := I) (M := M) g r s α S Idx Jdx) y =
    fderiv ℝ
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y :=
    Filter.EventuallyEq.fderiv_eq
      (heq.eventuallyEq_of_mem (hopen.mem_nhds hy))
  rw [euclidPartial_def, euclidPartial_def, hfderiv]

/-! ## The lower-order coefficient family `LO = ∑ coeff · raw` as a chart-target
function

The lower-order term `covDerivLowerOrderTerm` is, by construction, the finite
sum over component multi-index pairs `(Idx', Jdx')` of
`covDerivLowerOrderCoeff(y) · raw_α^{Idx',Jdx'}(symm y)`. The summand is the
product of two factors that are `C^∞` on the chart target: the coefficient,
and `rawComponentEuclid`. -/

/-- The `(p₁, p₂)`-summand of the lower-order term as a function on the
Euclidean model space: `covDerivLowerOrderCoeff … y · rawComponentEuclid …
y`. -/
noncomputable def lowerOrderSummand
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (p : (Fin r → Fin (Module.finrank ℝ E)) ×
         (Fin s → Fin (Module.finrank ℝ E))) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
      rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2 y

/-- Unfolding lemma for `lowerOrderSummand`. -/
@[simp] lemma lowerOrderSummand_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (p : (Fin r → Fin (Module.finrank ℝ E)) ×
         (Fin s → Fin (Module.finrank ℝ E)))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p y =
      covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
        rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2 y := rfl

/-- Each `lowerOrderSummand` summand is `C^∞` on the Euclidean chart target —
a product of the `C^∞` coefficient and `rawComponentEuclid`. -/
lemma lowerOrderSummand_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (p : (Fin r → Fin (Module.finrank ℝ E)) ×
         (Fin s → Fin (Module.finrank ℝ E))) :
    ContDiffOn ℝ ∞ (lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α m Idx p.1 Jdx p.2).mul
    (rawComponentEuclid_contDiffOn (I := I) (M := M) g r s α S p.1 p.2)

/-- The lower-order term `covDerivLowerOrderTerm` equals the finite sum over
component multi-index pairs of `lowerOrderSummand`. -/
lemma covDerivLowerOrderTerm_eq_sum_lowerOrderSummand
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p y := by
  rw [covDerivLowerOrderTerm_def]
  rfl

/-! ## The second-derivative lower-order coefficient families

The `n`-th Euclidean partial of the lower-order summand `coeff · raw` is, by
the Leibniz rule, `(∂_n coeff) · raw + coeff · (∂_n raw)`. We name the two
resulting coefficients:

* `secondCovDerivLO_gradCoeff` — the un-differentiated `covDerivLowerOrderCoeff`
  (multiplying `∂_n rawComponentEuclid`);
* `secondCovDerivLO_valueCoeff` — the `n`-th Euclidean partial of
  `covDerivLowerOrderCoeff` (multiplying `rawComponentEuclid`).

Both are `C^∞` on the Euclidean chart target. -/

/-- The smooth coefficient multiplying `∂_n raw_α^{Idx',Jdx'}` in the second-
derivative formula: just the original `covDerivLowerOrderCoeff`. -/
noncomputable def secondCovDerivLO_gradCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx' Jdx Jdx'

/-- The smooth coefficient multiplying `raw_α^{Idx',Jdx'}` in the second-
derivative formula: the `n`-th Euclidean partial of `covDerivLowerOrderCoeff`. -/
noncomputable def secondCovDerivLO_valueCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (m n : Fin (Module.finrank ℝ E))
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  euclidPartial (E := E) n
    (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx' Jdx Jdx')

/-- The `secondCovDerivLO_gradCoeff` coefficient is `C^∞` on the Euclidean
chart target. -/
theorem secondCovDerivLO_gradCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (secondCovDerivLO_gradCoeff (I := I) (M := M) g r s α m Idx Idx' Jdx Jdx')
      (chartTargetEuclid (I := I) (M := M) α) :=
  covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α m Idx Idx' Jdx Jdx'

/-- The `secondCovDerivLO_valueCoeff` coefficient is `C^∞` on the Euclidean
chart target. -/
theorem secondCovDerivLO_valueCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (m n : Fin (Module.finrank ℝ E))
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (secondCovDerivLO_valueCoeff (I := I) (M := M) g r s α m n Idx Idx' Jdx Jdx')
      (chartTargetEuclid (I := I) (M := M) α) :=
  euclidPartial_contDiffOn_chartTarget' (I := I) (M := M) α n
    (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α m Idx Idx' Jdx Jdx')

/-! ## The Leibniz expansion of the `n`-th Euclidean partial of one summand

For a multi-index pair `p = (Idx', Jdx')`, the `n`-th Euclidean partial of the
summand `coeff_p · rawComponentEuclid_p` is `(∂_n coeff_p) · raw_p + coeff_p ·
(∂_n raw_p)` at any chart-target point. -/

/-- The Leibniz rule for the lower-order summand at a chart-target point. -/
lemma euclidPartial_lowerOrderSummand_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m n : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (p : (Fin r → Fin (Module.finrank ℝ E)) ×
         (Fin s → Fin (Module.finrank ℝ E)))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) n
        (lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p) y =
      secondCovDerivLO_valueCoeff (I := I) (M := M) g r s α m n
          Idx p.1 Jdx p.2 y *
        rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2 y +
      secondCovDerivLO_gradCoeff (I := I) (M := M) g r s α m
          Idx p.1 Jdx p.2 y *
        euclidPartial (E := E) n
          (rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2) y := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hcoeff : ContDiffOn ℝ ∞
      (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2)
      (chartTargetEuclid (I := I) (M := M) α) :=
    covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α m Idx p.1 Jdx p.2
  have hraw : ContDiffOn ℝ ∞
      (rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2)
      (chartTargetEuclid (I := I) (M := M) α) :=
    rawComponentEuclid_contDiffOn (I := I) (M := M) g r s α S p.1 p.2
  -- Differentiability at `y` from `ContDiffOn` on the open set containing `y`.
  have hcoeff_diff : DifferentiableAt ℝ
      (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2) y := by
    have h : DifferentiableOn ℝ
        (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2)
        (chartTargetEuclid (I := I) (M := M) α) :=
      hcoeff.differentiableOn (by norm_cast)
    exact (h.differentiableAt (hopen.mem_nhds hy))
  have hraw_diff : DifferentiableAt ℝ
      (rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2) y := by
    have h : DifferentiableOn ℝ
        (rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2)
        (chartTargetEuclid (I := I) (M := M) α) :=
      hraw.differentiableOn (by norm_cast)
    exact (h.differentiableAt (hopen.mem_nhds hy))
  -- Apply Leibniz.
  have hleib := euclidPartial_mul (E := E) n hcoeff_diff hraw_diff
  rw [show lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p =
      (fun z =>
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 z *
          rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2 z) from rfl]
  rw [hleib]
  unfold secondCovDerivLO_valueCoeff secondCovDerivLO_gradCoeff
  ring

/-! ## The headline: the `n`-th Euclidean partial of `covDerivComponentEuclid`

By `covDerivComponentEuclid_eqOn`, on the open chart target
`covDerivComponentEuclid` equals `euclidPartial m (chartPushedRaw …) +
covDerivLowerOrderTerm`. The Fréchet derivative is local on open sets:
`covDerivComponentEuclid`'s Fréchet derivative at any chart-target point
coincides with that of the sum. Computing the Fréchet derivative summand-wise
through the Leibniz rule then yields the headline. -/

/-- The `n`-th Euclidean partial of `covDerivComponentEuclid` at a chart-target
point equals the `n`-th Euclidean partial of `euclidPartial m (chartPushedRaw
…) + covDerivLowerOrderTerm`. The Fréchet derivative is local on the open
chart target. -/
private lemma euclidPartial_covDerivComponentEuclid_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m n : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) n
        (covDerivComponentEuclid (I := I) (M := M) g r s α S m Idx Jdx) y =
      euclidPartial (E := E) n
        (fun y' =>
          euclidPartial (E := E) m
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y'
            + covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y') y := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have heq := covDerivComponentEuclid_eqOn (I := I) (M := M) g r s α S m Idx Jdx
  have hfderiv : fderiv ℝ
      (covDerivComponentEuclid (I := I) (M := M) g r s α S m Idx Jdx) y =
    fderiv ℝ
      (fun y' =>
        euclidPartial (E := E) m
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y'
          + covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y') y :=
    Filter.EventuallyEq.fderiv_eq
      (heq.eventuallyEq_of_mem (hopen.mem_nhds hy))
  rw [euclidPartial_def, euclidPartial_def, hfderiv]

/-- The `n`-th Euclidean partial of the sum `∂_m chartPushedRaw +
covDerivLowerOrderTerm` decomposes as the sum of the partials, since both
factors are `C^∞` (hence differentiable) at any chart-target point. -/
private lemma euclidPartial_sum_split
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m n : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) n
        (fun y' =>
          euclidPartial (E := E) m
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y'
            + covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y') y =
      euclidPartial (E := E) n
          (euclidPartial (E := E) m
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))) y
        + euclidPartial (E := E) n
            (covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx) y := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h1 : ContDiffOn ℝ ∞
      (euclidPartial (E := E) m
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)))
      (chartTargetEuclid (I := I) (M := M) α) :=
    euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M) g r s S α m Idx Jdx
  have h2 : ContDiffOn ℝ ∞
      (covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
    covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M) g r s S α m Idx Jdx
      (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
        (I := I) (M := M) g r s S α Idx' Jdx')
  have h1_diff : DifferentiableAt ℝ
      (euclidPartial (E := E) m
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))) y := by
    have hd : DifferentiableOn ℝ
        (euclidPartial (E := E) m
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)))
        (chartTargetEuclid (I := I) (M := M) α) :=
      h1.differentiableOn (by norm_cast)
    exact (hd.differentiableAt (hopen.mem_nhds hy))
  have h2_diff : DifferentiableAt ℝ
      (covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx) y := by
    have hd : DifferentiableOn ℝ
        (covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) :=
      h2.differentiableOn (by norm_cast)
    exact (hd.differentiableAt (hopen.mem_nhds hy))
  -- Use `fderiv_fun_add` and unfold `euclidPartial`.
  rw [euclidPartial_def, euclidPartial_def, euclidPartial_def]
  rw [fderiv_fun_add h1_diff h2_diff]
  rw [ContinuousLinearMap.add_apply]

/-- The `n`-th Euclidean partial of `covDerivLowerOrderTerm`, which is the
finite sum of `lowerOrderSummand` over multi-index pairs, equals the finite
sum of the partials of the individual summands. -/
private lemma euclidPartial_covDerivLowerOrderTerm_eq_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m n : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) n
        (covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx) y =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        euclidPartial (E := E) n
          (lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p) y := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  -- First convert `covDerivLowerOrderTerm` to a finite sum on the chart target.
  have heq : EqOn (covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx)
      (fun z =>
        ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p z)
      (chartTargetEuclid (I := I) (M := M) α) := by
    intro z _
    exact covDerivLowerOrderTerm_eq_sum_lowerOrderSummand
      (I := I) (M := M) g r s α S m Idx Jdx z
  -- Fréchet-derivative equality on open sets.
  have hfderiv : fderiv ℝ
      (covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx) y =
    fderiv ℝ
      (fun z =>
        ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p z) y :=
    Filter.EventuallyEq.fderiv_eq
      (heq.eventuallyEq_of_mem (hopen.mem_nhds hy))
  -- Each summand is differentiable at `y`.
  have hsummand_diff : ∀ p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      DifferentiableAt ℝ (lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p) y := by
    intro p
    have h := lowerOrderSummand_contDiffOn (I := I) (M := M) g r s α S m Idx Jdx p
    have hd : DifferentiableOn ℝ
        (lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p)
        (chartTargetEuclid (I := I) (M := M) α) :=
      h.differentiableOn (by norm_cast)
    exact hd.differentiableAt (hopen.mem_nhds hy)
  -- Use `fderiv_finset_sum`.
  have hfsum :
      fderiv ℝ
        (fun z =>
          ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p z) y =
        ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          fderiv ℝ (lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p) y :=
    fderiv_fun_sum (fun p _ => hsummand_diff p)
  rw [euclidPartial_def, hfderiv, hfsum]
  -- The CLM-evaluation distributes through finite sums.
  rw [show (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          fderiv ℝ (lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p) y)
        (EuclideanSpace.single n 1) =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        fderiv ℝ (lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p) y
          (EuclideanSpace.single n 1) by
    rw [ContinuousLinearMap.sum_apply]]
  rfl

/-! ## The headline second-derivative formula

The `n`-th Euclidean partial of `covDerivComponentEuclid` decomposes into the
mixed second partial of the chart-pushed raw, plus a finite sum, over
multi-index pairs, of `(∂_n coeff_p) · raw_p + coeff_p · (∂_n raw_p)`. -/

/-- **The chart-coordinate second covariant-derivative component formula.**
For `y ∈ chartTargetEuclid α`, the `n`-th Euclidean partial of the function
`covDerivComponentEuclid g r s α S m Idx Jdx`, which equals on the chart target
the wrapped `(Idx, Jdx)`-raw chart component of the chart-coordinate covariant
derivative `chartTensorRSCovariantDerivative … (chartBasisVecFiber α m)` pulled
back through `(extChartAt I α).symm ∘ toEuclidean.symm`, decomposes as

* the mixed second partial `∂_n ∂_m raw_α^{Idx, Jdx}` of the chart-pushed raw
  component, plus
* a finite sum, over component multi-index pairs `(Idx', Jdx')`, of the
  product `secondCovDerivLO_valueCoeff · raw_α^{Idx', Jdx'}`
  (zeroth-order-in-`S` term: the `n`-th Euclidean partial of the original
  Christoffel coefficient times the undifferentiated raw component), plus
* a finite sum, over component multi-index pairs `(Idx', Jdx')`, of the
  product `secondCovDerivLO_gradCoeff · ∂_n raw_α^{Idx', Jdx'}` (first-order-
  in-`S` term: the original Christoffel coefficient times the `n`-th Euclidean
  partial of the raw component).

All `secondCovDerivLO_*` coefficients are `C^∞` on the Euclidean chart target. -/
theorem covDerivComponent_second_eq_iteratedFDeriv_add_lowerOrder
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m n : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) n
        (covDerivComponentEuclid (I := I) (M := M) g r s α S m Idx Jdx) y =
      euclidPartial (E := E) n
          (euclidPartial (E := E) m
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))) y
        + (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            secondCovDerivLO_valueCoeff (I := I) (M := M) g r s α m n
                Idx p.1 Jdx p.2 y *
              rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2 y)
        + (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            secondCovDerivLO_gradCoeff (I := I) (M := M) g r s α m
                Idx p.1 Jdx p.2 y *
              euclidPartial (E := E) n
                (rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2) y) := by
  classical
  -- Step 1: Replace the LHS using the equality on the chart target.
  rw [euclidPartial_covDerivComponentEuclid_eq (I := I) (M := M)
    g r s α S m n Idx Jdx hy]
  -- Step 2: Distribute the `∂_n` across the sum `∂_m chartPushedRaw + LO`.
  rw [euclidPartial_sum_split (I := I) (M := M) g r s α S m n Idx Jdx hy]
  -- Step 3: Reduce the `∂_n LO` to a finite sum of `∂_n` summands.
  rw [euclidPartial_covDerivLowerOrderTerm_eq_sum (I := I) (M := M)
    g r s α S m n Idx Jdx hy]
  -- Step 4: Expand each summand's `∂_n` via Leibniz, and split the sum
  -- into the value-coefficient and gradient-coefficient parts.
  rw [show
      (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          euclidPartial (E := E) n
            (lowerOrderSummand (I := I) (M := M) g r s α S m Idx Jdx p) y) =
      (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          (secondCovDerivLO_valueCoeff (I := I) (M := M) g r s α m n
                Idx p.1 Jdx p.2 y *
              rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2 y +
            secondCovDerivLO_gradCoeff (I := I) (M := M) g r s α m
                Idx p.1 Jdx p.2 y *
              euclidPartial (E := E) n
                (rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2) y)) by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    exact euclidPartial_lowerOrderSummand_apply (I := I) (M := M)
      g r s α S m n Idx Jdx p hy]
  rw [Finset.sum_add_distrib]
  ring

/-! ## Existential form for downstream consumers

The downstream regularity bootstrap consumes the formula as an existential
statement: "there exist `C^∞` coefficients `(Coeff_2nd, Coeff_1n, Coeff_1m,
Coeff_0_first, Coeff_0_second)` such that the formula's RHS equals the
chart-coordinate-coefficient expansion". The `secondCovDerivLO_*` coefficients
naturally produce such an instantiation when the formula is integrated over a
finite multi-index family. -/

/-- **Existential form of the chart-coordinate second covariant-derivative
component formula.** For each chart-target point `y`, there exist `C^∞`
coefficient families such that the `n`-th Euclidean partial of
`covDerivComponentEuclid` equals the mixed second partial `∂_n ∂_m raw` plus a
finite linear combination of `∂_n raw_p` and `raw_p` with `C^∞`
coefficients.

The coefficients are indexed by component multi-index pairs `p = (Idx', Jdx')`:
the `valueCoeff p` multiplies `raw_p` (a derivative of the Christoffel
coefficient), and the `gradCoeff p` multiplies `∂_n raw_p` (the original
Christoffel coefficient). -/
theorem covDerivComponent_second_existential
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m n : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ (valueCoeff gradCoeff :
        (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)) →
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ),
      (∀ p, ContDiffOn ℝ ∞ (valueCoeff p)
              (chartTargetEuclid (I := I) (M := M) α)) ∧
      (∀ p, ContDiffOn ℝ ∞ (gradCoeff p)
              (chartTargetEuclid (I := I) (M := M) α)) ∧
      (∀ {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))},
        y ∈ chartTargetEuclid (I := I) (M := M) α →
          euclidPartial (E := E) n
              (covDerivComponentEuclid (I := I) (M := M) g r s α S m Idx Jdx) y =
            euclidPartial (E := E) n
                (euclidPartial (E := E) m
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))) y
              + (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                      (Fin s → Fin (Module.finrank ℝ E)),
                  valueCoeff p y *
                    rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2 y)
              + (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                      (Fin s → Fin (Module.finrank ℝ E)),
                  gradCoeff p y *
                    euclidPartial (E := E) n
                      (rawComponentEuclid (I := I) (M := M) g r s α S p.1 p.2) y)) := by
  classical
  refine ⟨fun p => secondCovDerivLO_valueCoeff (I := I) (M := M)
            g r s α m n Idx p.1 Jdx p.2,
          fun p => secondCovDerivLO_gradCoeff (I := I) (M := M)
            g r s α m Idx p.1 Jdx p.2, ?_, ?_, ?_⟩
  · intro p
    exact secondCovDerivLO_valueCoeff_contDiffOn (I := I) (M := M)
      g r s α m n Idx p.1 Jdx p.2
  · intro p
    exact secondCovDerivLO_gradCoeff_contDiffOn (I := I) (M := M)
      g r s α m Idx p.1 Jdx p.2
  · intro y hy
    exact covDerivComponent_second_eq_iteratedFDeriv_add_lowerOrder
      (I := I) (M := M) g r s α S m n Idx Jdx hy

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
