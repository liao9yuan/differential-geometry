import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.CovDerivIntrinsicComponent
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.CovDerivSlotCorrectionComponent

/-!
# The chart-coordinate covariant-derivative component formula

For a smooth, compactly-supported `(r, s)`-tensor section `S` over a closed
Riemannian manifold `(M, g)` and a chart center `α : M`, the chart-coordinate
covariant derivative `chartTensorRSCovariantDerivative r s g α S.toSection X b`
decomposes (see `ChartTensorRSCovariantDerivative.lean`) as

```
tensorRSIntrinsicChartCLM r s α S.toSection b (X b)
  + ∑ₖ chartTensorRSInputSlotCorrection …
  − ∑ₗ chartTensorRSOutputSlotCorrection …
```

The two companion files isolate the three pieces and compute their raw
chart-scalar components:

* the intrinsic (Fréchet-derivative) piece projects, along the `m`-th
  chart-coordinate basis vector field, to the `m`-th chart-Euclidean partial
  derivative of the Euclidean push-forward of the raw component
  (`tensorRSIntrinsicChartCLM_component_eq_euclidPartial`);
* each Christoffel slot correction projects to a finite linear combination of
  *undifferentiated* raw chart components, with `C^∞` coefficients
  (`chartTensorRSInputSlotCorrection_component_eq`,
  `chartTensorRSOutputSlotCorrection_component_eq`).

This file combines the three contributions. The raw chart-scalar component of
the chart-coordinate covariant derivative, along the chart-coordinate basis
vector field `chartBasisVecFiber α m`, is the plain chart-Euclidean partial
derivative `euclidPartial m` of the raw component, plus a *zeroth-order*
correction: a finite linear combination of undifferentiated raw chart
components of `S`, with `C^∞` coefficients on the Euclidean chart target. The
correction coefficients `covDerivLowerOrderCoeff` package the slot-correction
coefficients (`inputSlotCoeff`, `outputSlotCoeff`) of the two companion files,
summed over the input and output slot indices and re-indexed by full
component multi-index pairs.

This is the precise statement that the chart-coordinate covariant derivative
of a tensor component is, in chart-Euclidean coordinates, the plain partial
derivative plus first-order (in the metric, zeroth-order in `S`) Christoffel
corrections — the headline used by elliptic-regularity arguments to lift
component-wise scalar regularity to covariant tensor regularity.

## Main results

* `covDerivLowerOrderCoeff` — the `C^∞` coefficient family of the lower-order
  (zeroth-order in `S`) correction term.
* `covDerivLowerOrderCoeff_contDiffOn` — each coefficient is `C^∞` on the
  Euclidean chart target.
* `covDerivComponent_eq_euclidPartial_add_lowerOrder` — the headline: the raw
  chart-scalar component of the chart-coordinate covariant derivative is the
  chart-Euclidean partial derivative of the raw component plus the lower-order
  correction term.
* `covDerivComponent_lowerOrder_contDiffOn` — the lower-order correction term
  is `ContDiffOn ℝ ∞` on the Euclidean chart target.
* `covDerivComponent_lowerOrder_eq_linearCombination` — the lower-order term
  is, by construction, a finite linear combination of undifferentiated raw
  chart components of `S`.
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

/-! ## The lower-order correction coefficient family

The chart-coordinate covariant derivative decomposes as the intrinsic
Fréchet-derivative piece plus the Christoffel slot corrections. The two
companion files express each slot correction's raw chart-scalar component as a
finite linear combination of *undifferentiated* raw chart components:

* the `k`-th input-slot correction sums over input multi-indices `Idx'`,
  with the output multi-index `Jdx` unchanged, coefficients `inputSlotCoeff`;
* the `l`-th output-slot correction sums over output multi-indices `Jdx'`,
  with the input multi-index `Idx` unchanged, coefficients `outputSlotCoeff`.

To package both into a single sum over full component multi-index *pairs*
`(Idx', Jdx')`, we attach a Kronecker delta restoring the unchanged index:
the input contribution carries `[Jdx' = Jdx]`, the output contribution carries
`[Idx' = Idx]`. The lower-order correction coefficient is the input
contribution minus the output contribution. -/

/-- The lower-order correction coefficient of the chart-coordinate covariant
derivative along the chart-coordinate basis vector field `chartBasisVecFiber α
m`. For a source component multi-index pair `(Idx, Jdx)` and a target pair
`(Idx', Jdx')`, it is the sum over input slots `k` of the input-slot
coefficient `inputSlotCoeff` (restricted to `Jdx' = Jdx` by a Kronecker
delta), minus the sum over output slots `l` of the output-slot coefficient
`outputSlotCoeff` (restricted to `Idx' = Idx` by a Kronecker delta). As a
function on the Euclidean chart target, it is `C^∞`
(`covDerivLowerOrderCoeff_contDiffOn`). -/
noncomputable def covDerivLowerOrderCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    (∑ k : Fin r,
        inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y *
          (if Jdx' = Jdx then (1 : ℝ) else 0))
      - ∑ l : Fin s,
          outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y *
            (if Idx' = Idx then (1 : ℝ) else 0)

/-- Unfolding lemma for `covDerivLowerOrderCoeff`. -/
lemma covDerivLowerOrderCoeff_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx' Jdx Jdx' y =
      (∑ k : Fin r,
          inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y *
            (if Jdx' = Jdx then (1 : ℝ) else 0))
        - ∑ l : Fin s,
            outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y *
              (if Idx' = Idx then (1 : ℝ) else 0) := rfl

/-- **The lower-order correction coefficient is `C^∞` on the Euclidean chart
target.** Each summand is a `C^∞` slot-correction coefficient
(`inputSlotCoeff_contDiffOn`, `outputSlotCoeff_contDiffOn`) times a constant
Kronecker delta; a finite sum and difference of `C^∞` functions is `C^∞`. -/
theorem covDerivLowerOrderCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx' Jdx Jdx')
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- The input contribution: a finite sum of `C^∞` functions.
  have hinput : ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        ∑ k : Fin r,
          inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y *
            (if Jdx' = Jdx then (1 : ℝ) else 0))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine ContDiffOn.sum (fun k _ => ?_)
    exact (inputSlotCoeff_contDiffOn (I := I) (M := M) g r α m k Idx Idx').mul
      contDiffOn_const
  -- The output contribution: a finite sum of `C^∞` functions.
  have houtput : ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        ∑ l : Fin s,
          outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y *
            (if Idx' = Idx then (1 : ℝ) else 0))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine ContDiffOn.sum (fun l _ => ?_)
    exact (outputSlotCoeff_contDiffOn (I := I) (M := M) g s α m l Jdx Jdx').mul
      contDiffOn_const
  -- The coefficient is the input contribution minus the output contribution.
  have hsub := hinput.sub houtput
  refine hsub.congr (fun y _ => ?_)
  rw [covDerivLowerOrderCoeff_def]

/-! ## The wrapped raw-component projection as a continuous linear functional

Both companion files phrase their results on the
`continuousLinearMapAt`-wrapped raw-component projection of a section value:
the value is first re-trivialised through
`(trivializationAt …).continuousLinearMapAt ℝ b`, then projected to the
`(Idx, Jdx)`-component by `tensorChartComponentProjection`. Both operations
are continuous linear maps, so their composite is a continuous linear
functional on the `(r, s)`-tensor fibre. Bundling it explicitly lets the
3-way decomposition of `chartTensorRSCovariantDerivative` be pushed through
the projection by the `map_add` / `map_sub` / `map_sum` lemmas. -/

/-- The wrapped raw-component projection as a continuous linear functional on
the `(r, s)`-tensor fibre at `b`: the `continuousLinearMapAt`-trivialisation
at `b` composed with the `(Idx, Jdx)`-component projection. -/
noncomputable def wrappedComponentProj
    (r s : ℕ) (α b : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    TensorRSSpace r s I b →L[ℝ] ℝ :=
  (tensorChartComponentProjection (E := E) r s Idx Jdx).comp
    ((trivializationAt (TensorRSModel r s ℝ E)
        (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b)

/-- `wrappedComponentProj` applied to a fibre element is exactly the
`continuousLinearMapAt`-wrapped raw-component projection convention used by the
two companion files. -/
lemma wrappedComponentProj_apply
    (r s : ℕ) (α b : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (T : TensorRSSpace r s I b) :
    wrappedComponentProj (I := I) (M := M) r s α b Idx Jdx T =
      tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b
          T) := rfl

/-! ## The headline component formula

Decomposing `chartTensorRSCovariantDerivative` by `chartTensorRSCovariantDerivative_def`
and pushing the linear functional `wrappedComponentProj` through the sum /
difference splits the raw chart-scalar component into the intrinsic
contribution and the two slot-correction contributions. The intrinsic
contribution is the chart-Euclidean partial derivative (companion file 1); the
slot-correction contributions are finite linear combinations of
undifferentiated raw chart components (companion file 2). Re-indexing the slot
sums by full component multi-index pairs collects everything into a single
lower-order correction term with `covDerivLowerOrderCoeff` coefficients. -/

/-- The raw-component projection of the intrinsic-piece value, regrouped by
`chartTensorRSCovariantDerivative_def`. This records that the intrinsic term of
the 3-way split projects, along `chartBasisVecFiber α m`, to the
chart-Euclidean partial derivative — the content of companion file 1, recast
for the `wrappedComponentProj` functional. -/
private lemma wrappedComponentProj_intrinsic_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    wrappedComponentProj (I := I) (M := M) r s α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) Idx Jdx
        (tensorRSIntrinsicChartCLM (I := I) r s α S.toSection
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartBasisVecFiber (I := I) α m
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) =
      euclidPartial (E := E) m
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y := by
  rw [wrappedComponentProj_apply]
  exact tensorRSIntrinsicChartCLM_component_eq_euclidPartial
    (I := I) (M := M) g r s S α Idx Jdx m hy

/-- The raw-component projection of the `k`-th input-slot correction value,
recast for the `wrappedComponentProj` functional — the content of companion
file 2 (input-slot case). -/
private lemma wrappedComponentProj_inputSlot_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E)) (k : Fin r)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    wrappedComponentProj (I := I) (M := M) r s α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) Idx Jdx
        (chartTensorRSInputSlotCorrection (I := I) r s g α S.toSection
          (chartBasisVecFiber (I := I) α m)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) k) =
      ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
        inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y *
          tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  rw [wrappedComponentProj_apply]
  exact chartTensorRSInputSlotCorrection_component_eq
    (I := I) (M := M) g r s S α m k Idx Jdx hy

/-- The raw-component projection of the `l`-th output-slot correction value,
recast for the `wrappedComponentProj` functional — the content of companion
file 2 (output-slot case). -/
private lemma wrappedComponentProj_outputSlot_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E)) (l : Fin s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    wrappedComponentProj (I := I) (M := M) r s α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) Idx Jdx
        (chartTensorRSOutputSlotCorrection (I := I) r s g α S.toSection
          (chartBasisVecFiber (I := I) α m)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) l) =
      ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
        outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y *
          tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx'
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  rw [wrappedComponentProj_apply]
  exact chartTensorRSOutputSlotCorrection_component_eq
    (I := I) (M := M) g r s S α m l Idx Jdx hy

/-- Re-indexing of the input-slot contribution: the finite sum, over input
multi-indices `Idx'`, of `inputSlotCoeff · raw(Idx', Jdx)` equals the finite
sum over full component multi-index *pairs* `(Idx', Jdx')` of
`(inputSlotCoeff · [Jdx' = Jdx]) · raw(Idx', Jdx')`. The Kronecker delta
collapses the `Jdx'`-sum to the single term `Jdx' = Jdx`. -/
private lemma inputSlot_sum_reindex
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E)) (k : Fin r)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
    (b : M) :
    (∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
        inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y *
          tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx b) =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        inputSlotCoeff (I := I) (M := M) g r α m k Idx p.1 y *
          (if p.2 = Jdx then (1 : ℝ) else 0) *
          tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2 b := by
  classical
  -- Expand the product-type sum on the right as an iterated sum, outer index
  -- `Idx'`, inner index `Jdx'`.
  refine Eq.symm ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun Idx' _ => ?_)
  -- Collapse the inner `Jdx'`-sum via the Kronecker delta `[Jdx' = Jdx]`.
  rw [Finset.sum_eq_single Jdx]
  · rw [if_pos rfl, mul_one]
  · intro Jdx' _ hJdx'
    rw [if_neg hJdx', mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ Jdx) h

/-- Re-indexing of the output-slot contribution: the finite sum, over output
multi-indices `Jdx'`, of `outputSlotCoeff · raw(Idx, Jdx')` equals the finite
sum over full component multi-index *pairs* `(Idx', Jdx')` of
`(outputSlotCoeff · [Idx' = Idx]) · raw(Idx', Jdx')`. The Kronecker delta
collapses the `Idx'`-sum to the single term `Idx' = Idx`. -/
private lemma outputSlot_sum_reindex
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E)) (l : Fin s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
    (b : M) :
    (∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
        outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y *
          tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx' b) =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        outputSlotCoeff (I := I) (M := M) g s α m l Jdx p.2 y *
          (if p.1 = Idx then (1 : ℝ) else 0) *
          tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2 b := by
  classical
  -- Expand the product-type sum on the right as an iterated sum, outer index
  -- `Idx'`, inner index `Jdx'`; then collapse the outer `Idx'`-sum via the
  -- Kronecker delta `[Idx' = Idx]`.
  refine Eq.symm ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single Idx]
  · refine Finset.sum_congr rfl (fun Jdx' _ => ?_)
    rw [if_pos rfl, mul_one]
  · intro Idx' _ hIdx'
    refine Finset.sum_eq_zero (fun Jdx' _ => ?_)
    rw [if_neg hIdx', mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ Idx) h

/-- The lower-order correction term: the finite sum over component multi-index
pairs of `covDerivLowerOrderCoeff · raw(component)`. Defined separately so the
headline and its corollaries refer to a single expression. -/
noncomputable def covDerivLowerOrderTerm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) : ℝ :=
  ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
    covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
      tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))

/-- Unfolding lemma for `covDerivLowerOrderTerm`. -/
lemma covDerivLowerOrderTerm_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
          tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := rfl

/-- The sum, over input slots `k`, of the input-slot contributions equals the
input part of the lower-order term: the finite sum over component multi-index
pairs of `(∑ₖ inputSlotCoeff · [Jdx' = Jdx]) · raw(component)`. -/
private lemma sum_inputSlot_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (∑ k : Fin r,
        wrappedComponentProj (I := I) (M := M) r s α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) Idx Jdx
          (chartTensorRSInputSlotCorrection (I := I) r s g α S.toSection
            (chartBasisVecFiber (I := I) α m)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) k)) =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        (∑ k : Fin r,
            inputSlotCoeff (I := I) (M := M) g r α m k Idx p.1 y *
              (if p.2 = Jdx then (1 : ℝ) else 0)) *
          tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  -- Rewrite each input-slot summand via companion file 2, then re-index by
  -- component multi-index pairs.
  have hstep : (∑ k : Fin r,
        wrappedComponentProj (I := I) (M := M) r s α b Idx Jdx
          (chartTensorRSInputSlotCorrection (I := I) r s g α S.toSection
            (chartBasisVecFiber (I := I) α m) b k)) =
      ∑ k : Fin r,
        ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          inputSlotCoeff (I := I) (M := M) g r α m k Idx p.1 y *
            (if p.2 = Jdx then (1 : ℝ) else 0) *
            tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2 b := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [wrappedComponentProj_inputSlot_eq (I := I) (M := M) g r s S α m k
      Idx Jdx hy]
    exact inputSlot_sum_reindex (I := I) (M := M) g r s S α m k Idx Jdx y b
  rw [hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_mul]

/-- The sum, over output slots `l`, of the output-slot contributions equals the
output part of the lower-order term: the finite sum over component multi-index
pairs of `(∑ₗ outputSlotCoeff · [Idx' = Idx]) · raw(component)`. -/
private lemma sum_outputSlot_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (∑ l : Fin s,
        wrappedComponentProj (I := I) (M := M) r s α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) Idx Jdx
          (chartTensorRSOutputSlotCorrection (I := I) r s g α S.toSection
            (chartBasisVecFiber (I := I) α m)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) l)) =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        (∑ l : Fin s,
            outputSlotCoeff (I := I) (M := M) g s α m l Jdx p.2 y *
              (if p.1 = Idx then (1 : ℝ) else 0)) *
          tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hstep : (∑ l : Fin s,
        wrappedComponentProj (I := I) (M := M) r s α b Idx Jdx
          (chartTensorRSOutputSlotCorrection (I := I) r s g α S.toSection
            (chartBasisVecFiber (I := I) α m) b l)) =
      ∑ l : Fin s,
        ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          outputSlotCoeff (I := I) (M := M) g s α m l Jdx p.2 y *
            (if p.1 = Idx then (1 : ℝ) else 0) *
            tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2 b := by
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [wrappedComponentProj_outputSlot_eq (I := I) (M := M) g r s S α m l
      Idx Jdx hy]
    exact outputSlot_sum_reindex (I := I) (M := M) g r s S α m l Idx Jdx y b
  rw [hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_mul]

/-- The input part minus the output part collects into the lower-order term
with `covDerivLowerOrderCoeff` coefficients. -/
private lemma inputSlot_sub_outputSlot_eq_lowerOrderTerm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (∑ k : Fin r,
        wrappedComponentProj (I := I) (M := M) r s α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) Idx Jdx
          (chartTensorRSInputSlotCorrection (I := I) r s g α S.toSection
            (chartBasisVecFiber (I := I) α m)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) k))
      - (∑ l : Fin s,
          wrappedComponentProj (I := I) (M := M) r s α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) Idx Jdx
            (chartTensorRSOutputSlotCorrection (I := I) r s g α S.toSection
              (chartBasisVecFiber (I := I) α m)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) l)) =
      covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y := by
  classical
  rw [sum_inputSlot_eq (I := I) (M := M) g r s S α m Idx Jdx hy,
    sum_outputSlot_eq (I := I) (M := M) g r s S α m Idx Jdx hy,
    covDerivLowerOrderTerm_def, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [covDerivLowerOrderCoeff_def, ← sub_mul]

/-- The `wrappedComponentProj` functional distributes across the 3-way
decomposition `chartTensorRSCovariantDerivative_def` of the covariant
derivative: being a continuous linear functional it commutes with the finite
sum and the difference. -/
private lemma wrappedComponentProj_covDeriv_split
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (b : M) :
    wrappedComponentProj (I := I) (M := M) r s α b Idx Jdx
        (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
          (chartBasisVecFiber (I := I) α m) b) =
      wrappedComponentProj (I := I) (M := M) r s α b Idx Jdx
          (tensorRSIntrinsicChartCLM (I := I) r s α S.toSection b
            (chartBasisVecFiber (I := I) α m b))
        + (∑ k : Fin r,
            wrappedComponentProj (I := I) (M := M) r s α b Idx Jdx
              (chartTensorRSInputSlotCorrection (I := I) r s g α S.toSection
                (chartBasisVecFiber (I := I) α m) b k))
        - (∑ l : Fin s,
            wrappedComponentProj (I := I) (M := M) r s α b Idx Jdx
              (chartTensorRSOutputSlotCorrection (I := I) r s g α S.toSection
                (chartBasisVecFiber (I := I) α m) b l)) := by
  classical
  -- The 3-way decomposition of `chartTensorRSCovariantDerivative`.
  rw [chartTensorRSCovariantDerivative_def]
  -- `wrappedComponentProj` is a continuous linear functional: distribute it
  -- across the difference, the sum, and the finite slot-sums.
  rw [map_sub, map_add, map_sum, map_sum]

/-- **The chart-coordinate covariant-derivative component formula.** Let
`S : SmoothCcTensor g r s`, let `α : M` be a chart center, let
`m : Fin (finrank ℝ E)` index the chart-coordinate basis vector field
`chartBasisVecFiber α m`, and let `(Idx, Jdx)` be a component multi-index
pair. For `y` in the Euclidean chart target `chartTargetEuclid α`, set
`b := (extChartAt I α).symm (toEuclidean.symm y)`. Then the
`continuousLinearMapAt`-wrapped raw chart-scalar component, at `(Idx, Jdx)`, of
the chart-coordinate covariant derivative
`chartTensorRSCovariantDerivative r s g α S.toSection (chartBasisVecFiber α m)`
at `b` equals the `m`-th chart-Euclidean partial derivative `euclidPartial m`
of the Euclidean push-forward of the raw component, plus the lower-order
correction term `covDerivLowerOrderTerm` — a finite linear combination of
*undifferentiated* raw chart components of `S`, with `C^∞` coefficients
`covDerivLowerOrderCoeff`.

In words: the chart-coordinate covariant derivative of a tensor component is,
in chart-Euclidean coordinates, the plain partial derivative plus a
zeroth-order (in `S`) Christoffel correction. -/
theorem covDerivComponent_eq_euclidPartial_add_lowerOrder
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
            (chartBasisVecFiber (I := I) α m)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) =
      euclidPartial (E := E) m
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y
        + covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  -- Recast the goal through the bundled `wrappedComponentProj` functional.
  rw [← wrappedComponentProj_apply (I := I) (M := M) r s α b Idx Jdx]
  -- Push `wrappedComponentProj` through the 3-way covariant-derivative split.
  rw [wrappedComponentProj_covDeriv_split (I := I) (M := M) g r s S α m
    Idx Jdx b]
  -- The intrinsic term is the chart-Euclidean partial derivative (file 1).
  rw [wrappedComponentProj_intrinsic_eq (I := I) (M := M) g r s S α m
    Idx Jdx hy]
  -- Reassociate `(intrinsic + inputSum) − outputSum` as
  -- `intrinsic + (inputSum − outputSum)`.
  rw [add_sub_assoc]
  -- The input-slot sum minus the output-slot sum is the lower-order term.
  rw [inputSlot_sub_outputSlot_eq_lowerOrderTerm (I := I) (M := M) g r s S α m
    Idx Jdx hy]

/-! ## Corollaries for the downstream consumer

The two corollaries below extract from the headline the two facts that the
downstream covariant-tensor-regularity argument needs:

* the lower-order correction term is `C^∞` on the Euclidean chart target,
  given that the raw chart components of `S` are `C^∞` there;
* the lower-order correction term is, by construction, a finite linear
  combination of undifferentiated raw chart components of `S` (zeroth order
  in `S`).

The raw chart components of a smooth compactly-supported section are smooth on
the chart source (`tensorChartComponentRaw_contMDiffOn_chart_source`); their
chart-Euclidean push-forwards `chartPushedRaw` are correspondingly `C^∞` on the
Euclidean chart target. The first corollary is stated with that `C^∞`
hypothesis explicit so it can be discharged either from the chart-source
smoothness lemma or from any other source the consumer prefers. -/

/-- **The lower-order correction term is `C^∞` on the Euclidean chart
target.** Given that every Euclidean push-forward
`chartPushedRaw I α (tensorChartComponentRaw g r s S α Idx' Jdx')` of a raw
chart component of `S` is `ContDiffOn ℝ ∞` on the Euclidean chart target, the
lower-order correction term `covDerivLowerOrderTerm` — a finite linear
combination of those push-forwards with the `C^∞` coefficients
`covDerivLowerOrderCoeff` — is itself `ContDiffOn ℝ ∞` there. -/
theorem covDerivComponent_lowerOrder_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (hraw : ∀ (Idx' : Fin r → Fin (Module.finrank ℝ E))
        (Jdx' : Fin s → Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ ∞
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx'))
        (chartTargetEuclid (I := I) (M := M) α)) :
    ContDiffOn ℝ ∞
      (covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- Each summand is a `C^∞` coefficient times a `C^∞` raw-component
  -- push-forward; the raw component appears undifferentiated.
  have hsummand : ∀ p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ ∞
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
            tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro p
    -- The coefficient is `C^∞` (`covDerivLowerOrderCoeff_contDiffOn`).
    have hcoeff : ContDiffOn ℝ ∞
        (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2)
        (chartTargetEuclid (I := I) (M := M) α) :=
      covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α m
        Idx p.1 Jdx p.2
    -- On the Euclidean chart target the raw-component factor is, pointwise,
    -- the `C^∞` Euclidean push-forward `chartPushedRaw`.
    have hrawfac : ContDiffOn ℝ ∞
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) := by
      refine (hraw p.1 p.2).congr (fun y hy => ?_)
      exact (chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2) hy).symm
    exact hcoeff.mul hrawfac
  -- A finite sum of `C^∞` functions is `C^∞`.
  have hsum :
      ContDiffOn ℝ ∞
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
              tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) :=
    ContDiffOn.sum (fun p _ => hsummand p)
  -- The lower-order term is, definitionally, exactly this finite sum.
  exact hsum

/-- **The lower-order correction term is a finite linear combination of
undifferentiated raw chart components.** The lower-order correction term
`covDerivLowerOrderTerm` of the headline equals, at every Euclidean chart
target point `y`, the finite sum over component multi-index pairs
`(Idx', Jdx')` of `covDerivLowerOrderCoeff … y` times the raw chart component
`tensorChartComponentRaw g r s S α Idx' Jdx' b` of `S`, with
`b := (extChartAt I α).symm (toEuclidean.symm y)`. No derivative of `S`
appears: the correction is zeroth order in `S`, the coefficients
`covDerivLowerOrderCoeff` being `C^∞` (`covDerivLowerOrderCoeff_contDiffOn`)
and independent of `S`. -/
theorem covDerivComponent_lowerOrder_eq_linearCombination
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
          tensorChartComponentRaw (I := I) (M := M) g r s S α p.1 p.2
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) :=
  covDerivLowerOrderTerm_def (I := I) (M := M) g r s S α m Idx Jdx y

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
