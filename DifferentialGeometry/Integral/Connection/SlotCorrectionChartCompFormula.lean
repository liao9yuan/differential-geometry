import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.CovDerivSlotCorrectionComponent

/-!
# Chart-component formula for the input/output slot corrections, with general
vector-field argument

For an arbitrary vector field `B`, the chart-scalar component of
`chartTensorRSInputSlotCorrection r s g α T B b k` (resp. the output-slot
analog) is expressed as a finite sum

```
∑ m, (B^m at b) * ∑ Idx', inputSlotCoeff g r α m k Idx Idx' y *
  tensorChartComponentRaw g r s S α Idx' Jdx b
```

where `B^m(b) = ((chartModelBasis E).repr (trivToE α b (B b))) m` are the
chart components of `B`. The `chartBasisVecFiber`-case is supplied by the
companion file `CovDerivSlotCorrectionComponent.lean`; we extend it via
linearity in `B`.
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
namespace Integral
namespace Connection

open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Linearity of `chartLeviCivitaParallelCLM` in the field's value at `b`

On the chart base set, the value of the section `B` at `b` decomposes as
`B b = ∑_m B^m(b) • chartBasisVecFiber α m b`. The CLM
`chartLeviCivitaParallelCLM g α b B` is linear in `B b` (via
`christoffelCorrection`'s additivity in `Y` and `trivToE`'s linearity), so
the same finite-sum decomposition propagates through. -/

/-- `B b` decomposes in the chart frame on the chart base set. The chart
component `((chartModelBasis E).repr (trivToE α b (B b))) m` is the `B^m(b)`
factor. -/
lemma section_eq_sum_chartFrame
    (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (B : Π b' : M, TangentSpace I b') :
    B b =
      ∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
          chartBasisVecFiber (I := I) α m b := by
  classical
  -- Apply `sum_chartFrame_coord_eq` with `w = B b`, and convert `coord` to
  -- `repr` to match the headline shape.
  have h := sum_chartFrame_coord_eq (I := I) (M := M) α hb (B b)
  refine h.symm.trans ?_
  refine Finset.sum_congr rfl (fun m _ => ?_)
  -- `chartJ α b` and `trivToE α b` agree (both = `continuousLinearMapAt ℝ b`).
  have hchartJ_eq : chartJ (I := I) (M := M) α b (B b) =
      trivToE (I := I) α b (B b) := rfl
  rw [Module.Basis.coord_apply, hchartJ_eq]

/-- Auxiliary: `christoffelCorrection` is linear in its `Y` argument, applied
to a finite sum of scalar-weighted basis vectors. The coefficients `c m` and
vectors `w m` are free parameters; this is purely the linearity
`christoffelCorrection (∑ m, c m • w m) v = ∑ m, c m • christoffelCorrection
(w m) v`. -/
lemma christoffelCorrection_sum
    (g : SmoothRiemannianMetric I M) (α b : M)
    (c : Fin (Module.finrank ℝ E) → ℝ)
    (w : Fin (Module.finrank ℝ E) → E) (v : TangentSpace I b) :
    christoffelCorrection (I := I) g α b
        (∑ m : Fin (Module.finrank ℝ E), c m • w m) v =
      ∑ m : Fin (Module.finrank ℝ E),
        c m • christoffelCorrection (I := I) g α b (w m) v := by
  classical
  induction (Finset.univ : Finset (Fin (Module.finrank ℝ E))) using Finset.induction
    with
  | empty =>
      simp only [Finset.sum_empty]
      have h := christoffelCorrection_smul (I := I) g α b (c := 0)
        (Y := (0 : E)) v
      rw [zero_smul, zero_smul] at h
      exact h
  | insert m s hms ih =>
      rw [Finset.sum_insert hms, Finset.sum_insert hms]
      rw [christoffelCorrection_add (I := I) g α b]
      rw [christoffelCorrection_smul (I := I) g α b]
      rw [ih]

/-- On the chart base set, the chart Levi-Civita parallel CLM along an
arbitrary vector field `B` is the finite sum of `B^m(b)`-weighted parallel
CLMs along the chart coordinate basis vector fields. -/
lemma chartLeviCivitaParallelCLM_sum_decomposition
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (B : Π b' : M, TangentSpace I b') :
    chartLeviCivitaParallelCLM (I := I) g α b B =
      ∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
          chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α m) := by
  classical
  -- Both sides are CLMs `TangentSpace I b →L[ℝ] TangentSpace I b`. Reduce to
  -- equality of the underlying `christoffelCorrection` expression on `E`.
  ext v
  -- Expand the LHS via `chartLeviCivitaParallelCLM_apply`.
  rw [chartLeviCivitaParallelCLM_apply]
  -- Expand the RHS sum.
  rw [show (∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
          chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α m)) v =
      ∑ m : Fin (Module.finrank ℝ E),
        ((((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
          chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α m)) v by
    rw [ContinuousLinearMap.sum_apply]]
  -- Rewrite each summand via `chartLeviCivitaParallelCLM_apply` and unfold
  -- the scalar multiplication.
  have hRHS : ∀ m : Fin (Module.finrank ℝ E),
      ((((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
          chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α m)) v =
        (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
          trivFromE (I := I) α b
            (christoffelCorrection (I := I) g α b
              (trivToE (I := I) α b
                (chartBasisVecFiber (I := I) α m b)) v) := by
    intro m
    rw [ContinuousLinearMap.smul_apply, chartLeviCivitaParallelCLM_apply]
  rw [Finset.sum_congr rfl (fun m _ => hRHS m)]
  -- Pull `trivFromE α b` and `christoffelCorrection (· in argument Y)` out
  -- of the sum.
  rw [show ∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
          trivFromE (I := I) α b
            (christoffelCorrection (I := I) g α b
              (trivToE (I := I) α b
                (chartBasisVecFiber (I := I) α m b)) v) =
      trivFromE (I := I) α b
        (∑ m : Fin (Module.finrank ℝ E),
          (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
            christoffelCorrection (I := I) g α b
              (trivToE (I := I) α b
                (chartBasisVecFiber (I := I) α m b)) v) by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [map_smul]]
  congr 1
  have hsection := section_eq_sum_chartFrame (I := I) (M := M) α hb B
  have htriv : trivToE (I := I) α b (B b) =
      ∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
          trivToE (I := I) α b (chartBasisVecFiber (I := I) α m b) := by
    have := congrArg (trivToE (I := I) α b) hsection
    rw [map_sum] at this
    refine this.trans ?_
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [map_smul]
  nth_rewrite 1 [htriv]
  exact christoffelCorrection_sum (I := I) g α b
    (fun m => ((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m)
    (fun m => trivToE (I := I) α b (chartBasisVecFiber (I := I) α m b)) v

/-! ## Propagation through the slot correction -/

/-- The slot-substitution CLM combined with the tangent-slot CLM and the
chart Levi-Civita parallel CLM decomposes as a finite sum in `B`'s chart
components. This is the common core of both the input and output slot
correction decompositions. -/
lemma slotSubst_tangentSlot_parallel_sum_decomposition
    (g : SmoothRiemannianMetric I M) (α : M) (n : ℕ) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (B : Π b' : M, TangentSpace I b') (k : Fin n) :
    tensorSlotSubstCLM (I := I) n b
        (tangentSlotCLM (I := I) n k
          (chartLeviCivitaParallelCLM (I := I) g α b B)) =
      ∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
          tensorSlotSubstCLM (I := I) n b
            (tangentSlotCLM (I := I) n k
              (chartLeviCivitaParallelCLM (I := I) g α b
                (chartBasisVecFiber (I := I) α m))) := by
  classical
  refine ContinuousLinearMap.ext (fun τ => ?_)
  refine tensor0SSpace_ext n b (fun v => ?_)
  rw [tensorSlotSubstCLM_eval]
  rw [ContinuousLinearMap.sum_apply, ContinuousMultilinearMap.sum_apply]
  have hRHS : ∀ m : Fin (Module.finrank ℝ E),
      (((((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
          tensorSlotSubstCLM (I := I) n b
            (tangentSlotCLM (I := I) n k
              (chartLeviCivitaParallelCLM (I := I) g α b
                (chartBasisVecFiber (I := I) α m)))) τ) v =
        (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) *
          τ (fun i : Fin n => tangentSlotCLM (I := I) n k
            (chartLeviCivitaParallelCLM (I := I) g α b
              (chartBasisVecFiber (I := I) α m)) i (v i)) := by
    intro m
    rw [ContinuousLinearMap.smul_apply,
      ContinuousMultilinearMap.smul_apply, tensorSlotSubstCLM_eval, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun m _ => hRHS m)]
  have hΦB_decomp : chartLeviCivitaParallelCLM (I := I) g α b B =
      ∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
          chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α m) :=
    chartLeviCivitaParallelCLM_sum_decomposition (I := I) (M := M) g α hb B
  have hLHStuple : (fun i : Fin n => tangentSlotCLM (I := I) n k
        (chartLeviCivitaParallelCLM (I := I) g α b B) i (v i)) =
      Function.update (fun i : Fin n => v i) k
        (chartLeviCivitaParallelCLM (I := I) g α b B (v k)) := by
    funext i
    by_cases hi : i = k
    · subst hi
      rw [tangentSlotCLM_self, Function.update_self]
    · rw [tangentSlotCLM_other (I := I) n k _ hi, Function.update_of_ne hi]
      rfl
  have hRHStuple : ∀ m : Fin (Module.finrank ℝ E),
      (fun i : Fin n => tangentSlotCLM (I := I) n k
          (chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α m)) i (v i)) =
        Function.update (fun i : Fin n => v i) k
          (chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α m) (v k)) := by
    intro m
    funext i
    by_cases hi : i = k
    · subst hi
      rw [tangentSlotCLM_self, Function.update_self]
    · rw [tangentSlotCLM_other (I := I) n k _ hi, Function.update_of_ne hi]
      rfl
  rw [hLHStuple]
  rw [show (∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) *
          τ (fun i : Fin n => tangentSlotCLM (I := I) n k
            (chartLeviCivitaParallelCLM (I := I) g α b
              (chartBasisVecFiber (I := I) α m)) i (v i))) =
      ∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) *
          τ (Function.update (fun i : Fin n => v i) k
            (chartLeviCivitaParallelCLM (I := I) g α b
              (chartBasisVecFiber (I := I) α m) (v k))) by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [hRHStuple m]]
  have hΦBvk : chartLeviCivitaParallelCLM (I := I) g α b B (v k) =
      ∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
          chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α m) (v k) := by
    have h := congrArg (fun (φ : TangentSpace I b →L[ℝ] TangentSpace I b)
        => φ (v k)) hΦB_decomp
    simp only at h
    rw [h, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [ContinuousLinearMap.smul_apply]
  rw [hΦBvk]
  have htoML := τ.toMultilinearMap.map_update_sum
      (t := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
      (i := k)
      (g := fun m : Fin (Module.finrank ℝ E) =>
        (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
          chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α m) (v k))
      (m := fun i : Fin n => v i)
  have hτap1 : τ.toMultilinearMap (Function.update (fun i : Fin n => v i) k
          (∑ m ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
            (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
              chartLeviCivitaParallelCLM (I := I) g α b
                (chartBasisVecFiber (I := I) α m) (v k))) =
      τ (Function.update (fun i : Fin n => v i) k
          (∑ m ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
            (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
              chartLeviCivitaParallelCLM (I := I) g α b
                (chartBasisVecFiber (I := I) α m) (v k))) := rfl
  rw [hτap1] at htoML
  rw [htoML]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hτap2 : τ.toMultilinearMap (Function.update (fun i : Fin n => v i) k
        ((((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
          chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α m) (v k))) =
      τ (Function.update (fun i : Fin n => v i) k
        ((((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
          chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α m) (v k))) := rfl
  rw [hτap2]
  rw [τ.map_update_smul, smul_eq_mul]

/-- The chart-component projection of the trivialisation-image of the
input-slot Christoffel correction along a general field `B`, expressed as a
finite linear combination in `B`'s chart components, of chart-component
projections of slot corrections along chart coordinate basis vector fields. -/
lemma chartTensorRSInputSlotCorrection_chartComp_decomposition
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b : M, TensorRSSpace r s I b)
    (B : Π b : M, TangentSpace I b) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (k : Fin r)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) r s g α T B b k)) =
      ∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) *
          tensorChartComponentProjection (E := E) r s Idx Jdx
            ((trivializationAt (TensorRSModel r s ℝ E)
                (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b
              (chartTensorRSInputSlotCorrection (I := I) r s g α T
                (chartBasisVecFiber (I := I) α m) b k)) := by
  classical
  have hΨB := slotSubst_tangentSlot_parallel_sum_decomposition
    (I := I) (M := M) g α r hb B k
  -- With `hΨB` proved, the slot correction itself decomposes via composition
  -- on the right.
  have hslot : chartTensorRSInputSlotCorrection (I := I) r s g α T B b k =
      ∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
          chartTensorRSInputSlotCorrection (I := I) r s g α T
            (chartBasisVecFiber (I := I) α m) b k := by
    unfold chartTensorRSInputSlotCorrection
    rw [hΨB]
    rw [show (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b).comp
        (∑ m : Fin (Module.finrank ℝ E),
          (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
            tensorSlotSubstCLM (I := I) r b
              (tangentSlotCLM (I := I) r k
                (chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α m)))) =
        ∑ m : Fin (Module.finrank ℝ E),
          (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
            (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b).comp
              (tensorSlotSubstCLM (I := I) r b
                (tangentSlotCLM (I := I) r k
                  (chartLeviCivitaParallelCLM (I := I) g α b
                    (chartBasisVecFiber (I := I) α m)))) by
      rw [ContinuousLinearMap.comp_finset_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [ContinuousLinearMap.comp_smul]]
  rw [hslot]
  rw [show ((trivializationAt (TensorRSModel r s ℝ E)
        (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b
        (∑ m : Fin (Module.finrank ℝ E),
          (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
            chartTensorRSInputSlotCorrection (I := I) r s g α T
              (chartBasisVecFiber (I := I) α m) b k)) =
      ∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
          (trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b
            (chartTensorRSInputSlotCorrection (I := I) r s g α T
              (chartBasisVecFiber (I := I) α m) b k) by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [map_smul]]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [map_smul, smul_eq_mul]

/-- Symmetric statement for the output-slot Christoffel correction. -/
lemma chartTensorRSOutputSlotCorrection_chartComp_decomposition
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b : M, TensorRSSpace r s I b)
    (B : Π b : M, TangentSpace I b) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (l : Fin s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l)) =
      ∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) *
          tensorChartComponentProjection (E := E) r s Idx Jdx
            ((trivializationAt (TensorRSModel r s ℝ E)
                (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b
              (chartTensorRSOutputSlotCorrection (I := I) r s g α T
                (chartBasisVecFiber (I := I) α m) b l)) := by
  classical
  -- Apply the common slot-CLM decomposition helper.
  have hΨB := slotSubst_tangentSlot_parallel_sum_decomposition
    (I := I) (M := M) g α s hb B l
  -- The slot correction itself is `Ψ.comp (T b)`, so the sum factors out
  -- on the *left*.
  have hslot : chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l =
      ∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
          chartTensorRSOutputSlotCorrection (I := I) r s g α T
            (chartBasisVecFiber (I := I) α m) b l := by
    unfold chartTensorRSOutputSlotCorrection
    rw [hΨB]
    rw [show (∑ m : Fin (Module.finrank ℝ E),
          (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
            tensorSlotSubstCLM (I := I) s b
              (tangentSlotCLM (I := I) s l
                (chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α m)))).comp
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) =
        ∑ m : Fin (Module.finrank ℝ E),
          (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
            (tensorSlotSubstCLM (I := I) s b
              (tangentSlotCLM (I := I) s l
                (chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α m)))).comp
              (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) by
      rw [ContinuousLinearMap.finset_sum_comp]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [ContinuousLinearMap.smul_comp]]
  rw [hslot]
  rw [show ((trivializationAt (TensorRSModel r s ℝ E)
        (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b
        (∑ m : Fin (Module.finrank ℝ E),
          (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
            chartTensorRSOutputSlotCorrection (I := I) r s g α T
              (chartBasisVecFiber (I := I) α m) b l)) =
      ∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr (trivToE (I := I) α b (B b))) m) •
          (trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b
            (chartTensorRSOutputSlotCorrection (I := I) r s g α T
              (chartBasisVecFiber (I := I) α m) b l) by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [map_smul]]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [map_smul, smul_eq_mul]

/-! ## The final chart-component formula

Substituting the established formula
`chartTensorRSInputSlotCorrection_component_eq` (resp.
`chartTensorRSOutputSlotCorrection_component_eq`) into the decomposition
above yields the chart-component formula in the form of a smooth polynomial
in chart Christoffel data, the chart components of `B`, and the raw chart
components of `S`. -/

/-- **Chart-component formula for the input-slot Christoffel correction with
a general vector field.** Let `y` lie in the Euclidean chart target,
`b := (extChartAt I α).symm (toEuclidean.symm y)`, and let `S` be a smooth
compactly-supported `(r, s)`-tensor. The `continuousLinearMapAt`-wrapped
chart-component projection of the input-slot Christoffel correction of
`S.toSection` along an arbitrary section `B`, at the `(Idx, Jdx)` chart
component, equals the finite sum

```
∑ m, B_m(b) · ∑ Idx', inputSlotCoeff g r α m k Idx Idx' y ·
        tensorChartComponentRaw g r s S α Idx' Jdx b
```

where `B_m(b) = ((chartModelBasis E).repr (trivToE α b (B b))) m` is the
`m`-th chart component of `B` at `b`. Every coefficient is `C^∞` on the
chart Euclidean target (`inputSlotCoeff_contDiffOn`); no derivative of `S`
appears. -/
theorem chartTensorRSInputSlotCorrection_chartComp_formula
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (B : Π b : M, TangentSpace I b) (k : Fin r)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartTensorRSInputSlotCorrection (I := I) r s g α S.toSection B
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) k)) =
      ∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr (trivToE (I := I) α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
              (B ((extChartAt I α).symm
                ((toEuclidean (E := E)).symm y))))) m) *
          (∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
            inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y *
              tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb_chart
  -- Apply the decomposition lemma.
  rw [chartTensorRSInputSlotCorrection_chartComp_decomposition
    (I := I) (M := M) g r s α S.toSection B hb_base k Idx Jdx]
  -- Apply the established formula to each summand.
  refine Finset.sum_congr rfl (fun m _ => ?_)
  congr 1
  exact chartTensorRSInputSlotCorrection_component_eq
    (I := I) (M := M) g r s S α m k Idx Jdx hy

/-- **Chart-component formula for the output-slot Christoffel correction with
a general vector field.** Symmetric statement to the input case. -/
theorem chartTensorRSOutputSlotCorrection_chartComp_formula
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (B : Π b : M, TangentSpace I b) (l : Fin s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartTensorRSOutputSlotCorrection (I := I) r s g α S.toSection B
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) l)) =
      ∑ m : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).repr (trivToE (I := I) α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
              (B ((extChartAt I α).symm
                ((toEuclidean (E := E)).symm y))))) m) *
          (∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
            outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y *
              tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx'
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb_chart
  rw [chartTensorRSOutputSlotCorrection_chartComp_decomposition
    (I := I) (M := M) g r s α S.toSection B hb_base l Idx Jdx]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  congr 1
  exact chartTensorRSOutputSlotCorrection_component_eq
    (I := I) (M := M) g r s S α m l Idx Jdx hy

end Connection
end Integral
end DifferentialGeometry

end
