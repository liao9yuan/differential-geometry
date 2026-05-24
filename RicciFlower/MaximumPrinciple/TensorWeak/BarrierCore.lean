import RicciFlower.MaximumPrinciple.TensorWeak.Basic


set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace RicciFlower
namespace Realized

noncomputable section

open Bundle Tensor0SBundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]


/-!
# TensorWeak Barrier Core

Split-out component of `MaximumPrinciple.TensorWeak`.
-/

structure TensorSpatialDerivs
    (cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (S : TwoTensorSecFamily (I := I) (M := M))
    (nablaS : TensorNabla1SecFamily (I := I) (M := M))
    (nabla2S : TensorNabla2SecFamily (I := I) (M := M)) : Prop where
  first :
    ∀ t : Real,
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (cov t) (S t) (nablaS t)
  second :
    ∀ t : Real,
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 (cov t) (nablaS t) (nabla2S t)

/-- The section-backed barrier has the same spatial covariant derivative data
as `S`, because the metric addend has zero covariant derivative for a
metric-compatible connection. -/
theorem barrierDerivs
    [T2Space M]
    (cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (nablaS : TensorNabla1SecFamily (I := I) (M := M))
    (nabla2S : TensorNabla2SecFamily (I := I) (M := M))
    (epsilon delta t0 : Real)
    (hmc : ∀ t : Real,
      RicciFlower.Connection.IsMetricCompatible (I := I) (cov t) (G t))
    (hS : TensorSpatialDerivs (I := I) (M := M) cov S nablaS nabla2S) :
    TensorSpatialDerivs (I := I) (M := M) cov
      (tensorBarrierSecFamily (I := I) (M := M) G S epsilon delta t0)
      nablaS nabla2S := by
  constructor
  · intro t
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3
    have hmetric :
        TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 (cov t) (Tensor0SBundle.metricTensorField (I := I) (G t))
          (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (n := (∞ : WithTop ℕ∞)) 3) :=
      Tensor0SBundle.zero_realizes_metric (I := I) (cov t) (G t) (hmc t)
    have hscaled :
        TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 (cov t)
          ((epsilon * (delta + t - t0)) •
            Tensor0SBundle.metricTensorField (I := I) (G t))
          ((epsilon * (delta + t - t0)) •
            (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              (n := (∞ : WithTop ℕ∞)) 3)) :=
      TotalNabla0SRealizes.smul (I := I) (M := M)
        (epsilon * (delta + t - t0)) hmetric
    have hadd := TotalNabla0SRealizes.add (I := I) (M := M)
      (hS.first t) hscaled
    simpa [tensorBarrierSecFamily] using hadd
  · intro t
    exact hS.second t

/-- Barrier sizes used in the final tensor-WMP epsilon limit. -/
def SmallBarrierEps (epsilon : Real) : Prop :=
  0 < epsilon ∧ epsilon ≤ 1

/--
Hamilton's null-eigenvector condition for the reaction term.

At each point, whenever any symmetric two-tensor input is nonnegative and has a
null vector, the reaction term is nonnegative on that null vector.  This
reaction-wide shape is needed because Hamilton's barrier argument applies the
condition to `S_epsilon`, not only to the original tensor family.
-/
def TensorNullEigenvectorCondition
    (G : Real -> SmoothRiemannianMetric I M)
    (N : TwoTensorReaction (I := I) (M := M))
    (U : Set Real) : Prop :=
  ∀ t, t ∈ U -> ∀ A : RawTwoTensorField (I := I) (M := M), ∀ x,
    TwoTensorNonnegativeAt (I := I) (M := M) A x ->
    ∀ v : TangentSpace I x,
      A x v v = 0 ->
      0 ≤ N t (G t) A x v v

/--
Analytic regularity predicate for the tensor WMP barrier argument.

This records the concrete scalar-evaluation regularity and uniform small-barrier
reaction Lipschitz control needed by the barrier estimate.  The compact
first-null extraction and tensor heat-operator realization remain separate
frontiers.
-/
structure TensorBarrierRegularityOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (T : Real) : Prop where
  tensor_eval_continuous :
    ∀ x, ∀ v w : TangentSpace I x,
      ContinuousOn (fun t : Real => S t x v w) (Set.Icc 0 T)
  metric_eval_continuous :
    ∀ x, ∀ v w : TangentSpace I x,
      ContinuousOn (fun t : Real => (G t).inner x v w) (Set.Icc 0 T)
  barrier_eval_continuous :
    ∀ epsilon delta t0 : Real,
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      ∀ x, ∀ v w : TangentSpace I x,
        ContinuousOn
          (fun t : Real =>
            tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t x v w)
          (Set.Icc t0 (t0 + delta))
  metricGainControl :
    ∀ t0 : Real,
      t0 ∈ Set.Icc 0 T ->
      t0 < T ->
      ∃ delta0 : Real,
        0 < delta0 ∧ t0 + delta0 ≤ T ∧
          ∀ delta : Real,
            0 < delta ->
            delta ≤ delta0 ->
            ∀ epsilon : Real,
              SmallBarrierEps epsilon ->
              ∃ metricDeriv : TensorQuadraticFormFamily (I := I) (M := M),
                (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                  ∀ x, ∀ v : TangentSpace I x,
                    HasDerivWithinAt (fun s : Real => (G s).inner x v v)
                      (metricDeriv t x v) (Set.Icc t0 (t0 + delta)) t) ∧
                (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                  ∀ x, ∀ v : TangentSpace I x,
                    (epsilon / 2) * (G t).inner x v v ≤
                      epsilon * ((G t).inner x v v +
                        (delta + t - t0) * metricDeriv t x v))
  smallBarrierLip :
    ∀ delta0 t0 : Real,
      0 < delta0 ->
      Set.Icc t0 (t0 + delta0) ⊆ Set.Icc 0 T ->
      ∃ K : Real, 0 ≤ K ∧
        ∀ epsilon delta : Real,
          SmallBarrierEps epsilon ->
          0 < delta ->
          delta ≤ delta0 ->
          ∀ t, t ∈ Set.Icc t0 (t0 + delta) ->
            ∀ x, ∀ v : TangentSpace I x,
              |N t (G t) (S t) x v v -
                N t (G t)
                  (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t)
                  x v v| ≤
              K * |epsilon * (delta + t - t0) * (G t).inner x v v|

/--
Analytic predicate for the evaluated drifted parabolic supersolution
inequality.

The heat-with-drift term is evaluated by the direct tensor operator
`tensorHeatWithDrift2QuadMetricAt` from supplied first and second covariant
derivative tensors.
-/
def TensorParabolicInequalityWithDriftOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (nabla2S : TensorNabla2Family (I := I) (M := M))
    (nablaS : TensorNabla1Family (I := I) (M := M))
    (T : Real) : Prop :=
  ∃ timeDeriv : TensorQuadraticFormFamily (I := I) (M := M),
    (∀ t, t ∈ Set.Ioc 0 T ->
      ∀ x, ∀ v : TangentSpace I x,
        HasDerivWithinAt
          (fun s : Real => S s x v v)
          (timeDeriv t x v)
          (Set.Icc 0 T) t) ∧
    (∀ t, t ∈ Set.Ioc 0 T ->
      ∀ x, ∀ v : TangentSpace I x,
        tensorHeatWithDrift2QuadMetricAt (I := I) (G t) (X t)
            (nabla2S t x) (nablaS t x) v +
          N t (G t) (S t) x v v ≤ timeDeriv t x v)

/-- Strict evaluated drifted parabolic inequality for the positive barrier on a time set. -/
def TensorParabolicStrictInequalityWithDriftOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (nabla2S : TensorNabla2Family (I := I) (M := M))
    (nablaS : TensorNabla1Family (I := I) (M := M))
    (U : Set Real) : Prop :=
  ∃ timeDeriv : TensorQuadraticFormFamily (I := I) (M := M),
    (∀ t, t ∈ U ->
      ∀ x, ∀ v : TangentSpace I x,
        HasDerivWithinAt
          (fun s : Real => S s x v v)
          (timeDeriv t x v)
          U t) ∧
    (∀ t, t ∈ U ->
      ∀ x, ∀ v : TangentSpace I x,
        v ≠ 0 ->
        tensorHeatWithDrift2QuadMetricAt (I := I) (G t) (X t)
            (nabla2S t x) (nablaS t x) v +
          N t (G t) (S t) x v v < timeDeriv t x v)

/--
Local comparison estimates that turn the base parabolic inequality for `S`
into the strict parabolic inequality for the positive barrier.

The analytic work is concentrated in producing these estimates.  The order
argument consuming them is `strictBarrier_of_est` below.
-/
def TensorBarrierLocalEst
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (nabla2S : TensorNabla2Family (I := I) (M := M))
    (nablaS : TensorNabla1Family (I := I) (M := M))
    (nabla2Barrier : TensorNabla2Family (I := I) (M := M))
    (nablaBarrier : TensorNabla1Family (I := I) (M := M))
    (epsilon delta t0 : Real)
    (U : Set Real)
    (timeDerivS timeDerivBarrier :
      TensorQuadraticFormFamily (I := I) (M := M)) : Prop :=
  (∀ t, t ∈ U ->
    ∀ x, ∀ v : TangentSpace I x,
      HasDerivWithinAt
        (fun s : Real =>
          tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 s x v v)
        (timeDerivBarrier t x v) U t) ∧
  (∀ t, t ∈ U ->
    ∀ x, ∀ v : TangentSpace I x,
      ∃ heatErr reactionErr metricGain : Real,
        timeDerivS t x v + metricGain ≤ timeDerivBarrier t x v ∧
        tensorHeatWithDrift2QuadMetricAt (I := I) (G t) (X t)
            (nabla2Barrier t x) (nablaBarrier t x) v ≤
          tensorHeatWithDrift2QuadMetricAt (I := I) (G t) (X t)
              (nabla2S t x) (nablaS t x) v + heatErr ∧
        N t (G t)
            (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t)
            x v v ≤
        N t (G t) (S t) x v v + reactionErr ∧
        (v ≠ 0 -> heatErr + reactionErr < metricGain))

/-- Reduced local estimate when the barrier spatial derivative tensors are the
same supplied tensors as for `S`.  The remaining analytic inputs are the
barrier time derivative, the positive metric gain, and the reaction error. -/
def BarrierLocalCore
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (epsilon delta t0 : Real)
    (U : Set Real)
    (timeDerivS timeDerivBarrier :
      TensorQuadraticFormFamily (I := I) (M := M)) : Prop :=
  (∀ t, t ∈ U ->
    ∀ x, ∀ v : TangentSpace I x,
      HasDerivWithinAt
        (fun s : Real =>
          tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 s x v v)
        (timeDerivBarrier t x v) U t) ∧
  (∀ t, t ∈ U ->
    ∀ x, ∀ v : TangentSpace I x,
      ∃ reactionErr metricGain : Real,
        timeDerivS t x v + metricGain ≤ timeDerivBarrier t x v ∧
        N t (G t)
            (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t)
            x v v ≤
        N t (G t) (S t) x v v + reactionErr ∧
        (v ≠ 0 -> reactionErr < metricGain))

/-- Product rule for the pointwise time derivative of the barrier quadratic
form.  The derivative of the metric quadratic form is still supplied by the
caller; this lemma only packages the affine barrier coefficient calculation. -/
theorem hasDerivWithinAt_barrier_quad
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {epsilon delta t0 t dS dg : Real} {U : Set Real}
    {x : M} {v : TangentSpace I x}
    (hS : HasDerivWithinAt (fun s : Real => S s x v v) dS U t)
    (hG : HasDerivWithinAt (fun s : Real => (G s).inner x v v) dg U t) :
    HasDerivWithinAt
      (fun s : Real =>
        tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 s x v v)
      (dS + epsilon * ((G t).inner x v v + (delta + t - t0) * dg))
      U t := by
  have hid : HasDerivWithinAt (fun s : Real => s) 1 U t := by
    simpa using (hasDerivWithinAt_id t U)
  have hlin : HasDerivWithinAt (fun s : Real => delta + s - t0) 1 U t := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      ((hid.const_add delta).sub_const t0)
  have hprod :
      HasDerivWithinAt
        (fun s : Real => (delta + s - t0) * (G s).inner x v v)
        ((G t).inner x v v + (delta + t - t0) * dg)
        U t := by
    have h := hlin.mul hG
    simpa [one_mul, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using h
  have hmetric :
      HasDerivWithinAt
        (fun s : Real => epsilon * ((delta + s - t0) * (G s).inner x v v))
        (epsilon * ((G t).inner x v v + (delta + t - t0) * dg))
        U t := by
    exact hprod.const_mul epsilon
  have htotal := hS.add hmetric
  simpa [tensorBarrierFamily, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc] using htotal

/-- Build the reduced barrier core from the time derivatives of `S(t)(v,v)`
and `g(t)(v,v)`.  The remaining hypotheses are exactly the local gain,
reaction-error, and positive-margin estimates. -/
theorem barrierCore_deriv
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {epsilon delta t0 : Real} {U : Set Real}
    {timeDerivS metricDeriv reactionErr metricGain :
      TensorQuadraticFormFamily (I := I) (M := M)}
    (hS :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt (fun s : Real => S s x v v)
            (timeDerivS t x v) U t)
    (hG :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt (fun s : Real => (G s).inner x v v)
            (metricDeriv t x v) U t)
    (hGain :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          metricGain t x v ≤
            epsilon * ((G t).inner x v v +
              (delta + t - t0) * metricDeriv t x v))
    (hReaction :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          N t (G t)
              (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t)
              x v v ≤
            N t (G t) (S t) x v v + reactionErr t x v)
    (hMargin :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          v ≠ 0 -> reactionErr t x v < metricGain t x v) :
    BarrierLocalCore (I := I) (M := M) G S N epsilon delta t0 U
      timeDerivS
      (fun t x v =>
        timeDerivS t x v +
          epsilon * ((G t).inner x v v +
            (delta + t - t0) * metricDeriv t x v)) := by
  constructor
  · intro t ht x v
    exact hasDerivWithinAt_barrier_quad
      (I := I) (M := M) (hS t ht x v) (hG t ht x v)
  · intro t ht x v
    refine ⟨reactionErr t x v, metricGain t x v, ?_, hReaction t ht x v,
      hMargin t ht x v⟩
    have h := hGain t ht x v
    linarith

/-- Direct constructor for the reduced local barrier estimate from pointwise
time-derivative, reaction-error, and margin inequalities. -/
theorem barrierCore_of_pt
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {epsilon delta t0 : Real} {U : Set Real}
    {timeDerivS timeDerivBarrier :
      TensorQuadraticFormFamily (I := I) (M := M)}
    (reactionErr metricGain : TensorQuadraticFormFamily (I := I) (M := M))
    (hDerivB :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt
            (fun s : Real =>
              tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 s x v v)
            (timeDerivBarrier t x v) U t)
    (hTime :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          timeDerivS t x v + metricGain t x v ≤ timeDerivBarrier t x v)
    (hReaction :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          N t (G t)
              (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t)
              x v v ≤
            N t (G t) (S t) x v v + reactionErr t x v)
    (hMargin :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          v ≠ 0 -> reactionErr t x v < metricGain t x v) :
    BarrierLocalCore (I := I) (M := M) G S N epsilon delta t0 U
      timeDerivS timeDerivBarrier := by
  constructor
  · exact hDerivB
  · intro t ht x v
    exact ⟨reactionErr t x v, metricGain t x v,
      hTime t ht x v, hReaction t ht x v, hMargin t ht x v⟩

/-- If the metric barrier contributes no spatial heat-with-drift error, the
reduced time/reaction estimates produce the full local estimate expected by the
strict-barrier theorem. -/
theorem localEst_of_core
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real} {U : Set Real}
    {timeDerivS timeDerivBarrier :
      TensorQuadraticFormFamily (I := I) (M := M)}
    (hcore : BarrierLocalCore (I := I) (M := M) G S N epsilon delta t0 U
      timeDerivS timeDerivBarrier) :
    TensorBarrierLocalEst (I := I) (M := M) G S X N
      nabla2S nablaS nabla2S nablaS epsilon delta t0 U
      timeDerivS timeDerivBarrier := by
  constructor
  · exact hcore.1
  · intro t ht x v
    rcases hcore.2 t ht x v with
      ⟨reactionErr, metricGain, htime, hreaction, hmargin⟩
    refine ⟨0, reactionErr, metricGain, htime, ?_, hreaction, ?_⟩
    · linarith
    · intro hv
      have h := hmargin hv
      linarith

/-- Full local barrier estimate from pointwise time derivatives of `S` and
the metric quadratic form, when the metric barrier has already been eliminated
from the spatial heat term. -/
theorem localEst_deriv
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real} {U : Set Real}
    {timeDerivS metricDeriv reactionErr metricGain :
      TensorQuadraticFormFamily (I := I) (M := M)}
    (hS :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt (fun s : Real => S s x v v)
            (timeDerivS t x v) U t)
    (hG :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt (fun s : Real => (G s).inner x v v)
            (metricDeriv t x v) U t)
    (hGain :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          metricGain t x v ≤
            epsilon * ((G t).inner x v v +
              (delta + t - t0) * metricDeriv t x v))
    (hReaction :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          N t (G t)
              (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t)
              x v v ≤
            N t (G t) (S t) x v v + reactionErr t x v)
    (hMargin :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          v ≠ 0 -> reactionErr t x v < metricGain t x v) :
    TensorBarrierLocalEst (I := I) (M := M) G S X N
      nabla2S nablaS nabla2S nablaS epsilon delta t0 U
      timeDerivS
      (fun t x v =>
        timeDerivS t x v +
          epsilon * ((G t).inner x v v +
            (delta + t - t0) * metricDeriv t x v)) :=
  localEst_of_core (I := I) (M := M)
    (barrierCore_deriv (I := I) (M := M)
      hS hG hGain hReaction hMargin)

theorem strictBarrier_of_derivEst
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 T : Real}
    (hsub : Set.Ioc t0 (t0 + delta) ⊆ Set.Ioc 0 T)
    (hbase : TensorParabolicInequalityWithDriftOn (I := I) (M := M)
      G S X N nabla2S nablaS T)
    (metricDeriv reactionErr metricGain :
      TensorQuadraticFormFamily (I := I) (M := M))
    (hG :
      ∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt (fun s : Real => (G s).inner x v v)
            (metricDeriv t x v) (Set.Icc t0 (t0 + delta)) t)
    (hGain :
      ∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
        ∀ x, ∀ v : TangentSpace I x,
          metricGain t x v ≤
            epsilon * ((G t).inner x v v +
              (delta + t - t0) * metricDeriv t x v))
    (hReaction :
      ∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
        ∀ x, ∀ v : TangentSpace I x,
          N t (G t)
              (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t)
              x v v ≤
            N t (G t) (S t) x v v + reactionErr t x v)
    (hMargin :
      ∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
        ∀ x, ∀ v : TangentSpace I x,
          v ≠ 0 -> reactionErr t x v < metricGain t x v) :
    TensorParabolicStrictInequalityWithDriftOn (I := I) (M := M) G
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0) X N
      nabla2S nablaS (Set.Ioc t0 (t0 + delta)) := by
  rcases hbase with ⟨timeDerivS, hSbase, hbase_ineq⟩
  let timeDerivBarrier : TensorQuadraticFormFamily (I := I) (M := M) :=
    fun t x v =>
      timeDerivS t x v +
        epsilon * ((G t).inner x v v +
          (delta + t - t0) * metricDeriv t x v)
  have hSlocal :
      ∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt (fun s : Real => S s x v v)
            (timeDerivS t x v) (Set.Ioc t0 (t0 + delta)) t := by
    intro t ht x v
    have hsub_closed : Set.Ioc t0 (t0 + delta) ⊆ Set.Icc 0 T := by
      intro s hs
      exact ⟨le_of_lt (hsub hs).1, (hsub hs).2⟩
    exact (hSbase t (hsub ht) x v).mono hsub_closed
  have hGlocal :
      ∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt (fun s : Real => (G s).inner x v v)
            (metricDeriv t x v) (Set.Ioc t0 (t0 + delta)) t := by
    intro t ht x v
    exact (hG t ht x v).mono (by
      intro s hs
      exact ⟨le_of_lt hs.1, hs.2⟩)
  have hest :
      TensorBarrierLocalEst (I := I) (M := M) G S X N
        nabla2S nablaS nabla2S nablaS epsilon delta t0
        (Set.Ioc t0 (t0 + delta)) timeDerivS timeDerivBarrier :=
    localEst_deriv (I := I) (M := M)
      (G := G) (S := S) (X := X) (N := N)
      (nabla2S := nabla2S) (nablaS := nablaS)
      (epsilon := epsilon) (delta := delta) (t0 := t0)
      (U := Set.Ioc t0 (t0 + delta))
      (timeDerivS := timeDerivS) (metricDeriv := metricDeriv)
      (reactionErr := reactionErr) (metricGain := metricGain)
      hSlocal hGlocal hGain hReaction hMargin
  refine ⟨timeDerivBarrier, hest.1, ?_⟩
  intro t ht x v hv
  rcases hest.2 t ht x v with
    ⟨heatErr, reactionErr', metricGain', htime, hheat, hreaction, hmargin⟩
  have hbase_t := hbase_ineq t (hsub ht) x v
  have hmargin_t := hmargin hv
  linarith

theorem strictParabolic_of_est
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 T : Real} {U : Set Real}
    (hsub : U ⊆ Set.Ioc 0 T)
    (hbase : TensorParabolicInequalityWithDriftOn (I := I) (M := M)
      G S X N nabla2S nablaS T)
    (hest : ∀ timeDerivS : TensorQuadraticFormFamily (I := I) (M := M),
      ∃ timeDerivBarrier : TensorQuadraticFormFamily (I := I) (M := M),
        TensorBarrierLocalEst (I := I) (M := M) G S X N
          nabla2S nablaS nabla2Barrier nablaBarrier epsilon delta t0 U
          timeDerivS timeDerivBarrier) :
    TensorParabolicStrictInequalityWithDriftOn (I := I) (M := M) G
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0) X N
      nabla2Barrier nablaBarrier U := by
  rcases hbase with ⟨timeDerivS, _hbase_deriv, hbase_ineq⟩
  rcases hest timeDerivS with ⟨timeDerivBarrier, hbarrier_deriv, hcompare⟩
  refine ⟨timeDerivBarrier, hbarrier_deriv, ?_⟩
  intro t ht x v hv
  rcases hcompare t ht x v with
    ⟨heatErr, reactionErr, metricGain, htime, hheat, hreaction, hmargin⟩
  have hbase_t := hbase_ineq t (hsub ht) x v
  have hmargin_t := hmargin hv
  linarith

end

end Realized
end RicciFlower
