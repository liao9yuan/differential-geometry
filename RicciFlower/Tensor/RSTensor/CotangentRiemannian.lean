import RicciFlower.Tensor.RSTensor.TangentRiemannian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Riemannian Metrics on Cotangent Fibers

The Riemannian metric on `T_x M` induces the dual metric on `T_x^* M` by
raising covectors with the tangent sharp map.
-/

namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Interpret a realized cotangent vector as a continuous linear functional. -/
def cotangentToCLM {x : M} (α : Tensor0SSpace 1 I x) :
    TangentSpace I x →L[Real] Real :=
  continuousMultilinearCurryFin1 Real (TangentSpace I x) Real
    (Tensor0SSpace.toModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) α)

/-- Interpret a realized cotangent vector as an algebraic dual vector. -/
def cotangentToDual {x : M} (α : Tensor0SSpace 1 I x) :
    Module.Dual Real (TangentSpace I x) :=
  (cotangentToCLM (I := I) α).toLinearMap

@[simp] theorem cotangentToDual_apply {x : M}
    (α : Tensor0SSpace 1 I x) (X : TangentSpace I x) :
    cotangentToDual (I := I) α X = α (fun _ : Fin 1 => X) := by
  simpa [cotangentToDual, cotangentToCLM, Tensor0SSpace.toModel,
    tensor0SSpace_continuousLinearEquiv] using
    congrArg (fun v : Fin 1 -> TangentSpace I x => α v)
    (funext fun i => by fin_cases i; rfl)

/-- Raise a realized cotangent vector using the Riemannian metric. -/
def cotangentSharp (g : SmoothMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) : TangentSpace I x :=
  (tangentMetricData (I := I) g x).metric.sharp (cotangentToDual (I := I) α)

/-- The dual metric on cotangent vectors:
`<α, β> = g(α#, β#)`. -/
def cotangentInner (g : SmoothMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) : Real :=
  g.inner x (cotangentSharp (I := I) g x α) (cotangentSharp (I := I) g x β)

@[simp] theorem cotangentInner_eq_sharp
    (g : SmoothMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cotangentInner (I := I) g x α β =
      g.inner x (cotangentSharp (I := I) g x α)
        (cotangentSharp (I := I) g x β) := by
  rfl

/-- Metric data on `T_x^*M` induced by the tangent Riemannian metric.

Expected proof: use `cotangentInner`, build its flat map, prove injectivity by
the tangent sharp equivalence, then package symmetry and positivity from `g`. -/
def cotangentMetricData (g : SmoothMetric I M) (x : M) :
    MetricFiberData (Tensor0SSpace 1 I x) := by
  sorry

/-- The packaged cotangent metric computes the sharp-definition inner product. -/
theorem cotangentMetricData_inner
    (g : SmoothMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    (cotangentMetricData (I := I) g x).inner α β =
      cotangentInner (I := I) g x α β := by
  sorry

/-- A frame inverse-metric predicate at one point. -/
def MetricInverseInFrame {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (frame : Idx -> TangentSpace I x)
    (gInv : Idx -> Idx -> Real) : Prop :=
  forall i j : Idx,
    (∑ k : Idx, gInv i k * g.inner x (frame k) (frame j)) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx, g.inner x (frame i) (frame k) * gInv k j) =
        (if i = j then 1 else 0)

/-- Coordinate formula for the cotangent metric in a frame. -/
theorem cotangentInner_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (frame : Idx -> TangentSpace I x)
    (gInv : Idx -> Idx -> Real)
    (_hinv : MetricInverseInFrame (I := I) g x frame gInv)
    (α β : Tensor0SSpace 1 I x) :
    cotangentInner (I := I) g x α β =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * cotangentToDual (I := I) α (frame i) *
          cotangentToDual (I := I) β (frame j) := by
  sorry

/-- Coordinate formula for the packaged cotangent metric. -/
theorem cotangentMetricData_inner_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (frame : Idx -> TangentSpace I x)
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInFrame (I := I) g x frame gInv)
    (α β : Tensor0SSpace 1 I x) :
    (cotangentMetricData (I := I) g x).inner α β =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * cotangentToDual (I := I) α (frame i) *
          cotangentToDual (I := I) β (frame j) := by
  rw [cotangentMetricData_inner, cotangentInner_eq_coord (I := I) g x frame gInv hinv]

end

end Tensor0SBundle
