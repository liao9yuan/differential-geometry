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

/-- The linear identification from realized one-covariant tensors to the
algebraic dual of the tangent space. -/
def cotangentToDualLinear {x : M} :
    Tensor0SSpace 1 I x →ₗ[Real] Module.Dual Real (TangentSpace I x) where
  toFun := cotangentToDual (I := I)
  map_add' α β := by
    ext X
    rfl
  map_smul' c α := by
    ext X
    rfl

@[simp] theorem cotangentToDualLinear_apply {x : M}
    (α : Tensor0SSpace 1 I x) :
    cotangentToDualLinear (I := I) α = cotangentToDual (I := I) α := by
  rfl

theorem cotangentToDualLinear_injective {x : M} :
    Function.Injective (cotangentToDualLinear (I := I) (x := x)) := by
  intro α β h
  ext v
  have hv :
      (fun _ : Fin 1 => v 0) = v := by
    funext i
    fin_cases i
    rfl
  have h0 := congrArg (fun L : Module.Dual Real (TangentSpace I x) => L (v 0)) h
  simpa [cotangentToDualLinear, cotangentToDual_apply, hv] using h0

/-- The linear sharp map `T_x^*M -> T_xM` induced by `g`. -/
def cotangentSharpLinear (g : SmoothMetric I M) (x : M) :
    Tensor0SSpace 1 I x →ₗ[Real] TangentSpace I x :=
  ((tangentMetricData (I := I) g x).metric.sharp).toLinearMap.comp
    (cotangentToDualLinear (I := I) (x := x))

/-- Raise a realized cotangent vector using the Riemannian metric. -/
def cotangentSharp (g : SmoothMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) : TangentSpace I x :=
  cotangentSharpLinear (I := I) g x α

@[simp] theorem cotangentSharpLinear_apply
    (g : SmoothMetric I M) (x : M) (α : Tensor0SSpace 1 I x) :
    cotangentSharpLinear (I := I) g x α = cotangentSharp (I := I) g x α := by
  rfl

theorem cotangentSharpLinear_injective
    (g : SmoothMetric I M) (x : M) :
    Function.Injective (cotangentSharpLinear (I := I) g x) := by
  intro α β h
  apply cotangentToDualLinear_injective (I := I) (x := x)
  exact ((tangentMetricData (I := I) g x).metric.sharp.injective h)

/-- The dual metric on cotangent vectors:
`<α, β> = g(α#, β#)`. -/
def cotangentInner (g : SmoothMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) : Real :=
  g.inner x
    (cotangentSharpLinear (I := I) g x α)
    (cotangentSharpLinear (I := I) g x β)

@[simp] theorem cotangentInner_eq_sharp
    (g : SmoothMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cotangentInner (I := I) g x α β =
      g.inner x (cotangentSharp (I := I) g x α)
        (cotangentSharp (I := I) g x β) := by
  rfl

/-- The flat map on `T_x^*M`, obtained by pulling the tangent metric back along
the sharp map. -/
def cotangentFlatLinear (g : SmoothMetric I M) (x : M) :
    Tensor0SSpace 1 I x →ₗ[Real] Module.Dual Real (Tensor0SSpace 1 I x) where
  toFun α :=
    { toFun := fun β => cotangentInner (I := I) g x α β
      map_add' := by
        intro β γ
        let S := cotangentSharpLinear (I := I) g x
        have hS : S (β + γ) = S β + S γ := map_add S β γ
        change g.inner x (S α) (S (β + γ)) =
          g.inner x (S α) (S β) + g.inner x (S α) (S γ)
        rw [hS]
        simp
      map_smul' := by
        intro c β
        let S := cotangentSharpLinear (I := I) g x
        have hS : S (c • β) = c • S β := map_smul S c β
        change g.inner x (S α) (S (c • β)) = c * g.inner x (S α) (S β)
        rw [hS]
        simp }
  map_add' α β := by
    ext γ
    let S := cotangentSharpLinear (I := I) g x
    have hS : S (α + β) = S α + S β := map_add S α β
    change g.inner x (S (α + β)) (S γ) =
      g.inner x (S α) (S γ) + g.inner x (S β) (S γ)
    rw [hS]
    simp
  map_smul' c α := by
    ext β
    let S := cotangentSharpLinear (I := I) g x
    have hS : S (c • α) = c • S α := map_smul S c α
    change g.inner x (S (c • α)) (S β) = c * g.inner x (S α) (S β)
    rw [hS]
    simp

@[simp] theorem cotangentFlatLinear_apply
    (g : SmoothMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    cotangentFlatLinear (I := I) g x α β =
      cotangentInner (I := I) g x α β := by
  rfl

theorem cotangentFlatLinear_injective
    (g : SmoothMetric I M) (x : M) :
    Function.Injective (cotangentFlatLinear (I := I) g x) := by
  intro α β h
  have hsub : cotangentSharpLinear (I := I) g x (α - β) = 0 := by
    by_contra hsharp
    have hpos :
        0 <
          g.inner x
            (cotangentSharpLinear (I := I) g x (α - β))
            (cotangentSharpLinear (I := I) g x (α - β)) :=
      g.pos x (cotangentSharpLinear (I := I) g x (α - β)) hsharp
    have h_eval :
        cotangentFlatLinear (I := I) g x α (α - β) =
          cotangentFlatLinear (I := I) g x β (α - β) :=
      congrArg
        (fun L : Module.Dual Real (Tensor0SSpace 1 I x) => L (α - β)) h
    have hdiff : cotangentFlatLinear (I := I) g x (α - β) (α - β) = 0 := by
      calc
        cotangentFlatLinear (I := I) g x (α - β) (α - β)
            = (cotangentFlatLinear (I := I) g x α -
                cotangentFlatLinear (I := I) g x β) (α - β) := by
                exact congrArg
                  (fun L : Module.Dual Real (Tensor0SSpace 1 I x) => L (α - β))
                  (map_sub (cotangentFlatLinear (I := I) g x) α β)
        _ = cotangentFlatLinear (I := I) g x α (α - β) -
              cotangentFlatLinear (I := I) g x β (α - β) := rfl
        _ = 0 := sub_eq_zero.mpr h_eval
    have hzero :
        g.inner x
            (cotangentSharpLinear (I := I) g x (α - β))
            (cotangentSharpLinear (I := I) g x (α - β)) = 0 := by
      simpa [cotangentFlatLinear, cotangentInner] using hdiff
    exact (lt_irrefl (0 : Real)) (hzero ▸ hpos)
  apply cotangentSharpLinear_injective (I := I) g x
  have hdiff :
      cotangentSharpLinear (I := I) g x α -
        cotangentSharpLinear (I := I) g x β = 0 := by
    have hmap :
        cotangentSharpLinear (I := I) g x (α - β) =
          cotangentSharpLinear (I := I) g x α -
            cotangentSharpLinear (I := I) g x β :=
      map_sub (cotangentSharpLinear (I := I) g x) α β
    rwa [hmap] at hsub
  exact sub_eq_zero.mp hdiff

/-- Metric data on `T_x^*M` induced by the tangent Riemannian metric.

This is the pullback of the tangent metric along the sharp map
`T_x^*M -> T_xM`. -/
def cotangentMetricData (g : SmoothMetric I M) (x : M) :
    MetricFiberData (Tensor0SSpace 1 I x) :=
  MetricFiberData.ofFlat
    (cotangentFlatLinear (I := I) g x)
    (cotangentFlatLinear_injective (I := I) g x)
    (by
      intro α β
      change g.inner x
          (cotangentSharpLinear (I := I) g x α)
          (cotangentSharpLinear (I := I) g x β) =
        g.inner x
          (cotangentSharpLinear (I := I) g x β)
          (cotangentSharpLinear (I := I) g x α)
      exact g.symm x _ _)
    (by
      intro α
      by_cases hα : cotangentSharpLinear (I := I) g x α = 0
      · change 0 <=
          g.inner x
            (cotangentSharpLinear (I := I) g x α)
            (cotangentSharpLinear (I := I) g x α)
        rw [hα]
        simp
      · exact le_of_lt (g.pos x (cotangentSharpLinear (I := I) g x α) hα))

/-- The packaged cotangent metric computes the sharp-definition inner product. -/
theorem cotangentMetricData_inner
    (g : SmoothMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    (cotangentMetricData (I := I) g x).inner α β =
      cotangentInner (I := I) g x α β := by
  rfl

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
