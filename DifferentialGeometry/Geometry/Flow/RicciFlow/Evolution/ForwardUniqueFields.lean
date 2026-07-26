import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Christoffel
import DifferentialGeometry.Tensor.RSTensor.MetricCompatibility
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.ConnectionDifference
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetric
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Forward-uniqueness difference carriers (Route-K brick FIELDS)

The Kotschwar energy of `ShortTime/FORWARD_UNIQUE_PRO_RULING.md` §3–§4 is carried by
three **covariant** difference tensors, all lowered with the first metric `g₁`:

* `metricDiffAt g₁ g₂ x` — `h₀₂ = g₁ − g₂`, a `(0,2)` fiber tensor;
* `connDiffLowAt g₁ g₂ x` — `A₀₃ = g₁(∇¹ − ∇², ·)`, a `(0,3)` fiber tensor;
* `rmDiffLowAt g₁ g₂ x` — `S₀₄ = g₁(Rm¹ − Rm², ·)`, a `(0,4)` fiber tensor.

Keeping all three on the `Tensor0S` stack is what makes the rank-uniform moving-metric
norm derivative reusable and avoids any new generic mixed-tensor time-derivative theory.

The carriers are indexed by the two metrics rather than by two `SolutionOn`s: a
`SolutionFamily` carries only its metric, so for solutions `S₁ S₂` at time `s` the
carriers are `metricDiffAt (S₁.family.metric s) (S₂.family.metric s) x` and friends,
and equality of the two time-`s` metrics makes all three vanish (`*_self`).

`metricDiffSq`, `connDiffSq`, `rmDiffSq` name the `g₁`-squared norms that the energy
integrand `|h|² + |A|² + |S|²` is built from.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Carriers

/-! ## The metric difference `h₀₂` -/

/-- **`h₀₂`: the pointwise metric difference** of two smooth metrics, as a `(0,2)` fiber
tensor: the difference of their canonical `(0,2)` tensor fields `metricTensorField`. -/
def metricDiffAt (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x :=
  metricTensorField (I := I) g₁ x - metricTensorField (I := I) g₂ x

@[simp]
theorem metricDiffAt_apply (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 -> TangentSpace I x) :
    metricDiffAt (I := I) g₁ g₂ x v =
      g₁.inner x (v 0) (v 1) - g₂.inner x (v 0) (v 1) := by
  have h : metricDiffAt (I := I) g₁ g₂ x v =
      metricTensorField (I := I) g₁ x v - metricTensorField (I := I) g₂ x v :=
    Tensor0SSpace.sub_apply (I := I) 2 x
      (metricTensorField (I := I) g₁ x) (metricTensorField (I := I) g₂ x) v
  rw [h, metricTensorField_apply, metricTensorField_apply]

/-- Equal metrics give a vanishing metric-difference carrier. -/
@[simp]
theorem metricDiffAt_self (g : SmoothRiemannianMetric I M) (x : M) :
    metricDiffAt (I := I) g g x = 0 :=
  sub_self _

/-! ## The lowered connection difference `A₀₃` -/

/-- The connection difference of a covariant derivative with itself vanishes. -/
private theorem covDiff_self
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _)) (x : M) :
    CovariantDerivative.difference cov cov x = 0 := by
  classical
  refine ContinuousLinearMap.ext fun w => ?_
  obtain ⟨σ, hσx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M -> Type _)) x w
  have hσ : MDiffAt (T% fun y => σ y) x := σ.mdifferentiableAt
  have h := IsCovariantDerivativeOn.difference_apply
    cov.isCovariantDerivativeOnUniv cov.isCovariantDerivativeOnUniv
    (x := x) (Set.mem_univ x) (σ := fun y => σ y) hσ
  rw [sub_self] at h
  rw [← hσx]
  simpa [CovariantDerivative.difference] using h

/-- The output-first `g`-lowering of the connection-difference `(1,2)` tensor: the value
on `(w₀, w₁, w₂)` is `g(w₀, (∇ − ∇')_{w₁} w₂)`.  Implementation detail of
`connDiffLowAt`; the public carrier puts the lowered slot last. -/
private def connDiffOutAt (g : SmoothRiemannianMetric I M)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _)) (x : M) :
    Tensor0SSpace 3 I x :=
  Tensor0SSpace.ofModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (DifferentialGeometry.Integral.L2.lowerAllUpperIndices (I := I) (M := M) g 1 2 x
      (TensorRSSpace.toModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (connectionDifferenceTensorAt (I := I) cov cov' x)))

/-- Slot permutation moving the lowered output slot of `connDiffOutAt` from position `0`
to position `2`, so that the public carrier reads `(X, Y, Z) ↦ g(A(X, Y), Z)`. -/
private def connDiffStdPerm : Equiv.Perm (Fin 3) where
  toFun i := if i = 0 then 2 else if i = 1 then 0 else 1
  invFun i := if i = 0 then 1 else if i = 1 then 2 else 0
  left_inv i := by fin_cases i <;> simp
  right_inv i := by fin_cases i <;> simp

private theorem connDiffOutAt_apply (g : SmoothRiemannianMetric I M)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _)) (x : M)
    (w : Fin 3 -> TangentSpace I x) :
    connDiffOutAt (I := I) g cov cov' x w =
      g.inner x (w 0) (CovariantDerivative.difference cov cov' x (w 2) (w 1)) := by
  change
    DifferentialGeometry.Integral.L2.lowerAllUpperIndices (I := I) (M := M) g 1 2 x
        (TensorRSSpace.toModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (connectionDifferenceTensorAt (I := I) cov cov' x)) w = _
  rw [DifferentialGeometry.Integral.L2.lowerAllUpperIndices_apply]
  change
    connectionDifferenceOutput (I := I) (CovariantDerivative.difference cov cov' x)
        (Tensor0SSpace.ofModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (DifferentialGeometry.Integral.L2.separableFormAt (I := I) (M := M) g x 1
            (fun i : Fin 1 => w (Fin.castAdd 2 i))))
        (fun j : Fin 2 => w (Fin.natAdd 1 j)) = _
  rw [connectionDifferenceOutput_apply]
  change
    DifferentialGeometry.Integral.L2.separableFormAt (I := I) (M := M) g x 1
        (fun i : Fin 1 => w (Fin.castAdd 2 i))
        (fun _ : Fin 1 =>
          CovariantDerivative.difference cov cov' x
            (w (Fin.natAdd 1 (1 : Fin 2))) (w (Fin.natAdd 1 (0 : Fin 2)))) = _
  rw [DifferentialGeometry.Integral.L2.separableFormAt_apply]
  simp

/-- **`A₀₃`: the `g₁`-lowered connection difference** of the two Levi-Civita connections,
as a `(0,3)` fiber tensor with the standard slot order
`(X, Y, Z) ↦ g₁((∇¹ − ∇²)_X Y, Z)`. -/
def connDiffLowAt (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 3 I x :=
  ContinuousMultilinearMap.domDomCongr connDiffStdPerm
    (connDiffOutAt (I := I) g₁ (metricCov (I := I) g₁) (metricCov (I := I) g₂) x)

theorem connDiffLowAt_apply (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 3 -> TangentSpace I x) :
    connDiffLowAt (I := I) g₁ g₂ x v =
      g₁.inner x
        (CovariantDerivative.difference (metricCov (I := I) g₁) (metricCov (I := I) g₂) x
          (v 1) (v 0))
        (v 2) := by
  have h : connDiffLowAt (I := I) g₁ g₂ x v =
      g₁.inner x (v 2)
        (CovariantDerivative.difference (metricCov (I := I) g₁) (metricCov (I := I) g₂) x
          (v 1) (v 0)) :=
    connDiffOutAt_apply (I := I) g₁ (metricCov (I := I) g₁) (metricCov (I := I) g₂) x
      (fun i : Fin 3 => v (connDiffStdPerm i))
  rw [h]
  exact g₁.symm x (v 2)
    (CovariantDerivative.difference (metricCov (I := I) g₁) (metricCov (I := I) g₂) x
      (v 1) (v 0))

/-- Equal metrics give a vanishing connection-difference carrier. -/
@[simp]
theorem connDiffLowAt_self (g : SmoothRiemannianMetric I M) (x : M) :
    connDiffLowAt (I := I) g g x = 0 := by
  refine ContinuousMultilinearMap.ext fun v => ?_
  have h := connDiffLowAt_apply (I := I) g g x v
  rw [covDiff_self] at h
  simpa using h

/-! ## The lowered curvature difference `S₀₄` -/

/-- **`S₀₄`: the `g₁`-lowered Riemann-curvature difference** of the two metrics, as a
`(0,4)` fiber tensor.  Both terms lower the `(1,3)` Riemann tensor of the corresponding
Levi-Civita connection with the *same* metric `g₁`; the first term is the canonical
`metricRm04At g₁ x`. -/
def rmDiffLowAt (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 4 I x :=
  DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At
      (I := I) g₁ (metricCov (I := I) g₁) (metricCov_smooth (I := I) g₁) x -
    DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At
      (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x

theorem rmDiffLowAt_apply (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 4 -> TangentSpace I x) :
    rmDiffLowAt (I := I) g₁ g₂ x v =
      metricRm04At (I := I) g₁ x v -
        DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At
          (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x v :=
  Tensor0SSpace.sub_apply (I := I) 4 x _ _ v

/-- Standard-slot reading of `S₀₄`: it is the `g₁`-lowering of the difference of the two
canonical `(1,3)` Riemann tensors, `(X, Y, Z, W) ↦ g₁((Rm¹ − Rm²)(X, Y)Z, W)`. -/
theorem rmDiffLowAt_std (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) :
    rmDiffLowAt (I := I) g₁ g₂ x
        (DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y Z W) =
      metricRm13At (I := I) g₁ x
          (dualToCotangent_gen (I := I) (tangentFlatLinear_gen (I := I) g₁ x W))
          (DifferentialGeometry.Integral.Connection.vec3 (I := I) X Y Z) -
        metricRm13At (I := I) g₂ x
          (dualToCotangent_gen (I := I) (tangentFlatLinear_gen (I := I) g₁ x W))
          (DifferentialGeometry.Integral.Connection.vec3 (I := I) X Y Z) := by
  have hsub : rmDiffLowAt (I := I) g₁ g₂ x
        (DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y Z W) =
      DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At
          (I := I) g₁ (metricCov (I := I) g₁) (metricCov_smooth (I := I) g₁) x
          (DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y Z W) -
        DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At
          (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x
          (DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y Z W) :=
    Tensor0SSpace.sub_apply (I := I) 4 x _ _ _
  rw [hsub,
    DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At_eq_lower_riemannCurvatureAt
      (I := I) g₁ (metricCov (I := I) g₁) (metricCov_smooth (I := I) g₁) X Y Z W,
    DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At_eq_lower_riemannCurvatureAt
      (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) X Y Z W]
  rfl

/-- Equal metrics give a vanishing curvature-difference carrier. -/
@[simp]
theorem rmDiffLowAt_self (g : SmoothRiemannianMetric I M) (x : M) :
    rmDiffLowAt (I := I) g g x = 0 :=
  sub_self _

end Carriers

section Norms

/-- `|h₀₂|²_{g₁}` at a point: the energy's metric-difference integrand. -/
def metricDiffSq (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) : Real :=
  normSq0S (I := I) g₁ x 2 (metricDiffAt (I := I) g₁ g₂ x)

/-- `|A₀₃|²_{g₁}` at a point: the energy's connection-difference integrand. -/
def connDiffSq (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) : Real :=
  normSq0S (I := I) g₁ x 3 (connDiffLowAt (I := I) g₁ g₂ x)

/-- `|S₀₄|²_{g₁}` at a point: the energy's curvature-difference integrand. -/
def rmDiffSq (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) : Real :=
  normSq0S (I := I) g₁ x 4 (rmDiffLowAt (I := I) g₁ g₂ x)

theorem metricDiffSq_def (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    metricDiffSq (I := I) g₁ g₂ x =
      normSq0S (I := I) g₁ x 2 (metricDiffAt (I := I) g₁ g₂ x) := rfl

theorem connDiffSq_def (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    connDiffSq (I := I) g₁ g₂ x =
      normSq0S (I := I) g₁ x 3 (connDiffLowAt (I := I) g₁ g₂ x) := rfl

theorem rmDiffSq_def (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    rmDiffSq (I := I) g₁ g₂ x =
      normSq0S (I := I) g₁ x 4 (rmDiffLowAt (I := I) g₁ g₂ x) := rfl

end Norms

end DifferentialGeometry.PDE.RicciFlow

end
