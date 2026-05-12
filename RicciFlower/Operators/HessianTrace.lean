import RicciFlower.Connection.MetricCompatibility
import RicciFlower.Operators
import RicciFlower.Tensor.RicciIdentity

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option backward.isDefEq.respectTransparency false

/-!
# Scalar Laplacian as a Hessian Trace

This file contains the operator-level bridge between the scalar Laplacian
`div grad` and the metric trace of the covariant derivative of `df`.
-/

noncomputable section

namespace RicciFlower
namespace Realized

open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- The realized one-form `du`, represented as a `(0,1)` tensor. -/
def differential1FormFun (u : M -> Real) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  dualToCotangent (I := I) (mfderiv I 𝓘(Real, Real) u x).toLinearMap

/-- Raw differential one-form as a pointwise function. Bundling it as a smooth
section is kept as an explicit regularity/realization step. -/
def duField (u : M -> Real) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  differential1FormFun (I := I) u x

/-- A bundled one-form section realizes the raw differential of `u`. -/
def DuFieldRealizes (u : M -> Real)
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1) : Prop :=
  ∀ x : M, du x = duField (I := I) u x

/-- Section-level covariant derivative of a bundled differential one-form along
a smooth vector field. The separate `DuFieldRealizes` predicate records when
the supplied one-form is actually `du`. -/
noncomputable def nablaDuAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 cov X du x

/-- Supplied Hessian candidate at a point. The equality with `∇du` is recorded
by `HessianRealizesNablaDuAt`; this definition does not bake in that frontier. -/
def hessianAt
    (Hess : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  Hess x

/-- Pointwise frontier saying a supplied Hessian tensor is the tensor
`(X,Y) ↦ (∇_X du)(Y)`. -/
def HessianRealizesNablaDuAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1)
    (Hess : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M) : Prop :=
  ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
      (Y : TangentSpace I x),
    Hess x (vec2 (X x) Y) =
      nablaDuAt (I := I) cov X du x (fun _ : Fin 1 => Y)

theorem nablaDu_eq_hessian
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1)
    (Hess : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M)
    (hHess : HessianRealizesNablaDuAt (I := I) cov du Hess x)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Y : TangentSpace I x) :
    nablaDuAt (I := I) cov X du x (fun _ : Fin 1 => Y) =
      Hess x (vec2 (X x) Y) :=
  (hHess X Y).symm

/-- A supplied scalar second-derivative tensor realizes the scalar Laplacian
as its basis-level metric trace at `x`. -/
def ScalarLaplacianRealizesTraceAt
    {Idx : Type*} [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (f : M -> Real)
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Prop :=
  laplacian (I := I) cov g f x =
    metricTrace0S2InBasis (I := I) basis gInv hessF Fin.elim0

/-- Convert an explicit scalar Hessian trace equality into the scalar
Laplacian trace realization predicate. The actual analytic work is the supplied
trace equality. -/
theorem scalar_laplacian_trace_of_hessian
    {Idx : Type*} [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (f : M -> Real)
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (htrace :
      laplacian (I := I) cov g f x =
        metricTrace0S2InBasis (I := I) basis gInv hessF Fin.elim0) :
    ScalarLaplacianRealizesTraceAt (I := I) cov g basis gInv f hessF :=
  htrace

/-- A chosen family of smooth vector fields realizes a pointwise tangent basis
at `x`. -/
def SmoothBasisFieldsAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) : Prop :=
  ∀ i : Idx, X i x = basis i

/-- Metric-compatible Hessian trace theorem for the scalar Laplacian.

Mathematically, this is the identity
`div(grad f) = tr_g (∇ df)`. Metric compatibility rewrites
`(∇_X df)(Y)` as `g(∇_X grad f, Y)`, and the basis inverse turns the metric
trace of that bilinear form into `trace (∇ grad f)`. -/
theorem scalarLaplacianRealizesTraceAt_of_nablaDu
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (f : M -> Real)
    (duSec : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1)
    (hessF : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hdu : DuFieldRealizes (I := I) f duSec)
    (hHess : HessianRealizesNablaDuAt (I := I) cov duSec hessF x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    ScalarLaplacianRealizesTraceAt (I := I) cov g basis gInv f (hessF x) := by
  -- Direct proof frontier, not a scalar-Bochner adapter:
  -- 1. unfold `laplacian`/`divergence`;
  -- 2. use metric compatibility to rewrite
  --    `hessF x (vec2 (basis i) (basis j))` as
  --    `g.inner x (cov (gradientFun g f) x (basis i)) (basis j)`;
  -- 3. use `MetricInverseInBasis` to identify the resulting metric trace
  --    with `LinearMap.trace` of `(cov (gradientFun g f) x).toLinearMap`.
  sorry

end Realized
end RicciFlower
