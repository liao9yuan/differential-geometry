import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Pullback
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Pullback Tangent Fields and Ambient Covariant Derivatives

This file records the concrete Mathlib objects behind "vector fields along a
map".  The pullback bundle itself is Mathlib's `f *ᵖ E`; no new bundle
structure is introduced here.

The last definition is deliberately modest: it differentiates along `f` a
section of the target bundle that already comes from an ambient section.  A
full pullback connection on arbitrary sections of `f *ᵖ E` would require the
local-frame construction of pullback connections.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Bundle
open scoped ContDiff Manifold Topology

namespace SyntheticGeometry
namespace Riemannian

section PullbackFields

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
  {HN : Type*} [TopologicalSpace HN]
  {IN : ModelWithCorners 𝕜 EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]

/-- The pullback of a bundle `V` along `f`, using Mathlib's `Bundle.Pullback`. -/
abbrev PullbackBundle (f : N -> M) (V : M -> Type*) : N -> Type _ :=
  f *ᵖ V

/-- The pullback tangent bundle `f^* TM`. -/
abbrev PullbackTangent (f : N -> M) : N -> Type _ :=
  f *ᵖ (TangentSpace IM : M -> Type _)

/-- A vector field along `f`, i.e. a section of `f^* TM`. -/
abbrev VectorFieldAlong (f : N -> M) : Type _ :=
  forall x : N, TangentSpace IM (f x)

/-- A section of a general pulled-back bundle. -/
abbrev SectionAlong (f : N -> M) (V : M -> Type*) : Type _ :=
  forall x : N, V (f x)

/-- Restrict an ambient section to a section along `f`. -/
def restrictSectionAlong {V : M -> Type*} (f : N -> M)
    (s : forall y : M, V y) : SectionAlong f V :=
  fun x => s (f x)

/-- Restrict an ambient vector field to a vector field along `f`. -/
def restrictVectorFieldAlong (f : N -> M)
    (Y : forall y : M, TangentSpace IM y) : VectorFieldAlong (IM := IM) f :=
  restrictSectionAlong f Y

/--
Push a vector field on the source forward to a vector field along `f`.

This is not a vector field on the target unless `f` is suitably invertible;
the result naturally lives in `f^* TM`.
-/
noncomputable def pushForwardVectorFieldAlong (f : N -> M)
    (X : forall x : N, TangentSpace IN x) : VectorFieldAlong (IM := IM) f :=
  fun x => mfderiv IN IM f x (X x)

@[simp]
theorem restrictSectionAlong_apply {V : M -> Type*} (f : N -> M)
    (s : forall y : M, V y) (x : N) :
    restrictSectionAlong f s x = s (f x) :=
  rfl

@[simp]
theorem restrictVectorFieldAlong_apply (f : N -> M)
    (Y : forall y : M, TangentSpace IM y) (x : N) :
    restrictVectorFieldAlong f Y x = Y (f x) :=
  rfl

@[simp]
theorem pushForwardVectorFieldAlong_apply (f : N -> M)
    (X : forall x : N, TangentSpace IN x) (x : N) :
    pushForwardVectorFieldAlong (IN := IN) (IM := IM) f X x =
      mfderiv IN IM f x (X x) :=
  rfl

end PullbackFields

section PullbackCovariantDerivative

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
  {HN : Type*} [TopologicalSpace HN]
  {IN : ModelWithCorners 𝕜 EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M -> Type*}
  [TopologicalSpace (TotalSpace F V)]
  [forall y : M, TopologicalSpace (V y)]
  [forall y : M, AddCommGroup (V y)]
  [forall y : M, Module 𝕜 (V y)]
  [forall y : M, IsTopologicalAddGroup (V y)]
  [forall y : M, ContinuousSMul 𝕜 (V y)]
  [FiberBundle F V]

/--
The pullback covariant derivative applied to a section that is already the
restriction of an ambient section.

On paper this is `(f^* ∇)_X (s ∘ f) = ∇_{df(X)} s`, and the right-hand side is
well-typed because `df_x X_x : T_{f x} M`.
-/
noncomputable def covDerivAlongMapOfSection
    (cov : CovariantDerivative IM F V) (f : N -> M)
    (X : forall x : N, TangentSpace IN x) (s : forall y : M, V y) :
    SectionAlong f V :=
  fun x => cov s (f x) (mfderiv IN IM f x (X x))

@[simp]
theorem covDerivAlongMapOfSection_apply
    (cov : CovariantDerivative IM F V) (f : N -> M)
    (X : forall x : N, TangentSpace IN x) (s : forall y : M, V y) (x : N) :
    covDerivAlongMapOfSection (IN := IN) cov f X s x =
      cov s (f x) (mfderiv IN IM f x (X x)) :=
  rfl

theorem covDerivAlongMapOfSection_add
    (cov : CovariantDerivative IM F V) (f : N -> M)
    (X : forall x : N, TangentSpace IN x)
    {s t : forall y : M, V y} {x : N}
    (hs : MDiffAt (T% s) (f x)) (ht : MDiffAt (T% t) (f x)) :
    covDerivAlongMapOfSection (IN := IN) cov f X (s + t) x =
      covDerivAlongMapOfSection (IN := IN) cov f X s x +
        covDerivAlongMapOfSection (IN := IN) cov f X t x := by
  exact congrArg (fun L => L (mfderiv IN IM f x (X x)))
    (cov.isCovariantDerivativeOn.add hs ht)

theorem covDerivAlongMapOfSection_smul
    (cov : CovariantDerivative IM F V) (f : N -> M)
    (X : forall x : N, TangentSpace IN x)
    {g : M -> 𝕜} {s : forall y : M, V y} {x : N}
    (hs : MDiffAt (T% s) (f x)) (hg : MDiffAt g (f x)) :
    covDerivAlongMapOfSection (IN := IN) cov f X (g • s) x =
      g (f x) • (covDerivAlongMapOfSection (IN := IN) cov f X s x : V (f x)) +
        extDerivFun g (f x) (mfderiv IN IM f x (X x)) • s (f x) := by
  simpa [covDerivAlongMapOfSection] using congrArg
    (fun L => L (mfderiv IN IM f x (X x)))
    (cov.isCovariantDerivativeOn.leibniz hs hg)

variable [VectorBundle 𝕜 F V]

@[simp]
theorem covDerivAlongMapOfSection_zero
    (cov : CovariantDerivative IM F V) (f : N -> M)
    (X : forall x : N, TangentSpace IN x) :
    covDerivAlongMapOfSection (IN := IN) cov f X (0 : forall y : M, V y) = 0 := by
  ext x
  change cov 0 (f x) (mfderiv IN IM f x (X x)) = 0
  simp

end PullbackCovariantDerivative

end Riemannian
end SyntheticGeometry
