import RicciFlower.Realized.CurvatureTensor
import RicciFlower.Tensor.RSTensor.Tensor0SRiemannian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Rough Laplacian Preparation

This file provides the basis-level metric trace interface used by the scalar
and one-form Bochner layer.  It intentionally does not claim that the traced
object is already the intrinsic rough Laplacian tensor operation; that bridge is
recorded as an explicit realization predicate.
-/

namespace RicciFlower
namespace Realized

noncomputable section

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Insert two distinguished tangent vectors into the first two slots of a
covariant tensor input, leaving the remaining `s` slots to `tail`. -/
def metricTraceInput {x : M} {s : ℕ}
    (X Y : TangentSpace I x) (tail : Fin s -> TangentSpace I x) :
    Fin (s + 2) -> TangentSpace I x :=
  Fin.cases X (Fin.cases Y tail)

/-- Basis-level metric trace of the first two covariant slots of a `(0,s+2)`
tensor. This is the coordinate-side preparation interface for the rough
Laplacian. -/
def metricTrace0S2InBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    gInv i j * T (metricTraceInput (I := I) (basis i) (basis j) tail)

/-- Basis-level rough Laplacian value of a covariant tensor, represented as the
metric trace of a supplied second covariant derivative tensor. -/
def roughLap0SAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) : Real :=
  metricTrace0S2InBasis (I := I) basis gInv nabla2A tail

/-- One-form specialization of the basis-level rough Laplacian interface. -/
def roughLap1FormAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (Y : TangentSpace I x) : Real :=
  roughLap0SAt (I := I) basis gInv (s := 1) nabla2α (fun _ : Fin 1 => Y)

/-- Realization predicate saying that a supplied rough Laplacian tensor is the
basis-level metric trace of a supplied second covariant derivative tensor. -/
def RoughLap0SRealizesMetricTrace
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) : Prop :=
  ∀ tail : Fin s -> TangentSpace I x,
    roughA tail = roughLap0SAt (I := I) basis gInv nabla2A tail

theorem roughLap0SAt_eq_of_realizes
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (h : RoughLap0SRealizesMetricTrace (I := I) basis gInv roughA nabla2A)
    (tail : Fin s -> TangentSpace I x) :
    roughA tail = roughLap0SAt (I := I) basis gInv nabla2A tail :=
  h tail

theorem roughLap1FormAt_eq_of_realizes
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (roughα : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : RoughLap0SRealizesMetricTrace (I := I) basis gInv (s := 1) roughα nabla2α)
    (Y : TangentSpace I x) :
    roughα (fun _ : Fin 1 => Y) =
      roughLap1FormAt (I := I) basis gInv nabla2α Y :=
  h (fun _ : Fin 1 => Y)

end

end Realized
end RicciFlower
