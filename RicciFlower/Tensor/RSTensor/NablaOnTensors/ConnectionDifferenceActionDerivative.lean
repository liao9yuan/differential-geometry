import RicciFlower.Tensor.RSTensor.NablaOnTensors.ConnectionDifferenceActionIdentity

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# First derivative of the connection-difference action

This file starts the `k = 1` tensor-layer producer for MSM135 Chapter 4,
Lemma "Norms of covariant derivatives of tensors, I".

The checked support below only normalizes the antidiagonal Leibniz tensor at
order one.  The remaining target is a field-level realization theorem saying
that the `h`-covariant derivative of the connection-action tensor has this
order-one antidiagonal form.
-/

namespace Tensor0SBundle

noncomputable section

open Bundle Set TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]

set_option backward.isDefEq.respectTransparency false in
/-- Component normalization of the order-one antidiagonal connection-action
tensor.

For `k = 1`, the Leibniz antidiagonal consists of exactly the two terms
`A₀ ⋄ T₁` and `A₁ ⋄ T₀`, with binomial coefficient `1` on both terms. -/
theorem connActAntiTensorAt_one_comp {r s : Nat}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (A : Nat -> TensorRSSpace 1 2 I x)
    (T : Nat -> TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) :
    componentRS (I := I) basis
        (connActAntiTensorAt (I := I) basis 1 A T) upper lower =
      connActComp
        (fun l i j =>
          componentRS (I := I) basis (A 0)
            (fun _ : Fin 1 => l)
            (fun q : Fin 2 => if q = 0 then i else j))
        (fun upper' lower' =>
          componentRS (I := I) basis (T 1) upper' lower')
        upper lower +
      connActComp
        (fun l i j =>
          componentRS (I := I) basis (A 1)
            (fun _ : Fin 1 => l)
            (fun q : Fin 2 => if q = 0 then i else j))
        (fun upper' lower' =>
          componentRS (I := I) basis (T 0) upper' lower')
        upper lower := by
  classical
  rw [connActAntiTensorAt_comp]
  simp [Finset.antidiagonal]

set_option backward.isDefEq.respectTransparency false in
/-- Lift the order-one antidiagonal component formula to a tensor equality.

This is the target shape for the future derivative-realization theorem: once
the components of `S` are proved to be the two Leibniz terms, `S` is exactly the
order-one antidiagonal connection-action tensor. -/
theorem eq_connActAntiTensorAt_one_of_comp {r s : Nat}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (A : Nat -> TensorRSSpace 1 2 I x)
    (T : Nat -> TensorRSSpace r s I x)
    (S : TensorRSSpace r (s + 1) I x)
    (hcomp : forall upper : Fin r -> Idx, forall lower : Fin (s + 1) -> Idx,
      componentRS (I := I) basis S upper lower =
        connActComp
          (fun l i j =>
            componentRS (I := I) basis (A 0)
              (fun _ : Fin 1 => l)
              (fun q : Fin 2 => if q = 0 then i else j))
          (fun upper' lower' =>
            componentRS (I := I) basis (T 1) upper' lower')
          upper lower +
        connActComp
          (fun l i j =>
            componentRS (I := I) basis (A 1)
              (fun _ : Fin 1 => l)
              (fun q : Fin 2 => if q = 0 then i else j))
          (fun upper' lower' =>
            componentRS (I := I) basis (T 0) upper' lower')
          upper lower) :
    S = connActAntiTensorAt (I := I) basis 1 A T := by
  apply extRS_basis (I := I) basis
  intro upper lower
  rw [hcomp upper lower]
  rw [connActAntiTensorAt_one_comp (I := I) basis A T upper lower]

end

end Tensor0SBundle
