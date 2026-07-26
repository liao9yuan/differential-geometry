import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Slot-reindexing invariance of the covariant tensor inner product

`Tensor/RSTensor/NormSqProduct.lean` records `normSq0S_domDomCongr`: the squared Frobenius
norm of a covariant tensor is unchanged when its slots are reindexed by an equivalence
`Fin s ≃ Fin s'`.  This file adds the bilinear companion `inner0S_domDomCongr`, together
with the orthonormal-basis component formula `inner0S_identity_eq_sum` it is proved from.

Slot reindexing is what converts a curvature identity stated with the trace pair in one
position into the same identity with the trace pair in the first two slots (the position
`metricTraceFirstTwo0STensor` uses), so the pairings appearing in energy estimates have to
survive that move; `normSq0S_domDomCongr` alone only covers the diagonal case.
-/

noncomputable section

namespace Tensor0SBundle

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- In an orthonormal basis, the fiber inner product of two covariant tensors is the sum
over index tuples of the products of their components.  This is the bilinear form of
`normSq0S_identity_eq_sum_sq`. -/
theorem inner0S_identity_eq_sum {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric_gen I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s A B =
      ∑ slots : Fin s -> Idx,
        component0S (I := I) basis A slots * component0S (I := I) basis B slots := by
  rw [inner0S_eq_coord (I := I) g x s basis (identityInvMetric (Idx := Idx)) hinv,
    coordInner0S_identity_eq_sum (I := I) (x := x) s A B basis]
  apply Finset.sum_congr rfl
  intro slots _
  rfl

/-- **`inner0S` is invariant under simultaneous slot reindexing.**  Reindexing the slots of
both arguments by the same equivalence `e : Fin s ≃ Fin s'` (a permutation together with a
rank identification) leaves the fiber inner product unchanged: in an orthonormal basis it is
a sum over all index tuples, which the reindexing merely permutes.

This is the bilinear companion of `normSq0S_domDomCongr`; taking `B = A` recovers it. -/
theorem inner0S_domDomCongr {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric_gen I M) (x : M) {s s' : Nat}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (e : Fin s ≃ Fin s') (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s' (A.domDomCongr e) (B.domDomCongr e) =
      inner0S (I := I) g x s A B := by
  classical
  rw [inner0S_identity_eq_sum (I := I) g x s' basis hinv,
    inner0S_identity_eq_sum (I := I) g x s basis hinv]
  refine Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl Idx)) _ _ ?_
  intro w
  simp only [component0S_apply, Equiv.arrowCongr_apply, Equiv.symm_symm,
    Equiv.coe_refl, Function.comp, id_eq]
  rfl

end Tensor0SBundle
