import DifferentialGeometry.Synthetic.Realization.TensorContract

/-!
# Concrete `NablaTrComm`

This file wraps the already-proved concrete trace commutation theorem
`concrete_nabla_tr_comm` into the synthetic `NablaTrComm` proposition for
`concreteAbstractTrace`.

The heavy coordinate calculation lives in `Realization/NablaComm.lean`; the only
extra work here is unfolding `concreteAbstractTrace.tr` to `concreteTr`.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open Bundle CovariantDerivative SyntheticTensor
open TensorContractRealization

section Main

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- Concrete covariant derivatives commute with the concrete endomorphism trace.

This is the synthetic `NablaTrComm` wrapper around
`concrete_nabla_tr_comm`. -/
theorem concreteConn_NablaTrComm
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    NablaTrComm
      (concreteDerivationEmbedding I M)
      (concreteAbstractTrace I M)
      (concreteConn I M cov)
      (concreteConn_add_right I M cov)
      (concreteConn_leibniz I M cov) := by
  intro X L
  simpa [concreteAbstractTrace_tr, concreteDerivationEmbedding] using
    concrete_nabla_tr_comm I M cov X L

end Main

end
