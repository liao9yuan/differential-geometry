import DifferentialGeometry.Synthetic.Algebra.TensorAlgebra

variable {R V : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]

class PositiveSemiDefinite02 (T : TensorAlgebra.AbstractTensor R V 0 2) : Prop where
  nonneg : ∀ X : V, TensorAlgebra.tensor_eval T ![X, X] ![] ≥ 0

infix:50 " ≥₀ " => PositiveSemiDefinite02
