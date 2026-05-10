import DifferentialGeometry.Synthetic.Realization.Embedding

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Lie Bracket Scalar Action

This file keeps the upstream-style scalar Lie-bracket identity available under
`DifferentialGeometry.Integral.Connection` without importing the larger
connection stack.
-/

noncomputable section

namespace DifferentialGeometry
namespace Integral
namespace Connection

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

/-- The Lie bracket acts on scalar functions as the commutator of the two
directional derivative operators. -/
theorem extDerivFun_apply_mlieBracket
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (f : C^∞⟮I, M; ℝ⟯)
    (x : M) :
    extDerivFun (I := I) (fun y : M => f y) x
        (VectorField.mlieBracket I (fun y : M => X y) (fun y : M => Y y) x) =
      extDerivFun (I := I)
          (fun y : M => extDerivFun (I := I) (fun z : M => f z) y (Y y)) x
          (X x) -
        extDerivFun (I := I)
          (fun y : M => extDerivFun (I := I) (fun z : M => f z) y (X y)) x
          (Y x) := by
  have h := congrArg (fun g : C^∞⟮I, M; ℝ⟯ => g x)
    (embedDeriv_mlieBracket I M X Y f)
  simpa [vectorFieldAction, mlieBracketSection] using h

end Connection
end Integral
end DifferentialGeometry
