import DifferentialGeometry.Synthetic.Axioms
import Mathlib.Geometry.Manifold.DerivationBundle
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Dual
import DifferentialGeometry.VectorBundle.Section
import DifferentialGeometry.Tensor.RSTensor.Defs

/-!
# Bridge Scaffolding

Imports, instance verification, and `IsScalarTower` for the concrete instantiation
`k = ℝ`, `R = C^∞(M, ℝ)`, `V = Γ(TM)`, `Time = ℝ`.
-/

noncomputable section

open scoped Manifold ContDiff
open Bundle

-- ============================================================
-- Standard variable context
-- ============================================================

section BridgeContext

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

-- ============================================================
-- Instance verification
-- ============================================================

section InstanceVerification

example : CommRing C^∞⟮I, M; ℝ⟯ := inferInstance
example : Algebra ℝ C^∞⟮I, M; ℝ⟯ := inferInstance
example : Module C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := inferInstance
example : Module ℝ Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := inferInstance
example (x : M) : Module.Free ℝ (TangentSpace I x) := inferInstance
example (x : M) : FiniteDimensional ℝ (TangentSpace I x) := inferInstance
example : ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I := inferInstance

end InstanceVerification

-- ============================================================
-- IsScalarTower: ℝ-action compatible with C^∞(M,ℝ)-action
-- ============================================================

/-- Pointwise: `(r * f(x)) • s(x) = r • (f(x) • s(x))` by `mul_smul`. -/
instance smoothSectionScalarTower :
    IsScalarTower ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ where
  smul_assoc r f s := by ext x; exact mul_smul (r : ℝ) (f x : ℝ) (s x)

-- ============================================================
-- char_ne_2 for C^∞(M, ℝ)
-- ============================================================

/-- `CharZero ℝ` lifts pointwise: `2a = 0 → a = 0` in `C^∞(M, ℝ)`. -/
theorem char_ne_2_smooth_functions :
    ∀ (a : C^∞⟮I, M; ℝ⟯), (2 : C^∞⟮I, M; ℝ⟯) * a = 0 → a = 0 := by
  intro a ha
  have h2a : a + a = 0 := by rwa [← two_mul]
  ext x
  have := DFunLike.congr_fun h2a x
  simp only [ContMDiffMap.coe_add, Pi.add_apply, ContMDiffMap.coe_zero, Pi.zero_apply] at this ⊢
  linarith

end BridgeContext

end
