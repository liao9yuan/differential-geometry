import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Christoffel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Christoffel-difference time derivative (forward-uniqueness brick K1)

First Route-(K) brick of the `ricci_flow_forward_unique` campaign
(`ShortTime/FORWARD_UNIQUE_PRO_RULING.md` §5, K1): for two Ricci-flow solutions
carrying the same local frame, the frame components of `Γ(S₁) − Γ(S₂)` evolve
with derivative `RHS(S₁) − RHS(S₂)` — the exact component subtraction of the
two existing `ChristoffelEvolutionEquationInFrameOn` facts, with no star-sum
estimate.  A pointwise evaluation lemma identifies the component difference
with the frame coefficient of the connection-difference vector, so later
bricks can pass to the intrinsic connection-difference tensor without
re-expanding Christoffel symbols.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}

omit [DecidableEq Idx] in
/-- **K1: Christoffel-difference evolution in a common local frame.**  Two
Ricci-flow solutions on the same interval, each satisfying its raised
Christoffel evolution equation in the SAME local frame, have their
component-difference `Γ(S₁)^k_{ij} − Γ(S₂)^k_{ij}` differentiable in time with
derivative the difference of the two evolution right-hand sides. -/
theorem christoffelEvolutionDiffInFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S₁ S₂ : SolutionOn (I := I) (M := M) D)
    (gInv₁ gInv₂ : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic₁ nablaRic₂ : Real -> M -> Idx -> Idx -> Idx -> Real)
    (h₁ : ChristoffelEvolutionEquationInFrameOn
      (I := I) S₁ gInv₁ frame hframe nablaRic₁)
    (h₂ : ChristoffelEvolutionEquationInFrameOn
      (I := I) S₂ gInv₂ frame hframe nablaRic₂) :
    ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M), x ∈ u →
      ∀ i j k : Idx,
        HasDerivWithinAt
          (fun s : Real =>
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (S₁.family.connection s) frame hframe x i j k -
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (S₂.family.connection s) frame hframe x i j k)
          (christoffelEvolutionRHSInFrame (M := M) gInv₁ nablaRic₁ (t : Real) x i j k -
            christoffelEvolutionRHSInFrame (M := M) gInv₂ nablaRic₂ (t : Real) x i j k)
          D.carrier
          (t : Real) := by
  intro t x hx i j k
  exact (h₁ t x hx i j k).sub (h₂ t x hx i j k)

omit [Fintype Idx] [DecidableEq Idx] in
/-- Pointwise evaluation: the Christoffel component difference of two
solutions at one time is the frame coefficient of the connection-difference
vector `(∇¹_{e_i} e_j − ∇²_{e_i} e_j)(x)`.  This is the bridge later bricks use
to pass from component differences to the intrinsic connection-difference
object. -/
theorem christoffelDiff_coeff
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S₁ S₂ : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (s : Real) (x : M) (i j k : Idx) :
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (S₁.family.connection s) frame hframe x i j k -
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (S₂.family.connection s) frame hframe x i j k =
    hframe.coeff k x
      ((S₁.family.connection s (frame j) x) (frame i x) -
        (S₂.family.connection s (frame j) x) (frame i x)) := by
  simp [DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame, map_sub]

end Components

end DifferentialGeometry.PDE.RicciFlow

end
