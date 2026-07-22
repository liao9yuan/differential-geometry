import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.BernsteinShiHigher
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import Mathlib.Geometry.Manifold.Riemannian.Basic

set_option autoImplicit false

/-!
# Complete noncompact Bernstein estimates

This file owns the noncompact localization interfaces for the Bernstein
curvature tower.  A valid complete-manifold proof must consume quantitative
parabolic cutoffs and the curvature-tower Kato estimate before discarding the
negative next-level terms.

The legacy `estimate_complete` statement below predates that audit and has
insufficient hypotheses.  It remains temporarily for its current caller, but
must not be treated as the canonical target.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators Bundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [I.Boundaryless]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]

/-- Pointwise Kato control for the gradients of a Bernstein tower.  For the
curvature tower this is supplied by `towerNorm_grad_le`; it is generated from
the solution and is not an HCG input. -/
def TowerNormGradOn
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G) : Prop :=
  ∀ k : Nat, ∀ t : Real, t ∈ Set.Icc 0 B.T → 0 < t → ∀ x : M,
    (G.metric t).inner x
        (gradientFun (I := I) (G.metric t) (B.w k t) x)
        (gradientFun (I := I) (G.metric t) (B.w k t) x) ≤
      4 * B.w k t x * B.w (k + 1) t x

namespace BernsteinTower

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Legacy unsupported frontier.**  This statement is too weak for a
complete-noncompact Bernstein argument: metric equivalence and a Ricci lower
bound do not produce quantitative evolving-metric cutoffs, and the abstract
tower does not expose the Kato estimate needed to absorb cutoff-gradient
terms.  Replace its caller by a localized theorem consuming generated cutoff
data and `TowerNormGradOn`; do not fill this proof under the present
interface. -/
theorem estimate_complete
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (Ceq Kric : Real) (hCeq : 1 ≤ Ceq) (hKric : 0 ≤ Kric)
    (hequiv : ∀ t : Real, t ∈ Set.Icc 0 B.T → ∀ x : M,
      ∀ v : TangentSpace I x,
        Ceq⁻¹ * ‖v‖ ^ 2 ≤ (G.metric t).inner x v v ∧
          (G.metric t).inner x v v ≤ Ceq * ‖v‖ ^ 2)
    (hric : ∀ t : Real, t ∈ Set.Icc 0 B.T → ∀ x : M,
      ∀ v : TangentSpace I x,
        -Kric * (G.metric t).inner x v v ≤
          ricciTensor (I := I) (G.metric t) x v v) :
    ∀ m : ℕ, ∀ t : Real, t ∈ Set.Icc 0 B.T → 0 < t → ∀ x : M,
      t ^ m * B.w m t x ≤ (towerConst B.c B.α m) ^ 2 * B.K ^ 2 := by
  sorry

end BernsteinTower

end DifferentialGeometry.PDE.RicciFlow
