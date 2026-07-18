import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.BernsteinShiHigher
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import Mathlib.Geometry.Manifold.Riemannian.Basic

set_option autoImplicit false

/-!
# Complete noncompact Bernstein estimates

This file is the noncompact maximum-principle consumer for the abstract
Bernstein curvature tower.  The active Riemannian metric is the fixed complete
anchor metric.  The evolving metrics are uniformly equivalent to that anchor
on the slab and have a uniform Ricci lower bound.

The remaining proof is the cutoff/exhaustion maximum principle.  It is kept at
this analytic layer rather than being turned into a compactness-side input.
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

namespace BernsteinTower

/-- Bernstein's tower estimate on a complete, possibly noncompact manifold.

The active `IsRiemannianManifold` structure is the fixed complete anchor.  The
two displayed geometric hypotheses are exactly what the cutoff argument uses:
uniform equivalence of the evolving metrics to the anchor, and a slabwise
Ricci lower bound.  No injectivity-radius or compactness hypothesis occurs.
-/
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
