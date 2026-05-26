import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Basic
import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.CoveringMap
import Mathlib.Topology.Path
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Homotopy.Lifting

/-!
# Truncation-lift slice-topology continuity

Three placeholder lemmas for the truncation lift `s ↦ ⟨γ s, q.2.trans ⟦γ.truncate 0 s⟧⟩`
into the universal cover. Proofs are deferred.
-/

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

/-- Path-class identity expressing `γ.truncateOfLE 0 s` as the trans of two pieces. -/
lemma uc_trans_truncate_class
    {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b)
    {s₀ s : ℝ} (h0 : (0 : ℝ) ≤ s₀) (h0s : s₀ ≤ s) (hs1 : s ≤ 1) :
    True := sorry

/-- Continuity of the truncation lift in the slice topology. -/
lemma uc_truncLift_continuous
    {X : Type*} [TopologicalSpace X] [Inhabited X]
    {a b : X} (γ : Path a b)
    (q : UniversalCover X) (hq : q.1 = a) :
    True := sorry

/-- Value at `1` of the lift of a path starting at the basepoint. -/
lemma uc_liftPath_one_eq
    {X : Type*} [TopologicalSpace X] [Inhabited X]
    [ConnectedSpace X] [LocPathConnectedSpace X]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace X]
    {x : X} (γ : Path (default : X) x) :
    True := sorry

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry
