import DifferentialGeometry.Geometry.Riemannian.GaussLemma
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.UnitInterval

/-!
# Geodesic convexity and the good-cover property

This file develops the *structural* side of geodesic (Whitehead) convexity:
the part that is purely topological once a minimising-geodesic selector is
available.

A subset `S` of a manifold is **geodesically convex with respect to a joining
map** `join : M → M → ℝ → M` when, for every pair of points `a b ∈ S`, the
curve `t ↦ join a b t` stays inside `S` for `t ∈ [0,1]`, starts at `a`, ends at
`b`, and is continuous on `[0,1]`. The map `join` is meant to select *the*
minimising geodesic between two nearby points; on a Riemannian manifold this
selector exists and is continuous on a small enough region (the genuine
Whitehead content, supplied elsewhere).

The two facts proved here are the ones a *good cover* needs and that do **not**
depend on any further Riemannian input:

* `IsGeodesicallyConvexWith.joinedIn` — a geodesically convex set is internally
  path-connected: any two of its points are joined by a path inside it.
* `IsGeodesicallyConvexWith.inter` — the intersection of two sets that are
  geodesically convex **for the same joining map** is again geodesically convex
  for that map. (This is the algebraic heart of "intersections of convex normal
  balls are convex": because the selector is shared, the joining curve between
  two common points lies in both sets, hence in their intersection.)

Combining the two gives the good-cover obligation
`JoinedIn (S ∩ T) a b` for any two points `a b ∈ S ∩ T`, which is exactly the
`hpcInter` hypothesis consumed by the countable-fundamental-group argument.

The Riemannian existence statement — that small normal balls are geodesically
convex for a single global selector — is the remaining genuinely geometric
ingredient (Whitehead's theorem) and is *not* established here.
-/

open Set
open scoped unitInterval

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

/-- **Geodesic convexity with respect to a joining map.**

`IsGeodesicallyConvexWith join S` says that for any two points `a b ∈ S` the
curve `t ↦ join a b t` is a continuous curve on the unit interval, starts at
`a`, ends at `b`, and stays inside `S`.

The map `join` is an external datum (a minimising-geodesic selector). Phrasing
convexity relative to a *fixed* `join` is what makes convexity closed under
intersection: two sets convex for the *same* selector have a convex
intersection, because the single joining curve between two shared points is
forced to lie in both.

This is a genuine convexity predicate, not a restatement of any downstream
conclusion: it constrains the set `S` through the externally given geometric
datum `join`, exactly as ordinary convexity constrains a set through the
externally given affine segment map. -/
def IsGeodesicallyConvexWith {M : Type*} [TopologicalSpace M]
    (join : M → M → ℝ → M) (S : Set M) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S,
    ContinuousOn (join a b) I ∧ join a b 0 = a ∧ join a b 1 = b ∧
      (∀ t ∈ I, join a b t ∈ S)

namespace IsGeodesicallyConvexWith

variable {M : Type*} [TopologicalSpace M] {join : M → M → ℝ → M} {S T : Set M}

/-- A geodesically convex set is internally path-connected: any two of its
points are joined by a path that never leaves the set. -/
theorem joinedIn (hS : IsGeodesicallyConvexWith join S) {a b : M}
    (ha : a ∈ S) (hb : b ∈ S) : JoinedIn S a b := by
  obtain ⟨hcont, h0, h1, hmem⟩ := hS a ha b hb
  refine JoinedIn.ofLine hcont h0 h1 ?_
  rintro x ⟨t, ht, rfl⟩
  exact hmem t ht

/-- The intersection of two sets that are geodesically convex **for the same
joining map** is geodesically convex for that map.

The joining curve `t ↦ join a b t` between two points `a b ∈ S ∩ T` is the
*same* curve whether viewed through `S`'s convexity or `T`'s convexity (the
selector `join` is shared); convexity of `S` keeps it in `S`, convexity of `T`
keeps it in `T`, hence it stays in `S ∩ T`. -/
theorem inter (hS : IsGeodesicallyConvexWith join S)
    (hT : IsGeodesicallyConvexWith join T) :
    IsGeodesicallyConvexWith join (S ∩ T) := by
  rintro a ⟨haS, haT⟩ b ⟨hbS, hbT⟩
  obtain ⟨hcontS, h0, h1, hmemS⟩ := hS a haS b hbS
  obtain ⟨_, _, _, hmemT⟩ := hT a haT b hbT
  exact ⟨hcontS, h0, h1, fun t ht => ⟨hmemS t ht, hmemT t ht⟩⟩

/-- **Good-cover step.** If `S` and `T` are geodesically convex for a common
joining map, then any two points common to both are joined by a path lying
inside the intersection `S ∩ T`. This is precisely the pairwise-intersection
condition required of a good cover. -/
theorem joinedIn_inter (hS : IsGeodesicallyConvexWith join S)
    (hT : IsGeodesicallyConvexWith join T) {a b : M}
    (haS : a ∈ S) (haT : a ∈ T) (hbS : b ∈ S) (hbT : b ∈ T) :
    JoinedIn (S ∩ T) a b :=
  (hS.inter hT).joinedIn ⟨haS, haT⟩ ⟨hbS, hbT⟩

end IsGeodesicallyConvexWith

end Riemannian
end Geometry
end DifferentialGeometry

end
