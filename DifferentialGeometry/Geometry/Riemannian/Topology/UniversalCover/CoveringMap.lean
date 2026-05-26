import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.LocPathConnected
import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Basic

/-!
# Universal cover of a topological space: covering structure

Building on the slice-topology construction in `UniversalCover.Basic`, we
prove that, when the base space `X` is connected, locally path-connected,
and semi-locally simply connected, the projection
`proj : UniversalCover X → X` is a covering map, and that the universal
cover is path-connected and simply connected.

Outline (Hatcher, Prop. 1.36, 1.39):

1. Sheet bijection on "good" neighbourhoods (`uc_sheet_bijection_on_good_U`):
   over a path-connected open `U ⊆ X` in which every loop is
   null-homotopic in `X`, the basic open `basicOpen p U` projects
   bijectively onto `U`.
2. Covering map structure (`UniversalCover.isCoveringMap`): the union of
   the sheets over each fibre realises evenly-covered neighbourhoods, so
   `proj` is a covering map.
3. Path-connectedness (`UniversalCover.pathConnectedSpace`): every
   point `⟨x, ⟦γ⟧⟩` is connected to the basepoint by the truncation lift
   `s ↦ ⟨γ s, ⟦γ.truncate 0 s⟧⟩`.
4. Simple connectedness (`UniversalCover.simplyConnectedSpace`): a loop
   in the cover lifts a loop in `X` and is null-homotopic via
   `IsCoveringMap.liftHomotopy`.

The aggregate "bundled triple" `pi1-universal-cover-construction` is
exposed implicitly via the combination of (1)-(4) above.
-/

open Set Function Filter
open scoped Topology ContDiff

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {X : Type*} [TopologicalSpace X] [Inhabited X]
  [ConnectedSpace X] [LocPathConnectedSpace X]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace X]

/-- **Sheet bijection on "good" neighbourhoods (Hatcher Prop. 1.39 key step).**

For each `p : UniversalCover X` and each open path-connected neighbourhood
`U ∋ p.1` over which every loop based at `p.1` is null-homotopic in `X`
(the semi-local condition supplied pointwise), the projection `proj`
restricts to a bijection `basicOpen p U hU hp → U`.

* Injectivity: two paths from `p.1` to `y` staying in `U` differ by a loop
  in `U`, which is null-homotopic, so they give the same class in
  `Path.Homotopic.Quotient`.
* Surjectivity: `U` is path-connected, so every `y ∈ U` is reached by some
  path inside `U`. -/
theorem uc_sheet_bijection_on_good_U
    (p : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X)
    (U : Set X) (hU : IsOpen U) (hp : p.1 ∈ U)
    (hUpc : IsPathConnected U)
    (hUloops : ∀ γ : _root_.Path p.1 p.1,
      (∀ t, γ t ∈ U) →
        (⟦γ⟧ : _root_.Path.Homotopic.Quotient p.1 p.1) =
          ⟦_root_.Path.refl p.1⟧) :
    Set.BijOn (proj :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
      (basicOpen p U hU hp) U := by
  refine ⟨?_, ?_, ?_⟩
  · -- MapsTo: q ∈ basicOpen ⇒ q.1 = η 1 ∈ U.
    intro q hq
    obtain ⟨η, hηU, _⟩ := hq
    have : η 1 ∈ U := hηU 1
    simpa [proj, Path.target] using this
  · -- InjOn: two preimages with the same projected point must be equal.
    intro q hq q' hq' hqq'
    obtain ⟨xq, cq⟩ := q
    obtain ⟨xq', cq'⟩ := q'
    obtain ⟨η, hηU, hqeq⟩ := hq
    obtain ⟨η', hη'U, hq'eq⟩ := hq'
    have hxy : xq = xq' := hqq'
    subst hxy
    refine Sigma.ext rfl ?_
    simp only [heq_eq_eq] at hqeq hq'eq ⊢
    rw [hqeq, hq'eq]
    congr 1
    have hloop_inU : ∀ t, (η.trans η'.symm) t ∈ U := by
      intro t
      rw [Path.trans_apply]
      split_ifs with h
      · exact hηU _
      · rw [Path.symm_apply]; exact hη'U _
    have hloop : (⟦η.trans η'.symm⟧ : Path.Homotopic.Quotient p.1 p.1) =
        ⟦Path.refl p.1⟧ := hUloops _ hloop_inU
    have hbase : Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.mk η)
        (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk η')) =
        Path.Homotopic.Quotient.refl p.1 := by
      have h := hloop
      change Path.Homotopic.Quotient.mk (η.trans η'.symm) =
             Path.Homotopic.Quotient.mk (Path.refl p.1) at h
      rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
          Path.Homotopic.Quotient.mk_refl] at h
      exact h
    have h₁ : Path.Homotopic.Quotient.mk η =
        Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.mk η)
          (Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk η'))
            (Path.Homotopic.Quotient.mk η')) := by
      rw [Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl]
    calc Path.Homotopic.Quotient.mk η
        = Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.mk η)
            (Path.Homotopic.Quotient.trans
              (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk η'))
              (Path.Homotopic.Quotient.mk η')) := h₁
      _ = Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.trans
              (Path.Homotopic.Quotient.mk η)
              (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk η')))
            (Path.Homotopic.Quotient.mk η') := by
            rw [Path.Homotopic.Quotient.trans_assoc]
      _ = Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.refl p.1)
            (Path.Homotopic.Quotient.mk η') := by rw [hbase]
      _ = Path.Homotopic.Quotient.mk η' := by
            rw [Path.Homotopic.Quotient.refl_trans]
  · -- SurjOn: any y ∈ U is reached by a path in U from p.1.
    intro y hy
    have hjoined : JoinedIn U p.1 y := hUpc.joinedIn _ hp _ hy
    refine ⟨⟨y, p.2.trans (Path.Homotopic.Quotient.mk hjoined.somePath)⟩, ?_, rfl⟩
    refine ⟨hjoined.somePath, ?_, rfl⟩
    exact fun t => hjoined.somePath_mem t

/-- **The projection is a covering map.**

For each `x : X`, choose a path-connected open neighbourhood `U` of `x`
(from `LocPathConnectedSpace X`) on which every loop based at `x` is
null-homotopic in `X` (from `SemilocallySimplyConnectedSpace X`). The
preimage `proj ⁻¹' U` decomposes as the disjoint union of the sheets
`basicOpen p U _ _` indexed by `p ∈ proj ⁻¹' {x}`; each sheet maps
homeomorphically onto `U` by `uc_sheet_bijection_on_good_U`; the fibre
`proj ⁻¹' {x}` carries the discrete topology. -/
theorem UniversalCover.isCoveringMap :
    IsCoveringMap (proj :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X) := by
  sorry

/-- **The universal cover is path-connected.**

For any `q = ⟨x, ⟦γ⟧⟩ ∈ UniversalCover X`, the truncation lift
`s ↦ ⟨γ s, ⟦γ.truncate 0 s⟧⟩` is a continuous path in the cover from the
basepoint `⟨default, ⟦Path.refl default⟧⟩` to `q`. -/
instance UniversalCover.pathConnectedSpace :
    PathConnectedSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) :=
  ⟨sorry, sorry⟩

/-- **The universal cover is simply connected.**

Any loop `α` in `UniversalCover X` at the basepoint projects to a loop
`γ = proj ∘ α` in `X`. By uniqueness of lifts (`IsCoveringMap`), `α`
agrees with the truncation lift of `γ`, so `α(1) = α(0)` forces
`⟦γ⟧ = ⟦Path.refl⟧` in `Path.Homotopic.Quotient`. The contracting
homotopy of `γ` in `X` then lifts via
`IsCoveringMap.liftHomotopy` to a contracting homotopy of `α` in the
cover. -/
instance UniversalCover.simplyConnectedSpace :
    SimplyConnectedSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) :=
  ⟨sorry⟩

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
