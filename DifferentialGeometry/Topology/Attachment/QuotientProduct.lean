import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Maps.Basic

namespace DifferentialGeometry.Topology

universe u v w

open Filter
open scoped Filter
open scoped Topology

theorem isOpen_setOf_prod_subset {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {P : Set (X × Y)} (hP : IsOpen P) {K : Set Y} (hK : IsCompact K) :
    IsOpen {x : X | {x} ×ˢ K ⊆ P} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  have hPx : ∀ k ∈ K, P ∈ nhds (x, k) := by
    intro k hk
    exact hP.mem_nhds (hx (by simpa [Set.mem_prod] using hk))
  have hbox : ∀ k : K, ∃ U : Set X, ∃ W : Set Y,
      U ∈ nhds x ∧ W ∈ nhds (k : Y) ∧ U ×ˢ W ⊆ P := by
    intro k
    rcases mem_nhds_prod_iff.mp (hPx k.1 k.2) with ⟨U, hU, W, hW, hUW⟩
    exact ⟨U, W, hU, hW, hUW⟩
  choose U W hU hW hUW using hbox
  have hcover : K ⊆ ⋃ k : K, interior (W k) := by
    intro k hk
    exact Set.mem_iUnion.mpr ⟨⟨k, hk⟩, mem_interior_iff_mem_nhds.mpr (hW ⟨k, hk⟩)⟩
  rcases hK.elim_finite_subcover (fun k : K => interior (W k)) (fun k => isOpen_interior) hcover
    with ⟨t, hKt⟩
  let V : Set X := ⋂ k : {k : K // k ∈ (t : Set K)}, interior (U (k : K))
  have hVopen : IsOpen V := isOpen_iInter_of_finite
    (fun k : {k : K // k ∈ (t : Set K)} => isOpen_interior)
  have hxV : x ∈ V := by
    dsimp [V]
    rw [Set.mem_iInter]
    intro k
    exact mem_interior_iff_mem_nhds.mpr (hU (k : K))
  have hVsub : V ⊆ {x : X | {x} ×ˢ K ⊆ P} := by
    intro x' hx'
    dsimp [V] at hx'
    rw [Set.mem_iInter] at hx'
    intro k hk
    rcases Set.mem_prod.mp hk with ⟨hx'1, hkK⟩
    rcases Set.mem_iUnion₂.mp (hKt hkK) with ⟨k₀, hk₀t, hk₀W⟩
    have hx'1eq : k.1 = x' := by simpa using hx'1
    have hx'U : k.1 ∈ U k₀ := by
      simpa [hx'1eq] using (interior_subset (hx' ⟨k₀, hk₀t⟩))
    exact hUW k₀ ⟨hx'U, interior_subset hk₀W⟩
  exact ⟨V, ⟨hVsub, ⟨hVopen, hxV⟩⟩⟩

private theorem isQuotientMap_prodMap_swap {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [LocallyCompactSpace X]
    {f : Y → Z} (hf : Topology.IsQuotientMap f) :
    Topology.IsQuotientMap (Prod.map f (id : X → X)) := by
  rw [Topology.isQuotientMap_iff]
  constructor
  · intro ⟨z, x⟩
    rcases hf.surjective z with ⟨y, rfl⟩
    exact ⟨(y, x), rfl⟩
  · intro s
    constructor
    · intro hs
      exact IsOpen.preimage (f := Prod.map f (id : X → X)) (t := s)
        (hf.continuous.prodMap continuous_id) hs
    · intro hs
      rw [isOpen_iff_forall_mem_open]
      intro zx hzx
      rcases zx with ⟨z, x⟩
      rcases hf.surjective z with ⟨y, rfl⟩
      have hP : IsOpen ((Prod.map f (id : X → X)) ⁻¹' s) := hs
      have hxy : (y, x) ∈ (Prod.map f (id : X → X)) ⁻¹' s := by
        simpa using hzx
      rcases isOpen_prod_iff.mp hP y x hxy with ⟨V, W, hVopen, hWopen, hyV, hxW, hVW⟩
      rcases (compact_basis_nhds x).mem_iff.mp (hWopen.mem_nhds hxW) with ⟨K, hK, hKW⟩
      rcases hK with ⟨hKnh, hKc⟩
      have hKx : x ∈ interior K := mem_interior_iff_mem_nhds.mpr hKnh
      let S : Set Y := {y' : Y | {y'} ×ˢ K ⊆ (Prod.map f (id : X → X)) ⁻¹' s}
      have hSopen : IsOpen S := isOpen_setOf_prod_subset hP hKc
      have hyS : y ∈ S := by
        intro k hk
        rcases Set.mem_prod.mp hk with ⟨hky, hkK⟩
        have hk1_eq : k.1 = y := by simpa using hky
        have hk1V : k.1 ∈ V := by simpa [hk1_eq] using hyV
        exact hVW (Set.mem_prod.mpr (And.intro hk1V (hKW hkK)))
      have hSsat : ∀ ⦃y₁ y₂ : Y⦄, f y₁ = f y₂ → y₁ ∈ S → y₂ ∈ S := by
        intro y₁ y₂ hfy hy₁ k hk
        rcases Set.mem_prod.mp hk with ⟨hk1, hkK⟩
        have hk1eq : k.1 = y₂ := by simpa using hk1
        have h₁ : (y₁, k.2) ∈ (Prod.map f (id : X → X)) ⁻¹' s := by
          exact hy₁ (Set.mem_prod.mpr (And.intro (by simp) hkK))
        have h₂ : (f y₁, k.2) = (f y₂, k.2) := by rw [hfy]
        have h₃ : (y₂, k.2) ∈ (Prod.map f (id : X → X)) ⁻¹' s := by
          simpa [h₂] using h₁
        change (f k.1, k.2) ∈ s
        simpa [hk1eq] using h₃
      have hfSopen : IsOpen (f '' S) := by
        have hopen : ∀ t : Set Z, IsOpen t ↔ IsOpen (f ⁻¹' t) :=
          (Topology.isQuotientMap_iff.mp hf).2
        have hpre : f ⁻¹' (f '' S) = S := by
          apply Set.Subset.antisymm
          · intro y hy
            rcases (Set.mem_image f S (f y)).mp (Set.mem_preimage.mp hy) with ⟨y₁, hy₁, hfy⟩
            exact hSsat hfy hy₁
          · intro y hy
            exact Set.mem_preimage.mpr ((Set.mem_image f S (f y)).mpr ⟨y, hy, rfl⟩)
        rw [hopen]
        rwa [hpre]
      refine ⟨(f '' S) ×ˢ interior K, ?_, ?_⟩
      · intro p hp
        rcases p with ⟨z', k⟩
        rcases Set.mem_prod.mp hp with ⟨hz', hk⟩
        rcases (Set.mem_image f S z').mp hz' with ⟨y', hy', rfl⟩
        exact Set.mem_preimage.mp (hy' (Set.mem_prod.mpr
          (And.intro (show (y', k).1 ∈ ({y'} : Set Y) from by simp) (interior_subset hk))))
      · constructor
        · exact IsOpen.prod hfSopen isOpen_interior
        · exact Set.mem_prod.mpr (And.intro ⟨y, hyS, rfl⟩ hKx)

theorem isQuotientMap_prodMap {X : Type u} {Y : Type v} {Z : Type w} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] [LocallyCompactSpace X] {f : Y → Z}
    (hf : Topology.IsQuotientMap f) :
    Topology.IsQuotientMap (Prod.map (id : X → X) f) := by
  have hswap : Topology.IsQuotientMap (Prod.map f (id : X → X)) := isQuotientMap_prodMap_swap hf
  have hcomp : (fun p : Z × X => Prod.swap p) ∘ Prod.map f (id : X → X) ∘
      (fun p : X × Y => Prod.swap p) = Prod.map (id : X → X) f := by
    funext p
    rcases p with ⟨x, y⟩
    rfl
  rw [← hcomp]
  exact Topology.IsQuotientMap.comp
    (Homeomorph.prodComm Z X).isQuotientMap
    (Topology.IsQuotientMap.comp hswap (Homeomorph.prodComm X Y).isQuotientMap)

theorem continuous_quot_lift_prod {X : Type u} {Y : Type v} {Z : Type w} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] [LocallyCompactSpace X] {r : Y → Y → Prop}
    {f : X × Y → Z} (hr : ∀ x a b, r a b → f (x, a) = f (x, b)) (hf : Continuous f) :
    Continuous (fun p : X × Quot r => Quot.lift (fun y : Y => f (p.1, y)) (hr p.1) p.2) := by
  have hq : Topology.IsQuotientMap (Prod.map (id : X → X) (Quot.mk r)) :=
    isQuotientMap_prodMap (f := Quot.mk r) (isQuotientMap_quot_mk)
  refine (hq.continuous_iff).2 ?_
  have hcomp : (fun p : X × Y =>
      Quot.lift (fun y : Y => f (p.1, y)) (hr p.1) (Quot.mk r p.2)) = f := by
    funext p
    rfl
  simpa [Function.comp, hcomp]

end DifferentialGeometry.Topology
