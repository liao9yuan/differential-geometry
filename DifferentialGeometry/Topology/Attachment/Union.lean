import DifferentialGeometry.Topology.Attachment.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Separation.Hausdorff

namespace DifferentialGeometry.Topology

universe u v

open Filter Function Set

section UnionRealization

variable {Y : Type v} [TopologicalSpace Y] {n : ℕ}

def adjunctionUnionMap (X₀ : Set Y) (c : ClosedCell n → Y) :
    ClosedCell n ⊕ X₀ → {y : Y // y ∈ X₀ ∪ Set.range c} :=
  Sum.elim (fun d => ⟨c d, Or.inr ⟨d, rfl⟩⟩) (fun x => ⟨x, Or.inl x.2⟩)

omit [TopologicalSpace Y] in
theorem adjunctionUnionMap_rel {X₀ : Set Y} (c : ClosedCell n → Y) {φ : CellBoundary n → X₀}
    (hφ : ∀ b, (φ b : Y) = c (cellBoundaryInclusion n b)) :
    ∀ a b : ClosedCell n ⊕ X₀, adjunctionRel n φ a b →
      adjunctionUnionMap X₀ c a = adjunctionUnionMap X₀ c b := by
  intro a b h
  rcases h with ⟨x, hx | hx⟩
  · rcases hx with ⟨ha, hb⟩
    subst a
    subst b
    apply Subtype.ext
    exact (hφ x).symm
  · rcases hx with ⟨hb, ha⟩
    subst a
    subst b
    apply Subtype.ext
    exact hφ x

def adjunctionRealization (X₀ : Set Y) (c : ClosedCell n → Y) (φ : CellBoundary n → X₀)
    (hφ : ∀ b, (φ b : Y) = c (cellBoundaryInclusion n b)) :
    AdjunctionSpace n φ → {y : Y // y ∈ X₀ ∪ Set.range c} :=
  Quot.lift (adjunctionUnionMap X₀ c) (adjunctionUnionMap_rel c hφ)

theorem continuous_adjunctionUnionMap {X₀ : Set Y} (c : ClosedCell n → Y) (hc : Continuous c) :
    Continuous (adjunctionUnionMap X₀ c) := by
  dsimp [adjunctionUnionMap]
  exact Continuous.sumElim (hc.codRestrict (fun d => Or.inr ⟨d, rfl⟩))
    (continuous_subtype_val.codRestrict (fun x : X₀ => Or.inl x.2))

theorem continuous_adjunctionRealization {X₀ : Set Y} (c : ClosedCell n → Y)
    (φ : CellBoundary n → X₀)
    (hφ : ∀ b, (φ b : Y) = c (cellBoundaryInclusion n b)) (hc : Continuous c) :
    Continuous (adjunctionRealization X₀ c φ hφ) := by
  dsimp [adjunctionRealization]
  exact continuous_quot_lift (adjunctionUnionMap_rel c hφ)
    (continuous_adjunctionUnionMap c hc)

omit [TopologicalSpace Y] in
theorem adjunctionRealization_surjective {X₀ : Set Y} (c : ClosedCell n → Y)
    (φ : CellBoundary n → X₀)
    (hφ : ∀ b, (φ b : Y) = c (cellBoundaryInclusion n b)) :
    Function.Surjective (adjunctionRealization X₀ c φ hφ) := by
  intro ⟨y, hy⟩
  rcases hy with hy₀ | ⟨d, hd⟩
  · refine ⟨Quot.mk (adjunctionRel n φ) (Sum.inr ⟨y, hy₀⟩), ?_⟩
    apply Subtype.ext
    rfl
  · refine ⟨Quot.mk (adjunctionRel n φ) (Sum.inl d), ?_⟩
    apply Subtype.ext
    exact hd

omit [TopologicalSpace Y] in
private theorem adjunctionRealization_inl_inr {X₀ : Set Y} (c : ClosedCell n → Y)
    (φ : CellBoundary n → X₀)
    (hφ : ∀ b, (φ b : Y) = c (cellBoundaryInclusion n b))
    (hinterior : Disjoint (c '' Set.range (cellInteriorInclusion n)) X₀) {d : ClosedCell n}
    {x : X₀} (h : adjunctionUnionMap X₀ c (Sum.inl d) = adjunctionUnionMap X₀ c (Sum.inr x)) :
    Quot.mk (adjunctionRel n φ) (Sum.inl d) = Quot.mk (adjunctionRel n φ) (Sum.inr x) := by
  have hcd : c d = (x : Y) := congrArg Subtype.val h
  have hx₀ : c d ∈ X₀ := by
    rw [hcd]
    exact x.2
  have hnot : ¬ ‖(d : EuclideanSpace ℝ (Fin n))‖ < 1 := by
    intro hlt
    have hmem : c d ∈ c '' Set.range (cellInteriorInclusion n) :=
      ⟨cellInteriorInclusion n (⟨d, hlt⟩ : CellInterior n),
        ⟨⟨(⟨d, hlt⟩ : CellInterior n), rfl⟩, congrArg c (by ext; rfl)⟩⟩
    exact (Set.disjoint_left.mp hinterior) hmem hx₀
  have hEq : ‖(d : EuclideanSpace ℝ (Fin n))‖ = 1 := le_antisymm d.2 (le_of_not_gt hnot)
  let b : CellBoundary n := ⟨d, hEq⟩
  have hb : cellBoundaryInclusion n b = d := by
    ext
    rfl
  calc
    Quot.mk (adjunctionRel n φ) (Sum.inl d) = Quot.mk (adjunctionRel n φ) (Sum.inr (φ b)) := by
      rw [← hb]
      exact Quot.sound ⟨b, Or.inl ⟨rfl, rfl⟩⟩
    _ = Quot.mk (adjunctionRel n φ) (Sum.inr x) := by
      apply congrArg (fun t : X₀ => Quot.mk (adjunctionRel n φ) (Sum.inr t))
      apply Subtype.ext
      calc
        (φ b : Y) = c (cellBoundaryInclusion n b) := hφ b
        _ = c d := by rw [hb]
        _ = (x : Y) := hcd

omit [TopologicalSpace Y] in
theorem adjunctionRealization_injective {X₀ : Set Y} (c : ClosedCell n → Y)
    (φ : CellBoundary n → X₀)
    (hφ : ∀ b, (φ b : Y) = c (cellBoundaryInclusion n b)) (hc : Function.Injective c)
    (hinterior : Disjoint (c '' Set.range (cellInteriorInclusion n)) X₀) :
    Function.Injective (adjunctionRealization X₀ c φ hφ) := by
  intro z z' hzz'
  rcases Quot.exists_rep z with ⟨a, rfl⟩
  rcases Quot.exists_rep z' with ⟨b, rfl⟩
  change adjunctionUnionMap X₀ c a = adjunctionUnionMap X₀ c b at hzz'
  cases a with
  | inl d =>
      cases b with
      | inl d' =>
          exact congrArg (fun d : ClosedCell n => Quot.mk (adjunctionRel n φ) (Sum.inl d))
            (hc (congrArg Subtype.val hzz'))
      | inr x =>
          exact adjunctionRealization_inl_inr c φ hφ hinterior hzz'
  | inr x =>
      cases b with
      | inl d =>
          exact (adjunctionRealization_inl_inr c φ hφ hinterior hzz'.symm).symm
      | inr x' =>
          apply congrArg (fun t : X₀ => Quot.mk (adjunctionRel n φ) (Sum.inr t))
          ext
          simpa [adjunctionUnionMap] using congrArg Subtype.val hzz'

private def unionInclusionLeft (A B : Set Y) : {y : Y // y ∈ A} → {y : Y // y ∈ A ∪ B} :=
  fun y => ⟨y, Or.inl y.2⟩

private def unionInclusionRight (A B : Set Y) : {y : Y // y ∈ B} → {y : Y // y ∈ A ∪ B} :=
  fun y => ⟨y, Or.inr y.2⟩

private theorem isClosed_image_of_isClosed_preimage_unionInclusionLeft {A B : Set Y}
    (hA : IsClosed A) {W : Set {y : Y // y ∈ A ∪ B}}
    (hW : IsClosed (unionInclusionLeft A B ⁻¹' W)) :
    IsClosed (unionInclusionLeft A B '' (unionInclusionLeft A B ⁻¹' W)) := by
  rw [isClosed_induced_iff] at hW
  rcases hW with ⟨u, hu, huW⟩
  have hset : unionInclusionLeft A B '' (unionInclusionLeft A B ⁻¹' W) =
      Subtype.val ⁻¹' (u ∩ A) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      have hxy' : (x : Y) = (y : Y) := by
        simpa [unionInclusionLeft] using congrArg Subtype.val hxy
      have hyA : (y : Y) ∈ A := by
        rw [← hxy']
        exact x.2
      have hxu : (x : Y) ∈ u := by
        have hx' : x ∈ Subtype.val ⁻¹' u := by
          simpa [huW] using hx
        exact hx'
      exact ⟨by simpa [hxy'] using hxu, hyA⟩
    · intro hy
      rcases hy with ⟨hyu, hyA⟩
      refine ⟨⟨y, hyA⟩, ?_, ?_⟩
      · have hx' : (⟨y, hyA⟩ : {y : Y // y ∈ A}) ∈ Subtype.val ⁻¹' u := hyu
        simpa [huW] using hx'
      · apply Subtype.ext
        rfl
  rw [hset]
  exact (hu.inter hA).preimage continuous_subtype_val

private theorem isClosed_image_of_isClosed_preimage_unionInclusionRight {A B : Set Y}
    (hB : IsClosed B) {W : Set {y : Y // y ∈ A ∪ B}}
    (hW : IsClosed (unionInclusionRight A B ⁻¹' W)) :
    IsClosed (unionInclusionRight A B '' (unionInclusionRight A B ⁻¹' W)) := by
  rw [isClosed_induced_iff] at hW
  rcases hW with ⟨u, hu, huW⟩
  have hset : unionInclusionRight A B '' (unionInclusionRight A B ⁻¹' W) =
      Subtype.val ⁻¹' (u ∩ B) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      have hxy' : (x : Y) = (y : Y) := by
        simpa [unionInclusionRight] using congrArg Subtype.val hxy
      have hyB : (y : Y) ∈ B := by
        rw [← hxy']
        exact x.2
      have hxu : (x : Y) ∈ u := by
        have hx' : x ∈ Subtype.val ⁻¹' u := by
          simpa [huW] using hx
        exact hx'
      exact ⟨by simpa [hxy'] using hxu, hyB⟩
    · intro hy
      rcases hy with ⟨hyu, hyB⟩
      refine ⟨⟨y, hyB⟩, ?_, ?_⟩
      · have hx' : (⟨y, hyB⟩ : {y : Y // y ∈ B}) ∈ Subtype.val ⁻¹' u := hyu
        simpa [huW] using hx'
      · apply Subtype.ext
        rfl
  rw [hset]
  exact (hu.inter hB).preimage continuous_subtype_val

private theorem isClosed_union_of_isClosed_preimage {A B : Set Y} (hA : IsClosed A)
    (hB : IsClosed B) {W : Set {y : Y // y ∈ A ∪ B}}
    (hWA : IsClosed (unionInclusionLeft A B ⁻¹' W))
    (hWB : IsClosed (unionInclusionRight A B ⁻¹' W)) : IsClosed W := by
  have hset : W = unionInclusionLeft A B '' (unionInclusionLeft A B ⁻¹' W) ∪
        unionInclusionRight A B '' (unionInclusionRight A B ⁻¹' W) := by
    ext y
    constructor
    · intro hy
      rcases y.2 with hyA | hyB
      · exact Or.inl ⟨⟨y, hyA⟩, ⟨by simpa [unionInclusionLeft] using hy, by ext; rfl⟩⟩
      · exact Or.inr ⟨⟨y, hyB⟩, ⟨by simpa [unionInclusionRight] using hy, by ext; rfl⟩⟩
    · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
      · rw [← hx.2]
        exact hx.1
      · rw [← hx.2]
        exact hx.1
  rw [hset]
  exact (isClosed_image_of_isClosed_preimage_unionInclusionLeft hA hWA).union
    (isClosed_image_of_isClosed_preimage_unionInclusionRight hB hWB)

omit [TopologicalSpace Y] in
private theorem adjunctionRealization_leftPreimage_eq {X₀ : Set Y} (c : ClosedCell n → Y)
    (φ : CellBoundary n → X₀) (hφ : ∀ b, (φ b : Y) = c (cellBoundaryInclusion n b))
    (hc : Function.Injective c) (hinterior : Disjoint (c '' Set.range (cellInteriorInclusion n)) X₀)
    {C : Set (AdjunctionSpace n φ)} :
    unionInclusionLeft X₀ (Set.range c) ⁻¹' (adjunctionRealization X₀ c φ hφ '' C) =
      Sum.inr ⁻¹' (adjunctionMk n φ ⁻¹' C) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨z, hzC, hz⟩
    have hinj := adjunctionRealization_injective c φ hφ hc hinterior
    have hz' : z = Quot.mk (adjunctionRel n φ) (Sum.inr x) :=
      hinj (by
        calc
          adjunctionRealization X₀ c φ hφ z = ⟨x, Or.inl x.2⟩ := hz
          _ = adjunctionRealization X₀ c φ hφ (Quot.mk (adjunctionRel n φ) (Sum.inr x)) := by
            simp [adjunctionRealization, adjunctionUnionMap])
    rw [hz'] at hzC
    exact hzC
  · intro hx
    refine ⟨Quot.mk (adjunctionRel n φ) (Sum.inr x), hx, ?_⟩
    rfl

omit [TopologicalSpace Y] in
private theorem adjunctionRealization_rightPreimage_eq {X₀ : Set Y} (c : ClosedCell n → Y)
    (φ : CellBoundary n → X₀) (hφ : ∀ b, (φ b : Y) = c (cellBoundaryInclusion n b))
    (hc : Function.Injective c) (hinterior : Disjoint (c '' Set.range (cellInteriorInclusion n)) X₀)
    {C : Set (AdjunctionSpace n φ)} :
    unionInclusionRight X₀ (Set.range c) ⁻¹' (adjunctionRealization X₀ c φ hφ '' C) =
      (fun d : ClosedCell n => ⟨c d, ⟨d, rfl⟩⟩) '' (Sum.inl ⁻¹' (adjunctionMk n φ ⁻¹' C)) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨z, hzC, hz⟩
    have hd₀ : ∃ d : ClosedCell n, c d = (y : Y) := y.2
    let d₀ : ClosedCell n := Classical.choose hd₀
    have hd₀spec : c d₀ = (y : Y) := Classical.choose_spec hd₀
    have hinj := adjunctionRealization_injective c φ hφ hc hinterior
    have hz' : z = Quot.mk (adjunctionRel n φ) (Sum.inl d₀) :=
      hinj (by
        calc
          adjunctionRealization X₀ c φ hφ z = ⟨y, Or.inr y.2⟩ := hz
          _ = adjunctionRealization X₀ c φ hφ (Quot.mk (adjunctionRel n φ) (Sum.inl d₀)) := by
            simp [adjunctionRealization, adjunctionUnionMap, hd₀spec])
    have hd₀C : Quot.mk (adjunctionRel n φ) (Sum.inl d₀) ∈ C := by
      rw [← hz']
      exact hzC
    refine ⟨d₀, hd₀C, ?_⟩
    apply Subtype.ext
    exact hd₀spec
  · intro hy
    rcases hy with ⟨d, hdC, hdy⟩
    refine ⟨Quot.mk (adjunctionRel n φ) (Sum.inl d), hdC, ?_⟩
    change adjunctionUnionMap X₀ c (Sum.inl d) = ⟨y, Or.inr y.2⟩
    have hdy' : c d = (y : Y) := congrArg Subtype.val hdy
    dsimp [adjunctionUnionMap]
    apply Subtype.ext
    exact hdy'

theorem adjunctionRealization_isClosedMap {X₀ : Set Y} (c : ClosedCell n → Y)
    (φ : CellBoundary n → X₀)
    (hφ : ∀ b, (φ b : Y) = c (cellBoundaryInclusion n b)) (hc : Function.Injective c)
    (hcont : Continuous c) (hinterior : Disjoint (c '' Set.range (cellInteriorInclusion n)) X₀)
    (hclosed : IsClosed X₀) [T2Space Y] :
    IsClosedMap (adjunctionRealization X₀ c φ hφ) := by
  intro C hC
  let Q : Set (ClosedCell n ⊕ X₀) := adjunctionMk n φ ⁻¹' C
  have hQ : IsClosed Q := hC.preimage (continuous_adjunctionMk n φ)
  have hPc : IsClosed (Sum.inl ⁻¹' Q) := hQ.preimage continuous_inl
  have hPx : IsClosed (Sum.inr ⁻¹' Q) := hQ.preimage continuous_inr
  have hclosedRange : IsClosed (Set.range c) := by
    rw [← image_univ]
    exact (isCompact_univ.image hcont).isClosed
  refine isClosed_union_of_isClosed_preimage hclosed hclosedRange ?_ ?_
  · rw [adjunctionRealization_leftPreimage_eq c φ hφ hc hinterior]
    exact hPx
  · rw [adjunctionRealization_rightPreimage_eq c φ hφ hc hinterior]
    let c' : ClosedCell n → Set.range c := fun d => ⟨c d, ⟨d, rfl⟩⟩
    have hc'inj : Function.Injective c' := by
      intro d d' h
      apply hc
      exact congrArg Subtype.val h
    have hc'surj : Function.Surjective c' := by
      intro y
      rcases y.2 with ⟨d, hd⟩
      refine ⟨d, ?_⟩
      apply Subtype.ext
      exact hd
    have hc'cont : Continuous c' := hcont.codRestrict (fun d => show c d ∈ Set.range c from ⟨d, rfl⟩)
    let hc'homeo : ClosedCell n ≃ₜ Set.range c :=
      Continuous.homeoOfEquivCompactToT2
        (f := Equiv.ofBijective c' ⟨hc'inj, hc'surj⟩) hc'cont
    have hc'closedMap : IsClosedMap c' := by
      change IsClosedMap (fun d : ClosedCell n => (hc'homeo d : Set.range c))
      exact hc'homeo.isClosedMap
    exact hc'closedMap (Sum.inl ⁻¹' Q) hPc

noncomputable def adjunctionHomeomorphUnionImage {X₀ : Set Y} (c : ClosedCell n → Y)
    (φ : CellBoundary n → X₀) (hφ : ∀ b, (φ b : Y) = c (cellBoundaryInclusion n b))
    (hc : Function.Injective c) (hcont : Continuous c)
    (hinterior : Disjoint (c '' Set.range (cellInteriorInclusion n)) X₀)
    (hclosed : IsClosed X₀) [T2Space Y] :
    AdjunctionSpace n φ ≃ₜ {y : Y // y ∈ X₀ ∪ Set.range c} := by
  let f : AdjunctionSpace n φ → {y : Y // y ∈ X₀ ∪ Set.range c} :=
    adjunctionRealization X₀ c φ hφ
  have hfcont : Continuous f := continuous_adjunctionRealization c φ hφ hcont
  have hfclosed : IsClosedMap f := adjunctionRealization_isClosedMap c φ hφ hc hcont hinterior hclosed
  have hfinj : Function.Injective f := adjunctionRealization_injective c φ hφ hc hinterior
  have hfsurj : Function.Surjective f := adjunctionRealization_surjective c φ hφ
  exact IsHomeomorph.homeomorph (f := f)
    (isHomeomorph_iff_continuous_isClosedMap_bijective.mpr ⟨hfcont, hfclosed, ⟨hfinj, hfsurj⟩⟩)

end UnionRealization

end DifferentialGeometry.Topology
