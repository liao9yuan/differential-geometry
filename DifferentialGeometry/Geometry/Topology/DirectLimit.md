# DirectLimit.lean — sequential topological direct limit (MSM135 Ch4 F9–F13)

Target: the "Review of direct limits" subsection of MSM135 Ch4 (`lbl376`–`lbl381`,
book L603–780), the topology feeding Step D's limit manifold `M∞` (D3) for
`metricCompactness` (Thm 3.9). CHAPTER4_PLAN items **F9–F13**.

## Mathlib audit (2026-06-09)
No sequential topological direct limit exists: `Topology/Gluing.lean` is categorical
TopCat gluing along opens (different shape); algebraic `DirectLimit`/`DirectedSystem`
are Module/Ring-level. Build natively here (pure topology layer `Geometry/Topology/`).

## Design
Mathlib-style full-system input (like the algebraic `DirectedSystem`), bundled:

- `SeqSystem A`: data `F : ∀ {k ℓ}, k ≤ ℓ → A k → A ℓ` + `map_self` + `map_map`
  + `isOpenEmb : ∀ h, IsOpenEmbedding (F h)`. (Single-step `f k : A k → A (k+1)`
  builder via `Nat.leRecOn` deferred — the full system avoids the equation-lemma
  grind and is what the proofs use.)
- Relation on `Σ k, A k`: `⟨k,x⟩ ≈ ⟨ℓ,y⟩ ↔ ∃ m hk hℓ, F hk x = F hℓ y` (common
  target form — transitively closed; transitivity via `map_map` + push to `max`,
  proof-irrelevance identifies the two `≤`-proofs).
- `Lim := Quotient setoid`, topology = quotient of sigma (instances automatic).
- `incl ℓ := mk ∘ Sigma.mk ℓ`; book lemmas:
  F9: `incl_comp` (Iₗ = I_m ∘ F), `incl_injective`;
  F10: `incl_isOpenMap` (fiberwise: preimage = ⋃_{p≥max} F⁻¹(F''U), open) ⟹
       `incl_isOpenEmbedding`; cover `exists_incl_eq` (every point hit);
  F11 `lbl379`: compact K ⟹ K = incl k '' Kk, Kk compact (monotone open cover +
       finite subcover + embedding compactness transfer);
  F12 `lbl380`: σ-compact (countable union of incl-images of compacts);
       second-countability deferred (book's "in particular" needs locally-2nd-ctble
       glue; derive at the manifold level later if needed);
  F13 `lbl381`: T2 (lift two points to a common stage, separate, push by open incl);
  universal property: `lift ψ hψ : Lim → X` + `lift_incl` + `continuous_lift`
  (Step D will define the limit metric through it).

## Status — F9–F13 COMPLETE + verified + sorry-free + axiom-clean (2026-06-09)

All in `DirectLimit.lean`, namespace `DifferentialGeometry.SeqSystem`:
- F9: `SeqSystem` (bundled system), `Rel`/`setoid` (common-target relation; transitivity
  via `map_map` + push-to-max + definitional proof irrelevance), `Lim` (quotient,
  topology automatic), `incl`, `incl_comp` (Iₖ = Iₗ∘F), `incl_injective`,
  `exists_incl_eq` (lbl381(1)).
- F10: `incl_isOpenMap` (the saturation-fiber computation
  `mk⁻¹(Iₗ(U)) ∩ A_m = ⋃_{p≥m,ℓ} F⁻¹(F(U))` via `isOpen_coinduced` + `isOpen_sigma_iff`),
  `incl_isOpenEmb`, `range_incl_mono`, `iUnion_range_incl` (monotone open cover).
- F11 `lbl379`: `isCompact_exists` (finite subcover + `Finset.sup` + embedding
  compactness transfer `IsEmbedding.isCompact_iff`).
- F12 `lbl380`: `sigmaCompact` (pairing `Nat.pair/unpair` over `compactCovering`).
- F13 `lbl381`: `t2Space` (lift to common stage, separate, push by open injective incl).
- Universal property: `lift`/`lift_incl` (rfl)/`continuous_lift`
  (`Continuous.quotient_lift` + `continuous_sigma`) — Step D will define `g∞` etc.
  through it.

`#print axioms`: all five headline theorems `[propext, Classical.choice, Quot.sound]`,
sorryAx = 0.  Lean notes: Mathlib's `IsOpenEmbedding` lives in namespace `Topology` —
do NOT create a `DifferentialGeometry.Topology` namespace (shadowing); the
quotient-topology criterion is `isOpen_coinduced` (instance unfolds definitionally);
`IsOpenEmbedding.of_continuous_injective_isOpenMap` is the constructor.

Deferred (when Step D needs them): single-step builder (`f k : A k → A (k+1)` →
`SeqSystem` via `Nat.leRecOn`); second-countability glue (σ-compact + locally
second-countable); smooth/manifold structure on `Lim` (charts through `incl`).
