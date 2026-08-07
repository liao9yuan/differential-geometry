# `UnifPairRadii.lean` — plan note (brick γ, gap clusters G6 + G7)

**Status (2026-08-07): NOT STARTED IN LEAN — STOPPED BEFORE THE FIRST EDIT.**
No `UnifPairRadii.lean` exists.  The stop is architectural, not
mathematical: see §3.  The mathematics of the brick is *confirmed and
closed* (§2); it is the Lean expressibility that blocks.

Target (per ledger №222): the class-uniform radius floors
`bgPairRad_unif` (A1 side) and `a2PairRad_unif` (A2 side), radius only,
Lipschitz constants staying existential per `g`.

---

## 1. What was measured

A full mechanical trace of the radius provenance of the seven roots named
in the brick spec — `c0CorePair`, `c1_core_pair`, `c1_ext_pair`,
`c0bg_pair`, `c0Coeff_aff` (G6) and `a2_pair_lip`, `radialA2Bg_lip` (G7)
— following every `obtain ⟨ρ…⟩ := callee` edge transitively, with
namespace-qualified callees resolved.

| quantity | value |
|---|---|
| nodes on the radius chain | **109** |
| genuine radius **sources** (not a `min` of children) | **2** |
| nodes whose radius witness is a pure `min` of children's radii | **105 / 109** |
| already banked with a `_unif` sibling | 6 |
| nodes still to restate class-uniformly | **103** |
| …of those, inside a read-only standing monolith | **47** (37 `private`) |

Per cluster: **G6** 94 nodes / 89 to-do (34 read-only, 55 editable);
**G7** 24 nodes / 18 to-do (17 read-only — all in
`DeTurckRemainderLowBaseC2Lip.lean` — 1 editable).

## 2. The mathematics is CONFIRMED — and it is trivial

The design scout's claim in №222 is **exactly right**, and stronger than
it was stated.  The whole 109-node chain has only two radius sources:

- `inv_coeff_h2` (`Analysis/…/DeTurck/PrincipalCoeffH2.lean:202`),
  witness `let ρ : ℝ := min 1 (4 * Cop)⁻¹`, where
  `Cop = hs2OpActionC (morreyTwoC gBase Λ) Kcurv.rankTwo` is class data.
  **Already banked** as `inv_coeff_h2_unif` (`ShortTime/UnifInvCoeffH2.lean:60`),
  which selects that same radius before the class metric varies.
- `sharp_pair_h2` (`Analysis/…/DeTurck/DeTurckRemainderLowBaseC1Lip.lean:3972`),
  witness `let ρ : ℝ := 1` — **absolute**, hence trivially class-uniform.

plus, at `radialA2Bg_lip` only, the *passed-in* `ρ₀`, which the consumer
`bgA2_of_radial` instantiates at `K.realize` — class data, since `K`
comes from `exists_lowBounds`.

Everything else is verbatim `min` composition.  Therefore the honest
class-uniform floor for **all four pair chains at once** is

```
ρ̄  =  min (K.realize) (min 1 (4 * Cop(gBase, Λ))⁻¹)
```

i.e. literally `inv_coeff_h2_unif`'s radius met with the class
realization radius.

**No Lipschitz constant enters any radius anywhere.**  The brick spec's
contingency — "if a node's radius genuinely requires its constant (a
`1/(4C)`-shaped radius with `C` per-g), that node's constant enters the
gap honestly" — **does not fire at a single node**.  The one `1/(4C)`
radius in the whole chain is `inv_coeff_h2`'s, and its `C` is `Cop`,
which is class data already.  So the brick's premise ("radius only,
constants stay existential") is vindicated in full, and G6/G7 need
*nothing* from bricks α/β.

## 3. Why it nevertheless cannot be written (the blocker)

Every one of the 109 statements has the shape

```
∃ ρ C, 0 < ρ ∧ 0 ≤ C ∧ ∀ …, ‖T‖ ≤ ρ → ‖U‖ ≤ ρ → P(T, U, C)
```

`P` is downward-closed in `ρ` (a smaller ball is a weaker hypothesis),
but the existential **hides the witness**.  From `∃ ρ, P(ρ)` one cannot
derive `P(ρ̄)` for a `ρ̄` chosen in advance.  So a class floor cannot be
*extracted* from any of these theorems — each one has to be **restated**
with the radius quantified before `g` and **re-proved**, replaying its
own `min` arithmetic on top of already-uniform children.  The proof
bodies are otherwise unchanged (the constants are simply obtained after
`intro g hclass`), which is why the job is mechanical — but there are
103 of them.

Escapes checked and closed:

- *Lower bound already stated?*  No.  `radialA2Bg_lip`'s extra existential
  component is `hρ_le : ρ ≤ ρ₀` — an **upper** bound, the wrong direction.
  No node in the chain states a lower bound on its own radius.
- *Infimum over the class?*  The class is not compact in any sense that
  makes `inf_g ρ_g > 0` available without the quantitative re-proof.
- *Transfer from `gBase`?*  Not formal: the statements quantify over
  `SmoothCcTensor g 0 2`, whose type depends on `g`.

### The hard stop: the ready frontier is 100 % read-only

The uniformization must proceed bottom-up.  The nodes whose radius
children are *all* already banked — the only ones that can be written
today — are exactly these ten, and **every one of them is inside
`DeTurckRemainderLowBaseC2Lip.lean`**, a standing read-only file:

```
fullInsert2_pair :2858   fullSlot_h2_bdd  :2376   lieRefold_pair_lip :2150
pairTrace_bdd_h2 :4685   pairTrace_pair_h2:4655   phiMet_pair_lip    :3949
trace1_h2_lip    :4706   trace2_pair_h2   :5208   trace3_h2_lip      :4972
trace4_pair_h2   :5326
```

No node in an editable file has all its children banked.  Brick γ
therefore cannot take **a single step** without either editing a standing
file or replaying monolith proof bodies into a new file.

Privacy is a second-order aggravation, not the primary blocker: 15 of
G7's 17 monolith nodes are `private`, and their statements mention
private definitions (`c2Kernel` :4068, `c2JetSq` :229, `fullSlot2` :62).
That is *survivable* — the banked `curvMono_h2_lip_unif`
(`ShortTime/UnifTraceLip.lean:996`) shows the pattern: it restates the
private `c2JetSq g X` by unfolding it inline to its public expansion
`∑ j ∈ Finset.range 3, ‖iteratedCovGrad … j X‖ ^ 2`.  But `c2Kernel` and
`fullSlot2` are structural sections, not one-line sums, so the same trick
against them produces very large statements.

## 4. Recommendation (needs a user ruling)

**Preferred — lift the never-edit constraint additively for this job.**
Put each `_unif` radius sibling **inside the monolith, immediately after
its metricwise original**.  That is the only place where the private
statements are expressible and where the proof body can be reused rather
than copied, and it is purely additive (no existing declaration changes).
With that, G7 is 18 mechanical siblings in one file and G6 is 89 across
twelve; the per-node cost is small because the radius arithmetic is
already explicit at every node.

**Fallback — replay into light `Unif*.lean` files.**  Respects the
never-edit rule but requires copying ~2 400 lines of `C2Lip` internals
(G7) plus the `H2Pair` / `C1Lip` / `Lip` slices (G6) — precisely what
№194 and the "do not copy large proof bodies" rule forbid.  Not
recommended.

**Third option — dissolve the requirement.**  №221 records an unrecorded
escape hatch (a direct-smoothing order-two route) that would remove the
need for a class-uniform lift radius altogether.  It was noted as "not
live without a user ruling"; this finding raises its value considerably,
because it would retire all 103 nodes at once.

## 5. Re-pricing

№222 priced brick γ at **1–2 sessions** as the lowest-risk slice.  That
estimate assumed the metric-dependent links had `_unif` siblings to
substitute; in fact only 6 of 109 do, and the substitution route is not
available at all (§3).  Honest re-price:

- brick γ under the preferred recommendation: **≈10–20 sessions**
  (G7 ≈3–5, G6 ≈8–15) — comparable to brick α, not smaller than β.
- the master coefficient packet as a whole: **≈25–40 sessions**, not the
  10–15 of №222.

γ is no longer the right thing to dispatch first: it is the *cheapest per
node* but the *largest by node count*, and it is gated on a ruling.

## 6. What brick δ needs from γ

Unchanged in shape: δ needs one `ρ̄ > 0` valid for the whole class, to
serve as `D.coeffRadius`'s upper gate in `bgLift_of_radial`
(`ShortTime/LowRegBgLift.lean`, A1 half ρ₁ + A2 half ρ₂).  §2 now tells δ
*exactly* what that number is — `min (K.realize) (min 1 (4·Cop)⁻¹)` — so
δ's arithmetic can be written against a known formula.  What δ still
lacks is the Lean theorem asserting it.

## 7. Verification status

None run — **no Lean file was created or edited**, so there was nothing
to check.  The tree is exactly as found (`git status` unchanged by this
session apart from this note and the ledger entry).

## 8. Lessons

- Before pricing a "replace each link with its `_unif` sibling" brick,
  **count the links and grep for the siblings**.  Here the ratio was
  6 / 109; the brick was priced as if it were near 109 / 109.
- A `∃ ρ, P(ρ)` statement is a **one-way door** for uniformization: the
  witness is unrecoverable, so downward-closure of `P` in `ρ` buys
  nothing.  When a radius is intended to become class-uniform later,
  state it as `∀ ρ, 0 < ρ → ρ ≤ ρ̄ → P(ρ)` from the start, or export the
  witness formula as a `def`.  This is the single design change that
  would have made brick γ free.
- The right unit for a bottom-up uniformization lane is the **ready
  frontier** (nodes whose children are all banked), not the leaf count.
  Checking the frontier's *editability* is what turned this from "big but
  doable" into "cannot take one step".
