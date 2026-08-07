# `LowRegBgA1Refold`

## Role

This module combines the refolded order-zero action with the original
path-integrated order-one arm.  It exposes the complete same-background A1 on
both adjacent Sobolev scales, its smooth-core formula, the exact remainder
split, and the compatible time packet.

## 2026-08-02 downstream migration

The user verified the preceding version in VS Code.  The file itself took
roughly twenty seconds after a roughly twelve-minute cold dependency pass.

For the `LowRegLiftHfLo` migration, `refold_time` now retains the affine
pointwise bounds of its two component packets.  The combined bounds use only
the triangle inequality and the already chosen constants
`Z = Zc + Zo`, `L = Lc + Lo`.  No new estimate, state smallness, or derivative
is introduced.

Its intended consumer uses the returned low bound to recover the finite
M-witness along an a.e. bounded Duhamel trajectory while using the same `FLo`
in `lowreg_N_affine`.

## 2026-08-02 `refold_time` timeout fix

The first elaboration attempt of `refold_time` failed with two deterministic
timeouts that did not move when the heartbeat budget was raised fivefold: a
`whnf` timeout anchored at the declaration head and an `isDefEq` timeout on
`exact hcHi'.add hoHi'` inside `have hHi : MemLp AHi 2 (timeMeasure T)`.

Cause.  The proof built the time packet by splitting `AHi` into the two
component families `AcHi + AoHi`, transporting each component's `MemLp` across
`simpa`, and recombining with `MemLp.add` plus `MemLp.toLp_congr` /
`MemLp.toLp_add`.  Since Mathlib's `MemLp` is now stated for `ENorm`-classes
(`MemLp.add` needs `[TopologicalSpace ε] [ESeminormedAddMonoid ε]
[ContinuousAdd ε]`), applying it at `ε = metricH3 g →L[ℝ] metricH2 g` forces a
defeq comparison of two independently produced instance chains on a continuous
linear map space whose domain and codomain are reducible `abbrev`s over the
heavy `tensorHs` Lp completion.  That comparison unfolds `tensorHs` without
bound, so it diverges rather than merely being slow — hence the immunity to a
larger heartbeat budget.

Fix.  Do not reconstruct the packet from the two component packets at all.
`refold_time` already carries the combined affine bound
`hFHiBd : ∀ x, ‖FHi x‖ ≤ Z + L * ‖x‖`, so the whole `MemLp` plus norm estimate
comes in one step from `memLp_clm_affine`, exactly as `c0_time` does in
`LowRegBgC0Time.lean`.  Concretely: measurability of `AHi` from
`(ContinuousLinearMap.compL …).continuous₂.comp_aestronglyMeasurable₂`, the
pointwise bound from `radialCLM_norm` plus `opNorm_comp_le`, then
`obtain ⟨hHi, hHiNorm⟩ := memLp_clm_affine u AHi …`.  `memLp_clm_affine`
majorizes by a real-valued `L²` function and uses `MemLp.mono`, so no
`MemLp.add` is ever instantiated at the CLM type.  Both component `MemLp`
hypotheses coming out of the two packets are now unused.

The two component families `AcHi/AoHi/AcLo/AoLo` are still needed, but only for
the inclusion-commutation `hcomm`, whose inputs `hcComm`/`hoComm` are stated at
the component level.  There the function-level rewrite `rw [hAHi, hALo]` was
replaced by the two pointwise `rfl` facts `AHi t x = AcHi t x + AoHi t x` and
the matching one for `ALo`, so no `Pi.add`/`ContinuousLinearMap.add` equality
between whole operator families is ever formed.

Lesson.  On these `tensorHs`-valued CLM spaces, prefer lemmas whose statement
already produces the fact you want over generic algebraic combinators
(`MemLp.add`, `MemLp.toLp_add`, `MemLp.toLp_congr`).  A generic combinator has
to re-synthesize and then unify the `ENorm`/`ESeminormedAddMonoid` tower, and a
reducible `abbrev` over `tensorHs` gives that unification unbounded room to
unfold.  Deterministic timeouts that survive a heartbeat increase are the
signature of this, not of a large finite computation.

Verification: focused check passes, with only
`set_option synthInstance.maxHeartbeats 1000000` retained (the same
per-declaration convention `LowRegBgTime.lean` uses for this instance family).
The `maxHeartbeats` inflation was removed and the declaration now elaborates
inside the default term budget.

## 2026-08-02 (later pass) — `refold_time` → `refold_aff`, the quantifier hoist

`refold_time` quantified `∃ Z L FHi FLo` *after* its state argument
`u : timeL2 H³ T`, so the affine growth constant `L` was not in scope at the
point where a downstream endpoint has to choose a realization radius.  Since
`FHi`, `FLo`, `Z`, `L` are built from `(ρ, δ, hreal)` alone, this was a pure
re-ordering, not new mathematics.

`refold_time` is **replaced** by `refold_aff`:

- same `∃ ρ₀ > 0, ∀ ρ δ …` prefix, no `T` and no `u`;
- conjuncts: `Continuous FHi/FLo`, the two refolded smooth-core formulas
  (`c0CoreData … .a1* + oneCore … .a1*`), the two affine bounds
  `‖F x‖ ≤ Z + L‖x‖`, and the **u-free** square
  `∀ x, incl12 ∘ FHi x = FLo x ∘ incl32`;
- proof = the old summation part verbatim (`Z := Zc+Zo`, `L := Lc+Lo`,
  `F := Fc + Fo`) with the two lanes' packets `c0_pack` / `c1_bg_pack` in place
  of `c0_time` / `c1_bg_time`, plus a 10-line pointwise proof of the square from
  the two lanes' u-free squares.

Deleted with it: the ~105 lines of measurability / `memLp_clm_affine` /
`radialCLM_incl` plumbing that produced the per-`u` time certificates.  Those
were already dead weight — the only consumer, `lowreg_hfLo_data`, destructured
them as `⟨-, -, -, -, hcomm⟩` and rebuilt the `MemLp` witnesses itself from the
affine bounds via `refoldAffA1_memLp` / `refoldAffA1Hi_memLp`.  The one piece it
did use, the time-level square, is now derived from the u-free square inside
`refoldAffA1_compat`.

Side effect worth noting: `set_option synthInstance.maxHeartbeats 1000000 in`,
which the old `refold_time` needed (see the timeout section above), is **no
longer required**.  The blow-up came from the `timeL2` / `MemLp` / `toLp` layer
in the statement, not from the action maps.

Focused check + targeted `.olean` build GREEN; `refold_aff` axiom-clean.

## 2026-08-03 — brick G1: two-metric widening (`refold_aff_bg`), GREEN

Front 3's first dispatchable brick (`FRONT3_ASSEMBLY_PLAN.md` §7/§10).  The
DeTurck background was hard-wired to the state metric on this path in exactly
one definition, `oneCore g = (lowCoreDataBg g g …).C1`; the packet inherited it.

What is in the file now:

- `oneCoreBg g gB …` (`:56`) — the order-one arm at an arbitrary background,
  `C1 := (lowCoreDataBg g gB …).C1`, `C0 = C2 = 0`.
- `oneCore g … := oneCoreBg g g …` (`:71`) — unchanged signature and type; the
  diagonal wrapper.
- `refold_aff_bg hDim g gB` (`:345`) — the same packet shape as `refold_aff`
  with the smooth-core conjuncts reading `oneCoreBg g gB`, proved from
  `c0_pack g` (background-free) + `c1_bg_pack g gB` (already two-metric).
- `refold_aff hDim g` (`:488`) — statement byte-identical to the previous one,
  proved term-mode by `refold_aff_bg hDim g g`.

Why an instance theorem and not a redefinition of `refold_aff`.  The packet's
conclusion is carried as a *hypothesis* by seven downstream theorems
(`LowRegLiftHfLo`, `LowRegLiftAffine`, `LowRegForceHi`, `LowRegApplyTwo`,
`LowRegAllOrderJet`), all of which name `oneCore` in their statements.  Defining
`refold_aff := refold_aff_bg … g g` would have printed `oneCoreBg g g` in that
conclusion and forced a lock-step edit of all of them.  Keeping the old
statement and discharging it by `exact` costs one line and no churn.

Only unfolding site of `oneCore` in the whole tree: `refoldLo_core`'s
`simp only` (`:177`).  It now also lists `oneCoreBg`, because after the
redefinition `simp only [oneCore]` stops one delta-step short of the structure
literal and the `LowBaseActionData.a1` projections would not fire.  This is the
single thing to remember if another `oneCore`-unfolding proof is ever added.

Verification: focused check green; targeted module build green; downstream
`LowRegLiftAffine`, `LowRegLiftHfLo`, `LowRegApplyTwo` all green with **no
edits**, plus targeted builds of `LowRegLiftAffine`, `LowRegLiftHfLo`,
`LowRegForceHi`.  No `sorry`, no `set_option` (the №95 hoist still holds — the
packet statement has no `timeL2`/`MemLp` layer, so `synthInstance` stays cheap
even with the extra metric argument).

Nothing here moves mathematics: `c1_bg_pack`'s `hreal` hypothesis is about `g`
alone, so both lanes share their hypothesis bundle at any background and the
sum/affine-addition arguments never mention `gB`.  The plan's failure signal (a
`g g`-dependent `rfl` in the `a1Lo_congr` layer) did not appear.

## 2026-08-07 — brick B1: the corrected Bg refold bundle, GREEN

Repair brick for route error #2 (ledger №203).  `refoldCore`'s two-metric
widening `oneCoreBg` (brick G1, above) kept `C0 := 0` for the order-one arm and
so the widened bundle silently reused the DIAGONAL order-zero coefficient.  At
`gB ≠ g` the canonical low-base `C0` is background-dependent, so the bundle was
wrong away from the diagonal — it just could not be detected, because every
consumer so far was at `gB = g`.

**What landed** (public): `refoldCoreBg g gB` — same shape as `refoldCore`, with

- `C0 := c0CoreData.C0 + ((lowCoreDataBg g gB).C0 - (lowCoreDataBg g g).C0)`
- `C1 := c0CoreData.C1 + (lowCoreDataBg g gB).C1`
- `C2 := (lowCoreDataBg g gB).C2`

plus `refoldCoreBg_diag` (`refoldCoreBg g g = refoldCore g`) and the endpoint
`refold_split_bg`: for `S = lowRadial g ρ T`, `F = refoldCoreBg g gB`,

`deTurckSmoothRemainder g gB S - deTurckSmoothRemainder g gB 0 = F.a2 S + F.a1 S`.

Private helpers `refoldBg_c0/c1/c2` (`rfl`), `refoldBg_first/second/action`
mirror `refold_c0/c1/c2`, `refold_first/second/action` one-for-one.

**The ΔC0 passenger is phrased as a bare `lowCoreDataBg`-`C0` difference on
purpose.**  The scout's closed formula lives in `lowC0_bg_eq`
(`LowRegBgH2.lean:893`), but that theorem AND its `bgCorrInt` summand are both
`private`, so neither name is usable here.  Nothing is lost: B1 only needs the
difference to be *some* `SmoothCcTensor g 2 2`, and `sub_self` kills it on the
diagonal without ever knowing what it is.  B2 (the affine packet) is where the
closed formula is actually needed, and B2 will have to un-private
`lowC0_bg_eq`/`bgCorrInt` or route through the already-public H² bounds.

**Proof route** (all at the `appCc` level, no component work).  From
`lowCoreBg_split g gB` the LHS is `A.a2 S + A.a1 S` for `A = lowCoreDataBg g gB`.
The `a2` arm is `rfl`-level (`F.C2 = A.C2`).  For `a1`, the whole content is the
two-line bridge

```
hkey : appCc A.C0 S = appCc (A.C0 - D.C0) S + appCc D.C0 S
     := by rw [← appCc_add_left, sub_add_cancel]
```

(`D = lowCoreDataBg g g`), which converts the Bg order-zero self-action into
`ΔC0`-action plus the DIAGONAL order-zero self-action; the latter is exactly
what the pre-existing private `refold_zero` (i.e. `c0Core_self`) already trades
for `c0CoreData.a1 S`.  Two `appCc_add_left`s expand `F.C0`/`F.C1`, and `abel`
closes.  `appCc_sub_left` is NOT needed — `sub_add_cancel` under a single
`appCc_add_left` is strictly cheaper and avoids importing
`OperatorFieldDifferentiatedTowerNormalForm` reasoning into this file.

**Diagonal C1 relation, verified not assumed:** `oneCore g = oneCoreBg g g` by
`def`, and `oneCoreBg g gB |>.C1 = (lowCoreDataBg g gB).C1` by `def`, so
`oneCore.C1 = (lowCoreDataBg g g).C1` holds by `rfl`.  `refoldCore`'s `C1` is
literally `c0CoreData.C1 + (lowCoreDataBg g g).C1`, so the scout's field spelling
for `refoldCoreBg.C1` is the correct widening and `refoldCoreBg_diag`'s `C1`/`C2`
arms are `rfl`; only `C0` needs `sub_self, add_zero`.

**Byte-stability:** no existing declaration was edited.  `refoldLo_core`'s
`simp only` (`:177`, the `appCcRS_zero_left` site flagged in the dispatch) did
NOT need the `sub_self` rewrite — it is stated against `refoldCore`, which is
untouched.  The diagonal collapse is a separate lemma, as instructed.

Verification: focused check green, targeted module build green, no `sorry`, no
new `set_option`, no linter warnings from this file.  `refold_split_bg` and
`refoldCoreBg_diag` both `[propext, Classical.choice, Quot.sound]`.

**Still wrong after B1:** `refold_aff_bg` (`:345`) and every `IsBgA1At` field
downstream still name `c0CoreData + oneCoreBg`, i.e. the OLD (diagonal-`C0`)
bundle.  B1 supplies the corrected identity; B2 must restate those fields
against `refoldCoreBg` and add the third affine summand for the ΔC0 packet.

## 2026-08-07 — brick B2: STOPPED at part (a); nothing in this file changed

> SUPERSEDED by the B2c′ section below (ledger №206): route error #2 IS now
> repaired, and this file did change.  The gap analysis in this section is still
> accurate and is the spec for bricks B2a/B2b.

**This file is UNTOUCHED by B2.**  `refold_aff_bg` (`:551` after B1) and
`refold_aff` (`:694`) still carry the OLD core clauses `c0CoreData.a1Hi/a1Lo +
oneCoreBg.a1Hi/a1Lo`.  Route error #2 is therefore NOT yet repaired.

**Why (the exact gap, ledger №205).**  The restatement onto `refoldCoreBg`
requires a third affine summand — a packet for the ΔC0 passenger
`(lowCoreDataBg g gB … T).C0 - (lowCoreDataBg g g … T).C0` — and that packet's
AFFINE half has no producer:

- `exists_extend_le` needs a *continuous* envelope, and `IsBgA1At.a1Hi_bound`
  needs specifically the affine `Z + L‖x‖` (the №196 shape).
- `c0_bg_pair_h2` (public, already phrased on the bare `.C0` difference at a
  fixed background) gives the LIPSCHITZ input — apply it at `gB` and at `g`.
- `lowC0_bg_h2` gives only an opaque `B : ℝ → ℝ` (`0 ≤ B A` is all a consumer
  sees; internally degree six).  No affine information is extractable.
- `bgCorr_h2` / `bg0_pair_h2` are `public` in keyword only: their conclusions
  name the `private` `bgCorrInt` / `bg0PairInt`, so they cannot be applied
  from another module at all.

The missing producer is a TAME (affine) `H²` envelope for the background
correction — statement, engines, and cost are recorded in ledger №205.  It is
~400 lines in `LowRegBgH2.lean`, a session of its own; `c0bg_pack` is another.

**What B2 did land (elsewhere):** `a1Hi_add`/`a1Lo_add` (+ `a1Hi_app`/
`a1Lo_app`) in `DeTurckRemainderLowBaseA1Comm.lean`.  When B2 resumes, the
restatement's core clause is closed like this — `FHi := FcHi + FoHi + FdHi`,
then

`(refoldCoreBg g gB … S).a1Hi = (c0CoreData … S).a1Hi + (oneCoreBg … S).a1Hi
  + (ΔC0-bundle … S).a1Hi`

by `a1Hi_add` twice (the hypotheses are `refoldBg_c0`/`refoldBg_c1`, already
`rfl`), and `refold_aff` stays at its CURRENT statement — derive it from the
restated `refold_aff_bg` at `gB = g` via `refoldCoreBg_diag` plus one
`a1Hi_add` (`refoldCore.C0 = c0CoreData.C0 + oneCore.C0` needs `add_zero`;
`C1` is `rfl`).  Keeping `refold_aff`'s statement fixed is what keeps
`LowRegApplyTwo.lean:645` and the whole `lowreg_solve_open` chain
byte-untouched; the diagonal statement was never wrong.

**Consumer census for the eventual restatement (done, so B2b need not redo
it):** `refold_aff_bg` has exactly ONE consumer, `bgA1_of_refold`
(`LowRegBgLift.lean:217`).  `refold_aff` has exactly one, `lowreg_solve_open`
(`LowRegApplyTwo.lean:645`), which destructs the packet as
`⟨Z, L, hZ, hL, FHi, FLo, hFHi, hFLo, -, hFLoCore, hFHiBd, hFLoBd, hFComm⟩` —
it DISCARDS the Hi core clause and feeds `hFLoCore` to `lowreg_apply_two`
(`:303`), whose hypothesis is spelled `c0CoreData.a1Lo + oneCore.a1Lo`.

## 2026-08-07 — brick B2c′: the three-term split + the registered ΔC⁰ input

**Landed here (739 → 938 lines), sorry-free.**

- `deltaCoreBg g gB` (public): the ΔC⁰ passenger as an action bundle,
  `⟨lowCoreDataBg[gB].C0 − lowCoreDataBg[g].C0, 0, 0⟩`.
- `refoldBgMid` (private) + `refoldMid_split0/1` (private): the intermediate
  bundle `c0CoreData ⊕ oneCoreBg` and its two field equations against
  `refoldCoreBg`.  Both close by ONE `simp only [refoldCoreBg, refoldBgMid,
  deltaCoreBg, oneCoreBg, add_zero]` — the additive split is EXACT and needs
  only `add_zero` threading, which independently confirms B1's field spelling.
  The intermediate bundle is unavoidable: `a1Hi_add` is binary, the
  decomposition is ternary.
- **`refoldBg_a1Hi_split` / `refoldBg_a1Lo_split`** (public):
  `(refoldCoreBg … T).a1Hi = ((c0CoreData … T).a1Hi + (oneCoreBg … T).a1Hi) +
  (deltaCoreBg … T).a1Hi`, each two `a1Hi_add` (resp. `a1Lo_add`) rewrites.
  This is the bridge the previous section predicted, now proved.
- **`BgDeltaPack g gB : Prop`** (public), the REGISTERED HONEST INPUT of ledger
  №205/206: the trajectory-free affine packet of `deltaCoreBg`, clause-for-clause
  a mirror of `c0_pack`/`c1_bg_pack`.  It is NOT proved and must not be treated
  as settled API; its producer is B2a `c0Bg_diff_tame` + B2b `c0bg_pack`.

**Placement justification.**  `BgDeltaPack` lives HERE, not in
`LowRegBgLift.lean`, because it mentions only refold-layer objects
(`deltaCoreBg`, the private `metricH*` scale abbrevs, `incl12`/`incl32`) and
because its producer will sit BELOW the lift layer, alongside `c0_pack` — the
lift file only consumes it.

**Spec correction the reading forced.**  The dispatch hoped `a1_comm hDim g
(refoldCoreBg …)` might give `IsBgA1At.a1_square` for free.  It cannot:
`a1_comm` is an identity between ONE BUNDLE's two completions, so it only lands
at smooth states `x = ι S`, while `a1_square` is an identity between the two
MAPS at an arbitrary `x : H³`.  `BgDeltaPack` therefore carries its own square
clause (seven clauses, matching `c0_pack`), and the summand-square route in
`bgA1_of_refold` is mandatory, not a fallback.

**`refold_aff_bg` and `refold_aff` were NOT restated** — the whole
`lowreg_solve_open` chain stays byte-untouched, as the census above requires.
The restatement is unnecessary now: `bgA1_of_refold` combines the unchanged
`refold_aff_bg` packet with the `BgDeltaPack` packet and uses the split lemmas
above, which is strictly less invasive than №204's plan (c).

Verification passed (focused check + targeted build; axiom probes on
`refoldBg_a1Hi_split`, `refoldBg_a1Lo_split`, `deltaCoreBg`, `BgDeltaPack` all
clean).

## 2026-08-07 — brick B2b: `c0bg_pack` LANDED, `BgDeltaPack` is now a THEOREM

**Home decision (a correction to the dispatch).**  The dispatch suggested
`LowRegBgC0Time.lean` as the home "beside `c0_pack`".  That is impossible: the
import runs `LowRegBgA1Refold → LowRegBgC0Time`, so `deltaCoreBg` and
`BgDeltaPack` — both defined here — are invisible from `LowRegBgC0Time`.  The
producer therefore sits in THIS file, immediately after the predicate it
discharges, which is also the canonical-home reading (a producer next to its
interface, below the lift layer that consumes it).

**Landed (938 → 1494 lines), all private except the endpoint.**

- `zeroBundle` / `zeroBundle_a1` / `iterZ` / `lowJetZ` / `zeroBundle_pair` —
  mirrors of `LowRegBgC0Time`'s private zero-bundle block (private there, so not
  reusable across the module boundary).  `zeroBundle_pair` was strengthened to
  return the two `= 0` equalities directly rather than the two `‖·‖ = 0`s, which
  removes the `opNorm_zero_iff` step from every call site.
- `c0bg_aff` — the affine half.  Verbatim `c0_core_affine` with `c0Coeff_aff`
  replaced by `c0Bg_diff_tame` and `c0CoreData` by `deltaCoreBg`.  The whole
  radial block (`R2 := C2·ρ`, `A3 := C3·‖ι₃T‖`, `lowRadial_norm`,
  `lowRadialH3_le`/`_core`) transferred with no change; `Z := Ca·B0 R2`,
  `L := Ca·B1 R2·C3` as dispatched.  Because `c0Bg_diff_tame` needs no radius
  cap, `ρ0 := 1` here.
- `c0bg_pair` — the Lipschitz half.  **This is where the dispatch's recipe was
  incomplete.**  `c0_bg_pair_h2` is a SINGLE-background estimate, but
  `deltaCoreBg` is a background DIFFERENCE, so it must be consumed TWICE — once
  at `gB`, once at the diagonal `gB := g` — and the two recombined by `jetSub`
  along
  `ΔT.C0 − ΔU.C0 = (bg_gB(S) − bg_gB(V)) − (bg_g(S) − bg_g(V))` (`abel` after
  `simp only [deltaCoreBg, lowCoreDataBg]`).  The radial-difference plumbing
  (`lowRadial_lip`, `lowRadial_h3_sub`, `Lr := 1 + r₀/ρ`) is `c0CorePair`'s,
  transferred verbatim.  Each `c0_bg_pair_h2` envelope is turned into
  `2(P² + Q²)·D²` by `ring` after substituting `D2 = C2·D`, `D3 = C3·Lr·D`,
  `N = D`; the four constants are collected into `Ebg` and `Kc := √Ebg`, so
  `a1_diff` is fed at `R := Kc·D`.
- `c0bg_pack : BgDeltaPack g gB` — `c0_pack`'s assembly, line for line.

**The square clause was FREE, contra №207's "needs an `a1_comm_any` mirror".**
`a1_comm` (`DeTurckRemainderLowBaseA1Comm.lean:164`, public, in the import
closure) already holds for ANY `LowBaseActionData`, and is literally what the
private `a1_comm_any` wraps — that private copy predates the A1Comm file.  So
the pack's square is `a1_comm hDim g (deltaCoreBg …)` plus
`simp only [incl12, incl32]`, lifted to arbitrary `x` by exactly `c0_pack`'s
density step (`hdense.induction_on x (isClosed_eq hleft hright)`).  No mirror
was written.  №206's structural point still stands and is why the CLAUSE exists
at all: `a1_comm` alone lands only at `x = ι S`.

**Two small Lean facts worth keeping.**  (1) `incl32_c0` lives in the nested
namespace `…IntrinsicSpectral.LowRegBgC0Core`, so it needs the
`LowRegBgC0Core.` prefix from this file.  (2) The `hδZ` slot inside
`lowCoreDataBg` is `zero_fibre_bound` (private in `LowRegBgTime`), but supplying
this file's `zero_fb_refold` instead is fine — proof irrelevance is definitional,
and `simpa only [deltaCoreBg, lowCoreDataBg, …]` crosses it without a `change`.

**Verification.**  Focused check GREEN; targeted builds
`+…ShortTime.LowRegBgA1Refold` and `+…ShortTime.LowRegBgLift` both
`Build completed successfully`; axiom probes on `c0bg_pack` and the now
unconditional `bgA1_of_refold` both `[propext, Classical.choice, Quot.sound]`.
No `sorry`, no `set_option` added (the first draft's
`linter.unusedVariables false` on `c0bg_pair` turned out to be unnecessary and
was removed), no linter warning left.
