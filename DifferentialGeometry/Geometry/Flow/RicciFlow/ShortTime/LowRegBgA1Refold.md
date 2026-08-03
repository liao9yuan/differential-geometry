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
