# `DeTurckRemainderLowBaseA1Comm.lean`

## Role

Bundle-generic facts about the low-base first-order action that need NO
coefficient estimate at the call site: they hold for ANY
`A : LowBaseActionData g`, hence at an arbitrary DeTurck background.

- `a1_comm` — the adjacent-scale square
  `incl(1≤2) ∘ A.a1Hi = A.a1Lo ∘ incl(2≤3)`.
  Consumer: `lowA1Bg_comm_bg` (`ShortTime/LowRegBgTime.lean`).
- `a1Hi_app` / `a1Lo_app` — each completion realizes the smooth-core action
  `A.a1` on the dense smooth range.
- `a1Hi_add` / `a1Lo_add` — **both completions are additive in the
  coefficient data**: if `F.C0 = A.C0 + B.C0` and `F.C1 = A.C1 + B.C1`, then
  `F.a1Hi = A.a1Hi + B.a1Hi` (and likewise `a1Lo`).  `C2` is irrelevant
  (`a1` never reads it).
- private `a1_jetQ` — the shared producer: one explicit `Q` built from
  `A`'s own coefficient jets satisfying both hypotheses of `a1_pair`, for
  ANY `A`.  All four public theorems are three-line consequences of it.

### Why `a1Hi_add` matters (added 2026-08-07, ledger №205)

An affine packet (`c0_pack`, `c1_bg_pack`, …) is built one summand at a
time and produces a SUM of `a1Hi`s; a refolded bundle such as
`refoldCoreBg` (`ShortTime/LowRegBgA1Refold.lean`) is a SINGLE bundle whose
`C0`/`C1` are those sums.  `a1Hi_add`/`a1Lo_add` are the only bridge between
the two spellings, so they sit on the critical path of the B2 repair of
route error #2 under every design the planner may choose.  They are proved
by density (`ccToHsLin_dense` + `DenseRange.induction_on` + `isClosed_eq`)
from `a1Hi_app`/`a1Lo_app` and `appCc_add_left`; note that `a1Hi` is a
`LinearMap.extendOfNorm`, so additivity is NOT definitional and genuinely
needs the unconditional core-application lemmas.

## Why this file exists (route record, 2026-08-07)

The identity already existed PRIVATE as `a1_comm_any` in
`DeTurckRemainderLowBaseLip.lean:10764`, exported only through the
difference square `a1_sub_comm`.  The preferred route (expose it in place)
was attempted first and REVERTED: the Lip module is a 10.8k-line settled
monolith whose full re-elaboration DIES at the focused-check memory budget
(`lean::memory_exception` at ~375 s under `-LeanMemoryMB 6144`,
4 threads) — editing it for a thin wrapper is not payable.  Precedent
№162/№163 (the `symmS_jet_le` judgment): rebuild a small assembly from its
PUBLIC producers in a light module instead of landing a heavy claim on a
light consumer.

Producers reused (all public, all in the existing import cone):
`a1_pair` (`DeTurckRemainderLowBasePair.lean:300`),
`a1_h3_h2` / `a1_h2_h1` (`DeTurckRemainderLowBaseAction.lean:13122/:13189`).
The only private dependency of the original proof was the one-line
nonnegativity `jet_nonneg_lip`; reproduced here as the local `jetNN`.

Fold-back note: this file does NOT import the Lip module, so no cycle
arises if the Lip module ever imports it.  When that monolith is next
legitimately rebuilt (with an adequate memory budget), delete its private
`a1_comm_any` and let `a1_sub_comm` consume this `a1_comm`.

## Verification

Focused check GREEN (~18 s, warning-free); targeted module build GREEN.
No `sorry`, no new `maxHeartbeats`.  Axiom probe on `a1Hi_app`, `a1Hi_add`,
`a1Lo_add`: the three standard axioms only.

Lean lesson (2026-08-07): `omit [BoundarylessManifold I M] in` on
`a1_add_core` FAILS — `LowBaseActionData`/`appCc_add_left` reference that
instance, and the failed `omit` corrupts the declaration's binder list, so
the follow-on error is the misleading "Invalid argument name `I`" at every
call site.  Drop the `omit`, not the named arguments.

## Progress accounting

- `ricci_flow_unif_existence`: **0%**.
- This module: **100%** (four public theorems + two private helpers).
- It is enabling API for the arbitrary-background A1 packet; the genuine A1
  frontier (class-first constants for the actual `lowCoreDataBg` arms, and
  the tame ΔC0 envelope of №205) is untouched by it.
