# `LowRegLiftAffine`

## 2026-08-02 — refolded A1 consumer migration

The active state-level bridge must not consume `LowA1CorePair`: that predicate
encodes the obsolete raw first-order completion route.  The correct producer is
the self-action refold already exposed by `LowRegBgA1Refold`.

The source now introduces `refoldBaseN`, retaining the existing completed A2
term while taking the complete refolded low action `FLo` as its A1 term.
`lowreg_N_affine` has been rewritten to consume continuity and the smooth-core
formula for `FLo`, and its density argument uses `refold_split` and
`refoldLo_core`.

The A2 smooth-core input is stated directly against `refoldCore.a2Lo`.  This is
the right downstream interface because `refoldCore` retains the canonical C2
coefficient unchanged; the A2 producer still needs a small compatibility
read-off when this theorem is wired into its caller.

The user reports that VS Code elaboration completed without a diagnostic: the
newly imported dependency chain took roughly twelve minutes on its cold pass,
while this file itself then completed in roughly twenty seconds.  No command-
line focused check or module refresh has been run in this session.

## 2026-08-02 (later) — locked verification GREEN

After the whole upstream chain (C0Core split, restored C0Pair capstone,
repaired C0Time, restructured `refold_time`) reached exact GREEN, the
command-line focused check initially failed with a single application type
mismatch at `lowA1Lo_core`: `LowA1CorePair` was a `def`-wrapped Prop, and the
current elaborator no longer unfolds a semireducible `def` when checking the
`hpair` argument of `Analysis.extend_pair_apply` against the literal ∀∃ form.
Declared it `abbrev` (one word; the docstring already called it a "named
abbreviation"; all uses are hypothesis/conclusion positions, none rewrite it
by name).  Focused check 22 s + targeted module refresh 24 s GREEN; zero
sorry/admit/axiom.

Progress accounting: the `lowreg_N_affine` migration is now lock-verified
GREEN.  The dedicated uniform-existence machinery is not counted as
completion of `ricci_flow_unif_existence`, whose Lean theorem remains
unproved (0%).
