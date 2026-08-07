# InverseMetricRaisedEndomorphismJetBound

## 2026-07-27 API cleanup

The private slot-insertion add, composition, and identity lemmas were replaced
by the canonical public laws in `SlotInsertCovariantNaturality`.  The local
negation proof was also made explicit, avoiding an elaboration-sensitive
scalar inference.

Focused verification passed.  A later named producer refresh was stopped when
it expanded into an unrelated long connection-difference dependency replay;
there was no Lean error in this module, but the latest artifact refresh is not
counted as complete.

## 2026-08-06 class-first grid constants

The explicit inverse-difference recursion now chooses its zeroth-order and
recursive constants before either metric varies.  This exposes three concise
public producers: `invDiff_zero_unif`, `invDiff_slot_unif`, and
`invDiff_grid_unif`.  The former long metric-local theorem names remain as
compatibility wrappers and introduce no new frontier.

Focused verification passed.  The final grid producer depends only on the
standard `propext`, `Classical.choice`, and `Quot.sound` axioms.
