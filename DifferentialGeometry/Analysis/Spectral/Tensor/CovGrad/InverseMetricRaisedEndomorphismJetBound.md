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
