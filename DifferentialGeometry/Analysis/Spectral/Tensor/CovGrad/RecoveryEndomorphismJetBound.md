# RecoveryEndomorphismJetBound

## 2026-08-06 explicit self-endomorphism cap

The existing dimension-only estimate for the self sharp-flat endomorphism is
now public as `rfns_idEndo_le`.  Its statement is uniform over the metric and
provides the order-zero identity seed needed by class-first inverse and
connection-difference grids; the proof itself is unchanged.

Focused verification passed.  The new public theorem depends only on the
standard project axioms `propext`, `Classical.choice`, and `Quot.sound`.
The file still reports its pre-existing unused-section-variable warnings in
unrelated private helpers.

This producer is complete (100%).  It is infrastructure for the uniform RHS
coefficient producer, not a proof of `lowreg_bounds_unif` or the uniform Ricci
flow existence endpoint.
