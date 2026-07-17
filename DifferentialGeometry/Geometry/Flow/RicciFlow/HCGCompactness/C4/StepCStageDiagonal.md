# StepCStageDiagonal

## 2026-07-16 nested radius diagonal

This file builds the recursive strict-refinement tower from `HasStageSeed`.
The generic `NestedSubseq` API records each selector and its one-step
refinement, proves the diagonal strict, and constructs a strict factor of the
diagonal tail through every fixed tower level.

`StagePayload` keeps the source-local `LiveSlot` data attached to the exact net
on which it was produced.  It does not identify `InterSlot` types across
refinements.  For a fixed integer radius `q`, `HasRadiusTail` discards the
first `q` master terms, supplies one strict factor `rho`, identifies the
resulting stage selector with that tail of the master selector, and transports
the same `HasStageJetData` through its checked `subseq` theorem.

`HasStageSeed.exists_radius_diag` is the reusable seed-level theorem;
`MetricCompactBase.exists_stage_diag` chooses the seed and master selector in
one package.  There is deliberately no global factorization through a fixed
radius and no equivalence between old and refined dependent slot types.

Focused verification passed with no `sorry`.  The nested integer-radius
diagonal and dependent fixed-radius tail persistence are complete (100%).
`MetricCompactBase.exists_b1_raw` and the textbook Step B1 endpoint remain
unproved (0%); this file closes the master-extraction machinery only.
