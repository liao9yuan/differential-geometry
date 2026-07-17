# StepCStageSeed

## 2026-07-16 radius-independent stage seed

`IsStableNet` names the existing pairwise `B`-intersection stability property.
`HasStageRefine` is the transparent existential payload for one construction
radius, ending at the already checked `HasStageJetData`.  `HasStageSeed`
chooses one stable net and retains a refinement procedure for every later
stable net over the same `MetricCompactnessInputs`.

The checked producer chooses the minimizing scale, the large construction
divisor, `MetricCompactnessInputs`, its proper metrics, and one stable `L0`
exactly once.  Its retained refinement works for every stable `L` over that
same input and every nonnegative radius, then returns the existing
`HasStageJetData` payload.  It reuses the fixed-input support, selected-center,
diagonal convergence, metric convergence, stage-jet, and exact-basepoint
producers; it adds no endpoint field or radius assumption.

The intended recursive-radius consumer uses `HasStageSeed.subseq`; stability
of each further strict refinement is supplied by the existing
`NetLimitData.stable_subseq`.  No master radius diagonal is asserted here.

Focused verification and the exact module refresh passed with no `sorry`.
The seed theorem is complete (100%).  The recursive integer-radius master
diagonal remains a separate unstated/proof frontier (0%), and
`MetricCompactBase.exists_b1_raw` and the
textbook Step B1 endpoint remain unproved (0%); this file is dedicated
producer machinery, not endpoint completion.
