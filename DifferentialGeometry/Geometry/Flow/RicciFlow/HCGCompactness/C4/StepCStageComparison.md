# StepCStageComparison.lean - local identification of the global stage map

## 2026-07-18 framed migration: focused and exact green

The canonical stage-map statements and proofs now use `framedChartAt` at every
source and target center.  The item-3 target radius passed to
`stageWeight_small` is the intrinsic `expRadiusGp` bound.  The three chart-target
membership arguments use the checked `framedExp_source` reduction and the
orthonormal-frame radius comparison.  The sequence-level `normalTransition`
calls remain unchanged because that name is already the canonical framed alias.
No endpoint-radius hypothesis, compatibility wrapper, or public theorem rename
was introduced.  The complete selected-branch prerequisite chain through
`StepCSupportCapstone` has now been exact-refreshed on the framed semantics, and
this file passes focused Lean verification against those current artifacts.
Static source and diff review also passed.  Its exact target refresh then
completed successfully against the same canonical framed dependency chain.

The framed source migration and current module verification are 100%.  The live
`MetricCompactBase.exists_b1_raw` declaration already has a complete proof
body, but its canonical framed downstream validation is still in progress and
must not yet be reported as a fully revalidated producer.  The separately named
textbook Step B1 theorem and unconditional compactness endpoints remain
theorem-level 0%.  Dedicated B1 machinery is about 95%, Chapter 4 machinery
about 87%, and whole-HCG compactness machinery about 60%.

## 2026-07-15 checked identification seam

`uniqueStage_of_fill` proves that a local `CenterInput` for any active-filled
version of the actual direct stage targets supplies
`HasUniqueStageCenter` for the original finite-stage energy.  The proof routes
through energy invariance at zero-weight slots, so every local implicit branch
is identified through the same global minimizer.  It never compares local limit
weights across overlapping source charts.

`stageCompare_eq_cm` completes the identification: on the controlled source
ball, the global `stageComparisonMap` equals the `centerOfMass` selected from
any such filled local input.  The equality follows from global minimizer
uniqueness and is independent of the proof object used by the map definition.

Focused verification and the exact stage-comparison target refresh passed.
This proof-choice-independence seam is complete
(100%).  It does not provide a smooth active-slot filler, a moving common-domain
implicit solver, or an all-pairs chart tail.  Those are the current analytic
frontiers; `StepB1RawInput` and textbook B1 remain theorem-level 0%.

## 2026-07-16 all-pairs actual-map tail

The stage comparison layer now identifies the actual chart-independent
`stageComparisonMap` with the canonical moving root on one rectangular
all-pairs tail. The checked chain retains:

- the exact root readout in every live source chart;
- the root's membership in the target `normalBall`;
- direct decoding of the global map through the target normal exponential;
- target `normalExpPD.target` membership;
- one finite maximum over live source slots for smoothness and arbitrary
  finite `mapDerivNorm` order;
- the base-level `MetricCompactBase.exists_stage_data` producer on the
  single master subsequence.

The local limit weights remain source-chart local and are never compared on
overlaps. Focused verification passed for the exact root/readout and common
jet tail. The next checked consumer is the local-diffeomorphism tail, using
the generic coordinate-conjugation IFT adapter and this retained target
membership.

Exact global stage-map/root identification, the smaller-radius actual-map
chart-jet producer, the finite-source common pair tail, and
`exists_stage_data` are each **100%**. The all-pairs local-diffeomorphism and
global-injectivity theorem is still theorem-level **0%** until stated and
checked; its dedicated machinery is about **80%**. The concrete
`StepB1RawInput` producer and textbook B1 remain theorem-level **0%**.
Dedicated Step-B/B1 machinery is about **98%**, Chapter 4 machinery about
**90%**, and whole-HCG compactness machinery about **60%**.

## 2026-07-27 controlled-chart root readout

`actual_cm_tail` now returns `HasChartCmSol` at the selected legacy provider
and calls `exists_hat_cmC_at`. `stage_root_tail` consumes the packaged
`HasCmSolC`, obtains selected-branch target membership through
`HasCmSolC.target_mem`, and obtains the inverse-velocity root equation through
`HasCmSolC.invVel_zero`. Center decoding uses the saved restricted-chart target
membership rather than a separately expanded framed-chart source field.

The source migration is applied but not yet focused-verified because the new
lower exports are not current. The next check follows the ordered exact refresh
of `NormalBranchHessian`, `NormalBranchCage`, and `StepCHatReadout`.

## 2026-07-16 actual-map local diffeomorphism and pointed field

`HasStageJetData.hloc_tail` is now focused-green.  On every retained source
ball of radius strictly below the construction radius, it covers a point by
one live normal chart, restricts to an open intermediate-radius coordinate
neighborhood, obtains derivative invertibility from the order-one
`mapDerivNorm` estimate, and applies the generic coordinate IFT adapter to the
actual global `stageComparisonMap`.  The proof uses no chart selector in the
map definition and adds no endpoint-radius assumption.

The same package now retains `HasStageBaseTail`.  Its producer consumes the
existing finite item-3 scale tail and the focused-green exact theorem
`stageCompare_base`, so the actual maps satisfy `F_{k l}(O_k)=O_l` on one
rectangular tail.  This is the first directly filled field of the eventual
`StepB1RawInput`; it is producer output rather than a new assumption.

Actual-map local diffeomorphism and exact pointed preservation are each
**100%**.  Global injectivity remains theorem-level **0%**: the next producer
must retain the quantitative deep-core slack already present in the finite
source-cover proof, then prove target-ball and approximate-return tails.
`StepB1RawInput` and textbook B1 remain theorem-level **0%**.  Dedicated
Step-B/B1 machinery remains about **98%**, Chapter 4 machinery about **90%**,
and whole-HCG compactness machinery about **60%**.

## 2026-07-16 jet-tail persistence

`HasStageJetTail.subseq` is now checked for every further strict refinement.
The proof uses `stageCompare_subseq` for the actual global map and the existing
source-ball/center reindex identities; the earlier attempted definitional
`rfl` was invalid because the map contains dependent unique-center choices.
Focused verification and the exact module refresh passed after migrating the
four projection-only `StepCStageFill` consumers of the strengthened buffered
cover package.

This closes the persistence seam required by a later integer-radius diagonal.
The master-radius construction itself is not yet proved.  `StepB1RawInput`,
global injectivity, and textbook B1 remain theorem-level **0%**; dedicated
Step-B/B1 machinery is roughly **98%**, Chapter-4 machinery roughly **90%**,
and whole-HCG machinery roughly **60%**.

## 2026-07-16 retained metric core

`HasStageJetData` now retains, inside its existing per-source metric package,
the containment of `C1 alpha` in the phase-radius ball on which `gInf alpha`
and the stage normal-coordinate metrics converge.  This is producer output,
not a new assumption: `exists_stage_data` derives it from the already checked
`C1 alpha ⊆ ball 0 (q alpha / 2)` and
`6 * q alpha < normalRadius.phaseRadius (rInf alpha + 1)` estimates.

Focused verification and the exact module refresh passed.  This closes the
domain-alignment seam needed to instantiate the generic pullback-form
convergence theorem on the retained compact source cores.  The intrinsic
metric-error theorem itself remains theorem-level **0%**; its dedicated
machinery is about **90%**.  `StepB1RawInput` and textbook B1 remain
theorem-level **0%**; dedicated Step-B/B1 machinery is about **98%**, Chapter 4
machinery about **90%**, and whole-HCG compactness machinery about **60%**.

## 2026-07-16 full-package subsequence persistence

`HasStageBaseTail.subseq` and `HasStageJetData.subseq` are now checked. A
further strict refinement preserves the exact pointed tail, the buffered
source-cover package, the retained normal-metric convergence and ellipticity,
and every finite-order actual-map jet tail. The only local repair was to
identify the two iterated `NetLimitData.subseq` structures by eliminating the
underlying structure; their proof fields are propositionally irrelevant but
the two structures are not definitionally identical at the rewrite site.

Focused verification and the exact module refresh passed. This closes the
routine persistence API needed by the integer-radius master diagonal; the
seed/step diagonal theorem itself remains theorem-level **0%**. Global
injectivity remains theorem-level **0%** with dedicated machinery about
**80%**. `StepB1RawInput` and textbook B1 remain theorem-level **0%**;
dedicated Step-B/B1 machinery is about **98%**, Chapter 4 machinery about
**90%**, and whole-HCG compactness machinery about **60%**.

## 2026-07-27 H6 Gate 4 replay

The selected root proof now consumes provider-aware `HasChartCmSol` data and
reconstructs the selected branch target and zero equation directly from the
packaged `HasCmSolC` source/domain/zero fields. The decode uses the controlled
chart's restricted inverse rather than a legacy source-membership expansion.
One redundant `dsimp` was removed after `HasChartCmSol` was already unfolded.

The complete legacy-provider replay through Support, StageComparison, and
StageSeed passed in an isolated current-artifact tree. All preceding failures
were traced to stale exports in the Atom, SourceCover, NormalMetric,
StageMap/Fill, and inverse-velocity layers. Formal artifact refresh remains
pending while an unrelated writer is active.

Gate 4 is source-complete. Gate 5 now begins at `HasDiagPairConv`; the selected
diagonal, fence, stage configuration, inverse-velocity equation, and root
readout must carry one `NormalChartFamily` before the H6 provider can replace
the legacy provider. `exists_h6NormalData` remains theorem-level 0%; branch
parameterization is about 45%, all-order jet machinery about 35%, and overall
dedicated H6 producer machinery about 58%.

## 2026-07-28 Gate 5 coherent stage-map handoff

`uniqueStage_of_fill` and `stageCompare_eq_cm` now take an optional
`NormalChartFamily`, defaulting to `legacyChartFamily`, and thread it through
the active fill, unique-center predicate, global stage map, and energy
identification. The focused file check passed. Source-visible legacy defaults
exposed by the already-refreshed `StepCStageMap` signature were repaired
without a chart-agreement assumption.

`H6NormalData.weight_trans_mem` closes the source half of the nonzero-weight
decode bridge. It pulls actual gamma-hat membership from `seqWeights_data`,
uses `hat_dist_centerD` and `lamInf_lt_halfMin` against the H6 branch radius,
and invokes `H6ChartData.readout_mem` to identify and bound the same provider
chart inverse used by `stagePtsSub_eq_raw`. The focused file check passed. No
legacy nesting estimate or inverse-law assumption is used.

The next target is target-stage alpha-chart membership and decode for the raw
two-transition point, followed by the chart-parametric H6 `pts_target_tail`.
The direct distance constants must be checked explicitly; failure to compare
the active target scale with the alpha H6 radius is a mathematical blocker,
not a reason to reintroduce the `205 * exp(...)` legacy nesting bound.

That check is now exact.  For an interacting pair, `BInter` and the H6 radial
readout bound the raw target distance from the alpha center by
`5 * lamInf_alpha + 9 * lamInf_gamma`.  The reverse radius comparison bounds
`lamInf_gamma` by
`exp(C * (10 * lambda D 0)) * lamInf_alpha`.  On the other hand, the existing
`hqdata` inequalities force `48 * aMin < d.ratio`; with `hphys` and
`d.radius_eq`, the alpha H6 chart radius is therefore strictly larger than
`384 * lamInf_alpha`.  The remaining sufficient constant inequality is

`5 + 9 * exp(C * (10 * lambda D 0)) < 384`.

The current abstract `H6NormalData` does not retain a bound on
`d.ratio * inp.decay.mu 0`, so this inequality is not provable for arbitrary
`C`.  The concrete `h6Ratio` construction can supply the missing genuine
geometric fact after its launch radius is capped by one:
`d.ratio * inp.decay.mu 0 <= 1/2`.  That fact would imply
`lambda D 0 < 1 / (768 * exp C)` and close the displayed inequality via
`exp 1 < 3`.  The minimal next producer is therefore to retain this
normalization in `H6NormalData`; no synonym overlap assumption was added.
The producer file is currently protected by another existing claim, so it was
not edited or force-released.

The other routes do not remove this gap: the branch-radius ledger alone gives
only `32 * lamInf_alpha`, totalized transition convergence cannot supply a
`PartialEquiv` inverse law outside the target, and the legacy nesting constant
is too large for the H6 radius.  This is a missing quantitative producer/API
field, not a coercion or elaboration failure.

Gate 5 provider substitution is about 45%. The
dedicated H6 producer is 100%; the unconditional MSM135 endpoint is still
unstated and therefore 0%, and whole-HCG supporting machinery remains about
60%.

## 2026-07-29 H6 target decode and provider seam closure

The normalized H6 ratio closes the formerly missing pair-radius estimate:
`ratio_gt_48`, `pair_lam_lt_three`, `stage_radius_gt`, and `stage_rho_le`
give direct source and target membership without the oversized legacy nesting
bound. `target_mem` and `pts_target_tail` then decode the raw stage target in
the same H6 chart used by the weights.

`HasStageRootReadout`, `uniqueStage_of_fill`, `stageCompare_eq_cm`,
`HasStageJetTail`, and `HasStageBaseTail` are chart-parametric with legacy
defaults. Focused and exact verification are GREEN (`4142/4142`). The H6
specializations live in `StepCStageComparisonH6`.

The target-decode and comparison-map migration is complete (100%). Gate 5
provider substitution is complete after the H6 support producer and its direct
consumer are included. This does not state or prove the unconditional MSM135
endpoint, which remains 0%; whole-HCG supporting machinery is about 70%.

## 2026-07-29 selected-subsequence branch input

`H6NormalData.actual_cm_tail` now consumes its branch data on the already
selected subsequence `L.subseq hphi`, exactly matching every stage-map use in
the proof. No extra eventual transport or stronger branch assumption is
needed. Focused and exact verification are GREEN (`4142/4142`).

The generic provider boundary remains complete. The concrete H6 master
stage-data producer is recorded in `StepCStageComparisonH6`.
