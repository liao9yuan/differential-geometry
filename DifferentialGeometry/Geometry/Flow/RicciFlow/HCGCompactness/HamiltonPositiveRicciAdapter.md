# HamiltonPositiveRicciAdapter

## 2026-07-26 buffered Shi derivative input

The canonical source index now retains both the requested
`[-ham3_r0^2, 0]` window and the strict earlier Shi buffer
`[-2 * ham3_r0^2, 0]`.  The carrier and regular-time inclusions into each
untruncated rescaled solution are focused-verified.

`source_deriv` is a data constructor, not a theorem wrapper.  It applies the
constants-first compact estimate `movingRmOn` to each genuine untruncated
rescaling, restricts the result to the closed source interval, and packages the
uniform spacetime bounds together with the time-zero projection
`FlowDerivBounds.at_time`.  The time-restriction equality is proved directly
from the unchanged `SolutionOn.base`, avoiding a transported tensor equality.
The complete Adapter passes focused verification.  Its exact artifact refresh
against the newly exported `CurvTowerBridge` artifact is green
(`10165/10165`).  Independent axiom replay for `curvNormSq_eq`, `movingRmOn`,
and `source_deriv` reports only `propext`, `Classical.choice`, and `Quot.sound`;
no `sorryAx` enters this chain.

The former explicit dependency `curvNormSq_eq` is now proved by the scalar
slot-evaluation arity bridge in `CurvTowerBridge.lean`.  No whole-tensor cast,
consumer assumption, or replacement black box remains in this path.
Consequently:

- constants-first compact Riemann-tower producer: 100%;
- strict Hamilton buffer and source restriction: 100%;
- `source_deriv` and its `FlowDerivativeInput` production: 100% checked;
- closed-endpoint compactness upgrade theorem: 0%;
- `ham3_cgh_limit`: theorem-level 0%;
- whole-HCG dedicated machinery: about 60%.

The next endpoint boundary was rechecked against the live compactness APIs.
It is a genuine closed-endpoint analogue of `open_upgrade_canon`, producing
`FlowUpgradeData` and limit completeness when the common carrier is `Icc` and
the regular set is `Ioo`.  The existing open theorem requires zero to be an
interior time, while the older regular-slab theorem requires the endpoint to
belong to the regular set; neither can consume the Hamilton source.

Even after that new producer, unconditional `Ham3CGHLimitExists` has two
separate upstream gaps: Hamilton data do not yet construct the complete
`MetricCompactnessInputs` package, and `toHam3Exists` still asks for
connectedness plus the legacy Ricci-nonnegative/scalar-positive/pinching
transfer package.  Adding a conditional wrapper would only rename these
frontiers, so none was added.  A scalar strong maximum principle is not the
next missing theorem.

## 2026-07-25 canonical closed-window source sequence

Added the actual tail-reindexed Hamilton source rather than an existential
placeholder:

- `ham3SourceSeq` chooses the eventual window index from `Ham3Window`, uses
  `origIndex i = N + i`, restricts each genuine `ham3RescaledSol` to the common
  interval `[-ham3_r0^2, 0]`, and transports `IsSolutionOn` with the proved
  carrier and regular-set inclusions.
- `sourceSeq_carrier` and `sourceSeq_regular` expose the exact `Icc`/`Ioo`
  domains.
- `ham3SourceLink` supplies the identity diffeomorphisms, original indexing,
  basepoints, metrics, and scalar identities required by the existing
  `Ham3SourceLink` interface.

Focused verification passes. The identity-metric proof was deliberately
reduced to the scalar normal form `inner x v w`; replacing the whole
cross-model pullback metric by the same-model pullback made the focused check
roughly four times slower. No new consumer assumption, compactness witness, or
transfer predicate was added. The later buffered-Shi section supersedes this
historical artifact status.

The closed interval is the mathematically correct domain: time zero is in its
carrier but not its regular set. It can feed the carrier-generic
`compactnessSol_cond`, but not the legacy `compactnessSol` or
`open_upgrade_canon`, which require time zero to be interior to an open
interval. The Hamilton endpoint Shi/tower estimate and its concrete
`FlowDerivativeInput` are now supplied by `source_deriv`. The next honest
producer is the closed-endpoint `FlowUpgradeData`; limit connectedness remains
a separate topology projection after compactness.

Accounting: the canonical common-window source, source-link data, and
derivative input are 100% implemented and focused-verified. The distinct
closed-endpoint upgrade theorem is not yet stated or proved (0%), although it
can reuse the largely checked generic P4 machinery. `ham3_cgh_limit` therefore
remains theorem-level 0%, and whole-HCG supporting machinery remains about
60%.

## 2026-07-25 time-zero round limit and original-metric transfer

Added two honest final-assembly theorems over the raw common-window source and
the actual smooth-CGH witness:

- `round0_of_cgh` combines `tf_decay0_of_cgh`, `tf_zero_of_decay`,
  `limitEinstein_of_tf0`, retained base-scalar convergence, Schur constancy, and
  the ambient boundaryless/connected limit data to prove `LimitRoundAt Lh 0`.
- `const0_of_cgh` applies `limit_to_orig` to that exact time-zero slice and
  produces the canonical conclusion `AdmitsConstPosSec M`.

Both theorems pass focused verification. They do not consume
`Ham3PinchTransfer`, `LimitScalarPos`, `Ham3RicNonnegTransfer`, a scalar strong
maximum principle, or any newly introduced transfer predicate. The static
time-zero endgame is therefore 100% once the raw source sequence and genuine
smooth-CGH limit witness are supplied. Current exact-artifact status is
recorded in the top section.

This is infrastructure/conditional assembly, not construction of the
compactness witness: `ham3_cgh_limit` remains theorem-level 0%, its genuine
remaining frontier is the common-window source plus unconditional smooth-CGH
producer, and whole-HCG supporting machinery remains about 60%.

## 2026-07-24 fixed-time trace-free decay producer

Added `tf_decay0_of_cgh`, the direct time-zero transfer theorem for
`LimitTfDecayAt L 0`.  It combines the retained smooth-CGH scalar and intrinsic
Ricci-norm pullback convergence into convergence of
`|Ric|² - R² / 3`, freezes both source and limit functions at time zero, and
uses `FunctionPullbackTendsto.le_of_bound0` with the bound from
`ham3_tf_bound0` and the vanishing scale factor from `ham3_scale_decay`.

The source comparison is geometric rather than an added transfer predicate:
`Ham3SourceRealizes.metric_eq` identifies the source metric with the
cross-model pullback of the selected rescaling, and `tfRicNormSq_cross`
identifies the fully evaluated trace-free Ricci norms.  No new consumer
assumption, desired-conclusion wrapper, or strong maximum principle input was
introduced.

Focused verification passed after normalizing the fully applied scalar source
expression before rewriting the stored metric equality.  Thus
`tf_decay0_of_cgh` and its dedicated fixed-time transfer machinery are each
100%.  This does not complete the compactness endpoint:
`ham3_cgh_limit` remains theorem-level 0%, and the whole HCG machinery remains
about 60%.

## Current state — 2026-07-09 source realization and witness binding

`Ham3SourceLink` is now data, parameterized by the actual point-selection
witness.  It records the common-time inclusion, selected basepoint map, and
equality between each source metric and the pullback of the corresponding
`ham3RescaledSol` metric, while retaining the separate base-scalar identity.
`Ham3SourceLink.realizes` converts these fields mechanically into
`Ham3SourceRealizes` for the concrete `cghToHam3` record.

`HamCGHConclusion` now binds Ricci transfer, scalar positivity, and pinching
transfer inside the existential scope of the actual `L`, subsequence, smooth-CGH
witness, and completeness proof.  `toHam3Exists` no longer asks for any of
those conclusions for every arbitrary `Ham3CGHLimitData`, and boundarylessness
is obtained from the ambient model instance rather than presented as a fake
limit-topology producer.

Focused verification and the targeted adapter refresh passed after one local
namespace qualification.  The adapter contract is 100% checked infrastructure; construction of the actual
common-window source and the Hamilton compactness producer remain 0%.  Whole
HCG machinery remains about 45%, and endpoint theorems remain 0%.

The dated material below is historical unless an individual section explicitly
says otherwise.

## 2026-07-09 noncollapse cleanup

Removed the zero-callsite `noncollapseInput_of_ham3` projection and the arbitrary
numeric `NoncollapseInput` type it targeted.  The adapter must eventually
construct or identify the actual Hamilton rescaled `PointedFlowSeq`, prove
`IsFlowBaseVolBound`, and cross the single `flowInj_of_vol` CGT frontier.  A
basepoint scalar equality alone is insufficient to identify those flow balls.

Focused adapter verification is currently blocked before elaboration because
the shared workspace lacks `Lemma45Engine.olean` while that upstream source is
claimed by another active lane.  No adapter-local error has been observed.

Source used: the current `HamiltonPositiveRicci.lean` black-box interface around `Ham3CGHLimitData`, `Ham3LimitSubseq`, `Ham3LimitWindow`, `Ham3LimitFlow`, `Ham3CGHLimitExists`, and `ham3_cgh_limit`.

Introduced definitions: `pointedFlowToHam3` and theorem `toHam3Exists`.

2026-05-26 update: added `ham3OfCompactSol`, which is the intended derivation
shape for the Hamilton `ham3_cgh_limit` black box from the MSM135 Theorem 3.10
wrapper `compactnessSol`.  It takes the rescaled pointed-flow sequence `X`,
the three compactness inputs `CompleteInput`, `CurvBoundInput`, and `InjInput`,
the explicit time-zero metric compactness inputs, the derivative-input record,
and the smooth-flow upgrade backend. It then applies `compactnessSol` and feeds
the result through `toHam3Exists`.
The remaining explicit inputs are the Hamilton-specific limit-window,
regular-window, connectedness/boundarylessness, and tensor/scalar convergence
transfer producers.

Relation to `Ham3CGHLimitExists`: the adapter forgets the new convergence fields down to the current Section 12 limit-data record. The old proposition does not yet store the source rescaling relation, so the adapter needs the new compactness conclusion plus the fixed closed time-window inclusion and open regular-window inclusion.

2026-05-26 update: `Ham3CGHLimitExists` now also records connectedness and
boundarylessness for the limit.  The generic HCG `PointedFlowData` record does
not yet store those global manifold facts, so `toHam3Exists` takes them as
explicit adapter inputs rather than hiding them in the compactness conclusion.
This keeps the adapter checked while preserving the honest frontier: a future
CGH producer should prove connectedness/boundarylessness for limits of the
closed connected source manifolds.

2026-05-26 update: `Ham3CGHLimitExists` now also records basepoint scalar
convergence, the `Ham3RicNonnegTransfer` datum used by the Section 12 Ricci
nonnegativity inheritance step, and the `Ham3PinchTransfer` datum used by the
trace-free Ricci argument.  The adapter takes these as explicit inputs from the
HCG side; it does not pretend that the generic `PointedFlowData` record alone
contains those tensor/scalar/function-pullback convergence facts.

2026-05-27 update: `ham3OfCompactSol` was adjusted after `compactnessSol`
became an honest Theorem 3.10 wrapper requiring derivative and smooth-flow
upgrade inputs; the adapter still does not edit `HamiltonPositiveRicci.lean`.

2026-05-27 review update: after the pointed Riemannian rename and removal of
public `smoothPlus` fields from generic HCG data, the adapter now derives the
old `Ham3CGHLimitData.smooth_plus` field locally from `L.smooth`. The adapter
still only forgets the generic HCG conclusion into the old Hamilton endpoint
and does not edit `HamiltonPositiveRicci.lean`.

2026-05-27 update: added the first Hamilton transfer producer from the generic
smooth CGH convergence scaffold.  `Ham3BaseScalarSeq` records only the source
realization needed here: the time-zero basepoint scalar of the generic pointed
flow sequence is the Hamilton rescaled scalar from `(P,Q)`.  Then
`baseScalarConv_of_smoothCGH` proves `Ham3LimitBaseScalarConv` from
`SmoothCGHConverges.scalar_converges` and the comparison maps'
`basepoint_map`.  Consequently `toHam3Exists` and `ham3OfCompactSol` no longer
take the broad `hbaseScalar` transfer input; they take the narrower source
realization input and derive the scalar convergence internally.

Verification: focused checking passed for this file after refreshing stale
upstream HCG and curvature artifacts.  A later targeted adapter build was
blocked by an unrelated upstream failure in `DimensionThree/RicciControlsRm`;
the adapter source itself elaborated successfully.  Remaining explicit
Hamilton-specific inputs are connectedness, boundarylessness, Ricci
nonnegativity transfer, and pinching transfer.

2026-05-27 shape cleanup: moved connectedness and boundarylessness out of the
late Hamilton adapter assumptions.  The adapter now introduces
`HamCGHConclusion`, a Hamilton-specific strengthened compactness conclusion
containing the ordinary `SmoothCGHConverges` witness plus limit connectedness
and boundarylessness.  The package `HamCGHTopology` is the honest upstream
frontier: it should be proved from the connected/boundaryless source manifold
and the CGH construction, then used to lift `solutionCompactness`'s ordinary
`CompactnessConclusion`.  Consequently `toHam3Exists` consumes
`HamCGHConclusion`, while `ham3OfCompactSol` consumes `HamCGHTopology` and no
longer asks for per-limit `hconnected`/`hboundaryless` functions.

Verification: blocked before adapter elaboration by upstream Rm04 slot
migration failures in `RicciFlow/Evolution/ImprovedPinching/Definitions.lean`.
The visible upstream errors are old output/slot order assumptions now expecting
the corrected first-two input skew and standard `Rm04` order.  Re-run this file
after `ImprovedPinching.Definitions` is repaired.

2026-05-27 noncollapse producer update: added `noncollapseInput_of_ham3`,
which turns Hamilton's geometric `Ham3Noncollapse` ball/volume package into
the legacy HCG `NoncollapseInput` volume slot.  Because the Hamilton package is
eventual in the selected index while `NoncollapseInput` is currently a numeric
all-index record, the finite prefix is saturated by the lower-bound value
itself.  This does not prove the real noncollapse-to-injectivity-radius bridge;
that remains the next compactness producer needed by Theorem 3.10.

Verification: focused checking passed for this file.

2026-05-27 injectivity update: `ham3OfCompactSol` now carries `[I.Boundaryless]`
to pass the real normal-coordinate `FlowBaseInjBound` through
`compactnessSol`.  The adapter still does not edit `HamiltonPositiveRicci.lean`
and does not bridge the legacy `InjInput` to the new injectivity-radius
predicate.

Verification: focused checking of this adapter passed after the injectivity
update.  The targeted adapter module build and umbrella import are blocked by
the unrelated upstream `RicciFlow/Evolution/ImprovedPinching/Wrappers.lean`
slot-order mismatch at line 133, where the available `hRm` statement has the
last four slots ordered differently from the wrapper theorem input.

2026-05-27 alias cleanup: removed the HCG `LimitFlowData` abbrev and rewrote
the adapter directly over `PointedFlowData`.  The old namespace helper
`LimitFlowData.toHam3` is now the standalone adapter `pointedFlowToHam3`.

## 2026-06-19 comment cleanup

Moved source-comment lessons from `HamiltonPositiveRicciAdapter.lean` into this
same-name note.  The Lean comments now describe adapter interfaces without
embedding dated implementation plans.

Lessons preserved from the source comments:

- `HamCGHTopology` is consumed by the adapter.  Its producer belongs upstream in
  the CGH construction/source-topology transfer layer; connectedness and
  boundarylessness should not be treated as scalar or tensor convergence
  consequences.
- `noncollapseInput_of_ham3` only projects Hamilton's geometric noncollapse
  package into the legacy numeric `NoncollapseInput` slot.  Because the legacy
  record is all-index numeric data while the Hamilton package is eventual in the
  selected index, the finite prefix is saturated by the lower-bound value.  The
  real geometric producer remains the noncollapse-to-injectivity-radius bridge
  used by the Theorem 3.10 compactness interface.
- `toHam3Exists` forgets the strengthened HCG conclusion down to
  `Ham3CGHLimitExists`, including the fixed time window, regularity on the open
  window, topology facts, Ricci-flow predicate, Ricci nonnegativity transfer,
  basepoint scalar convergence, and pinching transfer.
- `ham3OfCompactSol` remains the intended replacement shape for the old
  `ham3_cgh_limit` black box: construct the pointed rescaled-flow sequence,
  prove the compactness inputs and smooth-flow upgrade inputs, then supply the
  Hamilton-specific scalar/tensor transfer producers from smooth CGH
  convergence.

Verification: focused checking passed for this cleanup pass.

## 2026-07-09 convergence-data retention

The old `pointedFlowToHam3` forgetful constructor was removed.  Its replacement
`cghToHam3` stores the actual source `PointedFlowSeq`, original Hamilton index
map, both strict-monotonicity proofs, `SmoothCGHConverges` witness and comparison
maps, source-to-original-manifold diffeomorphisms, and all-time limit
completeness.

`Ham3SourceLink` now exposes the original indexing and source topology instead
of pretending that a scalar equality alone realizes the Hamilton rescalings.
The stronger `HamCGHConclusion` includes limit completeness.  The arbitrary
`HamCGHTopology.lift` desired-conclusion wrapper and zero-callsite
`ham3OfCompactSol` were deleted; the adapter stops honestly at
`toHam3Exists` until the generic smooth-CGH limit-completeness/topology producer
is available.

The adapter theorem machinery is structurally complete, but the actual
common-window Hamilton source producer is about 20% and the Hamilton compactness
endpoint remains 0%.

## 2026-07-27 closed-window spatial jets

`ham3_stage_jet` is proved and exact-green.  It uses the untruncated Hamilton
rescaled solution as the ambient regular flow, restricts it to the CGH target
domain, pulls it back to the source domain, and applies
`ConvOut.gSeqJet_of_soln`.  The canonical closed window lies strictly inside
the ambient Shi window because the source start retains the earlier buffer.
The scalar metric realization is definitional after full evaluation; no new
consumer assumption or whole-metric equality was added.

`ham3_limit_jets` is also proved and focused-green.  It combines
`ham3_stage_jet`, the bump-family grow cover, and
`ConvOut.gramJets_of_stage` to obtain every finite spatial chart jet of the
Hamilton limit metric continuously on the full closed interval
`Icc (-(ham3_r0 ^ 2)) 0`.  This discharges the actual Hamilton stage-regularity
premise rather than repackaging it as a hypothesis.

The two jet producer theorems are 100%.  The closed `IsSolutionOn` assembly is
still unstated and therefore 0%; its dedicated machinery is about 90%.
`ham3_cgh_limit` itself remains an unproved endpoint (0%), and whole-HCG
machinery remains about 60%.

## 2026-07-27 closed-window Gram smoothness

`ham3_gram_smooth` specializes the generic closed-window bootstrap to
`Icc (-(ham3_r0 ^ 2)) 0` and feeds it with `ham3_limit_jets`.  It proves joint
`C∞` chart-Gram regularity on the full retained window, including time `0`;
no endpoint regularity assumption or new convergence package is introduced.

Focused verification passes.  Exact artifact refresh is pending at the time of
this note update.  The theorem and its dedicated machinery are 100% at source
level.  Closed `IsSolutionOn` is still unstated (0%), with dedicated machinery
about 96%; the remaining producer is the invariant metric PDE followed by
direct record assembly.  `ham3_cgh_limit` remains 0%, and whole-HCG machinery
is about 61%.

## 2026-07-27 closed limit solution assembly

`ham3_limit_soln` is now stated and proved at source level.  It combines the
closed metric-family package, the invariant limit metric PDE, and the
chart-Gram joint regularity consumers for scalar, Ricci, and lowered-Riemann
continuity with `isSolutionOn_of_reg`.  The source carrier is definitionally
the canonical `Icc`; no endpoint regularity, coefficient-bound package, or
synonymous solution assumption was added.

The ordered upstream refresh is exact-green, the Adapter focused check passes,
and the Adapter exact artifact refresh is green (`10190/10190`).
`#print axioms` for `ham3_limit_soln` reports only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`.  The theorem and its
dedicated common-window solution machinery are therefore 100%.

`ham3_cgh_limit` itself remains a separate unproved endpoint (0%).  The next
conditional producer is a closed-window `FlowUpgradeData` plus completeness
assembly; the next unconditional producer is the time-zero
`MetricCompactBase`.  Perelman noncollapsing supplies only fixed-scale
basepoint-ball volume data and does not replace the A0-prime arbitrary-center
overlap or H6 inputs of that metric-compactness bundle.
