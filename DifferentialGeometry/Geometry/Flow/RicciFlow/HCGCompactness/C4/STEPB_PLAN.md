# STEP B PLAN - local metrics, transition maps, and large-ball approximate isometries

Written 2026-06-13 for the planning/acceptance lane.  This file is the
self-contained execution plan for MSM135 Chapter 4 Step B, lines 1370-1882 of
`RicciFlow/RicciFlowBooksLatex/MSM135/tex/chapters/chapter4.tex`.

Do not treat this plan as Lean progress.  The Step B endpoint
`lbl397` / large-ball approximate isometry is still 0% as a Lean theorem until
it is stated and proved.  The metric-limit and transition-limit endpoints in
`lbl394` are also 0% as Lean endpoints; this plan only fixes the route and
execution order.

## Mandatory Reading

Every executor reads these before editing:

1. `CLAUDE.md`.
2. This file, especially the relevant brick, acceptance, coordination, and
   traps sections.
3. `chapter4.tex` lines for the brick:
   - `lbl394` metric/transition limits: 1370-1500.
   - `lbl395` normal-coordinate metric bounds: 1410-1437.
   - `lbl396`-`lbl397` large-ball approximate isometry: 1503-1523.
   - `lbl399`: 1525-1559.
   - `lbl402`-`lbl405`: 1721-1881.
4. Same-name notes carrying inputs: `MapConvergence.md`,
   `IsometryCompactness.md`, `StepBInputs.md`, `B0NormalCoordBounds.md`,
   `ConvexBalls.md`, `ExpBallDiffeo.md`, `GoodCoveringItem3.md`,
   `ApproxIsometryCompHigher.md`, `Lemma45F4.md`, plus `CHAPTER4_PLAN.md`
   section 2 and section 3.
5. Root `convention.md` and `dictionary.md` for tensor/component and
   RicciFlower-boundary conventions.

## Feasibility Verdict

Step B is mathematically feasible with one new analysis bridge.

The two limits in `lbl394` reduce to existing or legitimate inputs:

- Metric limits: `lbl395` normal-coordinate metric bounds give uniform
  Euclidean derivative bounds for the pulled-back local metrics; Arzela-Ascoli
  for maps gives a local smooth limit metric.
- Transition limits: S6 / `ExpInverseDerivBoundInput` gives uniform derivative
  bounds for normal-coordinate transition maps; F8 / `isometry_seq_diffeo`
  supplies the smooth limit transition map and inverse/cocycle argument.
- The only new analysis bridge for `lbl394` is the partial-domain problem:
  current F7/F8 are total-map theorems on `Set.univ`, while Step B maps and
  metrics live on nested Euclidean balls.

`lbl397` is gated on Step C's center-of-mass machinery (`lbl410`, especially
`lbl434` and `lbl436`).  The local metric and transition limits are not gated
on Step C.

Loud caveat for later acceptance: the F5/F6 approximate-isometry algebra
currently consumes `Lemma45F4.lean:lemma45_corII`, whose live proof still has a
documented mechanical `sorry`.  That does not block `lbl394`, but final
acceptance of `lbl405`/`lbl397` as axiom-clean is blocked until that F4
assembly is discharged or the endpoint is explicitly recorded as depending on
that frontier.

## Planner Rulings

### PLANNER RULING Q1 - `lbl395`

Take `lbl395` as an honest input now.

Reason: MSM135 explicitly cites Hamilton [H6] Corollary 4.12 for the normal
coordinate metric bounds.  The native Jacobi/Gronwall route is real and useful,
but it is a multi-session optional discharge path.  Blocking Step B on that
native proof would add a second large frontier before the partial-domain bridge
is settled.

Implementation consequence: add a `NormalCoordMetricBoundInput`-style honest
input near `StepBInputs.lean`, sibling to `ExpInverseDerivBoundInput`.  It must
record constants first, then expose:

- Euclidean uniform equivalence of each local normal-coordinate pulled-back
  metric to the standard metric on the relevant ball.
- Uniform bounds for all Euclidean iterated derivatives of the local metric
  map on compact subsets of the relevant ball.

Keep the native `B0NormalCoordBounds.md` route as optional later discharge, not
as a dependency of the first Step B implementation pass.

### PLANNER RULING Q2 - partial domains

Choose localized F7/F8 as the main bridge.

This is option (a) from the handoff, implemented with the book's nested-domain
policy from option (c): prove reusable localized convergence theorems, then
apply them on `E alpha`, `barE alpha`, and `vecE alpha` with the book's
shrink/containment relations.

Do not use a smooth cutoff extension as the main route.  It creates extra
extension data, risks proving convergence of an artificial total map, and does
not match the book's purpose for the nested balls.

Implementation consequence: create a localized convergence layer, tentatively
`StepBLocalizedAA.lean`, importing but not editing `MapConvergence.lean` and
`IsometryCompactness.lean`.  The target API should return
`MapCInfConvOnCompacts U ...` for an open domain `U`, from smoothness and
derivative bounds on compact subsets of `U`.  The localized F8 should also have
a local inverse/cocycle theorem; do not force everything through `Set.univ`.

### PLANNER RULING Q3 - metric convergence engine

Reuse the map convergence engine for local metric maps.

The coordinate metric is a map
`E -> ContinuousMultilinearMap Real (fun _ : Fin 2 => E) Real`
or an equivalent continuous bilinear-form target.  Since `E` is finite
dimensional, the target is finite dimensional by the same route as
`MapConvergence.cmm_finiteDimensional`.  No dedicated metric Arzela-Ascoli
engine is needed.

Implementation consequence: the B-metric brick should feed the bilinear-form
valued metric map to localized F7.  It should separately preserve
positive-definiteness/uniform equivalence from the `lbl395` input.

### PLANNER RULING Q4 - data layout

Keep Step B at model-coordinate level as long as possible.

Use model maps and model metric forms:

- `H_k^alpha` and restrictions only as the source of coordinate data;
- transition maps as `E -> E` functions, matching `normalTransition`;
- local metrics as `E ->` bilinear forms;
- manifold-level objects only through existing Step A / PointedRiemannian
  bridges such as `GoodCoveringItem3.exists_seqItem3Diffeo`.

Recommended file split:

- `StepBInputs.lean`: honest inputs only (`NormalCoordMetricBoundInput` plus
  existing S6).
- `StepBLocalizedAA.lean`: localized F7/F8 and local inverse/cocycle support.
- `StepBLocalMetrics.lean`: `lbl394` metric limits.
- `StepBTransition.lean`: `lbl394` transition limits and cocycle.
- `StepBApproxIso.lean`: `lbl399`, `lbl404`, `lbl405`, and the final
  `lbl397` wrapper once Step C is available.

## Brick Board

### Live framed-coordinate migration - 2026-07-18

The historical brick verdicts below describe the former raw model-coordinate
route.  The live route now chooses a centerwise metric-orthonormal frame and
uses `framedExpMap`, `framedExpDiffeo`, `framedChartAt`, and
`framedTransition` throughout.

Current status:

- `StepBInputs`: framed definitions and the origin metric identity are
  focused- and target-green.
- `ProperBallExp` and `GoodCoveringItem3`: framed source/image contracts are
  focused- and target-green.
- `MetricCompactnessInputs`: the radius profile now targets `expRadiusGp`
  directly and no longer carries the raw coercivity conversion; it is focused-
  and target-green.
- `StepCPairGeometry`: direct framed source/target containment is focused- and
  target-green. `StepCAtomConv`, `StepCTransitionRefine`, and `StepCPairTail`
  have completed their ordered exact refresh and are target-green.
- `StepBTransition`, `StepBTransitionOverlap`, `H6IsometryDeriv`, and
  `NormalCoordDistance` are framed and verified. `StepCTransitionRefine` is
  target-green with all four extraction layers on `expRadiusGp`.
- `NormalMetricExtend` is framed and target-green.  `NormalMetricLocal` is
  framed and focused- and target-green.
- `H6NormalCoord.exists_equiv_ball` is focused- and target-green and supplies the genuine
  per-center zero-order half/two estimate. It does not supply the
  sequence-uniform relative-radius profile or all-order metric constants.
- `H6NormalCoord.exists_equiv_radii` is focused- and target-green and packages the local
  choices for all `(k, x)`; the chosen radius still depends on `(k, x)`, so it
  does not advance the uniform-profile theorem itself.
- `H6NormalCoord.framed_rm04_of_seq` and `exists_rm04_radii` are focused- and
  target-green.
  Uniform bounded geometry now gives arbitrary-direction half/two metric
  equivalence on one curvature scale intersected with the pointwise
  `framedJacobiRadius`; this completes the Jacobi/Rm04 and scalar-budget bricks
  without claiming a uniform lower bound for the clamp.
- The framed Step-C producer chain through `StepCProducers` is target-green.
  In the first stage-consumer batch, `StepCStageMap` and `StepCStageFill` are
  target-green; `StepCStageCenter` and `StepCSupportCapstone` are now
  exact-green after the framed consumer chain through `StepCHatReadout`,
  `NormalMetricConv`, and `NormalLiveConv` was refreshed.
- `NormalPhase`, `NormalPhaseSmallness`, `NormalPhaseRealization`,
  `NormalPhaseSym`, and `NormalPhaseInverse` now expose `expRadiusGp` fences.
  Their source checks pass, and the exported phase-flow signatures needed by
  `NormalPhaseEndpoint` and the Stage consumers have been refreshed.
- `NormalPhaseConv` and `NormalDiagAt` are also source- and target-green on
  `expRadiusGp`; the fixed-radius branch fence now lands directly in the
  canonical framed `normalBall`.
- `NormalLimitPhase` and `NormalDiagBranch` are source- and target-green on the
  framed route.  The latter now carries fixed-center pair coordinates through
  `framedChartAt`/`framedExpDiffeo`, while preserving genuinely moving-base
  exponential uses in the phase endpoint path.
- `NormalBranchScale` and `NormalBranchMin` are source/focused- and
  target-green after the direct `expRadiusGp` and fixed-center framed-chart
  migration. They introduced no new radius assumption or branch wrapper.
- `StepCSmoothness` now exposes framed fixed-base parameters throughout the
  selected-branch equation and IFT stack, while retaining raw moving-base
  inverse-tangent readouts. `NormalBranchHessian` consumes that API directly;
  both modules are source/focused- and target-green.
- `JacobiVariation` retains the equation, regularity, first derivative, and
  endpoint equation on the explicit common radius
  `jacobiVarRadius = expMapC2Radius / 26`; the old existential declarations are
  compatibility wrappers. In addition, `intrinsic_jacobi` and
  `intrinsic_jacobi_one` are focused- and exact-green and prove the global Jacobi equation
  plus its exact time-one differential identity for the complete intrinsic
  exponential, without a clamp or launch-radius assumption.
- `IntrinsicFramedCoordinates.intrFrame_mfderiv` is source/focused-green and
  transports that identity through the normal frame. The HCG completeness
  boundary is now explicit in `H6NormalCoord.intr_metric_eq` and
  `exists_intr_eq_ball`, both focused-green. The next live H6 target is the
  quantitative intrinsic Rm04 half/two estimate; the qualitative agreement
  ball is not counted as a uniform profile.

Current B/C status: the complete stage chain through `StepCStageMaster` is
focused- and exact-green. `StepB1MetricBridge`, `StepB1MetricLocal`,
`StepB1Inverse`, `StepB1MetricReverse`, `StepB1MetricIntrinsic`,
`StepB1MetricCarrier`, and `StepB1RawProducer` are focused- and exact-green.
The canonical framed `MetricCompactBase.exists_b1_raw` producer is therefore
checked with all five `StepB1RawInput` fields closed; the reverse remains the
exact `Function.invFunOn`. The consumer chain through `StepCSupportCapstone` is
exact-green. The
independent H6 lane has completed
the explicit arbitrary-vector Rm04 endpoint, clamped sequence-uniform
zero-order metric estimate, sub-injectivity-ball `expDomain` containment, and
global smoothness of the basepoint-free geodesic spray, finite-time smooth-flow
  continuation, identification with the intrinsic geodesic velocity lift, and
  global intrinsic Jacobi equation. The smooth time-one intrinsic endpoint,
  affine two-parameter variation, and intrinsic endpoint differential identity
  are focused- and exact-green. The exact remaining branch
  gate is the canonical intrinsic-vs-chart-fixed exponential architecture and
  the canonical branch construction. In addition, H6 must choose the
  `NormalCoordMetricBoundInput.radius` together with its profile; no positive
  ratio follows for an arbitrary record whose radius may be shrunk. The
  decision prompt and exact signatures are in `H6_RADIUS_CONSULT.md`. The
  current `expMapC2Radius` inside `expRadiusGp` remains a qualitative choice
  and cannot be lower-bounded
by CGT injectivity. Do not add an endpoint wrapper or a synonym profile
assumption to bypass this gate.

Accounting: the canonical framed `MetricCompactBase.exists_b1_raw` theorem is
100% checked. Textbook B1 and the unconditional compactness endpoint remain
theorem-level 0%; the checked raw producer is dedicated machinery for those
future endpoints, not either endpoint itself.

### B-input - normal-coordinate metric honest input

Status: accepted 2026-06-13.

Acceptance verdict 2026-06-13: B-input is complete.  The implementation added
`normalCoordMetric`, `NormalCoordMetricEquivOn`,
`NormalCoordMetricDerivBound`, and `NormalCoordMetricBoundInput` in
`StepBInputs.lean`, with the same-name note updated.  Planner rechecked the
focused file and targeted module build successfully.  No theorem endpoint was
introduced; axiom audit on the concrete map `normalCoordMetric` is clean
(`propext`, `Classical.choice`, `Quot.sound` only).  The only planner edit
during acceptance was a wording correction in `StepBInputs.md`.

Target files: `StepBInputs.lean`, `StepBInputs.md`.

Goal: add the `lbl395` honest input in constants-first shape.  This brick does
not prove the native Jacobi/Gronwall theorem.  It must avoid pretending that
the metric maps have total `Set.univ` bounds; bounds are local to the relevant
normal-coordinate ball or compact subsets of it.

Acceptance endpoints:

- The new structure/predicates are Lean-checked.
- Same-name note records that `lbl395` was taken as book-external honest input.
- Axiom audit on any theorem endpoints introduced by the brick shows only the
  standard accepted axioms; if the brick only defines structures/predicates,
  record that no theorem endpoint was introduced.

### B-loc - localized map and isometry compactness

Status: accepted 2026-06-13.

Acceptance verdict 2026-06-13: B-loc is complete.  The accepted work added
the localized map extraction `exists_cInf_subseq_on` to `MapConvergence.lean`
and the localized isometry consumers in `StepBLocalizedAA.lean`:
`comp_eq_id_of_cInf_on`, `isometry_seq_cInf_on`, and
`isometry_seq_diffeo_on`.  The inverse identities are intentionally
domain-conditional, because the Step B transition maps are only controlled on
chart overlaps.  Planner rechecked focused files, refreshed targeted modules,
and audited the new public endpoints as axiom-clean (`propext`,
`Classical.choice`, `Quot.sound` only).

Target file: `StepBLocalizedAA.lean` plus same-name note.

Goal: localize the existing F7/F8 interfaces:

- localized AA for maps: bounds on compact subsets of an open `U` imply a
  subsequence and `MapCInfConvOnCompacts U`;
- localized isometry compactness: local versions of `isometry_seq_cInf`,
  `comp_eq_id_of_cInf`, and `isometry_seq_diffeo` suitable for paired domains
  and inverse maps on nested balls.

Reuse `MapConvergence.exists_cInf_subseq`, `MapCPConvOn.mono_set`,
`MapCInfConvOnCompacts.cPConvOn`, `MapCInfConvOnCompacts.comp_subseq`, and
`IsometryDerivBounds.comp_subseq` where possible.  If true `ContDiffOn` support
forces a substantial rewrite of the AA engine, stop and report the exact local
smoothness API gap before editing `MapConvergence.lean`.

Acceptance endpoints:

- Focused check and targeted module build green.
- `#print axioms` clean for localized AA and localized F8 endpoints.
- No edits to `IsometryCompactness.lean`; `MapConvergence.lean` was edited
  only for the planner-authorized localized extraction.

### B-metric - `lbl394` local metric limits

Status: generic engine, fixed-center HCG wrapper, forward `expMap C^infty`
input, and `normalCoordMetric_contDiffOn` accepted 2026-06-13; full `lbl394`
metric endpoint still blocked on the uniform domain/radius bridge needed to use
one fixed model domain `U` for all sequence members, plus the finite beta
diagonal.

Acceptance verdict 2026-06-13: `StepBLocalMetrics.lean` is accepted for the
generic bilinear-form limit theorem `exists_metricLimit_on` and the fixed
center normal-coordinate wrapper `exists_metricLimit_normalCoord`.  The wrapper
wires `NormalCoordMetricBoundInput` into the generic engine, preserving the
`1/2 delta <= g <= 2 delta` equivalence.  It deliberately keeps the missing
normal-coordinate smoothness as the bare hypothesis
`hsmooth : forall k, ContDiffOn R top (normalCoordMetric ...) U` and the domain
containment as `hdom`; this is not the unconditional manifold `lbl394`.
Planner verification passed focused checks, targeted module builds, and axiom
audit (`propext`, `Classical.choice`, `Quot.sound` only).
The historical `hsmooth` gap is now discharged by `normalCoordMetric_contDiffOn`;
`hdom`/uniform-radius bookkeeping remains.

Frontier-1 audit corrected 2026-06-13: the fixed-box ODE theorem is already
proved as `IsLocalFlow.contDiffOn_top` / `IsLocalFlow.contDiffOn_top_local`
and axiom-clean.  The finite-order `flowCkPred_all` route still has shrinking
boxes, but the correct next frontier is chart-phase wiring: apply the local
Hartman theorem to the geodesic chart-phase flow, package `combined_inf`, then
push the existing off-zero bridge to forward `expMap ContMDiffAt infinity` on a
uniform ball.  `StepBLocalMetrics.md` and
`Analysis/ODE/Flow/HigherRegularity/VariationalMapContDiffOnK.md` record the
correction.

Forward smoothness accepted 2026-06-13: `SmoothFlow.lean` now has
`exists_chartPhase_contDiffOn_isLocalFlow_combined_inf`, and `OffZero.lean` has
`expMap_contMDiffAt_infty_of_norm_lt`.  Planner checked `SmoothFlow`,
`OffZero`, and the `JacobiVariation` consumer; axiom audit is clean
(`propext`, `Classical.choice`, `Quot.sound` only).  This discharges the ODE /
forward-exp gate that fed the now-accepted metric smoothness producer.

Metric-smoothness audit accepted 2026-06-13: `OffZero.md` records that
`normalCoordMetric_contDiffOn` is feasible with existing tools, but not a
corollary.  The critical API exists
(`ContMDiffOn.contMDiffOn_tangentMapWithin`, `ContMDiffOn.clm_bundle_apply₂`,
`contMDiffOn_iff_contDiffOn`, and the `pullbackGram` pattern).  The remaining
work is a substantial geometry/bundle assembly: compare the C1
`expMapDiffeo` derivative with the forward `expMap` derivative on an open ball,
build smooth pushforward sections, then assemble the
`E ->L E ->L R`-valued pullback metric in coordinates.

Metric smoothness producer accepted 2026-06-13: `StepBInputs.lean` proves
`normalCoordMetric_contDiffOn`, with helper endpoints
`expMapDiffeo_contMDiffOn_ball` and `normalCoordMetric_apply`.  Focused check,
targeted module build, and axiom audit passed.  The next B-metric commission is
not another smoothness lemma: relate the existential radius from
`normalCoordMetric_contDiffOn` to the fixed Step-B model domain `U` along the
sequence, using Step-A fixed-scale/radius data, then consume
`exists_metricLimit_normalCoord`.

Pure-ball producer accepted 2026-06-13 (session 3): `normalCoordMetric_contDiffOn_ball`
(`∃ r > 0, ContDiffOn R top (normalCoordMetric Y x) (ball 0 r)`) landed in
`StepBInputs.lean` (focused check green, axiom-clean) — folds a positive ball of
`expMapDiffeo.source` into the producer, dropping the `∩ source` wrinkle.  This is the
smallest domain/radius lemma of the bridge.

HARD STOP #1 reached on the fixed-`U` discharge.  Correcting the line above ("not another
smoothness lemma"): the uniform-radius step is NOT pure Step-A bookkeeping.  The producer
radius `r_k` ultimately comes from `expMap_contMDiffAt_infty_of_norm_lt` ⟵
`exists_unified_chartFlow_data_inf`, an opaque ODE existential `δ_k=(T_match/2)·ρ` with no
geometric anchor.  Step-A uniformly controls `injRadius` (`InjRadiusDecayInput`) and
`expMapC2Radius` (`Item3RadiusInput`), but `expMapC2Radius` uses a *separate*
`Classical.choose (expMap_contMDiffAt2_of_norm_lt)` (only **C²**); nothing relates `δ_k` to
either.  So `inf_k r_k > 0` is unprovable ⇒ `U ⊆ ball 0 r_k` (fixed `U`, all `k`) is
unprovable.  EXACT MISSING THEOREM: a named-radius ∞ producer
`expMap_contMDiffAt_infty_of_norm_lt_radius : ‖w‖ < expMapC2Radius g p → ContMDiffAt ∞ (expMap g p) w`
(or anchored to a fixed fraction of `injRadius`).  This is smoothness-layer work
(re-deriving the OffZero off-zero ∞ producer on a geometrically-named radius), so it is
deferred per the "frontier is no longer smoothness" scope.  Full record + the post-unblock
discharge chain in `StepBLocalMetrics.md`.

Target file: `StepBLocalMetrics.lean`.

Goal: from `NormalCoordMetricBoundInput`, Step A chart/radius data, and
localized AA, produce local limit metrics `gInf beta` on the model balls, with
`C^infty` convergence on compact subsets and retained uniform equivalence to
the Euclidean metric.

Acceptance endpoints:

- Metric-limit theorem for a fixed beta/domain.
- Finite beta diagonal or explicit plan for the finite diagonal over
  `alpha <= A(r)`.
- Axiom audit clean except accepted classical axioms.

### B-trans - `lbl394` transition limits and cocycle

Status: generic engine and fixed-pair HCG wrapper accepted 2026-06-13;
full `lbl394` transition endpoint still blocked.

Acceptance verdict 2026-06-13: `StepBTransition.lean` is accepted for
`exists_transitionLimit_on`, the honest overlap predicate `NormalOverlapOn`,
and the fixed-pair normal-transition wrapper
`exists_transitionLimit_normalTransition`.  The wrapper wires
`ExpInverseDerivBoundInput` into localized isometry compactness and states the
limit cocycle conditionally on limit-domain membership.  It deliberately keeps
the missing transition smoothness as the bare hypotheses `hsmoothJ` and
`hsmoothJbar`, plus explicit overlap/domain inputs; this is not the
unconditional finite-pair diagonal `lbl394`.  Planner verification passed
focused checks, targeted module builds, and axiom audit (`propext`,
`Classical.choice`, `Quot.sound` only).

Target file: `StepBTransition.lean`.

Goal: use `normalTransition`, `ExpInverseDerivBoundInput`, Step A intersection
stability, and localized F8 to construct limit transition maps
`JInf alpha beta` on the correct nested domains.  Prove the local inverse /
cocycle identity needed by the book.

Acceptance endpoints:

- Transition-limit theorem for intersecting `alpha,beta` pairs.
- The index orientation is type-checked against the actual domain/codomain
  statements; do not copy the book's notation if the domain labels force an
  `alpha`/`beta` correction.
- Axiom audit clean except accepted classical axioms.

### B-Falpha - local maps converge to identity (`lbl399`)

Status: `C^0` compact convergence core accepted 2026-06-13; full `C^infty`
`lbl399` remains blocked on composition-convergence calculus.

Acceptance verdict 2026-06-13: `StepBApproxIso.lean` is accepted for the
generic `comp_tendsto_id_on` theorem.  It proves the uniform-on-compact `C^0`
identity limit for two independently convergent local map sequences with the
limit inverse identity supplied conditionally.  It does not prove the full
`C^infty` convergence of compositions; that remains the Faà-di-Bruno
composition-convergence frontier.

Target file: `StepBApproxIso.lean`.

Goal: define the coordinate expression
`F_{k l,beta}^alpha = barJ_l^{alpha beta} o J_k^{beta alpha}` and prove its
convergence to the identity on compact subsets of the appropriate inner
domain.  This is the direct pre-center-of-mass consequence of transition-map
convergence.

Acceptance endpoints:

- `lbl399` theorem shape present and checked.
- Uses B-trans convergence and cocycle; no new compactness engine.

### B-404 - almost-identity pullback lemma

Status: not started; blocked on the same Faà-di-Bruno
composition-convergence frontier as full `lbl399`.

Target file: `StepBApproxIso.lean` or a small Euclidean helper file if the
proof is generic.

Goal: formalize the Euclidean calculus lemma `lbl404`: if `phi_k -> id` and
`h_k -> hInf` in `C^infty` on compact sets, with uniform equivalence and
derivative bounds, then `phi_k^* h_k -> hInf` in `C^p` on compact sets.

Acceptance endpoints:

- The statement is generic over a model vector space and bilinear-form-valued
  metrics.
- No manifold-level approximate-isometry assumptions are introduced.

### B-glue - `lbl402`, `lbl403`, `lbl405`, `lbl397`

Status: blocked on Step C center-of-mass machinery and on the F4 axiom caveat
for final axiom-clean acceptance.

Target file: `StepBApproxIso.lean`.

Goal: after Step C supplies center-of-mass existence, smoothness, and
convergence-to-identity (`lbl434`, `lbl436`), assemble the averaged maps
`F_{k l;r}`, prove local convergence to identity (`lbl402`), local diffeo
(`lbl403`), pre-approximate isometry (`lbl405`), and final approximate
isometry on the large ball (`lbl397`).

Acceptance endpoints:

- Step C inputs are explicit, not hidden as new assumptions with polished
  names.
- `lbl405` use of F5/F6 records whether `lemma45_corII` is already discharged.
- Final `lbl397` is not accepted as axiom-clean while any `sorryAx` flows
  through F4 or Step C.

## Acceptance Criteria

For every Lean brick:

- Claim editable Lean files through `./scripts/lake-locked.ps1 claim` before
  editing and release after.
- Use focused locked check first, then targeted module build for the edited
  module/import.
- Run `#print axioms` on all new public theorem endpoints.  Accepted output is
  only `[propext, Classical.choice, Quot.sound]` unless the theorem is
  deliberately marked as an honest input boundary.
- Review the diff before returning the brick to the planner.
- Update the same-name `.md` note.  Do not paste exact build logs; record pass
  or fail and the precise blocker if it failed.
- Commit locally if and only if the brick is accepted.  Never push.

STRICT constants-first rule:

- Every new existential bound must put constants before the varying sequence,
  map, metric, tensor, or field it will bound.
- For Step B, a constant depending on `r`, `p`, a fixed finite cover index, or a
  fixed compact set may appear before `k,l`; it must not be chosen after the
  sequence element whose uniformity it claims to control.
- If a theorem cannot satisfy this order, stop and report the dependency that
  prevents uniformity.

## Coordination

Current branch: `short-time-existence`.

Before assuming files are free, run `./scripts/lake-locked.ps1 status`.

Consume-only for Step B executors:

- `MapConvergence.lean`
- `IsometryCompactness.lean`
- `Lemma45*.lean`
- `ApproxIsometry*.lean`
- `GoodCoveringSeq.lean`
- `GoodCoveringOrdered.lean`
- `ExpBallDiffeo.lean`

Off-limits P3 / Lemma 3.11 track:

- `MetricPreconv*`
- `RicBound*`
- `StarSum*`
- `NablaTraceGen.lean`
- `MetricCovDerivTimeDeriv.lean`
- `AllTimesBounds.lean`

The working tree may contain other agents' uncommitted files.  Do not revert or
format unrelated files.

## Traps Table

| Trap | Failure signal | Required response |
| --- | --- | --- |
| Applying F7/F8 to `normalTransition` on `Set.univ` | The only bounds are on chart overlap / nested ball | Use B-loc; do not invent total bounds. |
| Smooth cutoff extension | New proof obligations about extension smoothness and equality on balls | Reject as main route unless planner explicitly reopens Q2. |
| Treating `lbl395` as native Step B work | Work expands into Jacobi/Gronwall x-derivative induction | Use honest input now; record native route as optional discharge. |
| Final `lbl397` before Step C | Center-of-mass existence or convergence appears as a new assumption | Stop; Step C is the gate. |
| Hidden F4 dependency | `#print axioms` includes `sorryAx` through `lemma45_corII` | Do not accept final approx-isometry endpoints as clean. |
| Book index typo / notation drift | `J` composition types do not line up | Follow Lean domain/codomain types, record the corrected orientation. |
| Metric AA as a new engine | A new dedicated Arzela-Ascoli proof appears for metrics | Reuse localized map AA on bilinear-form-valued maps. |
| Component API drift | Proof unfolds tensor internals or hand-builds coordinate components | Route through existing component/model-coordinate APIs. |

## First Executor Kickoff Prompt

Work in `DifferentialGeometry/` on branch `short-time-existence`.  You are the
implementing agent for **B-input** of MSM135 Chapter 4 Step B (HCG compactness):
the `lbl395` normal-coordinate metric-bound honest input.

1. Read in order: `CLAUDE.md`; `HCGCompactness/STEPB_PLAN.md` sections
   "Planner Rulings", "B-input", "Acceptance Criteria", "Coordination", and
   "Traps Table"; `chapter4.tex` lines 1410-1452; then
   `StepBInputs.md`, `B0NormalCoordBounds.md`, `GoodCoveringItem3.md`,
   `ExpBallDiffeo.md`, `convention.md`, and `dictionary.md`.
2. Implement B-input in `HCGCompactness/StepBInputs.lean` and update
   `HCGCompactness/StepBInputs.md`.  Add a constants-first
   `NormalCoordMetricBoundInput`-style structure/predicate for the book-external
   `lbl395` normal-coordinate metric bounds, sibling to
   `ExpInverseDerivBoundInput`.  The statement should expose local
   Euclidean-metric equivalence and all-orders Euclidean derivative bounds for
   the pulled-back normal-coordinate metric maps on compact subsets of the
   relevant normal-coordinate ball.  Do not claim `IsometryDerivBounds` on
   `Set.univ`; the partial-domain bridge is reserved for B-loc.
3. Claim files with `./scripts/lake-locked.ps1` before editing.  Consume-only
   files are listed in `STEPB_PLAN.md`; do not edit the P3/Lemma 3.11 track.
4. Acceptance: focused locked check and targeted module build green for
   `StepBInputs`; `#print axioms` on any new theorem endpoints is clean
   (`propext`, `Classical.choice`, `Quot.sound` only).  If you only add
   definitions/structures, say so in `StepBInputs.md`.  Commit locally after
   acceptance, never push.
5. Stop and report to the planner if the honest input cannot be stated without
   first introducing a separate Step B chart-data record for `H_k^alpha` /
   pulled-back metric maps.  In that case, report the smallest chart-data record
   needed; do not create an ad hoc parallel API.
## 2026-07-27 H6 intrinsic ODE status

- `Rm04OperatorBound.riemannOp_sq_le`: focused green.
- `IntrinsicGronwall.intrJacobi_ode`: focused and exact green.
- `IntrinsicFramedJacobi.intr_metric_jacobi`: focused and exact green.
- `H6NormalCoord.exists_intr_radii`: focused and exact green. It gives one uniform
  positive radius for the total intrinsic framed pullback metric, with the
  half/two estimate and no `expRadiusGp` or qualitative-branch clamp.
- `H6NormalCoord.exists_intr_branches`: focused and exact green. On the same radius it
  excludes conjugate launch vectors and selects the existing smooth intrinsic
  inverse branch pointwise, without a new assumption or wrapper frontier.
- The unclamped route now derives the Gronwall ODE from sequence `Rm04` bounds
  and constant intrinsic speed; no chart-radius clamp remains in this producer.
- H6 relative profile theorem: 0% because it is not yet stated.
- Dedicated zero-order machinery: 100%.
- Whole-plan consultation correction: do not redefine `expRadiusGp` as a
  fraction of injectivity radius. Injectivity alone does not imply a local
  diffeomorphism. Keep Route A, but make Route C carry the controlled
  whole-ball branch as part of `H6NormalData`.
- Required producer inputs are `SeqMetricComplete`, connectedness,
  `SeqBoundedGeometry`, `hd : InjRadiusDecayInput`, and
  `hreal : hd.RealizesEdist`. The latter supplies the missing global estimate
  `hd.mu distance <= hd.mu 0`.
- Gates 1--3 are complete: intrinsic injectivity, the fixed relative
  whole-ball partial diffeomorphism, and the provider-native Hessian/implicit
  function package are focused/exact green.
- Gate 4 is source-complete. `HasCmSolC`, `HasChartCmSol`, the finite-hat
  readout, support packages, `actual_cm_tail`, `stage_root_tail`, and
  `StepCStageSeed` all pass in one isolated current-artifact replay under
  `legacyChartFamily`. The only source repairs were moving the generic
  `mapCInf_apply` projection to `MapConvergenceComp`, removing one empty
  `dsimp`, and using the controlled chart's explicit source/domain/zero fields
  in the selected-root proof. All other failures were stale exports. Formal
  artifacts remain pending while an unrelated writer is active.
- Gate 5 structural preparation is complete. The common `NormalChartFamily` now lives in
  `StepBInputs`; `HasDiagPairConv` preserves it through subsequences,
  stage-branch congruence, fences, and inverse data; and
  `pairStageFillSub`/`stagePtsSub`/`stageWeightSub`/`stageCfgSub` use one
  family for every transition and readout. The same family now also passes
  through `stageInvVelSub`, `stageRootSub`, `HasStageRootCube`, and
  `HasSuppCmData`. `StepCSupportCapstone.exists_supp_cm_fin` returns that
  package directly instead of restating the legacy chart formula. The full
  current-interface replay through the support capstone passes under
  `legacyChartFamily`.
- Gate 5 cannot yet perform the provider substitution. The first remaining
  consumer, `HasSuppConvData.actual_cm_tail`, uses quantitative transition
  compactness as well as chart notation. The intrinsic producer for that
  compactness is `H6NormalData.trans_bounds_on`/`exists_trans_lim`, which
  consumes the all-order `metric_deriv` field. Parameterizing
  `actual_cm_tail` before constructing that field would only move the missing
  mathematics into a wrapper assumption. Gate 6 is therefore active now;
  after `exists_h6NormalData` is proved, return to Gate 5 and instantiate the
  existing H6 transition producer in the selected support/root chain.
- Feasibility correction: the H6 provider cannot be substituted only in
  `stage_root_tail`. That proof still builds its equation and decode using the
  legacy `chiK`, `chiL`, `qstar`, `zc`, `xi`, and `normalExpPD`. The H6
  whole-ball chart is not known to agree with the legacy chart on that whole
  ball, so no global compatibility rewrite is available or mathematically
  justified. The selected diagonal/root package itself must be
  chart-parametric; do not add an agreement assumption or a parallel H6
  wrapper.
- `NormalRadiusProfile` and final `exists_h6NormalData`: theorem-level 0%.
  Radius/branch infrastructure: about 80%. Branch-parametric consumer
  migration: about 72%. All-order metric-jet machinery: about 35%. Overall
  native H6 producer machinery: about 64%.
- The independent all-order curvature-to-coordinate-metric jet induction is
  the dominant remaining theorem. Its target and all migration gates are
  recorded in `H6_RADIUS_CONSULT.md`. The order-zero base and the final
  provider-transfer step are focused-green:
  `NormalBallChart.MetricEquivOn.deriv_zero`,
  `H6ChartData.metric_eq_intr`, and
  `NormalBallChart.MetricDerivBound.of_eqOn`. The focused-green
  `exists_intr_control` now chooses one radius for both the half/two estimate
  and local diffeomorphism, and `H6BallData` retains that estimate on the exact
  relative chart ball. `H6NormalData` is now focused-green against an isolated
  overlay containing the current `H6NormalCoord` export; the only local repair
  was an explicit `change` past the result-type `let hEnorm`. The formal
  artifacts remain pending while an unrelated exact writer is active.
  Therefore the next Gate 6 target is specifically the
  fixed-tube, sequence-uniform parameter-jet induction for the intrinsic
  geodesic/Jacobi flow, not another chart compatibility or radius-coherence
  lemma.
  State it for an arbitrary finite launch radius: the focused-green
  `H6ChartData.radius_le_global` bounds every selected chart radius by
  `d.ratio * hd.mu 0`, which is the final instantiation.
- Gate 6 progress: `Variation.cov_commute_curv` is focused-green with no
  diagnostics.  It supplies the general intrinsic identity
  `D_s D_t V - D_t D_s V = R(partial_s f, partial_t f) V` needed to
  differentiate a Jacobi field whose value is not itself a variation velocity.
  `IntrinsicJacobiJets.intrLaunch3`, its joint smoothness, and launch-derivative
  commutation are also focused-green.  The exact artifact refresh is deferred
  while another lane owns the shared writer.
- Gate 6 progress: `IntrinsicJacobiJets.intrLaunchJ` now packages the
  second-launch Jacobi field as the total derivative in direction `((0,1),0)`.
  `intrLaunchJ_smooth` proves joint smoothness in the remaining launch
  parameter and geodesic time, while `intrLaunchJ_eq` identifies this bundled
  field with the existing one-variable Jacobi derivative. All three are
  focused-green. This removes the six separate regularity guesses that would
  otherwise be needed at `cov_commute_curv`.
- Gate 6 progress: `Variation.jacobi_var_eq` is focused-green with no
  diagnostics or proof frontier. It differentiates a smooth family of Jacobi
  equations, commutes the parameter derivative past both time derivatives,
  and exposes one `curvDerivAlong` term plus the five lower curvature-slot
  terms. The exact artifact refresh is deferred while another lane owns the
  shared writer.
- Gate 6 progress: `IntrinsicJacobiJets.intrLaunch_var_eq` now instantiates
  that equation for `intrLaunch3` and `intrLaunchJ`. A source-current combined
  check is green; ordinary downstream focused/exact verification awaits the
  upstream artifact window.
- Gate 6 progress: `PointwiseCurvatureDerivative.nablaRiemannOp_eq` and
  `nablaRiemannOp_sec` are focused-green, and the owning artifact is current.
  They identify the pointwise `(nabla_D R)(X,Y)Z` with the existing
  section-level Leibniz derivative without relying on the unstable
  `nablaBaseSlotCurv_eq_of_leftMid` signature.
- Gate 6 progress: `HasCurvDerivBound.nablaRiemannOp_le` and `riemannOp_le` are
  focused- and exact-green (`BoundedGeometry` 3930/3930). They turn the sequence
  C1 and C0 tensor bounds into the dimension-free metric norm bounds for the
  pointwise vector-valued `(nabla_D R)(X,Y)Z` and `R(X,Y)Z`, respectively.
- Gate 6 progress: the full arbitrary-field curvature-derivative bridge is
  complete. `Variation.curvDeriv_restrict` handles restrictions of smooth
  global fields; `curvDeriv_congr_at` proves point-value dependence in all
  three slots; and `curvDeriv_eq_nabla` identifies the actual smooth
  along-curve object with `nablaRiemannOp`. The successful point-value proof
  uses one smooth ambient chart-frame, globally smooth scalar coefficient
  germs, and the existing finite-sum/smooth-scalar slot linearity. It introduces
  no forcing or extension-compatibility assumption. Focused verification is
  green, the exact module refresh is green 3803/3803, and the file has no
  `sorry`/`admit`/`axiom`.
- Gate 6 progress: `H6JacobiForce.jacVarForce_le` now bounds the exact forcing
  in the first differentiated Jacobi equation. It uses
  `curvDeriv_eq_nabla` plus `nablaRiemannOp_le` for the two `nabla R` terms and
  `riemannOp_le` for the four `R` terms, retaining the coefficient two on
  `varCurv`. `intrJacForce_le` instantiates this estimate for `intrLaunch3` and
  `intrLaunchJ`; the new exact-current `intrLaunchDir_smooth`,
  `intrLaunchA_eq`, and `intrLaunchT_eq` discharge all seven smoothness
  obligations without a forcing assumption. The H6 forcing file is
  focused- and exact-green (`3935/3935`) and has no
  `sorry`/`admit`/`axiom`.
- Gate 6 progress: `Variation.covGronwall_force_at` is focused- and
  exact-green (`3704/3704`).
  It transfers an inhomogeneous covariant second-order estimate with metric
  norm initial bounds to the existing fixed-space `gronwallBound`; this is the
  common Gronwall consumer for every positive launch-jet order.
- Gate 6 progress: `IntrinsicJacobiJets.intrLaunch_dmix0` is focused- and
  exact-green (`3804/3804`). Together with `intrLaunch_mix_zero`, the first
  differentiated Jacobi field has both zero launch initial conditions without
  any supplied initial-data assumption.
- Gate 6 immediate target: expose the position-velocity pair estimate already
  proved internally by `norm_le_gronwall_secondOrder`, transport its velocity
  projection through `CovariantGronwall`, and combine those bounds with
  `intrLaunch_var_eq` and `intrJacForce_le`. The derivative projection is
  required because the exact force contains `D_t A` and `D_t J`, not only
  `A` and `J`.
- Gate 6 progress: `SecondOrderGronwall.pair_le_gronwall2` and
  `deriv_le_gronwall2` are focused- and exact-green (`2094/2094`). The old
  `norm_le_gronwall_secondOrder` API is preserved as the position projection.
- Gate 6 progress: `Variation.covGronwall_pair_at` and
  `covGronwall_deriv_at` are source/focused-green. The existing
  `covGronwall_force_at` statement remains the position projection. Exact
  artifact refresh is pending writer coordination.
- Gate 6 progress: the existing `Variation.chartRep_snd_diff` helper is now
  public and focused-green. It supplies the chart-readout differentiability of
  any jointly smooth launch field and of its time covariant derivative; no new
  regularity assumption is needed. Exact artifact refresh is pending.
- Gate 6 progress: `VolumeComparison.intrJacobi_pair` specializes the
  position-velocity Gronwall estimate to an intrinsic Jacobi field, while
  `intrForce_pair` derives the regularity needed for an inhomogeneous field.
  `H6JacobiPair.intrJacobi_pair_le`, `intrMix_force_le`, and
  `intrMix_pair_le` are now focused- and exact-current. Thus both the
  order-zero pair bound and the first differentiated launch pair are closed
  without a supplied forcing or initial-data assumption.
- Gate 6 progress: the canonical tensor layer now has the full frozen-slot
  covariant Leibniz formula `freezeNabla_leibniz`; the older
  `allBut0SFreezeNabla` is its zero-correction corollary. This layer is focused-
  and exact-green (`3555/3555`).
- Gate 6 progress: `CurvOpTower.curvOpN_cov_sum` is focused-green. It raises
  the frozen one-form formula and gives exactly one next-curvature-order main
  term plus the finite sum in which one lower slot is replaced by its
  covariant derivative. The previous `curvOpN_cov` constant-slot API remains
  intact.
- Gate 6 progress: `Variation.jacJetResidual_succ` is exact-current in
  `CovariantJet`, while `Variation.jacCurv_smooth` gives the required honest
  joint regularity of its curvature term. `IntrinsicJacobiJets` now exports
  `intrJetResidual_zero`, `intrJetCurv_smooth`, and
  `intrJetResidual_succ`; focused and exact verification are green
  (`3819/3819`). Thus the arbitrary finite-order launch-Jacobi residual
  recurrence is closed without a supplied forcing or ODE-jet assumption.
- Gate 6 next target: normalize `intrJetCorr n` into a finite sum of
  `curvOpN` evaluations and lower launch jets, using `curvOpN_cov_sum` whenever
  a launch derivative hits curvature. Then derive constants-first force and
  pair bounds on an arbitrary finite launch radius. Do not introduce a
  supplied forcing bound or a generic ODE-jet assumption.
- Current accounting: `NormalRadiusProfile` and `exists_h6NormalData` remain
  theorem-level 0%; radius/branch infrastructure is about 80%;
  branch-parametric consumer migration is about 72%; dedicated all-order
  metric-jet machinery is about 66%; overall native H6 producer machinery is
  about 73%.

### 2026-07-28 Gate 6 closure

- `IntrinsicJacobiJets` is exact GREEN (`3819/3819`),
  `IntrinsicMetricJets` is exact GREEN (`3828/3828`), and `H6MetricJet` is
  exact GREEN (`3964/3964`).
- `exists_h6NormalData` is focused and exact GREEN (`3983/3983`). It constructs
  the branch-carrying uniform normal-coordinate package from
  `SeqMetricComplete`, connectedness, `SeqBoundedGeometry`, and a realized CGT
  injectivity profile. No new radius, chart-agreement, forcing, or
  consumer-side assumption is used.
- Gate 6 and the dedicated H6 normal-coordinate producer are 100% complete.
  The earlier percentage lines above are historical progress snapshots.
- Resume Gate 5 next: instantiate `H6NormalData.trans_bounds_on` and the
  existing H6 readout/transition producers in the selected support/root chain.
  Do not restart the all-order Jacobi/metric-jet route.
- `NormalRadiusProfile.le_exp_radius` remains an independent legacy theorem at
  0%; the unconditional MSM135 endpoint remains unstated at 0%.

### 2026-07-28 Gate 5 resumption

- `HasSuppConvDataOn` now carries the source cover, atom limits, transition
  limits, and transition smoothness for one `NormalChartFamily`.
- `HasSuppConvData.toOnLegacy` is focused-green and preserves the established
  public package unchanged while exposing it through `legacyChartFamily`.
- The next concrete target is `HasSuppConvDataOn.actual_cm_tail`.  Its proof
  must use the family chart/readout/transition operations throughout; the old
  `HasSuppConvData.actual_cm_tail` remains a compatibility wrapper.
- After that generic consumer is green, instantiate the selected support/root
  chain with `H6NormalData.chart`, using
  `H6NormalData.trans_bounds_on`/`exists_trans_lim` rather than adding a new
  transition hypothesis.
- Current accounting: the compatibility brick is 100%; Gate 5 provider
  substitution is about 20%; the dedicated H6 producer is 100%;
  `NormalRadiusProfile.le_exp_radius` and the unconditional MSM135 endpoint
  remain theorem-level 0%.
