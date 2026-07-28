# GPT Pro consultation: canonical H6 radius architecture

Public repository: `https://github.com/liao9yuan/differential-geometry`.
Use the remote `short-time-existence` branch (currently
`7cbd2b4c5e679db34f815090712069ee9bdd22d4`) as the inspectable reference.
The checked local aligned worktree is `codex/short-time-existence-align` at
`94b4b457d2e21da96107c3ab7f5f6e5302d5ad50`, with additional uncommitted
declarations quoted below. Those local signatures and verification results are
newer than the remote branch and are authoritative for this consultation.

## 2026-07-27 whole-plan reconsultation

This is an end-to-end review of H6, not a request for the shortest next lemma.
The response must decide whether the entire route from the current intrinsic
geometry through `NormalRadiusProfile` and the all-order
`NormalCoordMetricBoundInput` producer is mathematically sufficient and
formalizable without adding the desired conclusion as a new assumption.

The following local results are newer than the historical status below and are
authoritative:

1. `IntrinsicGronwall.intrJacobi_ode` and `intrJacobi_bounds` are exact-green.
2. `IntrinsicFramedJacobi.intr_metric_jacobi`,
   `intrFrame_deriv_inj`, and `intrFrame_not_conj` are exact-green.
3. `H6NormalCoord.exists_intr_radii` is exact-green. It gives one
   sequence-uniform `r0 > 0` on which every complete intrinsic framed pullback
   metric satisfies the half/two quadratic-form estimate, with no
   `expRadiusGp` or qualitative branch clamp.
4. `H6NormalCoord.exists_intr_branches` is exact-green. On that same ball,
   every launch vector is nonconjugate and lies in the source of a selected
   smooth intrinsic inverse branch.
5. These local inverse branches do not by themselves prove injectivity on the
   whole ball. The formal `injRadius` and `expRadiusGp` still use the old
   chart-fixed/qualitatively selected exponential APIs.
6. The target theorem constructing `NormalRadiusProfile` is still unstated
   and therefore 0% complete. The all-order theorem constructing
   `NormalCoordMetricBoundInput` is also unstated and 0% complete.

The consultation must review the complete architecture:

- Verify all mathematical hypotheses needed by H6, including completeness,
  bounded curvature derivatives, CGT injectivity/noncollapse data, and the
  nonnegativity or metric realization of `InjRadiusDecayInput.dist`.
- Decide the final canonical intrinsic exponential, chart, pullback metric,
  injectivity-radius, and smooth-radius APIs. Do not leave a second polished
  hierarchy next to the existing framed API.
- Decide the final combined producer boundary, such as `H6NormalData`, which
  chooses the shrinkable bounds record and its relative profile together.
- Prove the quantifier order for one positive global ratio multiplying
  `hd.mu`; explicitly identify the theorem bounding `mu` above, or the missing
  distance-realization hypothesis needed to do so.
- Explain how CGT ballwise injectivity and the exact-green pointwise
  nonconjugacy results produce one partial diffeomorphism on a whole ball.
  State whether an off-zero chart-fixed/intrinsic agreement theorem is needed
  after the chosen canonical migration.
- Separate the radius/injectivity architecture from the independent all-order
  curvature-to-coordinate-metric jet induction.
- Give a migration DAG that keeps the selected diagonal/readout consumers
  checkable, including exact feasibility gates, expected blast radius, and
  stop/rollback conditions.
- Classify each remaining stage by mathematical and Lean difficulty. Identify
  the first substantial theorem, not merely the shortest syntactic lemma.
- Report theorem completion separately from infrastructure completion.

## Whole-plan consultation verdict

The end-to-end route is feasible. Retain Route A plus Route C, but strengthen
Route C: the H6 output must carry the controlled whole-ball inverse branch as
well as the radius and metric bounds. The earlier proposal

```lean
ENNReal.toReal (min injRadius 1) / 2
```

must not simply replace `expRadiusGp`. It gives a radius of injectivity only.
Injectivity of a smooth map does not imply an invertible differential or a
smooth inverse, while the current downstream meaning of `expRadiusGp` includes
exactly those local-diffeomorphism/source facts.

Do not add a `nonconjRadius` supremum to the H6 critical path. Such an API could
be mathematically valid, but the checked `exists_intr_radii` already supplies
the stronger fact needed here: one sequence-uniform ball on which the
intrinsic framed differential has a quantitative positive lower bound.
Packaging that fact into another supremum and then taking a minimum would add
a hierarchy with no independent consumer.

### Final hypotheses

The native producer has the following honest inputs:

```text
SeqMetricComplete X
forall k, ConnectedSpace (X.obj k).M
SeqBoundedGeometry X
hd : InjRadiusDecayInput X
hreal : hd.RealizesEdist
```

Completeness and connectedness support the total intrinsic exponential.
`SeqBoundedGeometry.C p` supplies the all-order curvature tower. `hd.decay`
supplies ballwise injectivity, after the `HasInjRadiusAt` backend is migrated
to the intrinsic framed exponential. `hreal` is not optional bookkeeping:
`hreal.dist_nonneg` and `hd.mu_antitone` give the global upper bound

```text
hd.mu (hd.dist k x basepoint) <= hd.mu 0.
```

The endpoint records already carry `realizes`, so this requires no new
consumer assumption.

### Correct radius quantifiers

Let `r0 > 0` be the exact-green uniform radius from `exists_intr_radii`, and
write `mu0 := hd.mu 0`. Choose

```text
aH6 := min (1 / 2) (r0 / (2 * mu0))
rho k x := aH6 * hd.mu (hd.dist k x basepoint).
```

Positivity of `mu0` gives `aH6 > 0`. Distance nonnegativity and antitonicity
give `rho k x <= r0 / 2 < r0`. Also `aH6 < 1`, so

```text
ofReal (rho k x) < ofReal (hd.mu distance) <= intrinsic injRadius.
```

Thus one positive ratio works for every sequence index and center. There is no
need to convert `injRadius` to a real number, and no attempt is made to compare
`rho` with the legacy qualitative `expRadiusGp`.

### Whole-ball branch assembly

The two inputs to the generic glue have separate provenance:

```text
IsLocalDiffeomorphOn on ball 0 rho
  <- rho < r0
  <- exists_intr_radii / intrFrame_not_conj / the existing local branches

InjOn on ball 0 rho
  <- rho < hd.mu distance
  <- hd.decay, after the intrinsic injectivity backend migration.
```

Add one canonical geometry theorem above `IntrinsicFramedJacobi`:

```lean
theorem intrFrame_localOn
    (hlower :
      forall z in Metric.ball 0 r,
        forall v, c * norm v ^ 2 <= intrFrameMetric ... z v v)
    (hc : 0 < c) :
    IsLocalDiffeomorphOn modelWithCornersSelf I infinity
      (intrinsicFramedExp ...) (Metric.ball 0 r)
```

It may use the exact-green pointwise `ExpInvBranch` witnesses. Restrict it to
`ball 0 rho`, combine it with intrinsic `InjOn`, and apply the existing generic
`exists_diffeo_of_injOn`. The result is one `C-infinity` partial
diffeomorphism whose source is exactly `ball 0 rho`.

### Final data boundary

First introduce a branch-parametric consumer interface, tentatively:

```lean
structure NormalBallChart (Y) (x : Y.M) where
  radius : Real
  radius_pos : 0 < radius
  hom : PartialDiffeomorph modelWithCornersSelf I E Y.M infinity
  ball_subset : Metric.ball 0 radius <= hom.source
  hom_eq : Set.EqOn hom (intrinsicFramedExp ...) (Metric.ball 0 radius)
```

The legacy selected branch can implement this interface during migration; the
H6 branch will implement it with equality in `ball_subset`. Consumers should
depend on this interface, not on the global qualitative choice
`framedExpDiffeo`.

The final H6 package should then have the semantic shape:

```lean
structure H6NormalData (X) (hd : InjRadiusDecayInput X) where
  ratio : Real
  ratio_pos : 0 < ratio
  chart : forall k x, NormalBallChart (X.obj k) x
  radius_eq : forall k x,
    (chart k x).radius =
      ratio * hd.mu (hd.dist k x (X.obj k).basepoint)
  metricC : Nat -> Real
  metricC_nonneg : forall p, 0 <= metricC p
  metric_equiv : forall k x, NormalCoordMetricEquivOn ...
      (Metric.ball 0 (chart k x).radius)
  metric_deriv : forall k p x, NormalCoordMetricDerivBound ...
      (Metric.ball 0 (chart k x).radius) p (metricC p)
```

It should expose projections to the reusable downward-closed
`NormalCoordMetricBoundInput`. The current `NormalRadiusProfile.le_exp_radius`
is a migration field, not part of the final contract: after consumers use
`chart.ball_subset`, remove that field and the endpoint dependency on
`expRadiusGp`.

The producer theorem must construct this package:

```lean
theorem exists_h6NormalData
    (hcomplete : SeqMetricComplete X)
    (hconn : forall k, ConnectedSpace (X.obj k).M)
    (hgeom : SeqBoundedGeometry X)
    (hd : InjRadiusDecayInput X)
    (hreal : hd.RealizesEdist) :
    Nonempty (H6NormalData X hd)
```

It is not acceptable to take `H6NormalData`, `NormalBallChart`, or a radius
floor as a new endpoint assumption.

### All-order metric-jet producer

The radius/branch construction and the all-order H6 estimate are independent
proof stages. The checked first-variation Jacobi theorem proves only the
zeroth-order metric comparison and first differential nonsingularity. It does
not imply

```text
norm (iteratedFDeriv Real p (intrFrameMetric ...) z) <= metricC p
```

for every `p`.

The remaining high-order route is:

1. formulate parameter-jet bounds for the intrinsic radial geodesic/Jacobi
   flow on the fixed `r0` tube;
2. differentiate the variational ODE in the launch parameter, with the
   order-`p` forcing expressed from `nabla^q Rm` and lower flow jets;
3. prove the constants-first induction using `SeqBoundedGeometry.C q` and the
   existing second-order Gronwall engine;
4. transfer endpoint flow jets to `iteratedFDeriv` of `intrFrameMetric` using
   the pullback-metric product formula;
5. restrict those estimates to `ball 0 rho` and fill `metricC`.

The dominant remaining theorem is an all-order uniform endpoint such as:

```lean
theorem exists_intr_metricJets
    (hcomplete : SeqMetricComplete X)
    (hconn : forall k, ConnectedSpace (X.obj k).M)
    (hgeom : SeqBoundedGeometry X) :
    exists r0 > 0, exists C : Nat -> Real,
      forall k p x,
        NormalCoordMetricDerivBound ... (Metric.ball 0 r0) p (C p)
```

The exact indexing of curvature orders versus metric orders should be fixed
when the differentiated variational equation is stated; do not hide it behind
an assumption record.

### Ordered migration DAG and gates

1. **Gate 0, intrinsic injectivity backend.** Move `injRadiusSet`,
   `injRadius`, and `HasInjRadiusAt` to the intrinsic framed-map semantics.
   Preserve temporary chart-fixed names only for low-level compatibility.
   Stop if `hd.decay` cannot yield `InjOn` for every strictly smaller intrinsic
   model ball.
2. **Gate 1, intrinsic local-diffeomorphism ball.** Prove
   `intrFrame_localOn` from the checked uniform metric lower bound.
3. **Gate 2, scalar ratio.** Prove the displayed `aH6` inequalities using
   `hreal.dist_nonneg`, `mu_antitone`, and `mu_pos`.
4. **Gate 3, whole-ball branch.** Lower the generic glue to a cycle-free
   module and construct the single intrinsic branch on `ball 0 rho`.
5. **Gate 4, provider migration.** Add the branch-parametric chart interface
    and migrate consumers under the legacy provider first. Focused/exact checks
    must remain green before changing providers. The live order is:
    `HasCmSolC.invVel_zero` and `HasNormalBrFull.exists_cmC`;
    `exists_hat_cmC_at`; the `StepCHatReadout` tail/min package;
    `StepCSupportCapstone` and `StepCStageSeed`; then
    `HasSuppConvData.actual_cm_tail` and `stage_root_tail`. Preserve the old
    `chartCmEqnB` declarations only as compatibility API while this order is in
    progress.
6. **Gate 5, provider switch.** Install the intrinsic H6 provider, switch the
    selected diagonal/readout chain, then delete `le_exp_radius` and obsolete
    `expRadiusGp` source proofs from the endpoint path. The switch is not a
    final-theorem substitution: first make the stage diagonal/root equation
    carry the same chart family as the center readout. In particular,
    `HasDiagPairConv` must carry that family through its `IsNormalDiag` and
    `NormalDiagFence` fields, and the `stageCfgSub`/`stageInvVelSub` root path
    must use it consistently. Only after that feasibility gate may
    `actual_cm_tail` and `stage_root_tail` be instantiated by the H6 family.
7. **Gate 6, metric jets.** Prove the independent all-order induction and
   assemble `H6NormalData`.
8. **Gate 7, endpoint replay.** Reconstruct `MetricCompactBase` from native
   producers and replay the already checked B/C, Step D, and public endpoint
   DAG.

The generic `exists_diffeo_of_injOn` should move to a low-level
local-diffeomorphism glue file. The intrinsic injectivity API should live above
`IntrinsicFramedCoordinates` but below HCG. `intrFrame_localOn` belongs in an
intrinsic ball-chart module above `IntrinsicFramedJacobi`. `H6NormalData`
belongs in a new C4 producer file importing `H6NormalCoord` and Step-A inputs;
putting it back into `StepBInputs` would create an import cycle.

### Difficulty and honest accounting

- Intrinsic injectivity backend: moderate semantic migration, broad proof-shape
  blast radius.
- `intrFrame_localOn` and the scalar ratio: routine-to-moderate, with the
  required mathematical inputs already exact-green.
- Whole-ball branch: moderate reusable API/assembly work.
- Branch-parametric consumer migration: broad but mechanical; current search
  counts are 38 Lean files mentioning `framedExpDiffeo`, 34 mentioning
  `framedChartAt`, and 56 mentioning `expRadiusGp`. Not every occurrence needs
  editing, but this is not a narrow two-file change.
- All-order curvature-to-metric jet induction: substantial mathematical and
  formalization frontier; it dominates the remaining H6 effort.

The first non-mechanical integration endpoint is the whole-ball intrinsic
branch from `hd.decay` and `exists_intr_radii`. The principal H6 theorem
frontier remains `exists_intr_metricJets`.

`NormalRadiusProfile` native producer: unstated, 0%. Full
`exists_h6NormalData`: unstated, 0%. Dedicated zero-order Jacobi/Rm04
machinery: 100%. Radius/injectivity/branch infrastructure: about 55%. Dedicated
all-order metric-jet machinery: about 35%. Overall H6 producer machinery:
about 40%. Unconditional MSM135 Theorem 3.9 remains 0%; whole HCG supporting
machinery remains about 60%.

## Decision and execution status

The consultation verdict is accepted: use Route A for the canonical geometry
and branch-carrying Route C at the H6 producer boundary. There must be one total
intrinsic framed exponential and one induced pullback metric. The H6 partial
diffeomorphism is a controlled whole-ball witness stored by the producer, not
a second canonical chart hierarchy. The legacy `expRadiusGp` remains only as a
migration provider until consumers are branch-parametric; it is not a
geometric lower-bound target.

The Lean import DAG requires one adjustment to the proposed order. The current
`FramedNormalCoordinates.lean` cannot import the intrinsic stack without a cycle
through Hopf-Rinow, Gauss, injectivity, and framed coordinates. Stage 1 therefore
lives temporarily in
`Geometry/Exponential/IntrinsicFramedCoordinates.lean`, above both stacks.
It is focused-green and exact-green and proves the intrinsic framed map is smooth,
fixes the origin, has the normal-frame derivative there, and agrees with the
legacy map on a positive ball. The fixed-model-norm bridge is explicit as
`intrFrameCLM`. It also provides the migration-only intrinsic local partial
diffeomorphism and the pullback metric of the total intrinsic map, with agreement
to the legacy metric on the migration source.

Current status: Gates 1--3 are complete. The intrinsic total map, pullback
metric, zero-order uniform estimate, intrinsic injectivity backend,
nonconjugacy, whole-ball branch assembly, and provider-native Hessian/implicit
function package are focused/exact green. `NormalBallChart` is the single
branch-parametric interface; no second chart hierarchy was introduced.

Gate 4 is in progress. `HasCmSolC`, `HasChartCmSol`, the H6 finite-hat
readout, `StepCCmDomain.centerReadoutB_min`, and
`HasNormalBrFull.exists_cmC` are checked. `NormalChartFamily` now names the
stage-indexed provider. It has been threaded in source through
`HasSuppCmFin`, `HasSourceCmFin`, `HasSuppCmData`, and the stage-seed
consumer, with `legacyChartFamily` preserving the checked route. The selected
finite-hat tail and first stage-root consumer have also been migrated in
source to `HasChartCmSol`. Their ordered focused/exact verification is still
pending because an unrelated exact writer currently owns the shared artifact
chain and `NormalBranchHessian.olean` is absent; this is a tooling block, not a
proof failure. Gate 5 has not switched the selected route to the H6 provider,
so `NormalRadiusProfile.le_exp_radius` remains a migration dependency. Gate 6,
the all-order intrinsic metric-jet producer, remains independent and open. Its
generic order-zero base is now focused-green as
`NormalBallChart.MetricEquivOn.deriv_zero`; this does not advance the unstated
all-order producer theorem. The provider-transfer end of Gate 6 is also now
focused-green: `H6ChartData.metric_eq_intr` identifies the H6 chart metric with
`intrFrameMetric` on the controlled ball, and
`NormalBallChart.MetricDerivBound.of_eqOn` transfers every future intrinsic
jet bound without changing its constant. Thus no chart-agreement assumption is
missing from final assembly; the fixed-tube quantitative jet induction remains
the sole Gate 6 mathematical frontier. `exists_intr_control` is focused-green
and chooses one radius carrying both half/two equivalence and the local
diffeomorphism property. `H6BallData` now retains that exact zero-order estimate
on its selected relative ball; the downstream `normal_equiv` projection awaits
only the coordinated upstream artifact refresh. This prevents final assembly
from mixing independently chosen radii. `H6ChartData.radius_le_global` also
places every selected chart ball inside the explicit fixed launch ball of
radius `d.ratio * hd.mu 0`. The quantitative theorem should therefore accept
an arbitrary nonnegative finite launch radius and return constants depending
on it; final assembly instantiates that theorem at this global radius instead
of trying to recover the earlier local-diffeomorphism radius witness.

Gate 5 needs a broader chart-identity migration than the earlier five-name
list suggested. The stage-indexed family

```lean
forall (k : Nat) (x : (X.obj k).M), NormalChartAt (I := I) (X.obj k) x
```

already reaches the support/seed layer. Before the provider switch, thread it
through the selected diagonal/root owners: `HasDiagPairConv` and its
`IsNormalDiag`/`NormalDiagFence` witnesses, then the
`stageCfgSub`/`stageInvVelSub` root equation and the target-chart readout in
`actual_cm_tail`/`stage_root_tail`. The current root proof still defines
`chiK`, `chiL`, `qstar`, `zc`, and `xi` with the legacy framed chart and
decodes through `normalExpPD`; a solution stated in the H6 chart cannot be
transported into that equation by definitional equality. Nor may the proof
assume global H6/legacy agreement, because the H6 whole-ball radius is not
bounded by the migration-only legacy agreement radius. First recheck this
parameterized chain with `legacyChartFamily`, then instantiate the identical
declarations by `H6NormalData.chart`. Do not replace the family by an
existential witness, add a compatibility assumption, or introduce a parallel
H6 capstone hierarchy.

The immediate next target remains Gate 4 verification, in dependency order:
`NormalBranchHessian`, `HatChartReadout`, `NormalBranchCage`,
`StepCHatReadout`, `StepCSupportCapstone`, `StepCStageSeed`, and
`StepCStageComparison`. Once exact-current, Gate 5 begins at
`NormalBranchConv.HasDiagPairConv`, not at the final `stage_root_tail`
rewrite.

`exists_h6NormalData` remains theorem-level 0% because it is not yet stated.
Dedicated radius/branch machinery is about 80%; branch-parametric consumer
migration is about 35%; all-order metric-jet machinery is about 35%; overall
dedicated H6 producer machinery is about 55%. Completeness stays explicit in
the producer theorem.

The latest Gate 6 assembly check is source-green against an isolated
`H6NormalCoord` artifact overlay. In particular, `H6BallData.intr_equiv`,
`H6BallData.normal_equiv`, and `exists_h6BallData` elaborate together. The
single local correction was binder normalization past the result-type
`let hEnorm`; no new hypothesis, branch agreement, or radius comparison was
needed. A formal exact refresh remains deferred until the unrelated shared
writer exits.

The sections below preserve the original consultation input and historical
route comparison. Where they conflict with the whole-plan verdict above, the
whole-plan verdict is authoritative.

## Goal

Choose the smallest mathematically honest architecture that lets Hamilton H6
produce the sequence-relative normal-coordinate radius used by Step B/C. Do
not add a consumer assumption equivalent to the desired radius floor, and do
not create a second polished normal-coordinate hierarchy beside the canonical
one.

## Newly verified state

The intrinsic geodesic route is no longer an analytic frontier.

1. `Geometry/Geodesic/CrossVFReduction.lean` proves global smoothness of the
   basepoint-free geodesic spray.
2. `Analysis/ODE/TimeDependentFlow/SmoothDependence/CompactTrajectory.lean`
   proves finite-time smooth dependence along every compact reference orbit.
3. `Geometry/Exponential/IntrinsicVelocity.lean` proves:

   ```lean
   intrinsicExp_smooth
   intrinsicFiber_smooth
   intrinsicVar_smooth
   ```

   for the complete intrinsic exponential and fixed-base affine velocity
   variations. This module is focused- and exact-green.
4. `Geometry/Exponential/JacobiVariation.lean` proves:

   ```lean
   intrinsic_jacobi
   intrinsic_jacobi_one
   ```

   The first is the global Jacobi equation for
   `s,t |-> intrinsicGeodesic p (x + s*w) t`; the second identifies its
   time-one variation field with the vector-slot manifold derivative of
   `expMapIntrinsic`. Both declarations are focused- and exact-green; the
   coordinated refresh passed (`3799/3799`).
5. `C4/H6NormalCoord.lean` has exact-green sequence-uniform Rm04/Jacobi
   estimates and zero-order half/two metric equivalence on

   ```lean
   ball 0 (min r0 (expRadiusGp metric x / 26)).
   ```
6. `Comparison/InjectivityRadius.lean` proves that injectivity of the current
   framed ordinary exponential on a model ball forces that ball into the
   current chart-fixed `expDomain`.
7. `Comparison/ExpBallDiffeo.lean` already exposes

   ```lean
   IsLocalDiffeomorphOn.exists_diffeo_of_injOn
   ```

   so partial-diffeomorphism gluing is not missing.

No theorem above introduces a new assumption, `sorry`, `admit`, or axiom.

## Current canonical definitions

`FramedNormalCoordinates.lean` still defines

```lean
def framedExpMap (g) (p) : E -> M :=
  fun z => expMap g p (normalFrame g p z)

def framedExpDiffeo (g) (p) :=
  -- conjugates the qualitative chart-fixed expMapDiffeo by normalFrame
```

Here `expMap g p v := maximalGeodesic g p v 1` is the chart-fixed
totalized exponential. Its own documentation states that it becomes junk once
the geodesic leaves `(chartAt H p).source`. By contrast,
`expMapIntrinsic g hEnorm p v` follows the complete geodesic across charts.

`GaussLemmaPullback.lean` defines `expRadiusGp` from the qualitatively selected
`expMapC2Radius` and coercivity constants. It is therefore a radius for the
current chart-fixed selected partial diffeomorphism, not a geometric
injectivity radius.

`Comparison/InjectivityRadius.lean` currently defines

```lean
def injRadiusSet (g) (p) : Set ENNReal :=
  {r | Set.InjOn (framedExpMap g p) (Metric.eball 0 r)}

def injRadius (g) (p) : ENNReal := sSup (injRadiusSet g p)
```

Thus this `injRadius` is also tied to the chart-fixed ordinary exponential.

The Step-B record is

```lean
structure NormalCoordMetricBoundInput (X) where
  metricC : Nat -> Real
  metricC_nonneg : forall p, 0 <= metricC p
  radius : forall k, (X.obj k).M -> Real
  radius_pos : forall k x, 0 < radius k x
  metric_equiv : forall k x,
    NormalCoordMetricEquivOn (X.obj k) x (Metric.ball 0 (radius k x))
  metric_deriv : forall k p x,
    NormalCoordMetricDerivBound (X.obj k) x
      (Metric.ball 0 (radius k x)) p (metricC p)
```

and the compatibility record is

```lean
structure NormalRadiusProfile (hd : InjRadiusDecayInput X)
    (hb : NormalCoordMetricBoundInput X) where
  ratio : Real
  ratio_pos : 0 < ratio
  le_radius : forall k x,
    ratio * hd.mu (hd.dist k x (X.obj k).basepoint) <= hb.radius k x
  le_exp_radius : forall k x,
    ratio * hd.mu (hd.dist k x (X.obj k).basepoint) <=
      expRadiusGp (X.obj k).metric x
```

## Two feasibility failures

### 1. `NormalRadiusProfile` cannot be produced from an arbitrary `hb`

The data in `NormalCoordMetricBoundInput` is downward closed in `radius`: from
any valid record one may replace `radius k x` by an arbitrarily smaller
positive value and restrict both estimates. Therefore no theorem of the form

```lean
forall hd hb, NormalRadiusProfile hd hb
```

can be true. Even on one fixed flat metric, choose `hb.radius k x = 1/(k+1)`
while `hd.mu` is constant. The required positive global `ratio` cannot exist.

The H6 producer must choose the radius together with the metric-bound record,
or the record must carry an honest source-radius floor as part of its H6 data.
It cannot be recovered afterward from the current fields.

### 2. Geometric injectivity cannot lower-bound the current `expRadiusGp`

`expRadiusGp` contains an arbitrary qualitative IFT/chart choice. A sequence of
flat manifolds can use center charts whose source neighborhoods shrink with
the sequence while the intrinsic geometry and geometric injectivity radius
stay unchanged. CGT injectivity controls `expMapIntrinsic`; it cannot uniformly
lower-bound a chart-dependent selected radius.

The same issue affects the current `injRadius`, because its map is
`framedExpMap = expMap o normalFrame`, not the complete intrinsic exponential.
The new global Jacobi/differential theorems do not repair this representation
mismatch.

## Architecture decision requested

Please choose and justify the smallest route among these, or give a better one.

### Route A: migrate the canonical framed API to the intrinsic exponential

Parameterize the canonical framed exponential/partial diffeomorphism by the
metric-enorm compatibility proof already used by the intrinsic API:

```lean
hEnorm : forall x (v : TangentSpace I x),
  eNorm v = ENNReal.ofReal (Real.sqrt (g.inner x v v))
```

Then redefine or replace, in dependency order:

```lean
framedExpMap
framedExpDiffeo
framedChartAt
normalCoordMetric
injRadius
expRadiusGp
```

using `expMapIntrinsic`. Preserve the existing public names if possible and
migrate the current framed B/C consumers once, rather than maintaining two
normal-coordinate hierarchies.

Questions for Route A:

1. What is the narrowest canonical file for the intrinsic framed map and its
   local partial diffeomorphism?
2. Should `hEnorm` be an explicit argument throughout, or can an existing
   metric/bundle package provide it without introducing a new foundational
   typeclass?
3. Can positivity of the intrinsic injectivity radius be proved most cheaply
   by transferring the existing local ordinary branch through the already
   proved small-radius equality, or should one apply the manifold IFT directly
   to `intrinsicFiber_smooth` and the identity derivative at zero?
4. Give the smallest migration order that keeps the current B/C selected
   branch usable after each step.

### Route B: keep local ordinary charts, add one geometric branch beneath H6

Keep the current local `framedExpDiffeo` for existing consumers, but construct
one intrinsic injective partial diffeomorphism on a CGT-controlled ball from:

```text
intrinsicFiber_smooth
  + intrinsic_jacobi_one
  + Rm04 derivative estimates
  + intrinsic injectivity
  + exists_diffeo_of_injOn.
```

Then make the H6 metric bounds and all downstream radius-sensitive consumers
use that branch. Explain how this avoids becoming a second polished
normal-coordinate hierarchy and how the existing `normalCoordMetric` is
transported to it without any qualitative agreement radius.

### Route C: combined H6 output first

Change the producer boundary so H6 returns a chosen metric-bound record and its
profile together, for example:

```lean
structure H6NormalData (X) (hd : InjRadiusDecayInput X) where
  bounds : NormalCoordMetricBoundInput X
  profile : NormalRadiusProfile hd bounds
```

This fixes the shrinkable-radius quantifier problem but not by itself the
chart-fixed `expRadiusGp` problem. State what canonical exponential migration
must accompany it.

## Requested answer

1. Verdict and selected architecture.
2. Exact first public theorem or definition to implement, with a Lean-like
   signature and natural file.
3. Proof/migration dependency chain.
4. Which current public definitions must change and which can remain stable.
5. How to package the H6 radius so it is chosen with the all-order metric
   estimates rather than demanded from arbitrary shrinkable input data.
6. How the intrinsic Rm04/Jacobi endpoint proves local-diffeomorphism and
   metric-equivalence bounds on the chosen geometric ball.
7. Whether the high-order curvature-to-coordinate-metric induction is an
   independent remaining theorem after the radius architecture is corrected.
8. Difficulty classification: routine migration, missing reusable API,
   substantial design choice, or genuine mathematical obstruction.

## Constraints

- Work on the `short-time-existence` branch.
- Preserve the current quantitative selected diagonal branch and its transport
  theorems.
- Do not add a synonymous radius-floor assumption downstream.
- Do not claim `NormalRadiusProfile` is proved merely because intrinsic
  smoothness and Jacobi identities are proved.
- Do not derive a positive ratio from an arbitrary shrinkable `hb.radius`.
- Do not claim CGT controls the current chart-dependent `expRadiusGp` without
  changing or quantitatively identifying that API.
- Do not introduce a new foundational class without explaining why existing
  metric/bundle data cannot carry `hEnorm` explicitly.
- Keep the high-order H6 curvature-jet induction visible as a separate
  producer if it is still required.
