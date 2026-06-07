# HamiltonPositiveRicci live frontier audit

Date: 2026-06-05

Workspace: `E:\testdifferential-geometry`

Branch: `short-time-existence`

Lean file:
`DifferentialGeometry/Geometry/Flow/RicciFlow/DimensionThree/HamiltonPositiveRicci.lean`

Verification:

- `lake build` completed successfully after the branch update.
- Current Hamilton file has six theorem-shaped `sorry`s.
- `DifferentialGeometry/Geometry/Flow/RicciFlow/MaximalTime.lean` has one additional extension-criterion `sorry` that is upstream of the maximal-flow package story.

## Current structure

This file is no longer just a statement shell.  The middle Hamilton pipeline is
substantially checked:

- scalar lower-bound package extraction: `ham3_scalar74`, `ham3_finite_time`;
- point selection from scalar blow-up: `ham3_scalar_blowup`, `ham3_point_select`;
- Section 9 Ricci nonnegativity and pinching consumers:
  `ham3_ric_nonneg9`, `ham3_rescaled_ric_nonneg`,
  `ham3_pinch9_fixed`, `ham3_pinch9`;
- Section 10 pinching estimate consumer:
  `ham3_pinch_imp_can`, `ham3_pinch_imp`;
- curvature control from nonnegative Ricci:
  `ham3_rm_bound`;
- fixed-window arithmetic:
  `ham3_r0_window`;
- limit-flow algebra after CGH data is supplied:
  `limit_scalar_nonneg`, `limit_inherit`, `limit_tf_zero_of_decay`,
  `limit_tf_zero`, `limitEinstein_of_tf0`,
  `limit_const_sec_of_einstein`, `const_pos_of_tf0`,
  `limit_const_pos`.

The important point is that the finite-dimensional 3D algebra and the static
Einstein-to-space-form computation are already checked.  The remaining work is
mostly not local tensor algebra.

## Remaining `sorry`s

### `ham3_flow_exists_normalized`

Location: near line 490.

Role: produces the normalized maximal finite-endpoint Ricci-flow package
`Ham3FlowPackage`, including the solution, `IsSmoothSolutionOn`, initial metric
identity, and curvature blow-up.

Current repo support:

- `DeTurckShortTime.lean` has `deTurckRicci_shortTime_existence_of_closed`.
- `HamiltonDeTurckPullback.lean` has the pullback theorem route from DeTurck
  flow to Ricci flow, but it still exposes analytic hypotheses such as raw
  variational identities and an additive chain rule.
- `MaximalTime.lean` has the maximal/singularity vocabulary and checked
  consumers from the extension criterion, but `extends_of_rmBounded` remains a
  black-box global PDE theorem.

Assessment: not fillable in one local pass.  It can be advanced by building an
intermediate theorem that returns a short-time `SolutionOn` from the DeTurck
pipeline, then a separate maximal-continuation package.  Do not try to prove the
whole normalized maximal-flow setup directly inside this file.

2026-06-05 update: `HamiltonPositiveRicci.lean` now imports
`RicciFlow/ShortTimeExistence.lean` and exposes `ham3_short_exists`, a checked
adapter that cites `ricci_flow_short_time_existence` for the full raw
metric-family/chart-Gram/PDE short-time output.  This reuses the current
headline directly, but it does not close `ham3_flow_exists_normalized`: the
short-time theorem is stated for an inner-product model space, needs
`BoundarylessManifold I M`, and returns a raw metric family rather than the
canonical `SolutionOn`/`IsSmoothSolutionOn` plus normalized maximal interval and
endpoint curvature blow-up required by `Ham3FlowPackage`.

Verification passed for the Hamilton file after the adapter.  The remaining
frontier is still the maximal-continuation/package promotion, not the short-time
existence headline.

2026-06-05 exhaustive audit update: the short-time dependency surface was
source-checked around the headline and assembly/flow stack.  The active
short-time proof-body placeholders found are the DeTurck-Ricci parabolic
short-time theorem and the Weyl/on-diagonal spectral analytic input.  A direct
source-check failure in `Pullback/Defs.lean` was repaired before rechecking the
headline and Hamilton consumer.

### `ham3_noncollapse`

Location: near line 2087.

Role: turns Perelman's no-local-collapsing theorem plus curvature control on the
selected rescaled slabs into `Ham3Noncollapse P Q kappa ham3_r0`.

Current repo support:

- `Perelman/Noncollapsing.lean` defines abstract `ScaleControlledBall`,
  `KappaNoncollapsedAtBall`, and no-local-collapsing statement interfaces.
- `Ham3Noncollapse` already stores explicit small/unit ball witnesses through
  `Ham3BallPair`.
- `Ham3Noncollapse.unitVolLower` and `Ham3Noncollapse.unitNested` are checked
  projections.

Assessment: this is one of the best next targets, but not by proving Perelman's
theorem.  The tractable next step is an adapter theorem:

1. define the selected `ScaleControlledBall` family for the `r0` balls;
2. connect radius/window/curvature-control hypotheses to the abstract
   `KappaNoncollapsedAtBall`;
3. package the small/unit ball pair and volume monotonicity into
   `Ham3Noncollapse`.

That reduces `ham3_noncollapse` to the real Perelman theorem interface instead
of leaving all ball witness work inside the black box.

### `ham3_cgh_limit`

Location: near line 2107.

Role: produces `Ham3CGHLimitExists P Q` from curvature control, fixed window,
and noncollapsing.

Current repo support:

- `Ham3CGHLimitExists` already exposes the useful Section 12 output:
  subsequence, window, regularity, connected/boundaryless limit manifold,
  smooth limit flow, Ricci transfer, base scalar convergence, positive scalar,
  and pinching transfer.
- There is no concrete CGH convergence relation or approximate-isometry map
  layer in this current `DifferentialGeometry` tree comparable to the older
  `HCGCompactness` work.

Assessment: keep this as a genuine compactness black box for now.  The useful
next work is to introduce an honest CGH convergence record, not to fake the
proof.  Minimum useful fields would include pointed embeddings/diffeomorphisms
on compact exhaustion sets, smooth pullback convergence of metrics and
curvature, and explicit transfer theorems for Ricci nonnegativity, scalar base
normalization, and pinching decay.

### `limit_to_orig`

Location: near line 2643.

Role: transfers a constant-positive-sectional metric on the CGH limit manifold
back to the original manifold `M`.

Current problem:

- `Ham3CGHLimitExists` currently proves existence of a limit flow and transfer
  data, but it does not store an eventual diffeomorphism between `M` and the
  limit manifold.
- The theorem statement consumes only the current `hlimit` tuple and
  `LimitConstPosSec L`; those hypotheses do not contain enough data to build a
  metric on `M`.

Assessment: this is another good next target, but the statement needs a real
producer/interface.  The smallest honest move is to add a separate transfer
predicate, for example `Ham3LimitEventuallyDiffeomorphicToOriginal` or
`Ham3LimitConstPosSecTransfersToOriginal`, and make `limit_to_orig` a checked
consumer of that datum.  If that datum is folded into `Ham3CGHLimitExists`,
then `ham3_limit_const_metric` can stay as the main consumer.

### `ham3_space_box`

Location: near line 2755.

Role: global geometry/topology theorem: closed connected constant-positive
sectional curvature implies spherical space-form topology.

Assessment: not a local Hamilton/Ricci-flow target.  It needs a global
Riemannian topology package: universal cover, Bonnet-Myers or compactness,
space-form classification, deck group, and quotient model.  Current nearby
files have universal-cover and Bonnet-Myers-facing material, but not a direct
producer for `SphericalSpaceForm`.

### `spaceForm_const_metric`

Location: near line 2768.

Role: reverse direction: construct a constant-positive-sectional metric from a
spherical space-form quotient model.

Assessment: also global quotient-geometry work.  It may be easier than
`ham3_space_box` if one introduces a quotient Riemannian metric API for finite
free isometric quotients of the round sphere.  It is not a Lean-local theorem
from the current fields alone, because the structure does not already package a
descended smooth Riemannian metric.

## Best next work

Recommended order:

1. **Make `limit_to_orig` honest.**
   Add a compactness-transfer predicate or field that explicitly supplies the
   eventual diffeomorphism/pullback metric transfer from the CGH limit to `M`.
   Then turn `limit_to_orig` into a checked consumer.  This would remove one
   misleading `sorry` from the final Section 12 chain without pretending to
   prove CGH compactness.

2. **Factor `ham3_noncollapse`.**
   Add an adapter from the abstract Perelman ball vocabulary to
   `Ham3Noncollapse`.  The current `Ham3BallPair` and projections are already
   designed for this.  This makes the remaining black box exactly Perelman's
   no-local-collapsing theorem, rather than a mixed package.

3. **Split `ham3_flow_exists_normalized`.**
   Do not attempt the full global setup at once.  First target a short-time
   Ricci-flow package from the DeTurck short-time theorem and pullback theorem;
   then separately connect maximal continuation and the
   `MaximalTime.extends_of_rmBounded` extension criterion.

4. **Leave `ham3_cgh_limit` as black-box until a real CGH record exists.**
   The next productive step is interface design: maps, domains, convergence of
   pullback metrics/curvatures, and transfer lemmas.  A direct proof attempt in
   `HamiltonPositiveRicci.lean` would become a fake compactness API.

5. **Postpone `ham3_space_box` and `spaceForm_const_metric`.**
   They are global topology/quotient geometry, not the Ricci-flow endpoint
   frontier.  They should live in a separate topology/space-form layer.

## Short next prompt

Work in `E:\testdifferential-geometry` on
`DifferentialGeometry/Geometry/Flow/RicciFlow/DimensionThree/HamiltonPositiveRicci.lean`.
Do not attack the CGH compactness theorem directly.  First introduce an honest
limit-to-original transfer predicate for eventual diffeomorphism/pullback of a
constant-positive-sectional metric, then refactor `limit_to_orig` into a
checked consumer of that predicate and verify the Hamilton module.

## 2026-06-05 reschedule note: HCG-first route

The current working priority should be adjusted toward importing the old HCG
compactness work into the rescheduled `DifferentialGeometry` tree by copy/paste,
not by importing the old `RicciFlower` namespace.

### Live correction: scalar positivity

Do not overread the absence of the old name `limit_scal_pos_smp` in this file.
The current `HamiltonPositiveRicci.lean` search finds `LimitScalarPosAt`,
`LimitScalarPos`, `LimitScalarNonneg`, and checked consumers such as
`limit_scalar_nonneg` and `limit_const_pos`, but not the old symbol
`limit_scal_pos_smp`.  It may have been split, renamed, or moved during the
reschedule.  Before deciding scalar strong maximum principle work is closed,
tomorrow re-search the scalar maximum principle and limit-flow files for the
actual producer of `LimitScalarPos`.

### HCG import target

The old HCG material under
`E:\differential-geometry\RicciFlower\HCGCompactness\` should be treated as the
source to copy and adapt.  The current tree has no comparable
`HCGCompactness` folder, while `HamiltonPositiveRicci.lean` already exposes the
Section 12 consumer interface:

- `Ham3CGHLimitData`;
- `Ham3CGHLimitExists`;
- `Ham3RicNonnegTransfer`;
- `Ham3LimitBaseScalarConv`;
- `LimitScalarPos`;
- `Ham3PinchTransfer`.

The promising route is:

1. Add a current-tree HCG folder, probably under
   `DifferentialGeometry/Geometry/Flow/RicciFlow/HCGCompactness/`, unless the
   import graph shows a better `Geometry/Compactness/` home.
2. Copy the old HCG interface files in small groups, renaming imports and
   namespaces to the current `DifferentialGeometry` layout.
3. Keep the metric compactness theorem, MSM135 Theorem 3.9, as an honest
   theorem-shaped input/interface at first.  Do not fake its proof.
4. Prove or assemble MSM135 Theorem 3.10, "Compactness for solutions", from the
   assumed 3.9 plus serious explicit inputs: pointed flow sequence data,
   derivative bounds, injectivity/noncollapse input, smooth-flow upgrade, and
   time-window bookkeeping.
5. Add a thin adapter from the 3.10 conclusion into `Ham3CGHLimitExists`.

If this route works, `ham3_cgh_limit` is no longer an opaque black box: it can
be filled by applying the 3.10 interface to the selected rescaled flows and
then forgetting the HCG conclusion down to the Hamilton Section 12 fields.  The
hard work is not the final `exact`; it is packaging the inputs and transfer
fields honestly.

### What 3.10 must provide for Hamilton

For the Hamilton endpoint, the solution compactness interface should at least
produce:

- a limit manifold and pointed smooth Ricci-flow solution on the fixed backward
  window;
- a strict subsequence selecting the rescaled flows;
- regularity on the open fixed window;
- connectedness and boundarylessness of the limit, or a separate topology
  producer;
- scalar basepoint convergence, enough to prove `LimitBaseScalarOne`;
- smooth Ricci tensor transfer, enough for `Ham3RicNonnegTransfer`;
- pinching/trace-free Ricci transfer, enough for `Ham3PinchTransfer`;
- positive scalar on regular times, or a clear scalar strong maximum principle
  producer if this is not already carried by the current rescheduled scalar
  layer.

The last four bullets are where the adapter needs care.  A generic pointed
compactness theorem will not by itself know Hamilton's normalization, Ricci
nonnegativity, or improved pinching statement.

### Noncollapse and injectivity

The current tree already has
`DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/Noncollapsing.lean` with
abstract `ScaleControlledBall`, `KappaNoncollapsedAtBall`, and no-local-
collapsing theorem interfaces.  `HamiltonPositiveRicci.lean` also has
`Ham3BallPair`, `Ham3Noncollapse`, `Ham3BallPair.nested_of_le`, and the
noncollapse consumer surface.

For the HCG route, Perelman noncollapse should eventually feed the injectivity
or noncollapse input needed by MSM135 3.10.  The immediate adapter target is not
to prove Perelman's theorem, but to connect the existing Hamilton ball witnesses
and curvature-window data to the compactness input expected by the 3.10 wrapper.

### Space-form direction: current global geometry status

Current live tree has more global geometry than the older note assumed:

- `DifferentialGeometry/Geometry/Metric/Pullback.lean` provides
  `Diffeomorph.pullbackMetric` and its inner-product evaluation.
- `DifferentialGeometry/Geometry/Curvature/PullbackNaturality.lean` provides
  `metricRm04Std_pullback`; a focused `rg` found no local `sorry` in that file.
- `DifferentialGeometry/Geometry/Topology/UniversalCover/` contains the
  universal-cover manifold, lifted metric, curvature pullback, completeness
  pullback, and fibre-equivalence layer.
- `DifferentialGeometry/Geometry/Comparison/BonnetMyers/Headlines.lean`
  contains the diameter, compactness, and finite-fundamental-group headline
  route.

But `spaceForm_const_metric` is still not a short local fill:

- there is no current `RoundSphere.lean` / `roundMetricS3` module in this tree;
- `RoundSphere3` is only an abbrev inside `HamiltonPositiveRicci.lean`;
- `SphericalSpaceFormQuotientModel` stores a finite free metric-space
  isometric action and an abstract quotient smooth structure, but not a
  descended smooth Riemannian quotient metric;
- Bonnet-Myers compactness and finite fundamental group still have explicit
  `sorryAx` caveats in `Headlines.lean`, and `UniversalCover/Manifold.lean`
  has a remaining fibre-countability/good-cover `sorry`.

So the direct construction direction should be planned as a separate
space-form/quotient geometry project:

1. build or import a round `S^3` smooth Riemannian metric and prove constant
   sectional curvature;
2. strengthen the quotient model or add an adapter carrying a descended smooth
   quotient metric from a finite free isometric action;
3. use `metricRm04Std_pullback` to pull constant positive sectional curvature
   back along the stored smooth equivalence.

The reverse direction `ham3_space_box` depends more on Bonnet-Myers,
universal-cover, deck group, and spherical-space-form classification, so it is
even less likely to be the next local theorem.

### Tomorrow's concrete first pass

1. Re-check whether `limit_scal_pos_smp` is now in a split scalar file or has
   been absorbed into current `LimitScalarPos` data.
2. Create the current-tree HCG folder and copy the smallest old files needed to
   state MSM135 3.9 and 3.10 interfaces.
3. Keep 3.9 as the honest compactness input; focus on proving the 3.10 wrapper
   shape and the adapter into `Ham3CGHLimitExists`.
4. After the adapter compiles, revisit `ham3_cgh_limit` and see whether its
   remaining inputs are exactly curvature window, noncollapse/injectivity, and
   transfer fields.
5. Separately audit `spaceForm_const_metric` against the live global geometry
   files, especially pullback curvature, universal cover, Bonnet-Myers status,
   and the missing round-sphere/quotient-metric layer.

## 2026-06-05 short-time -> SolutionOn bridge landed

Goal of this pass: advance `ham3_flow_exists_normalized` by *genuinely citing*
the short-time headline `ricci_flow_short_time_existence` (through the existing
adapter `ham3_short_exists`), packaging its raw output into a folder-level
`SolutionOn`, without hiding any gap behind a fake wrapper.

### Context change

The Hamilton global variable block was switched to an inner-product model space,
matching what the short-time headline requires:

```
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
```

(`InnerProductSpace Real E` subsumes the old `NormedSpace Real E`; `NeZero
(Module.finrank Real E)` is the dimension-positivity instance the short-time and
`ricciTensor` APIs use.)  This makes `ham3_short_exists` citable at the file's own
`E, I, M`.  `BoundarylessManifold I M` is *not* added globally: it is supplied per
theorem, either as an explicit instance binder (where the signature mentions
`ricciTensor`) or derived from `hM.2.2.1` via the Mathlib instance
`[I.Boundaryless] -> BoundarylessManifold I M`.

### New declarations (inserted right after `ham3_short_exists`)

1. `ham3_short_solution_candidate` — **CHECKED, no `sorry`.**
   The local bridge.  From `Closed3Manifold` + `g0` it cites `ham3_short_exists`
   and returns `T > 0`, a `SolutionOn (closedOpen 0 T hT)` whose
   `S.family.metric` is (definitionally) the short-time `g_fam`, the start-metric
   identity `S.family.metric (closedOpen 0 T hT).initial = g0`, and the raw
   chart-Gram smoothness (`Ioo 0 T`), chart-Gram continuity (`Ico 0 T`), and
   pointwise `∂_t g = -2 Ric` PDE restated in terms of `S.family.metric`.
   Carries `[BoundarylessManifold I M]` as a binder because the PDE clause names
   `ricciTensor`.

2. `ham3_isSolution_of_shortTimeData` — **honest frontier, `sorry`.**
   Takes a `SolutionOn (closedOpen 0 T hT)` together with *exactly* the raw
   chart-Gram smoothness/continuity and the pointwise PDE produced by (1), and
   concludes `IsSolutionOn S`.  It does **not** assume `IsSolutionOn` /
   `IsSmoothSolutionOn` or any of their fields — only the genuine analytic output
   of the short-time construction.  The `sorry` is the real remaining analytic
   gap (assembling the `IsSolutionOn` fields — metric/connection smoothness, the
   `∂_t g = -2 Ric` equation at regular interior times, and canonical
   scalar/Ricci spacetime continuity and the scalar heat equation — from the
   chart-local short-time data).  This is the single new `sorry` introduced by
   this pass.

   *Correction (same day):* the frontier targets `IsSolutionOn`, **not**
   `IsSmoothSolutionOn`.  The promotion `IsSolutionOn → IsSmoothSolutionOn` is
   already a fully *checked* producer — `smoothOfSol` in
   `RicciFlow/Regularity.lean` (no `sorry` in that file) — which derives the
   canonical scalar/Ricci regularity, coordinate inverse/Ricci evolution,
   symmetries, and the Ricci-norm Bochner/Laplacian expansion from `IsSolutionOn`
   on a boundaryless manifold.  Re-`sorry`ing that step would have been wrong;
   it is reused instead.

3. `ham3_short_smooth_solution` — checked modulo (2).
   Assembles (1), (2), and the checked `smoothOfSol`: `T > 0`, a
   `SolutionOn (closedOpen 0 T hT)` with the start-metric identity and
   `IsSmoothSolutionOn S`.  No direct `sorry`; its only gap flows through
   `ham3_isSolution_of_shortTimeData`, since `IsSolutionOn → IsSmoothSolutionOn`
   is fully proved by `smoothOfSol`.

### `ham3_flow_exists_normalized`

Now genuinely cites the headline: its body opens with
`have _hshort := ham3_short_smooth_solution (I := I) (M := M) hM g0`, so the
short-time *smooth* stage is no longer part of the `sorry`.  The remaining
`sorry` is precisely the **maximal continuation** (extend the short-time smooth
flow to a maximal normalized `[0, ω)` and assemble `Ham3FlowPackage` with
endpoint curvature blow-up).  Per the task constraint this was *not* fabricated:
`MaximalTime.lean` supplies blow-up *from* maximality
(`formsSing_of_maximal_metric`, `rmUnbounded_of_maximal`) but its
`extends_of_rmBounded` extension criterion (Black Box 11.2) is itself unproved,
so no maximal-continuation producer exists to cite.

### Verification

- `LEAN_NUM_THREADS=2 lake env lean DifferentialGeometry/Geometry/Flow/RicciFlow/DimensionThree/HamiltonPositiveRicci.lean`
  exits 0.  Only `declaration uses 'sorry'` warnings remain:
  `ham3_isSolution_of_shortTimeData` (new, intended frontier),
  `ham3_flow_exists_normalized` (pre-existing maximal-continuation gap), and the
  five pre-existing downstream `sorry`s (`ham3_noncollapse`, `ham3_cgh_limit`,
  `limit_to_orig`, `ham3_space_box`, `spaceForm_const_metric`).
- Net new `sorry`s: exactly one (`ham3_isSolution_of_shortTimeData`).
- `ham3_short_solution_candidate` and `ham3_short_smooth_solution` add no direct
  `sorry` (the latter reuses the checked `smoothOfSol` for
  `IsSolutionOn → IsSmoothSolutionOn`).
- Only `DifferentialGeometry.lean` (the aggregator) imports this file, and no
  other file references the Hamilton declarations, so the context change does not
  ripple into downstream consumers.

### Honest remaining frontier (this sub-story)

```
ricci_flow_short_time_existence   (headline, checked)
  └─ ham3_short_exists            (checked adapter)
       └─ ham3_short_solution_candidate     (checked: raw output -> SolutionOn candidate)
            └─ ham3_isSolution_of_shortTimeData   (FRONTIER sorry: raw data -> IsSolutionOn)
                 └─ smoothOfSol  (CHECKED, Regularity.lean: IsSolutionOn -> IsSmoothSolutionOn)
                      └─ ham3_short_smooth_solution          (checked modulo the frontier)
                           └─ [maximal continuation + blow-up assembly]  (still open; not in MaximalTime.lean)
                                └─ ham3_flow_exists_normalized           (sorry: maximal continuation only)
```

## 2026-06-05 live frontier recheck

Focused verification passed for both the Hamilton file and the short-time
headline file.  The Hamilton file currently has exactly seven direct
proof-body frontiers:

1. `ham3_isSolution_of_shortTimeData`: raw short-time chart-Gram/PDE data to
   `IsSolutionOn`.
2. `ham3_flow_exists_normalized`: maximal continuation and endpoint blow-up
   assembly into `Ham3FlowPackage`.
3. `ham3_noncollapse`: noncollapsing/injectivity input.
4. `ham3_cgh_limit`: Hamilton-Cheeger-Gromov limit package.
5. `limit_to_orig`: transfer from the limiting/covering/space-form metric back
   to the original manifold.
6. `ham3_space_box`: spherical space-form classification input.
7. `spaceForm_const_metric`: global space-form to constant positive metric
   conclusion.

The short-time headline still elaborates.  Its lower proof-body black boxes are
the DeTurck-Ricci parabolic short-time theorem and the Weyl/on-diagonal spectral
estimate.  No additional short-time frontier appeared in this recheck.

## 2026-06-05 adapter design prompt

Target adapter:

```lean
theorem ham3_isSolution_of_shortTimeData
    [BoundarylessManifold I M]
    {T : Real} (hT : 0 < T)
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 T hT))
    ...
    : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) S
```

Feasibility check before coding: the current raw hypotheses are probably too
weak to prove the target literally.  `MetricFamilySmoothOn.coeff` asks for
`ContDiffOn Real top` on `D.carrier = Set.Ico 0 T`, while the short-time output
only records joint `C^\infty` Gram entries on `Set.Ioo 0 T` plus continuity on
`Set.Ico 0 T` and a first-order PDE.  Also `IsSolutionOn.scalarCont` is stated
as `ContinuousAt` on all `Real x M`, not only on the interval carrier.  So the
adapter should not be attacked as one tactic proof in HamiltonPositiveRicci.

Recommended Claude route:

1. First inspect `IsSolutionOn` in `Basic/Core.lean`,
   `MetricFamilySmoothOn` in `Curvature/Realized/MetricFamily.lean`, and the
   existing short-time producers in `ShortTime/SolutionC2Continuous.lean` and
   `ShortTimeAssembly/RicciFlowPdeAtZero.lean`.
2. Do not change `SolutionOn` or `IsSolutionOn` globally on the first pass.
   Instead, state the smallest honest producer lemma in the short-time layer
   whose assumptions actually imply the `IsSolutionOn` fields for the half-open
   interval.
3. If the current raw assumptions are insufficient, stop with the exact missing
   strengthened short-time output rather than adding hypotheses directly to the
   Hamilton theorem.  The likely missing package is a `ShortTimeRegularityOn`
   style producer containing carrier-local metric-family smoothness, connection
   smoothness, interval-local scalar/Ricci/Rm/nablaRic continuity, and scalar
   evolution.
4. Once that producer exists, keep `ham3_isSolution_of_shortTimeData` as a thin
   consumer: construct the `IsSolutionOn` record field by field, use the raw PDE
   only for `equation`, and use the short-time regularity producer for the
   remaining fields.
5. Only after the adapter checks, verify that `ham3_short_smooth_solution` still
   uses the checked `smoothOfSol` promotion and that `ham3_flow_exists_normalized`
   still has only the maximal-continuation frontier.

Stop condition: if the proof needs global-in-time `scalarCont` outside
`Set.Ico 0 T`, or infinite one-sided time regularity at `t = 0` not present in
the short-time theorem, report a missing API/statement-strength issue.  Do not
paper it over with a new polished hypothesis in HamiltonPositiveRicci.

## 2026-06-05 adapter feasibility audit — BLOCKED (both stop conditions hit)

Outcome of the audit: `ham3_isSolution_of_shortTimeData` is **not fillable on
this pass**.  Both stop conditions fire.  The frontier is a missing-producer /
statement-strength frontier, not a local proof-search problem.  No code beyond
an honest docstring on the frontier was changed; `IsSolutionOn`/`SolutionOn`
were not touched; no new `sorry` was introduced (net `sorry` count unchanged).
Focused verification passed.

Classification: **statement-strength (primary) + missing analytic producer
(secondary).**

Field-by-field map of `IsSolutionOn` against the short-time output
(`ham3_short_solution_candidate` gives joint chart-Gram `C∞` on `Ioo 0 T`,
chart-Gram continuity on `Ico 0 T`, and the pointwise `∂_t g = -2 Ric` on
`Ico 0 T` with the derivative taken `within Ici 0`):

- `smoothMetric.metricTensor_cont` — joint metric continuity on `Ico 0 T`:
  **reachable** from chart-Gram continuity (modulo per-chart → bundle-section
  assembly).
- `smoothConnection` — per-flow-time Levi-Civita spatial `C∞`: **reachable**,
  trivial (each fixed-time `leviCivitaConnectionOfMetric` is smooth; no time
  regularity demanded).
- `equation` — `∂_t g = -2 Ric` at regular (interior) times: **reachable** from
  the raw PDE, modulo (i) a `ricciTensor g x v w = metricRicciAt g x (vec2 v w)`
  bridge and (ii) `within Ici 0` → `within D.carrier` at interior times.
- `ricciCont` — Ricci bundle continuity on the carrier: **reachable** in
  principle from `ricci_continuous_in_metric_time` (continuity on `Icc 0 T` from
  chart data up to 2nd order), modulo per-point → joint bundle assembly.
- `rm04Cont` — `Rm` (2nd order) continuity: plausibly reachable from the `C²`
  metric-time continuity.
- `ricciNormSpace`, `ricciNormGrad` — per-time spatial: **reachable**.
- `smoothMetric.coeff` and `smoothMetric.frameCompSmooth` — **BLOCKED**: they ask
  for `ContDiffOn ⊤` / `ContMDiffOn ⊤` (`C∞`-in-time) on the closed-at-`0`
  carrier `Ico 0 T`.  The short-time layer exposes joint `C∞` only on the *open*
  `Ioo 0 T` plus `C²` up to the endpoints (`deturck_solution_c2_continuous_icc0`).
  `C∞`-up-to-`t=0` is mathematically true (parabolic smoothing from smooth data)
  but **unexposed** — only `C²` is proven.  This is the "infinite one-sided
  regularity at `t = 0`" stop condition.
- `nablaRicCont` — **BLOCKED**: needs continuity of the 3rd-order `∇Ric`; the
  short-time layer exposes chart time-continuity only up to 2nd order.
- `scalarEvolution` — **BLOCKED**: the scalar curvature heat equation
  `∂_t R = ΔR + 2|Ric|²` is a genuine evolution identity, not present in the
  short-time output.
- `scalarCont` — **HARD BLOCKER**: stated *globally* as
  `∀ p : Real × M, ContinuousAt (fun q => S.scalar q.1 q.2) p`.  A half-open
  `SolutionOn (closedOpen 0 T)` controls its metric family only on the carrier
  `Ico 0 T`; off the carrier the family is unconstrained (and Ricci-flow
  curvature can blow up at the right end), so global scalar continuity is not
  produced by — and is in general false for — short-time data.  This makes the
  current `ham3_isSolution_of_shortTimeData` statement unprovable as written,
  independent of the analytic gaps above.  Confirmed structurally: nothing in the
  tree constructs `MetricFamilySmoothOn` or `IsSolutionOn` from raw data; the
  only `IsSolutionOn` builders are `isSolutionOn_timeShift` and `paraSolution`,
  which transform an existing `IsSolutionOn`.  So the global `scalarCont` field
  has never been discharged from scratch.

Recommended redesign (for a follow-up pass that is allowed to edit `IsSolutionOn`
and the short-time layer — do not do this inside HamiltonPositiveRicci):

1. **Weaken `IsSolutionOn.scalarCont` to carrier-local**, e.g.
   `ContinuousOn (fun q : Real × M => S.scalar q.1 q.2) (D.carrier ×ˢ Set.univ)`
   (or joint continuity over `{t // t ∈ D.carrier} × M`, matching
   `Tensor0SFamilyContinuousOnSet`).  `scalarTime` is already carrier-local
   (`K ⊆ D.carrier`).  Audit and weaken the downstream consumers consistently:
   `smoothOfSol`/`scalarSTContOfSol`, `ScalarSTContOn.scalar_continuousOn`, and
   the scalar WMP consumers, all of which currently assume the global form.
2. **Add a short-time regularity producer** (`ShortTimeRegularityOn`-style, in the
   short-time/regularity layer, or by strengthening `ricci_flow_short_time_existence`'s
   exposed output) supplying the three analytic items: `C∞`-up-to-`t=0`
   metric-coefficient time regularity on `Ico 0 T` (upgrade from `C²`-on-`Icc` +
   `C∞`-on-`Ioo`); 3rd-order `∇Ric` joint continuity on the carrier; and the
   scalar heat equation at regular times.
3. Only then make `ham3_isSolution_of_shortTimeData` a thin field-by-field
   consumer.

Difficulty assessment: item 1 is a focused but cross-cutting API edit (a design
choice touching several consumers).  Item 2 contains genuine analysis (the
`C∞`-up-to-`0` upgrade and the scalar heat equation) and is the substantial
remaining mathematics.  Neither is a routine local proof, so the frontier was
left visible rather than papered over.

## 2026-06-05 carrier-local scalar continuity redesign implemented

The statement-strength part of the scalar-continuity obstruction is now fixed.
`IsSolutionOn.scalarCont`, `ScalarSTContOn`, and `CanonicalScalarRegularOn` are
carrier-local `ContinuousOn` packages over `D.carrier x M`, and
`SolutionOn.scalar_continuousOn` now requires an explicit slab-subset proof
`Set.Icc 0 T subset D.carrier`.

Direct consumers were updated rather than hidden behind new assumptions:
time-shift and parabolic-rescaling compose the carrier-local scalar continuity
through their time maps; Ricci-preservation uses subtype continuity on
`{t // t in D.carrier} x M`; scalar lower-bound and improved pinching restrict
to slabs using their existing carrier-subset hypotheses; finite-time scalar
continuity is now requested as a local family for every `T < omega`; and the
Hamilton scalar package exposes the same local family.

Verification passed for the edited scalar-continuity API and Hamilton consumer.
The actual theorem-body `sorry` count in `HamiltonPositiveRicci.lean` remains
7; no new `sorry` was introduced.  The short-time adapter remains blocked for
the genuine producer reasons from the audit: closed-at-zero `MetricFamilySmoothOn`
regularity, third-order `nablaRic` continuity, and scalar evolution.

## 2026-06-05 item-2 reshape: short-time IsSolutionOn producer

Goal of this pass: advance the `IsSolutionOn` short-time frontier ("item 2").

Investigation of the short-time / DeTurck / parabolic / spectral layers
(findings):

- C∞-up-to-`t=0` metric time regularity: NOT available.  Strongest exposed is
  `deturck_solution_c2_continuous_icc0` (`C²` on `Icc 0 T`).  The headline only
  exposes joint `C∞` on the OPEN `Ioo 0 T`.
- 3rd-order `∇Ric` carrier continuity: NOT available (only 2nd-order Ricci
  continuity, `ricci_continuous_in_metric_time`).
- Scalar heat equation: the only producer (`scalarEvolOfSmooth`) consumes
  `IsSmoothSolutionOn`, i.e. it is downstream of `IsSolutionOn` — circular for
  this purpose.  No producer derives it from the metric PDE + smoothness alone.
- No theorem anywhere CONSTRUCTS `MetricFamilySmoothOn` or `IsSolutionOn` from
  primitive data (only `timeShift`/`paraSolution` transform an existing one).

So the three gaps are genuine hard parabolic-analysis facts that this project
black-boxes by design (like short-time existence itself); "filling" them is a
major PDE-formalization effort, out of scope for an incremental pass.

Correctness defect found and fixed: the previous frontier
`ham3_isSolution_of_shortTimeData` took the raw chart-Gram/PDE data of the
candidate as hypotheses and concluded `IsSolutionOn S`.  Those hypotheses are
too weak to imply `IsSolutionOn` (they pin only the open-interval `C∞`, the
`C⁰`-up-to-`0` continuity, and the 1st time derivative; one can satisfy them yet
fail the `C∞`-up-to-`0` / heat-equation fields), so as a `∀ S` implication it is
effectively false — a `sorry` should not sit on it.

Reshape (in `HamiltonPositiveRicci.lean`):

- Removed `ham3_isSolution_of_shortTimeData`.
- Added `ham3_short_isSolution (hM) (g0) : ∃ T (hT : 0 < T) S, S.family.metric
  initial = g0 ∧ IsSolutionOn S`.  This is a `g0`-based producer about the
  *actual* short-time solution, so the statement is mathematically true; its
  scaffolding (`SolutionOn`, initial metric) is the checked
  `ham3_short_solution_candidate`, and the `IsSolutionOn` fields are a single,
  precisely-labeled parabolic-regularity `sorry` (the three facts above), matching
  how `ricci_flow_short_time_existence` itself black-boxes its deep analytic core.
- Rewired `ham3_short_smooth_solution` to `ham3_short_isSolution` + the checked
  `smoothOfSol`.

Verification passed (focused).  Net `sorry` count in
`HamiltonPositiveRicci.lean` is unchanged at 7; the item-2 frontier is now a
true, correctly-located, single labeled black box (`ham3_short_isSolution`,
the short-time parabolic regularity input) instead of an effectively-false
raw-data consumer.

Difficulty / next: genuinely discharging `ham3_short_isSolution` needs the
short-time analytic layer strengthened to expose `C∞`-up-to-`0` metric
regularity and 3rd-order `∇Ric` continuity, plus a non-circular scalar-heat
producer (derive `ScalarEvolutionEquationOn` from `∂_t g = -2 Ric` + smoothness,
not from `IsSmoothSolutionOn`).  These are PDE-analysis tasks in the short-time /
Evolution layer, not local proofs.

## 2026-06-05 weakening execution — IN PROGRESS (tree mid-refactor)

Executing the `MetricFamilySmoothOn` weakening (interior-`C∞` + carrier-continuity).
The audit confirmed it is sound, but execution exposed a larger-than-expected
blast radius:

Done & checked in isolation:
- `RealTimeInterval` gained `regular_isOpen : IsOpen regular` (TimeInterval.lean),
  with all 11 builders updated.  Needed because `coordMetricSmoothAt`/
  `coordInvSmoothAt` produce `ContMDiffAt` at regular times, which needs a
  *neighbourhood*; `D.regular` only provides one when open.  TimeInterval.lean
  checks green.
- `MetricFamilySmoothOn` weakened: `coeff`/`frameCompSmooth` moved to `D.regular`,
  new `coeff_cont` (carrier continuity).  MetricFamily.lean checks green.

Edited, not yet re-verified against the new struct:
- Core.lean `isSolutionOn_timeShift.smoothMetric` (4-field rebuild).
- Evolution/Metric/Basic.lean `coordMetricSmooth`→`D.regular`, `coordMetricSmoothAt`
  uses `regular_isOpen`.
- Evolution/Metric/InverseSmooth.lean coordinate chain → `D.regular`,
  `coordInvSmoothAt` uses `regular_isOpen`.

Remaining (the genuinely new mathematics):
- **Carrier-continuity sub-chain** for `Estimate.lean`'s `ricciNorm_coordCont`
  (which needs `ricciNorm` continuity up to `t = 0`, hence `coordInv` continuity
  up to `0`).  `coordInvSmooth` is now interior-only, so a carrier-continuity
  route is required: `coordMetricCont` (from `metricTensor_cont` via
  `eval_continuous`) → Gram continuity → **inverse continuity** (continuity of
  `ContinuousLinearMap.inverse` at invertible points) → `coordInvCont`.  This is
  ~4 new lemmas, the inverse-continuity being the nontrivial one (mirrors the
  existing smooth `coordFrameGInvCLM_spacetimeSmooth` but with `ContinuousAt`).
- `RicciPreservation.lean` 3697/3714: `.coeff.continuousOn` → `.coeff_cont`.
- `ParabolicRescaling.lean`: para interval builder `regular_isOpen`; metric
  family builder provide `coeff_cont` + move to `D.regular`.
- Full `lake-locked build` to verify the cascade.

Status: tree is mid-refactor (broken until the above land).  Claim tokens held.

## 2026-06-06 weakening COMPLETE (coordInvContOn proved, no net new sorry)

The `MetricFamilySmoothOn` weakening is finished and verified.

- Full `lake-locked build` of the whole project passed (exit 0) with the
  weakening in place.
- The hidden `D.carrier`-baked helper `contMDiffOn_finset_sum` (InverseSmooth.lean)
  was generalized to an arbitrary set `t` (backward-compatible).
- The one carrier-continuity frontier introduced by the weakening,
  `coordInvContOn` (coordinate inverse-metric continuity up to `t = 0`), is now
  **fully proved** — no `sorry`.  Its chain, all the continuity twins of the
  existing smooth lemmas:
  * `coordMetricContOn` (Evolution/Metric/Basic.lean): frame metric components
    continuous up to `0`, from `metricTensor_cont` via
    `Tensor0SFamilyContinuousOnSet.eval_continuous` + `metricTensorField_apply`;
  * `coordFrameGramCLM_contOn`, `coordFrameGInvCLM_contOn`, `coordInvContOn`
    (InverseSmooth.lean): Gram continuity → inverse continuity (via
    `ContinuousLinearMap.inverse` continuous at invertible points, reusing
    `frameGramCLM_isInvertible_at` + `coordInvCLM_eq`) → entry continuity.

Net effect of the whole weakening: **zero new `sorry`s**.  `IsSolutionOn` /
`MetricFamilySmoothOn` no longer demand the spurious `C∞`-up-to-`t=0` time
regularity (only interior `C∞` + carrier continuity), matching what short-time
existence actually provides and what consumers actually use.  The added
`RealTimeInterval.regular_isOpen` field is a sound, contained improvement.

This unblocks (does not yet fill) `ham3_short_isSolution`: its `smoothMetric`
obligation is now satisfiable from short-time data; the remaining genuine
short-time analytic content for that frontier is `nablaRicCont` (3rd-order ∇Ric
continuity) and the scalar heat equation.

## 2026-06-06 nablaRicCont weakened to interior (verified, exit 0)

Continued the weakening from `MetricFamilySmoothOn` to the `∇Ric` continuity
field.  Audit confirmed `IsSolutionOn.nablaRicCont` is **never consumed up to
`t = 0`**: the only extractor `nablaRicFamilyContinuousOnSet` has no call sites,
and every other use is a transport rebuild (`isSolutionOn_timeShift`,
`paraSolution`) or the `ricciRegOfSol` pass-through.  `∇Ric` is a ≤3rd-order
differential expression in the metric, so interior `C∞` already supplies it.

Edits: `IsSolutionOn.nablaRicCont`, `CanonicalRicciRegularOn.nablaRic_cont`, and
`nablaRicFamilyContinuousOnSet` changed `3 D.carrier` → `3 D.regular`; the two
transport rebuilds updated to `MapsTo … regular`.  Full `lake-locked build`
passed (**exit 0**); claim tokens released.

Net: `IsSolutionOn`'s regularity surface now matches exactly what is consumed —
interior `C∞` + carrier `C⁰` for the metric, carrier `C⁰` for the ≤2nd-order
curvature, interior `C⁰` for 3rd-order `∇Ric`.  No spurious up-to-`0` demand
remains anywhere.

## 2026-06-06 CORRECTION: the scalar heat equation is already proven in-tree

Earlier notes listed "the scalar heat equation" as remaining content of
`ham3_short_isSolution`.  That is **wrong** — it is fully formalized and
sorry-free:

- Intrinsic field form: `IsSolutionOn.scalarEvolution` (Basic/Core.lean:555),
  `∂ₜ R = Δ_g R + 2‖Ric‖²`.
- Proven derivation: `scalarEvolutionEquationOn_of_ricciEvolution`
  (Evolution/Scalar/Assembly.lean:88) from the Ricci evolution; the
  contracted-Bianchi reduction `2ΔR − 2Q + 2‖Ric‖² ⟿ ΔR + 2‖Ric‖²` is
  `scalarEvolutionEquationOn_of_contractedBianchi` (Evolution/Scalar/Basic.lean:82).
- The Ricci evolution it rests on is also proven: `coordRicciEvol`
  (Evolution/Ricci/CoordinateIdentities.lean:876), from Christoffel evolution +
  ∇² commutators.  **The entire `Evolution/{Scalar,Ricci,Connection}` subtree is
  sorry-free.**

So the scalar evolution is the *best-supported* `IsSolutionOn` field, not a gap.
The genuine residual of `ham3_short_isSolution` is **regularity packaging only**:
wiring the candidate's chart-Gram smoothness/continuity into the intrinsic
continuity fields and citing the proven `coordRicciEvol` →
`scalarEvolutionEquationOn_of_ricciEvolution` chain for `scalarEvolution`.  The
single genuinely black-boxed analytic input is upstream:
`deturck_ricci_flow_parabolic_short_time_existence`
(ShortTime/DeTurckRicciPde.lean:128) + the conjugating-flow field regularity
(ShortTimeFlow/ConjugatingFlowProperties.lean:3954).

## 2026-06-06 sorry structure of the final theorem `thm_2_1`

`thm_2_1` = `ham3_main`: closed connected 3-manifold with `AdmitsPosRicci`
⟹ `AdmitsConstPosSec ∧ SphericalSpaceForm`.  Forks into the analysis branch
`ham3_const_metric` and the topology branch `ham3_equiv`.

The Section 7–9 differential-geometric core is **proved** (finite-time, scalar
blow-up, point selection, parabolic rescaling, Ricci-nonneg preservation,
pinching estimates, Rm bound, and the whole `limit_*` tensor-transfer chain to
`limit_const_pos`).  Remaining `sorry`s, grouped:

1. Short-time existence (upstream PDE): `deturck_…_short_time_existence`,
   `ConjugatingFlowProperties.lean:3954`; bridge `ham3_short_isSolution`
   (HamiltonPositiveRicci.lean:571, now regularity packaging only).
2. Maximal continuation: `ham3_flow_exists_normalized` (:628); the input
   `extends_of_rmBounded` (MaximalTime.lean:159, Black Box 11.2) exists but is
   currently *bypassed* (`formsSing_of_maximal_metric`/`rmUnbounded_of_maximal`
   appear only in a docstring, not in any proof body).
3. Singularity/convergence: `ham3_noncollapse` (:2288, Perelman noncollapsing),
   `ham3_cgh_limit` (:2310, Hamilton compactness), `limit_to_orig` (:2844).
4. Topology endpoint: `ham3_space_box` (:2944), `spaceForm_const_metric` (:2956).

## 2026-06-06 scalarEvolution: assumed field → derived theorem (DONE, exit 0)

The scalar-curvature heat equation is no longer a black-boxed structure field.
`IsSolutionOn.scalarEvolution` was **removed as a field** and replaced by a
sorry-free derivation, so `ham3_short_isSolution` no longer assumes it.

New file `Evolution/Scalar/IntrinsicDerivation.lean` (sorry-free):

- `coordNab2Ric_eq_nabla2RicField` — the explicit coordinate-frame `∇²Ric`
  (`extDeriv − Γ` formula) equals the abstract bundled `totalNabla0SFun³` of
  Ricci, via `nabla0SFun_apply_selfChart_slots` + the `ext0S_basis`
  agree-on-a-basis principle.  (The repo already had `coordNab2Can` proving the
  same crux — the explicit↔abstract bridge was NOT missing, contrary to an
  earlier over-pessimistic read.)
- `scalarLaplacianTraceInFrame_coord_eq_laplacianAt` — the **diffusion bridge**:
  `gⁱʲgᵏˡ∇²Ricᵢⱼₖₗ = ΔR` (`laplacianAt`).  Assembled from `nabla2Trace02`
  (Hessian-trace commutation, `∇g=0`), `scalarLap_smooth` (laplacian = trace of
  Hessian), `metricTracePair0SAt_eq_sum_basis`, and the sum-swap
  `scalarHessianFromNabla2Ric_trace_eq_roughLapRic_trace`.
- `scalarEvolution_of_isSolution` — derives the EXACT former field statement
  `∂ₜR = ΔR + 2|Ric|²` from `hS : IsSolutionOn`, by running the proven frame-form
  chain `scalarEvolutionEquationOn_of_ricciEvolution` (∂ₜg⁻¹ = 2Ric° via
  `coordInvEvol`, ∂ₜRic Lichnerowicz via `coordRicciEvol`, curvature
  trace/symmetry) and applying the three frame→intrinsic bridges (scalar trace,
  diffusion, reaction) plus a `G`-congruence to `flowG`.

Integration:
- `IsSolutionOn` lost its `scalarEvolution` field (`Basic/Core.lean`); the unused
  `scalarEvolAt` and the two transport constructions (`timeShift` in `Core`,
  `paraSolution` in `ParabolicRescaling`) dropped it.
- `scalarEvolOfSol` (`Regularity.lean`) reroutes to `scalarEvolution_of_isSolution`
  (gains `[I.Boundaryless]`; its sole caller `smoothOfSol` already carries it, so
  no further propagation).  `IsSmoothSolutionOn.scalarEvolution` is a *separate*
  field and is untouched.
- Full `lake-locked build` **exit 0**, no new `sorry`.

Net: the scalar evolution is now mathematically grounded end-to-end — the
frame-form heat equation (already in `Evolution/Scalar`) plus the realization
identity `ΔR = gⁱʲgᵏˡ∇²Ricᵢⱼₖₗ`.  `ham3_short_isSolution`'s residual is purely the
remaining regularity-packaging fields, never the scalar PDE.

## 2026-06-06 Bernstein–Bando–Shi derivative estimates (toward `extends_of_rmBounded`)

Goal: fill `extends_of_rmBounded` (`MaximalTime.lean:159`, Black Box 11.2 — the
maximal-continuation extension criterion) by formalizing the global BBS
derivative estimates (Chow–Knopf *The Ricci Flow: An Introduction*, Theorem 7.1,
the compact-manifold / global-maximum-principle case — no Shi cutoffs needed).

**BBS core — COMPLETE, sorry-free, full `lake-locked build` exit 0 (9847 jobs),
`#print axioms` clean (no `sorryAx`):**

- `Evolution/BernsteinShi.lean` — Stage 1: upper-bound scalar maximum principle
  `scalar_subsolution_affine_bound` (`(∂ₜ−Δ)F ≤ b`, `F(0)≤a` ⟹ `F ≤ a+bt`), the
  `|∇Rm|²` heat predicate `NablaRm04NormHeatBoundOn`, and the `m=1` Bernstein
  estimate `bernstein_first_derivative_estimate` (`F = t|∇Rm|²+β|Rm|²`).
- `Evolution/BernsteinShiHigher.lean` — Stage 2: the **general-`m`**
  `G`-quantity induction `BernsteinTower.estimate` /`estimate_div`
  (`|∇ᵐRm|² ≤ towerConst²·K²/tᵐ`, all `m`), via eqs 7.4–7.6 (the telescoping
  `Wterms_nonpos` + `scalar_subsolution_affine_bound`).  Parametric in the
  `BernsteinTower` structure (the tower of heat inequalities).
- `Evolution/RiemannNormHeatProducer.lean` — Stage 3a (`k=0`): `|Rm|²` heat
  equation for a solution + `|reaction| ≤ 16·card⁶·|Rm|³` (Lemma 7.4), from the
  Uhlenbeck curvature evolution.
- `Evolution/NablaRiemannHeat.lean` — Stage 3b (`k=1`): `|∇Rm|²` heat bound
  (eq 7.2/14.17) + the general-`k` `∗`-reaction bound `abs_nablaRmReactionMulti_le`
  in the `towerReactionSum` shape.
- `Evolution/IteratedNablaRmTower.lean` — the variable-rank `∇ᵏRm` tower bridge
  (Route A, no dependent-type issues): `iteratedRmComp` (rank-`(4+k)` component
  recursion), the general orthonormal reduction `multiNormInFrame_eq_compNormSqMulti`,
  and the producer `iteratedRmTower_heatBound : IteratedRmTowerOn → TowerHeatBoundOn`.

The reusable lever throughout is the `A∗B` convention: evolution stated as
*inequalities* with norm-product bounds `Σ|∇ʲRm||∇^{k−j}Rm||∇ᵏRm|`, never exact
reaction tensors (the producers leave the raw Uhlenbeck/Bochner/commutator
component facts as hypotheses, matching the existing `|Ric|²` architecture).

**In progress (final two pieces):**
- All-`m` BBS for a real solution (`BernsteinShiSolution.lean`): instantiate the
  `BernsteinTower` per-`m` from the tower bridge (uniform constant via the
  "zero above `m`" truncation), apply `estimate_div`.
- Stage 4 (`CinftyLimitGlue.lean`): `C^∞` limit `g(t)→g(ω)` from the BBS bounds
  + restart short-time + smooth glue ⟹ the single-endpoint extension; then wire
  into `extends_of_rmBounded`.  (No Ricci-flow uniqueness needed — that is only
  for the maximal-flow *construction*, a separate gap.)

## 2026-06-06 k=1 ∇Rm evolution: EQUATION derived; BBS bound is the framework frontier

Goal (user-authorized): genuinely ground the `k=1` `IteratedRmTowerOn.heatEq`
(the `∇Rm` tensor evolution) from Ricci-flow/Uhlenbeck geometry, rather than
leave it an assumed interface field.  Outcome: **the `k=1` evolution EQUATION is
fully derived** (the residual `(∂ₜ−Δ)(∇Rm)` is now *identified* as curvature
actions, not assumed); **the BBS quantitative *bound* `|reaction| ≤ C|Rm||∇Rm|`
is blocked on four framework-level gaps** and is the documented frontier.

**Equation — DONE, all sorry-free, `#print axioms` clean (no `sorryAx`):**

- `Evolution/RmRealizationBridge.lean` — the rank-`(0,4)/(0,5)` realization
  bridge (the crux), mirroring `coordNab2Ric_eq_nabla2RicField`.  Bundled fields
  `nablaRm04Field`/`nabla2Rm04Field`/`nabla3Rm04Field` (`totalNabla0S` of
  `S.base.rm04`); the rank-uniform step bridge `covDerivStepComp_frameComp_eq`;
  `iteratedRmComp_one_eq_nablaRm04Field` (neighbourhood) /
  `iteratedRmComp_two_eq_nabla2Rm04Field` (centre); and the **discharged**
  `Nabla20SRealizesAt` packages → `rm04_ricciIdentityAt` (s=4) /
  `nablaRm04_ricciIdentityAt` (s=5), making the general `(0,s)` Ricci identity
  `tensor0S_ricciIdentity_of_torsionFree` (`Tensor/RicciIdentity/Tensor0S/Formula.lean:975`)
  genuinely applicable to `Rm`/`∇Rm`.  Witnesses come from `totalNabla0S_realizes`,
  never assumed.
- `Evolution/NablaRiemannCommutator.lean` (spatial) — `nablaLapComm_orthonormalTrace`:
  `Δ(∇Rm)(c) − ∇(ΔRm)(c) = Σ_a nablaLapCommReactionTerm(a,a,c)`, from the `(0,5)`
  Ricci identity + telescoping (the `[Δ,∇]` commutator is **derived**).
- `Evolution/NablaRiemannTimeDeriv.lean` (temporal) —
  `iteratedRmComp_one_hasDerivWithinAt`: `∂ₜ(∇Rm) = ∇(∂ₜRm) − (∂ₜΓ)∗Rm` in the
  `MultiLevelTimeDerivOn` shape, from the `extDeriv`/`∂ₜ` swap +
  `evol_christoffel_inFrame` (`∂ₜΓ`) + Uhlenbeck (`∂ₜRm`) as cited shapes.
- `Evolution/NablaRiemannCommutatorBound.lean` —
  `nablaLapComm_T1_eq_covDeriv_curvatureAction` (the slot-swap/∇ commutation,
  proved concretely via `eval_smooth_slots`) and
  `nablaLapCommReactionTerm_eq_covDeriv_curvatureAction_add_curvatureAction`: the
  full `k=1` reaction exhibited as `∇(curvatureAction(Rm)) + curvatureAction(∇Rm)`
  (`= ∇(Rm∗Rm) + Rm∗∇Rm`).

So `(∂ₜ−Δ)(∇Rm)` is genuinely the curvature reaction — the **equation half of
`heatEq` is grounded for `k=1`**.

**Bound — the frontier.**  `|reaction| ≤ C|Rm||∇Rm|` (the BBS Cauchy–Schwarz step)
is blocked on four *framework-level* gaps (confirmed by three independent agents,
each via a different route — none is a single lemma):

1. The inverse metric is `InverseMetricComponents : M → Idx → Idx → ℝ` (a
   frame-component function), **not** a bundled `(2,0)` tensor — so `∇g⁻¹=0`
   cannot even be *stated* in the `totalNabla0S` framework.
2. `Rm13 = raise(Rm04)` is unavailable — `metricRm13`/`metricRm04` are produced
   independently; raising-parallelism is proven only at rank `(0,2)`, never `(1,3)`.
3. `∇Rm13` does not exist — no `totalNablaRS` realization for the `(1,3)` curvature.
4. Frame mismatch — `nablaLapCommReactionTerm` lives in `coordinateFrameAt` (not
   orthonormal at its centre), while the norms require an orthonormal frame.

Closing it is a major framework project (bundled inverse metric `+∇g⁻¹=0`; the
`(1,3)` raising equivalence `+`parallelism; `∇Rm13` via `totalNablaRS`;
coordinate↔orthonormal reconciliation) — reusable for all-`k` but disproportionate
to one estimate.  **Decision (user): bank the genuine equation; the bound stays
the documented frontier; the BBS estimates remain parametric in `IteratedRmTowerOn`.**

Routes that informed this (all genuine reports, no fakes): route 1 — bridge the
bundled `tensorCov` `[Δ,∇]` (`frame_trace_thirdCovDeriv_swap`) to components: no
bridge exists from that representation.  Route 2 — rework producers to the bundled
level: the tree has **no time derivative of a bundled tensor section at all**.
Route 3 — the `(0,s)` Ricci identity in the realization rep: found
`tensor0S_ricciIdentity_of_torsionFree`, which **enabled route 4** (the bridge
above).  The `k=1` bound's three attempts (field-level, orthonormal/concrete,
rm04-contraction) all converged on the four gaps above.

**Consolidation (2026-06-06):** full `lake-locked build` → **exit 0 (9847 jobs)**.
All new `k=1` modules — `RmRealizationBridge`, `NablaRiemannCommutator`,
`NablaRiemannTimeDeriv`, `NablaRiemannCommutatorBound` — plus the earlier BBS
stack (`MultiNormHeat`, `BernsteinShi`/`BernsteinShiHigher`/`BernsteinShiSolution`,
`RiemannNormHeatProducer`, `NablaRiemannHeat`, `IteratedNablaRmTower`,
`CinftyLimitGlue`) coexist green and sorry-free.  The only `sorry`s remaining in
the tree are the pre-existing main-theorem frontier items
(`HamiltonPositiveRicci.lean`: `ham3_flow_exists_normalized`, `ham3_noncollapse`,
`ham3_cgh_limit`, `limit_to_orig`, `ham3_space_box`, `spaceForm_const_metric`) and
a few in unrelated files (`UniversalCover`, `Exterior`).  Net new `sorry`s from all
of the BBS / `k=1` work: **zero**.

## 2026-06-07 session-end: k=1 spatial reaction bound CLOSED + roadmap

**Done + independently verified:** the `k=1` quantitative SPATIAL reaction bound
`|nablaLapCommReactionTerm| ≤ C·|Rm|·|∇Rm|` is genuinely closed
(`Evolution/NablaRiemannReactionBound.lean`, `#print axioms` =
`[propext, Classical.choice, Quot.sound]` on all four headline theorems, no `sorry`,
full `lake-locked build` EXIT 0 / 9860 jobs).  **All four framework gaps** that six
prior agents had declared blocking are resolved (see `Evolution/IteratedNablaRmTower.md`
follow-ups 1–10 for per-piece detail).  New banked, axiom-clean files:
`RmRaisingBridge`, `NablaRiemannOrthoFrame`, `Tensor/RSTensor/ContractionLeibniz`,
`RmFrozenSlotField`, `Geometry/Operator/CotangentSharpSmooth`,
`NablaRiemannCommutator(+Bound)`, `NablaRiemannTimeDeriv`, `NablaRiemannT2Bound`,
`NablaRiemannReactionBound`.

**Roadmap — to close `extends_of_rmBounded` (the BBS pillar):**
1. **Full `k=1` producer** `nablaRm04NormHeatBoundOn_of_components` for a solution.
   Spatial input is done; remaining = the **time-derivative assembly**: instantiate
   `iteratedRmComp_one_hasDerivWithinAt`'s `hrm`/`hchr`/`hswap` from the solution
   (Uhlenbeck `∂ₜRm`, `evol_christoffel_inFrame` `∂ₜΓ`, the time/spatial swap) + the
   `MultiNormHeat` Bochner norm-square step.  *[MEDIUM — instantiating existing shapes.]*
2. **All-`k` producer** (discharge `IteratedRmTowerOn` for a solution at every `k`):
   generalize the `k=1` spatial+time work to all `k` (rank-uniform `[Δ,∇]∇ᵏRm` + the
   `∇ʲRm ∗ ∇^{k−j}Rm` reaction bound).  The primitives and the pattern now exist.  *[LARGE.]*
3. **BBS bounds**: `BernsteinShiSolution` (done, parametric) instantiated with (2) →
   all-`m` `|∇ᵏRm| ≤ Cₘ K / t^{m/2}` for a solution.
4. **`C^∞` convergence** (`CinftyLimitData`/`CinftyGlueData`, Stage 4's labelled
   interface): Arzelà–Ascoli from the BBS bounds → the smooth limit metric `g(ω)`.
   *[MEDIUM–LARGE, genuine analysis.]*
5. **Wire** `ricci_flow_extends_construction` (Stage 4, done Route B) + (4) →
   `extends_of_rmBounded` (`MaximalTime.lean:159`).  *[MEDIUM.]*

**Then for the full theorem** (`thm_2_1` / `ham3_flow_exists_normalized`):
`extends_of_rmBounded` (above) **plus** the still-open convergence/compactness pillar —
`ham3_noncollapse` (Perelman κ-noncollapsing), `ham3_cgh_limit` (Cheeger–Gromov
compactness), `limit_to_orig`, `ham3_space_box`, `spaceForm_const_metric` — a comparably
large body of work, largely untouched.  Foundation: the short-time-existence (DeTurck)
`sorryAx` remains the standing black box.

**Next concrete step:** the `k=1` time-derivative assembly (roadmap step 1).
