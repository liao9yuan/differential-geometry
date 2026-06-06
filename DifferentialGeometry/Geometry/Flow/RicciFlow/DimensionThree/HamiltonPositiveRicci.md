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
   `smoothOfSol`/`scalarSTContOfSol`, `ScalarSTContOn.scalar_continuousAt`, and
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
