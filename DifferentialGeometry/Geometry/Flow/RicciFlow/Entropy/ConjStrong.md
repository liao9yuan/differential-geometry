# Strong reversed conjugate heat

## Completed

`conjA2MR` and `conjA1MR` put the genuine moving-Laplacian and scalar-potential
operators into the literal `a + 2` / `a + 1` exponent normal forms consumed by
maximal regularity.  They precompose with the canonical spectral inclusion,
which is the identity on coefficients and has norm at most one.

`conj_inputs` shrinks the two producer intervals to one positive interval,
transfers continuity and bounds to the adapted operators, and proves the
combined contraction inequality.  `conj_strong_exists` then applies
`nonaut_strong_exists` at `a = r = s = 0`.  All measurability and norm-bound
proofs are existential outputs, not new consumer assumptions.

Focused verification and the targeted module build both pass.  The source has
no local warning, `sorry`, or `admit`; the targeted build reports only replayed
upstream warnings.

## Exact remaining frontier

The checked result is a spectral strong solution: `timeH1 H^0`, an
`L²_t(H^2)` solution field, and an equality in `timeL2 H^0`.  It does not yet
produce the jointly smooth scalar field required by `IsHeatPotOn`.

The smallest missing public producer is `heatpot_of_maxreg` (17 characters),
best placed in
`Analysis/Spectral/Intrinsic/HeatSemigroup/ScalarNonautRegularity.lean`.
On every strictly shorter interval it should turn the canonical scalar
maximal-regularity solution with smooth initial data and smooth
metric/potential coefficients into an `IsHeatPotOn` field, without adding a
regularity or realization assumption to the Entropy consumer.

This producer must genuinely address four issues:

1. identify the bounded A2/A1 extensions with the weak geometric moving
   Laplacian and multiplier beyond the finite spectral core;
2. prove interior regularity for the second-order non-autonomous A2 term;
3. upgrade all-order spatial/time information to joint spacetime smoothness;
4. upgrade the `timeL2` equation to the pointwise `HasDerivAt` equation.

The existing `solField_into_all_tensorHs_interior` route does not close this:
it yields only `L²_t(H^sigma)` and its coupling hypothesis is first order,
whereas A2 is order two.  `PointwiseDeriv.lean` also needs a continuous time
derivative representative that the current strong theorem does not provide.
The finite-core realization theorems `lapDiffA20_core` and `scalarPotOp_core`
do not by themselves identify the extensions on arbitrary strong-solution
values.

## Consult prompt

The local A2/A1 producers and `ConjStrong.lean` may be ahead of the pushed
branch.  Attach those local files to the consultation; use the GitHub branch
below as the project-wide code reference rather than claiming it contains the
unpublished edits.

```text
I am working in a large Lean 4/mathlib differential-geometry project. Do not write code first. Diagnose the analytic/API obstruction and give only the next smallest producer theorem.

Target theorem:
`heatpot_of_maxreg` (new theorem name must stay <= 20 characters), in a new native file
`DifferentialGeometry/Analysis/Spectral/Intrinsic/HeatSemigroup/ScalarNonautRegularity.lean`.

Desired role/statement normal form:
Given the canonical `a = 0` scalar maximal-regularity strong solution produced by
`Entropy.conj_strong_exists`, smooth initial scalar data, and the already-proved smooth
Ricci-flow metric/scalar-potential coefficients, show on every strictly shorter interval
`[0,tau']`, `0 < tau' < tau`, that there exists a jointly smooth scalar field `v` satisfying
`IsHeatPotOn` for the reversed metric and potential, with the prescribed initial field.
Do not add a classical-regularity or geometric-realization hypothesis to the consumer.

Current checked input:
- `conj_strong_exists`: `u : timeH1 H^0`, a companion `L2_t(H^2)` field, trace equality,
  and the time-L2 equation for the genuine adapted A2/A1 continuous-linear maps.
- `lapDiffA20_core` and `scalarPotOp_core`: geometric realization only on finite spectral core.
- A2 is genuinely second order `H^2 -> H^0`; A1 is `H^1 -> H^0`.

Exact obstruction:
- `IsHeatPotOn` requires joint C-infinity, closed-carrier joint continuity, smooth slices,
  and a pointwise `HasDerivAt` equation.
- `solField_into_all_tensorHs_interior` only gives L2-in-time all-order spatial regularity and
  assumes a first-order coupling `H^(d+1) -> H^d`, so it cannot absorb the genuine second-order A2.
- `maxreg_l2deriv_to_pointwise_hasderivwithinat` requires a continuous derivative representative.
- no theorem currently extends the finite-core geometric realization to arbitrary H2/H1 values in
  the weak/distributional equation used by the fixed point.

What was tried/audited:
1. fixed-semigroup interior smoothing: wrong order for A2 and only L2_t regularity;
2. all-scale time-continuity route: specialized to the DeTurck `(0,2)` first-order coupling and still
   does not give joint spacetime smoothness;
3. pointwise derivative bridge: blocked because the RHS has only an L2 representative;
4. pointwise smooth representative selection at each time: not parameter-continuous and not joint smooth.

GitHub reference to inspect before answering:
- Branch: https://github.com/liao9yuan/differential-geometry/tree/short-time-existence
- Nonautonomous engine: https://github.com/liao9yuan/differential-geometry/blob/short-time-existence/DifferentialGeometry/Analysis/Parabolic/QuasiLinear/TensorMaximalRegularity/Nonautonomous.lean
- Solution space: https://github.com/liao9yuan/differential-geometry/blob/short-time-existence/DifferentialGeometry/Analysis/Parabolic/QuasiLinear/TensorMaximalRegularity/SolutionSpace.lean
- Classical interface: https://github.com/liao9yuan/differential-geometry/blob/short-time-existence/DifferentialGeometry/Analysis/Parabolic/ScalarTimeDependent.lean
- Existing interior smoothing: https://github.com/liao9yuan/differential-geometry/blob/short-time-existence/DifferentialGeometry/Analysis/Spectral/Intrinsic/HeatSemigroup/ParabolicInteriorSmoothing.lean
- Pointwise derivative bridge: https://github.com/liao9yuan/differential-geometry/blob/short-time-existence/DifferentialGeometry/Analysis/Spectral/Intrinsic/PointwiseDeriv.lean
- Local changed files to attach: `ConjStrong.lean`, `ConjPotential.lean`, `MetricLapDiffH0.lean`, `MetricLapDiffMeas.lean`, and `ScalarPotential.lean`.

Constraints:
- Work in `DifferentialGeometry/`; do not import or edit RFreference.
- No `HasLocallyConstantChartAt`.
- No new consumer assumptions or regularity wrapper hypotheses.
- Preserve the existing A2/A1 public APIs.
- Avoid whole-tensor/whole-Hom definitional equalities; use applied or weak scalar normal forms.
- Prefer one narrow producer theorem over a broad parabolic refactor.
- Explicitly cite the GitHub files/lines you used.

Tasks:
1. Classify whether the smallest honest next step is weak realization, second-order interior bootstrap,
   joint-smooth reconstruction, or a different statement split.
2. Give the precise Lean statement of the first producer theorem only, with all necessary hypotheses and
   no consumer-facing frontier assumptions.
3. Identify existing project/mathlib lemmas that should prove it, with direct GitHub references.
4. Give the proof architecture and the exact next file to edit.
5. State the failure signal that should make the implementing agent stop and consult again.
```

## Progress accounting

- genuine A2 and A1 input producers: 100%;
- specialized spectral strong-existence theorem: 100%;
- `heatpot_of_maxreg`: not stated/proved (0%); its directly reusable machinery
  is about 20%;
- classical moving conjugate-heat existence theorem: 0%; its dedicated
  analytic machinery is about 70%;
- Perelman no-local-collapsing and `ham3_noncollapse`: 0%; dedicated analytic
  producer machinery is about 32%;
- whole HCG compactness machinery remains about 45%, with endpoint theorems 0%.
