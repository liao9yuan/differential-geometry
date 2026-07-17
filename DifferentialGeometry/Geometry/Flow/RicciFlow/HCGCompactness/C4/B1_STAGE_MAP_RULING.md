# B1 global stage-map ruling

## Architecture

Preserve `StepB1RawInput` unchanged.  The canonical comparison map is the one
global finite-stage map built from the actual normalized source-stage weights,
the direct source-chart to target-chart points, and the unique global minimizer
of the target-stage center energy.  Source slots are proof indices only.  Do not
glue chart-local limit weights and do not introduce a pointwise chart selector.

For a forward map from stage `k` to stage `l`, the frozen center manifold is the
target stage `l`; the reverse comparison map is used only as an approximate
return map.  The exact reverse map required by `StepB1RawInput` remains
`Function.invFunOn` after local diffeomorphism and global injectivity have been
proved.

The frozen quantifier shape

```text
eventually n, exists N_n, forall a b >= N_n, P n a b
```

does not imply the required all-pairs tail under further reindexing.  The next
center producer must give a common threshold, preferably

```text
exists N, forall n a b >= N, P n a b,
```

before the reference manifold is frozen.

## Checked on 2026-07-15

- `CenterOfMass.centerEnergy_congr`,
  `centerAverage.energy_activeFill`, and
  `centerAverage.uniqueMin_activeFill` make zero-weight replacement
  energy-invariant and preserve the unique global minimizer.
- `StepCStageMap.lean` defines `stageTarget`, `HasUniqueStageCenter`, and
  `stageComparisonMap` without a chart selector; `stageTarget_local` supplies
  the manifold-level local-transition decode under the existing chart-source
  premise.
- `StepCStageComparison.uniqueStage_of_fill` identifies any checked local
  filled center branch with the original global stage energy, and
  `stageCompare_eq_cm` proves that the global map equals its selected center.
- `MetricCompactnessInputs.exists_live_cores` returns fixed compact cores
  `C0 alpha ⊆ interior (C1 alpha) ⊆ C1 alpha ⊆ U alpha` on the existing
  subsequence, and the strict inner-core images cover the frozen source ball.
  `exists_atom_supp_fin`, `HasSuppConvData`, `exists_supp_pts_fin`, and
  `MetricCompactBase.exists_supp_cm_fin` retain those cores on the same master
  subsequence as the support-local center solutions.
- `ContDiffBump.radial` supplies the reusable safety clamp.  `StepCStageFill`
  implements the fixed `6/7` activity bump, fixed `7/8` safety bump,
  old-`InterSlot` finite totalization, actual refined weights/points, and full
  configuration convergence for every pair of reindexings tending to
  infinity.  `stagePtsSub_eq_ne` gives exact raw-target agreement at every
  retained nonzero interacting slot.
- `HasSuppConvData` retains the all-stage two-sided transition smoothness
  already proved by its producer's common finite-pair shift; no new endpoint
  input or second source-chart diagonal is used.

All listed files passed focused verification; the canonical stage-map module
and the canonical energy module also passed exact module refreshes.

## Exact analytic stop point

The analytic route is now decomposed at native layers.  Metric-jet to spray
convergence is checked algebraic packaging: `MetricKoszul.metricSpray_conv` and
`normalGeodesicSpray_conv` use a proof-independent inverse Gram expression and
introduce no velocity, stage-stay, or endpoint-radius assumption.

The earliest genuinely new theorem is
`MapCInfConvOnCompacts.ode_solutionAt`, deriving compact-tube containment and
all parameter-jet convergence from limit-trajectory containment.  Its exact
analysis-layer statement is typechecked, while its proof remains 0% with one
honest `sorry`.  Once it is proved, forward normal-phase endpoint convergence
is a thin specialization.  A fixed compact root tube then supplies inverse
convergence; the same moving-root API is later applied to `invVelSum`, not
directly to `chartCmEqnB`.

After the all-pairs chart tail, exact-local-inverse convergence and the
chart-to-`tensor02CovDerivNormWith` bridge remain independent frontiers.  See
`B1_MOVING_ROOT_CONSULT.md` for the answered architecture request and current
theorem-level accounting.

## Forbidden repairs

- Do not change `StepB1RawInput`.
- Do not add a branch-specific field to `MetricCompactnessInputs`.
- Do not glue local limit weights or select a source chart pointwise.
- Do not impose whole-cage target containment or an endpoint-radius assumption.
- Do not identify the reverse comparison map with the exact inverse.

## Accounting

The canonical map-definition seam, nested-core producer, and smooth Route-A
configuration convergence are each checked.
The proof-independent metric spray and `normalGeodesicSpray_conv` are checked
(100%).  `MapCInfConvOnCompacts.ode_solutionAt` has its final public statement
and canonical placement (100%), but its theorem proof and dedicated all-order
stability machinery remain 0%.
The all-pairs stage-map chart-tail theorem, concrete `StepB1RawInput` producer,
and textbook B1 theorem remain 0%.  Rounded dedicated Step-B/B1 machinery stays
about 95%, Chapter 4 machinery about 87%, and whole-HCG machinery about 57%.
All compactness endpoints remain theorem-level 0%.
