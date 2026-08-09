# HamiltonCompactness

Source used: MSM135 Chapter 3 theorem "Compactness for solutions"; MSM135 Chapter 4 was checked to identify the true proof backend.

## Current canonical route (2026-07-27)

`compactnessSol_cond` is the canonical wrapper over `solutionComp_cond`.  It
consumes `MetricCompactnessInputs`, the concrete conditional Theorem 3.9
conclusion, and `FlowUpgradeData`; it calls neither unconditional
`metricCompactness` nor any exact-conclusion backend.

This conditional consumer body is checked infrastructure. Conditional
Theorem 3.9 and the P4 producer `open_upgrade_canon` are now checked.

The file now also states the genuine target `compactnessSol`.  Its time-domain
hypothesis is the literal book domain
`X.D = RealTimeInterval.openInterval α b 0 h0`; no endpoint/exhaustion
predicate is introduced.  Its remaining inputs are completeness, compact-time
curvature bounds, the genuine time-zero basepoint injectivity-radius bound, and
connectedness.  The compact-window curvature input is a locally uniform
strengthening of the book conclusion from a weaker hypothesis than one global
constant on the whole open interval.

The target conclusion now explicitly includes completeness of every limit
time-slice.  This strengthens only `compactnessSol`; the generic
`CompactnessConclusion` remains unchanged because it has existing consumers.
There were no `compactnessSol` call sites to migrate. The proof body checks the
first reduction, `CompleteInput.at_time` at `t = 0`, before the remaining
explicit `sorry`. The all-time flow-upgrade and limit-completeness side is no
longer the blocker: `open_upgrade_canon` consumes the checked no-extra-input
`movingShi_open` route and returns both `FlowUpgradeData` and completeness of
every limit time-slice.

The precise missing producer is earlier, at time zero. The present hypotheses
do not yet construct

```text
MetricCompactBase (X.atZero)
  -> MetricCompactnessInputs (X.atZero)
  -> StepDCanonData (X.atZero).
```

Once that data exist, the remaining final assembly is the short call
`open_upgrade_canon canon h0 hD hcomplete hcurv`, followed by
`FlowUpgradeData.toConclusion`. Native construction of `MetricCompactBase`
still depends on the CGT injectivity-decay producer, the unconditional
Bishop--Gromov volume-overlap producer, the sequence-uniform H6 radius profile,
and the all-order `NormalCoordMetricBoundInput` producer. Consequently
`compactnessSol` remains theorem-level 0%; the P4 producer/assembly is 100%,
and whole-HCG machinery remains about 60%. Focused verification of the source
is green with the expected warning at the one visible endpoint `sorry`.

The target proof is now filled through that boundary. Its single `sorry` is the
local proof of

```text
Nonempty (MetricCompactBase (X.atZero)).
```

After choosing this base, the checked code constructs `StepDCanonData`, calls
`open_upgrade_canon`, uses `FlowLimitData.converges`, and returns both smooth
CGH convergence and completeness of every limit slice. Focused verification is
green; no downstream assembly hole remains.

The generic carrier-capable `CompactnessConclusion` and conditional consumers
remain unchanged.  This is intentional: the Hamilton blow-up adapter separately
uses scalar convergence at the nonregular carrier endpoint `t = 0`.

## Removed legacy route (superseded)

> **Superseded as current instructions.**  The former exact-conclusion-backed
> `compactnessSol`/`solutionCompactness` route was deleted on 2026-07-09 and
> must not be restored.  The current `compactnessSol` reuses only the name: its
> statement is the honest open-interval MSM135 theorem and its unproved P4 body
> remains visible.

The deleted wrapper had carried `_hinj : InjInput` and an exact-conclusion
backend.  The canonical theorem instead exposes the real
`hflowInj : FlowBaseInjBound` and concrete `FlowUpgradeData`.

The zero-callsite `hamiltonCompactness` wrapper and its arbitrary numeric
`NoncollapseInput` were removed on 2026-07-09.  Volume noncollapse now reaches
the compactness route only through the explicit CGT frontier `flowInj_of_vol`
in `NoncollapseInjectivity.lean`.

The 2026-05-27/28 review notes about the pointed Riemannian rename,
`[I.Boundaryless]`, and `_hinj` are historical context for the deleted route,
not a live API or resume point.

## 2026-07-29 unconditional endpoint closure

`compactnessSol` is now fully proved.  The open-window complete-Shi route
supplies `CurvBoundInput.atZeroGeomOpen`; the proof then constructs the
provider-neutral `MetricCompactSeed`, chooses the native `H6NormalData`, builds
`StepDCanonData` with `metricCanonH6`, and feeds it to the already checked
`open_upgrade_canon`.  The obsolete `Nonempty (MetricCompactBase
(X.atZero))` boundary and its only `sorry` were removed.

Focused verification is green, and the exact module build is green
(`9982/9982`).  Direct axiom replay for `compactnessSol` contains only
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

Honest accounting:

- unconditional MSM135 Theorem 3.10 `compactnessSol`: 100%;
- its dedicated time-zero, H6 metric, and open-window flow-upgrade machinery:
  100%;
- whole-HCG supporting machinery: approximately 84%;
- `ham3_cgh_limit`, the later Hamilton blow-up consumer, remains a distinct
  theorem-level 0% until it is migrated to this endpoint.
