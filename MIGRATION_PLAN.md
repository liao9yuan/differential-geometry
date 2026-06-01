# MIGRATION_PLAN.md — restructuring md2 to the target architecture

Authority: `STRUCTURE.md` (file/folder grammar) + `NAMING.md` (declaration names).
Target tree: see `STRUCTURE.md` §7 and the adversarial final tree below.
Binding constraint: **`lake build` stays green; every committed checkpoint builds.**
Working branch: **md2** (worktree at `/Users/qzy/differential-geometry/.claude/md2`).
Baseline: green (9584 jobs) at session start; only pre-existing `sorry` warnings.

## Execution model (build-safe waves, green checkpoints)
- Work directly on md2, commit every green checkpoint, so any failure reverts to the last green commit.
- Each step: make a coherent batch (mostly `git mv` + import-path rewrites) → `lake build` → green ⇒ commit; red ⇒ fix or revert the batch.
- **Folder renames change only import MODULE PATHS** (`import DifferentialGeometry.Old…` → `…New…`). Namespaces
  are decoupled from paths (STRUCTURE §6) and are NOT touched in the move waves — that keeps moves mechanical and
  safe. Namespace alignment to the new paths is a separate, lower-priority follow-up pass.
- **Author-attributed files: `git mv` whole, never split.**
- `sorry`-carrying files: re-homed by content like any other (no quarantine).

## Wave order (lowest build-risk first)
- **W1 — pure folder renames** (no content split): `VectorBundle→Bundle`; `Analysis/HeatEquation→Analysis/Heat`;
  `DifferentialForm→Tensor/Exterior`; `PDE/DeTurck→Flow/DeTurck`, `PDE/RicciFlow→Flow/RicciFlow` (+ loose PDE → Flow).
- **W2 — selective pillar moves**: `Integral/{Measure,L2,DivergenceTheorem}→Integration/*`; `Coordinates→Riemannian/Connection/Chart`;
  `Geometry/Riemannian→Riemannian/*` (Geodesic/Exponential/Comparison/Boundary/Hodge/Topology); loose `Geometry/*→Riemannian/Operator`+`Curvature`.
- **W3 — the splits (higher risk, careful)**: `Integral/Connection` → `Riemannian/{Connection,Curvature}` + analysis bits → `Analysis/Elliptic/ConnectionLaplacian`;
  metric hoist + 3→1 dedup (`ChartDensity`/`MetricFamily`/`Metric/Basic` → `Riemannian/Metric/Basic`) + `Integral/L2/PointwiseInner`→`Riemannian/Metric` + the 6 RSTensor metric-tainted files (breaks D1);
  `Realized/*` dissolve into `Riemannian/{Connection,Curvature}`; `Analysis/Laplacian→Analysis/Elliptic` + extract `Analysis/Spectral`.
- **W4 — delete `Interface/`** (0 importers; relocate `ricciBilinear`→`Riemannian/Curvature` first); update aggregate.
- **W5 — naming-debt + R5 (declaration-level)**: collapse `Riemannian/Exponential/` 19→~3; one-cluster-per-file splits of the worst lumped files.
  HIGHEST RISK — done only with per-file build verification; deferred items are documented in PROGRESS.md if green cannot be guaranteed.

## Hard prerequisites / adversarial fixes (from the critique)
1. `chartChristoffel` HOIST out of `Geometry/Hessian` → `Riemannian/Connection/Christoffel` must precede Curvature moves
   (else Curvature→Operator edge). 
2. `LichnerowiczSpectral` (imports `Analysis.Spectral`+`Heat`) STAYS in `Analysis/Spectral`; only POINTWISE Lichnerowicz → `Riemannian/Comparison`.
3. `ChartBridge/{Ricci,Riemann}` → `Riemannian/Curvature` (not Operator); `SlotCorrectionChartCompFormula` → `Riemannian/Connection/Chart`.
4. Intra-`Riemannian/` sub-dir rank lint (`Metric<Connection<Curvature/Operator<Geodesic/Exp/Hodge<Comparison`; `Topology` incomparable) — a CI requirement.
5. `LocalChartConsistency.lean` (HLCC) is live on this branch — excise as its own sequenced task, do not re-home.

## Resumability
`PROGRESS.md` tracks each wave/step (done/green-commit-hash/remaining). On resume, read it + `git log` to continue
from the last green checkpoint. Build is verified per checkpoint; the last commit is always green.
