# PROGRESS.md — restructuring execution tracker

Branch: md2. Binding constraint: `lake build` green at every committed checkpoint.
Resume: read this + `git log --oneline`, continue from the last green checkpoint.

## Status legend: ☐ todo · ◐ in progress · ☑ done (green commit)

### Setup
- ☑ Design finalized (STRUCTURE.md, NAMING.md, MIGRATION_PLAN.md, CLAUDE.md written + whitelisted)
- ☑ Baseline build green (9584 jobs)

### W1 — pure folder renames (import-path only; namespaces untouched)
- ☐ VectorBundle → Bundle
- ☐ Analysis/HeatEquation → Analysis/Heat
- ☐ DifferentialForm → Tensor/Exterior
- ☐ PDE/DeTurck → Flow/DeTurck ; PDE/RicciFlow → Flow/RicciFlow ; loose PDE → Flow

### W2 — selective pillar moves
- ☐ Integral/{Measure,L2,DivergenceTheorem} → Integration/*
- ☐ Coordinates → Riemannian/Connection/Chart
- ☐ Geometry/Riemannian → Riemannian/* ; loose Geometry/* → Riemannian/{Operator,Curvature,Metric}

### W3 — splits
- ☐ chartChristoffel hoist → Riemannian/Connection/Christoffel (prereq)
- ☐ Integral/Connection → Riemannian/{Connection,Curvature} (+ analysis bits → Analysis/Elliptic/ConnectionLaplacian)
- ☐ metric hoist + 3→1 dedup + PointwiseInner + 6 RSTensor-tainted → Riemannian/Metric (breaks D1)
- ☐ Realized/* dissolve → Riemannian/{Connection,Curvature}
- ☐ Analysis/Laplacian → Analysis/Elliptic ; extract Analysis/Spectral

### W4 — delete Interface (relocate ricciBilinear first)
- ☐ Interface/ deleted, aggregate updated

### W5 — naming-debt + R5 declaration-level (highest risk; defer if green at risk)
- ☐ Exponential 19→~3
- ☐ one-cluster-per-file for worst lumped files

## Log
- (setup) docs written; baseline green.
