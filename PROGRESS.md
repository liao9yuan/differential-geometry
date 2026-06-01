# PROGRESS.md — restructuring execution tracker

Branch: md2. Binding constraint: `lake build` green at every committed checkpoint (HELD throughout).
Resume: read this + `git log --oneline`, continue from the last green commit.

## DONE (each a green-build commit)
- ☑ Conventions + plan committed (CLAUDE.md, STRUCTURE.md, NAMING.md, MIGRATION_PLAN.md) — f720f9fa
- ☑ W1 renames: VectorBundle→Bundle, HeatEquation→Heat, DifferentialForm→Tensor/Exterior, PDE→Flow — d45a68aa
- ☑ Batch A: Integral→Integration; Geometry/Riemannian+Curvature+operators→Riemannian; Coordinates→Riemannian/Connection/Chart — ec22c521
- ☑ Batch B: Integral/Connection→Riemannian/Connection (D2); Analysis/Laplacian→Analysis/Elliptic; Realized→Riemannian/Connection/Realized — 9bca9957
- ☑ Batch C+D: Metric→Riemannian/Metric; delete Interface — b837d6d0
- ☑ Batch E: lift 40 connection-Laplacian analysis files → Analysis/Elliptic/ConnectionLaplacian — aa460779
- ☑ Batch F: Riemannian sub-routing → Comparison/, Hodge/, and loose files into Curvature/Metric/Connection/Exponential — (this commit)

## ACHIEVED TOP-LEVEL ARCHITECTURE (matches target)
```
DifferentialGeometry/
  Bundle/        (was VectorBundle/)
  Tensor/        Multilinear Product Mixed Alternating Auxiliary RSTensor Exterior(was DifferentialForm)
  Riemannian/    Metric Connection Curvature Operator Geodesic Exponential Comparison(BonnetMyers,Variation,…) Hodge Topology
  Integration/   Measure L2 DivergenceTheorem   (was Integral/)
  Analysis/      Sobolev Elliptic(was Laplacian; +ConnectionLaplacian) Parabolic Heat ODE SpectralBounds
  Flow/          DeTurck RicciFlow   (was PDE/)
  External/      VENDORED, untouched
```
Old dirs fully gone: Integral, Geometry, Coordinates, Realized(top), Interface, PDE, VectorBundle, DifferentialForm, Metric(top), Synthetic(already absent). Files 1341→1336 (−5 = Interface).

## METHOD NOTE
All structural moves were file/dir renames + consistent import-path rewrites (helper `_migrate.py`),
which preserve the import DAG ⇒ green by construction. Namespaces were intentionally NOT renamed
(decoupled from paths, Mathlib-style); `open`/qualified refs still resolve. Author-attributed files
moved whole (`git mv`). No content was split.

## DEFERRED — review-appropriate (content-risky or dedup-entangled); NOT done tonight to keep build green
1. **Metric 3→1 dedup + ChartDensity content-split (D1 root).** `SmoothRiemannianMetric` still defined in
   Integration/Measure/ChartDensity + Riemannian/Connection/Realized/MetricFamily + Riemannian/Metric/Basic.
   Unifying needs namespace work; the metric TYPE should move out of ChartDensity into Riemannian/Metric.
2. **Curvature/Operator extraction from Riemannian/Connection.** ~51 curvature + 4 operator files still sit in
   Connection; moving them collides with existing Curvature/{Ricci,Riemann} + Operator/{Gradient,Hessian,Laplacian}
   — i.e. entangled with the D3 duplicate-merge (two `Ricci.lean`, etc.). Needs the dedup decision first.
3. **Realized/ internal routing** (Riemannian/Connection/Realized): its curvature realizations → Curvature.
4. **Exponential 19→~3 content collapse** (merging files = content op).
5. **R5 declaration-level one-cluster-per-file splitting** of lumped files (the highest-risk content op).
6. **Namespace alignment** to the new paths (cosmetic; everything builds with old namespaces).
7. **Analysis/Spectral extraction** from Parabolic/TensorSpectral + Elliptic/Spectral.
8. **Boundary infra → Riemannian/Boundary** (currently under Integration/DivergenceTheorem/WithBoundary).

## Log
- All 7 structural waves landed green. Top-level architecture = target. Deferred items are the
  content-changing / dedup-entangled refinements, left for a reviewed pass (build stays green now).
