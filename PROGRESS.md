# PROGRESS.md — restructuring execution tracker

Branch: md2. Binding constraint: `lake build` green at every committed checkpoint (HELD throughout).
Verify builds by grepping the log for "Build completed successfully" (shell is zsh; exit-code echoes unreliable).
Resume: read this + `git log --oneline`, continue from the last green commit. Scratch movers: `_migrate.py`,
`_applyplan.py`, `_stage1.py`, `_stage2.py`, `_rename.py` at the worktree root (gitignored).

## ACHIEVED — final architecture (by REASONING NATURE), all green
```
DifferentialGeometry/
  Bundle/     Tensor/        -- algebraic FOUNDATIONS (multilinear algebra over bundles)
  Geometry/                  -- GEOMETRIC reasoning
      Metric/ Connection/{…,Realization(ex-bridges)} Curvature/ Operator/ Geodesic/ Exponential/
      Comparison/{BonnetMyers,…} Boundary/ Hodge/ Topology/ Flow/{DeTurck-geometric, RicciFlow flow-specific}
  Analysis/                  -- DRY ANALYTIC / PDE reasoning
      Integration/{Measure,L2,DivergenceTheorem} Sobolev/{…,HebeyBlock,Embedding,IntrinsicFlow}
      Elliptic/{…,ConnectionLaplacian} Spectral/{…,Intrinsic,Tensor} Parabolic/{…,RicciLinearization,
      DeTurckLinearization,ShortTime} ODE/{…,TimeDependentFlow} Heat/
  External/                  -- VENDORED (De Giorgi-Nash-Moser), untouched
```
1319 files. Old top-levels gone: Integral, Geometry(old), Coordinates, Realized, Interface, PDE, VectorBundle,
DifferentialForm, Metric(top), Synthetic, Riemannian, Flow, SpectralBounds.

## DONE — Atom/Concept/Area granularity (R1/R2 concept-folder grouping), all green
Flat Areas regrouped into Concept sub-folders (Defs/Basic/Aspect pattern; build-safe git-mv + import rewrite):
- round 1 (commit e871bac4): Geometry/Curvature {Riemann,CurvatureOperator,Bochner,FiberNormParseval,
  CovGradRoughLap,Order2Defect}; Geometry/Connection {LeviCivita,ChartFrame,TensorNabla,ChartTensorNabla,
  MetricCompatibility,Laplacian,ParallelTransport}; Analysis/Spectral/Intrinsic {DeTurck,HeatSemigroup,Garding}.
- round 2+3 (commit 8a7496ff): Geometry/Exponential {Smoothness,ChartFlow}; Analysis/Heat {Smoothing,Semigroup};
  Analysis/ODE/Flow; Analysis/Elliptic/TensorRegularity {Bootstrap,WeakSolution,CovDeriv}; Analysis/Spectral/Tensor
  {Spectrum,Variational,UniformChartBounds,NormEstimates,CovGrad}; Analysis/Parabolic {DeTurckRicci,AbstractSemigroup}.
- ConnectionLaplacian grouping (commit bcf4abb0): the unified 84-file dir → 8 concepts {GreenIdentityAndIBP,
  RiemannianFiberNormSq, ChartCoordinateExpansion, ChartReprDerivativeBounds, CovApplyAndSlotCorrectionBounds,
  ChartFiberTrivialisationOpNorm, RawConnLapPointwiseFiberBounds, RawConnLapL2SobolevBounds} (lean-researcher partition).
- Sobolev grouping: 4 sub-areas → concepts (lean-researcher partition): Chart {ChartTransition,CrossChartBounds,
  AtlasNorm,BanachCompleteness,SmoothDensity;Defs@root}; Nirenberg {TestFunction,SubstitutionIdentity,
  ChartBilinearDischarge,MasterInequality,CrossTermBoundsNonSmooth,H2Regularity}; HebeyBlock {ChartParallelTransportOpNorm,
  ChristoffelCorrectionL2,FiberNorm,NablaTensor,TensorChartComponentSobolev,PouSobolevIso}; Euclidean {IteratedSobolevSpace,
  Completeness,ChainRule,Multiplication,Embedding,SupportAndDomain;Setup,Density@root}.
GRANULARITY PASS COMPLETE: every genuinely-oversized multi-concept flat Area (25–84 files) is now concept-organized.
Remaining ≥18-file dirs are either External/DeGiorgi (vendored, untouchable) or coherent single concepts
(RSTensor, Elliptic/Regularity/{Iterated,DiffChart}, ODE/TimeDependentFlow/*, DivergenceTheorem/WithBoundary,
RicciFlow/Pullback) at acceptable R1 granularity. NOT YET DONE (optional R2 polish): per-concept aggregator/headline
files (Concept.lean re-exports) — deferred; the root DifferentialGeometry.lean already imports every leaf directly.
- CROSS-PILLAR CONSOLIDATION (by reasoning nature): the scattered analytic connection-Laplacian estimate cluster
  (33 flat in Geometry/Connection + 10 in Geometry/Connection/Laplacian + 1 in Geometry/Curvature) was fixpoint-
  analyzed (/tmp/_moveA.json) and the 36 purely-analytic files moved → Analysis/Elliptic/ConnectionLaplacian
  (now 84 files). The 6 files that genuinely-geometric facts depend on (Voss-Weyl divergence, chart-Christoffel
  Riemann identity, cov-grad naturality) STAY in Geometry as the thin support layer; residual acyclicity violations = 0.
  Geometry/Connection flat is now just the 4 geometric support files. ConnectionLaplacian (84) then concept-grouped.
NOTE on a PRE-EXISTING tangle (out of scope): Geometry/Curvature still holds Bochner L²-estimate files
  (CovGradRoughLapCurvL2Bound, FiberNormParseval/*, Order2Defect/*) that already import Analysis (pre-existing
  Geometry→Analysis edges, compile green). A future "consolidate the Bochner L²-estimate apparatus" pass could
  move them; deferred (riskier, needs the same fixpoint treatment).

## Commit trail (md2, all green)
f720f9fa docs → d45a68aa W1 → ec22c521 → 9bca9957 → b837d6d0 → aa460779 → bd6eb3ff → e1be3452 (Spectral)
→ 35eec9a9 (Boundary) → 4fbd4f97 (ChartGram split, D1) → f96c4f98 (D1 PointwiseInner+RSTensor down)
→ 27292c99 (curvature consol + Integration fold + Realized reloc + SpectralBounds) → 87210380 (Geometry
rename + Realized DELETED + DeTurck distribute + curvature-estimates→Analysis) → eddd638b (Flow dissolve:
RicciFlow general→Analysis, flow-specific→Geometry/Flow/RicciFlow).

## DONE this round (deferred items)
- ☑ Metric D1 fix (ChartGram split + PointwiseInner/RSTensor-Riemannian → Geometry/Metric; Tensor Integration-free)
- ☑ Boundary infra → Geometry/Boundary
- ☑ D3 curvature consolidation (Connection→Curvature); analytic norm-estimates → Analysis
- ☑ Realized DELETED (redundant ex-Synthetic; verified no external importers); 7 load-bearing Realization
     bridges relocated → Geometry/Connection/Realization (plain glue, no longer "Realized")
- ☑ Geometry rename (Riemannian→Geometry); Integration folded into Analysis
- ☑ Flow dissolved by reasoning nature (DeTurck + RicciFlow distributed)
- ◐ file-name optimization: 12 safe effort-suffix strips applied (build pending)

## DONE round 3 (file reorg by reasoning nature + names) — all green
- ☑ Geometry rename; Flow dissolved; Realized deleted; Integration→Analysis fold; D1/D3/boundary/Integration
- ☑ 81 effort/cryptic file RENAMES → content names (12 + 69); attributed (McCarthy/Kudryashov/Liao) files untouched
- ☑ Folder-organizing: 86-file EigenvectorWeakSolution → 8 concept sub-folders; ODE TimeDependentFlow double-nest flattened
- ☑ 6 read-only planning agents (Agent tool reads md2 correctly — only the WORKFLOW tool reads the wrong worktree)
NOTE: most files are already single-cluster → R5 declaration-splitting largely UNNEEDED; merge-clusters are >500L
so they stay split (rename-only) per STRUCTURE §1. The FILE-level architecture + file-names are COMPLETE.

## REMAINING — DISTINCT next phases (not file-reorg; need review or the master rename-map)
- DECL-name cleanup (theorem names, NAMING.md): leaked node-IDs bm_c_*/h1_/h2_/h3_/stub_ in declaration names
  across Comparison/Geodesic/SmoothDependence etc. This is THEOREM renaming (global identifier replace + build),
  NOT file reorg; per NAMING.md the orchestrator owns the master rename-map (collision care). Large separate pass.
- Semantic dedups: Exponential's 4 iterations of `expMap_contMDiffAt_zero` (FinalClosure/SmoothnessClose/
  SmoothnessUnconditional/Unconditional) — keep ONE, delete the redundant 3 (needs a which-is-canonical decision).
  Plus the agents' MERGE suggestions (Semigroup/Smoothing) — better done as concept sub-folders if at all.
- Namespace alignment: namespaces stale (DifferentialGeometry.{Riemannian,Integral,PDE,Realized}.*) vs paths;
  OPTIONAL per STRUCTURE §6 (decoupled). Large all-references rewrite.

## (superseded note below)
- File-rename clusters that need MERGE not strip: Exponential effort-cluster (Final/FinalClosure/Unconditional/
  SmoothnessClose/SmoothnessUnconditional/UnifiedPackaging — all "exp C∞-at-0" facets → collapse to ~3 content files);
  CovGradRoughLapCommutator{Close2,Close3,DoubleUnfold,Assembly}; Order2Defect* route-named files.
- R5 declaration-level one-cluster-per-file splitting of lumped files (hundreds; content-risky).
- Namespace alignment: namespaces are now stale (DifferentialGeometry.{Riemannian,Integral,PDE,Realized}.*) vs
  the new paths. OPTIONAL per STRUCTURE.md §6 (namespaces decoupled from paths) but cosmetically confusing;
  a full realign is a large all-references rewrite — defer / do with review.
- Realized↔intrinsic semantic dedup was avoided (Realized deleted instead, cleaner).
