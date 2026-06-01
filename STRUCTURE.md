# STRUCTURE.md — file & folder grammar (authority)

Companion to `NAMING.md` (which governs *declaration* names). This doc governs how mathematical
content maps to **files and folders**. Every migration/refactor obeys it.

## 0. The four locked principles
1. Reusable-math library is PRIMARY; Ricci flow / Hamilton / Perelman are THIN capstones consuming it.
2. Scope = differential geometry broadly construed; root namespace `DifferentialGeometry` fixed.
   Geometric analysis + the topology DG uses + Lie groups are first-class second-level domains; no
   speculative algebraic-topology / algebraic-geometry pillars.
3. `Analysis/` (geometric analysis) is a first-class peer pillar — never a separate package; internals
   are refined, mis-placed items relocated in.
4. `External/` is VENDORED third-party — 100% untouched.

## 1. Granularity tiers (when folder vs file)
- **Atom** = one coherent result-cluster (one public headline + the private lemmas serving only it) → **a file**.
- **Concept** = a definition + its API + several result-clusters → **a folder**.
- **Area** = a mathematical subject containing several Concepts → **a folder of Concepts**.
- Promote a file → folder when it exceeds ~400–500 lines OR mixes a definition with its deep theory.

## 2. Concept folder skeleton + aggregators
```
Concept/
  Defs.lean        -- definitions (def/structure/class/abbrev/notation). Minimal imports (low-rank anchor).
  Basic.lean       -- foundational API right on the defs (constructors, simp, basic properties).
  <Aspect>.lean    -- one thematic result-cluster each (Smoothness, Continuity, Comp, MetricCompatible, …).
  Concept.lean     -- (sibling) thin aggregator: imports the whole Concept/ folder.
```
Three aggregator levels: per-Concept `Concept.lean`, per-Area `Area.lean`, and the single root
`DifferentialGeometry.lean` (the ONE place new imports are added). Upper levels import lower aggregators.

## 3. The seven rules
- **R1** three tiers (above).
- **R2** skeleton + aggregators (above).
- **R3** name by CONTENT (math object/conclusion), files UpperCamelCase. **Forbidden** effort/status
  suffixes: `Final, FinalClosure, Unconditional, Close, Unconditional, UnifiedPackaging, v2, strong,
  clean, assembly`. **Allowed** mathematical qualifiers: `_withBoundary, _of_closed, _intrinsic, _pointwise, _seq`.
- **R4** loose `Defs.lean` (defs + a few immediate lemmas may co-locate), but its imports stay minimal.
- **R5** one cluster per file.
- **R6** thin headline at the top of its folder, assembling from siblings.
- **R7** re-export (`export`), never re-derive: one canonical home per definition; elsewhere a thin re-export.

## 4. Variant rule (boundary, scalar/tensor, chart/intrinsic, local/global, time-dependent/static)
Decide by whether the **conclusion changes**:
- **Conclusion differs** → **parallel co-equal siblings** (`Boundaryless.lean ∥ WithBoundary.lean` sharing
  `Defs.lean`); neither a corollary of the other. (Boundary divergence theorem `=∫_∂` vs closed `=0` is the archetype.)
- **Same conclusion, a specialization** → **general-primary + special-corollary** (collapse).
Boundary infrastructure (outward normal, surface measure, second fundamental form, boundary manifold) is
liberated to first-class `Riemannian/Boundary/`, never duplicated per theorem. Library center of gravity =
closed (boundaryless) manifolds (the Poincaré target).

## 5. Layering rule
Only hard constraint: **Lean's no file-level import cycle**. On top: foundational geometry that Analysis
builds on (`Riemannian/{Metric,Connection,Curvature}`) must not import Analysis; high-level geometry that
consumes analysis MAY (geodesics ↔ `Analysis/ODE`; spectral geometry ↔ `Analysis/Spectral`). Guardrail =
**per-concept (sub-directory) rank table + acyclicity lint**; rank NEVER in path names. Inside `Riemannian/`
the sub-dir rank is `Metric < Connection < Curvature/Operator < Geodesic/Exponential/Hodge < Comparison`,
with `Topology` a side-branch (rank-incomparable to Comparison).

## 6. Misc conventions
- Namespaces follow the math object/area, not the full folder path (Mathlib-style decoupling).
- Depth follows mathematical containment, up to ~5 levels where warranted.
- Default working context = a standard `variable` block for the closed Riemannian manifold (not a bespoke
  bundled `structure`), for Mathlib compatibility.
- **Author-attributed files are moved whole (`git mv`), never split** at the declaration level.
- Only true duplicates are deleted (merge to one canonical + re-exports). `sorry`-files are re-homed by
  math content like everything else.
- No `Copyright (c) …` headers; module header + per-decl `/-- … -/` docstrings; no proof-body comments /
  section dividers. `External/` exempt from all of this (vendored).

## 7. Target top-level tree
```
DifferentialGeometry/
  Bundle/        smooth vector bundles (foundations, metric-free)
  Tensor/        Multilinear/ Product/ Mixed/ Alternating/ Auxiliary/ RSTensor(metric-free)/ Exterior(de Rham)/
  Riemannian/    Metric/ Connection/{LeviCivita,Christoffel,Chart,Tensor,Realization,Laplacian,ParallelTransport}
                 Curvature/{Riemann,Ricci,Bianchi,Identities,Bochner,Sectional} Operator/ Geodesic/ Exponential/
                 Comparison/{BonnetMyers,InjectivityRadius,NormalCoordinates,Lichnerowicz(pointwise)} Boundary/ Hodge/ Topology/
  Integration/   Measure/ L2/ DivergenceTheorem/
  Analysis/      Sobolev/ Elliptic/ Spectral/ Parabolic/ Heat/ ODE/   (+ lifted connection-Laplacian analysis)
  Flow/          DeTurck/ RicciFlow/{Equation,ShortTimeExistence,Evolution,ODE,Pullback,…}
  External/      VENDORED, untouched
```
Headlines live in topic homes (thin): `bonnet_myers_*` ∈ `Riemannian/Comparison`,
`ricci_flow_short_time_existence` ∈ `Flow/RicciFlow`. Future Hamilton/Perelman/3-manifold-topology homes
are created only when the first theorem lands there.
