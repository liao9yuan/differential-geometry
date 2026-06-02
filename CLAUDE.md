# DifferentialGeometry — project conventions

A Lean 4 / Mathlib formalization of **differential geometry, broadly construed** (differential
geometry + geometric analysis + the topology/Lie theory DG uses), working toward Ricci flow →
Hamilton's → Perelman's Poincaré. Licensed Apache-2.0. Two convention authorities govern the library:

- **`NAMING.md`** — naming of *declarations* (theorem/def names).
- **`STRUCTURE.md`** — organization of *files and folders* (the file/folder grammar).

This file is the loaded-every-session summary; the two docs above are the full authority.

## Four locked architectural principles

1. **Library is primary; flows are thin capstones.** Every reusable piece of math built incidentally
   for Ricci flow is promoted to its proper mathematical topic home as first-class API, never buried
   as a flow helper. Per-file test: general → topic home; genuinely flow-specific glue → thin `Flow/`.
   (Splits routinely *liberate buried byproducts*: e.g. an even-reflection Euclidean extension, a generic
   L²-multiply engine, an orthonormal-frame trace calculus — extract them to their own first-class file.)
2. **Scope = differential geometry broadly construed.** Root namespace `DifferentialGeometry` is fixed
   (no rename). Geometric analysis + the topology DG uses + Lie groups are first-class second-level
   domains. No speculative algebraic-topology / algebraic-geometry pillars (YAGNI).
3. **Organize by REASONING NATURE, not by application.** The top level splits into algebraic foundations
   (`Bundle`, `Tensor`), geometric reasoning (`Geometry`), and dry analytic/PDE reasoning (`Analysis`).
   Geometric analysis is a first-class peer pillar `Analysis/` — never a separate package, never an
   "engine room". A file goes where its *reasoning* lives: a curvature definition → `Geometry`; an L²
   estimate that merely uses curvature → `Analysis`.
4. **`External/` is VENDORED third-party (De Giorgi–Nash–Moser).** Leave it 100% untouched — never
   move, rename, reorganize, or restyle it. It is the one exception to every other rule.

## Top-level structure (ACHIEVED — flat Mathlib-style root, all green)

```
DifferentialGeometry/
  Bundle/   Tensor/        -- ALGEBRAIC FOUNDATIONS (multilinear algebra over bundles, metric-free; Tensor incl. Exterior/de Rham)
  Geometry/                -- GEOMETRIC reasoning
      Metric/ Connection/ Curvature/ Operator/ Geodesic/ Exponential/
      Comparison/{BonnetMyers, HopfRinow, Variation, …} Boundary/ Hodge/ Topology/
      Flow/{DeTurck-geometric core, RicciFlow/{ShortTime, ShortTimeExistence, …}}   -- the thin flow capstone
  Analysis/                -- DRY ANALYTIC / PDE reasoning
      Integration/{Measure, L2, DivergenceTheorem} Sobolev/ Elliptic/{Regularity, ConnectionLaplacian, …}
      Spectral/{Intrinsic, Tensor, …} Parabolic/ ODE/ Heat/
  External/                -- VENDORED (De Giorgi), untouched
```

Headline theorems live in their topic home: `bonnet_myers_diameter_of_ricci_bound` ∈
`Geometry/Comparison/BonnetMyers`, `ricci_flow_short_time_existence` ∈ `Geometry/Flow/RicciFlow`.
The root `DifferentialGeometry.lean` is a single FLAT list of `import`s of every leaf module (auto-generated;
the one place imports are tracked). There is **no per-directory aggregator/headline file** — Lean has no
glob import, but Mathlib uses one flat root, not a `Concept.lean`/`Area.lean` re-export layer per folder.

## File/folder grammar (full detail in STRUCTURE.md)

- **R1 — three granularity tiers.** Atom (one result-cluster) → a file; Concept (a definition + API +
  several clusters) → a folder; Area (a subject) → a folder of Concepts. Promote a file to a folder
  when it exceeds ~400–500 lines or mixes a definition with its deep theory.
- **R2 — Concept folder skeleton.** `Defs.lean → Basic.lean → <Aspect>*.lean`. NO per-directory aggregator
  files. Do NOT name a folder's main file after the folder (`Bochner/Bochner.lean` is wrong — use
  `Bochner/Defs.lean` or a content name, Mathlib's `Topology/Basic.lean` style).
- **R3 — name by content, never by effort.** Files UpperCamelCase naming the math object/conclusion.
  Forbidden fragments: `Final/Closure/Unconditional/Close/Assembly/Packaging/v2/Strong/Clean/Canonical/`
  `Witness/Scaffold/Stub/Aux/Step/Route/Discharge/Gate/Direct` and pure node-ids. Vague glue (`Bridge/Gen/Raw`)
  only if it names real math. Mathematical qualifiers are encouraged: `_withBoundary`, `_of_closed`, `_intrinsic`.
- **R4 — loose `Defs.lean`.** Definitions plus a few immediately-needed lemmas may co-locate, but
  `Defs.lean` keeps its imports minimal (it is the low-rank anchor everyone imports).
- **R5 — one cluster per file** (cluster = one public headline + only the private lemmas serving it).
  Each theorem/def/lemma lives in the file whose content it *is*; move a misplaced decl to its real home.
- **R6 — folder = math grouping only** (no headline/aggregator file; a folder is navigated, not imported as a unit).
- **R7 — re-export, never re-derive.** Each canonical definition has exactly one home; visibility
  elsewhere is a thin `export`, never a second definition (a re-declared `abbrev` is an R7 violation).

### Variant rule (boundary, scalar/tensor, chart/intrinsic, …)
Decide by whether the **conclusion changes**:
- **Conclusion differs** (boundaryless divergence theorem `= 0` vs with-boundary `= ∫_∂`) →
  **parallel co-equal sibling files** sharing `Defs.lean`; neither is a corollary of the other.
  Co-locate the two variants (e.g. boundary ∥ boundaryless Bochner-concrete sit together).
- **Same conclusion, one is a specialization** (general (r,s)-tensor ⊃ scalar) → **general-primary +
  special-corollary** (collapse).
Boundary infrastructure (outward normal, surface measure, second fundamental form, boundary manifold)
is liberated to first-class `Geometry/Boundary/`. The library's center of gravity is closed
(boundaryless) manifolds (the Poincaré target).

### Layering rule
The only HARD constraint is **Lean's: no file-level import cycle**. On top of that: *foundational*
geometry that Analysis builds on (`Geometry/{Metric, Connection, Curvature}` definitions) should not
import Analysis; but *high-level* geometry that consumes analysis **may and should** import it (geodesics
↔ `Analysis/ODE`, spectral geometry ↔ `Analysis/Spectral`, the Bochner L²/Gårding tower ↔
`Analysis/Elliptic/ConnectionLaplacian`) — geometry and analysis are intertwined. When relocating a file
ACROSS pillars, do a per-file cycle check: does the file import the target pillar? do non-capstone files
in the target import it back? (e.g. a flat-pile of analytic estimates misfiled in `Geometry/Connection`
moves to `Analysis/Elliptic/ConnectionLaplacian`, but a thin support layer that genuinely-geometric facts
depend on stays). Genuine divergence/IBP/measure content is analytic and lives in `Analysis` even when
phrased geometrically.

## Namespaces (DECOUPLED from paths — a deliberate, Mathlib-standard feature)

- **Namespaces follow the MATH OBJECT/AREA, not the folder path** (exactly as Mathlib's `Mathlib/Analysis/…`
  files declare `namespace Real`/`Complex`, never `Analysis`). A decl's full name is independent of which
  file/folder holds it.
- The library's namespaces (e.g. `DifferentialGeometry.Integral.*`, `.PDE.*`, `.Riemannian.*`, `.Geometry.*`,
  `.Tensor.*`) are legitimate math namespaces and were **deliberately kept stable** even though the *paths*
  were reorganized. **Do NOT bulk-rename namespaces to match paths** — it is a 1000s-of-references churn for
  negative value, and risks merge-collisions. Decoupling is the intended state, not a defect.
- Only `import` lines reference paths; moving/renaming a *file* never changes a decl's name, so file
  reorganization is green-by-construction (just rewrite the `import` module token across all importers).

## Soundness / integrity discipline (a green build does NOT prove soundness)

- **No hypothesis-packaging** (the single most severe violation): never add a hypothesis whose type is
  (defeq to) the conclusion and prove the goal by `exact h`. The theorem must not assume what it claims.
- **No vacuous predicates.** A predicate meant to constrain an object must actually use it and reject a
  degenerate witness. Anti-pattern: `def P F := let _ := F; …` (discards F) or `∃ σ, σ = fixedThing`
  (trivially true). Litmus test: *does the predicate reject the zero/degenerate witness?* — and prove it
  (`not_P_zero`). A vacuity is invisible to `#print axioms` and sorry-grep; only adversarial statement-reading
  catches it.
- **Honest `sorry`.** A `sorry`/`admit` is acceptable ONLY as a clearly-labelled, isolated *deferred input*
  (e.g. the local Weyl law, the DeTurck quasilinear principal-symbol match, a forward Picard flow). NEVER
  let a docstring read as a finished proof over a `sorry` body — disclose deferred status, and note that
  consumers transitively depend on `sorryAx`. `#print axioms <headline>` is the ground truth for what is
  genuinely proven (sorry-free ⟺ only `propext, Classical.choice, Quot.sound`).
- **Prohibited predicate:** `HasLocallyConstantChartAt` (and any global-flatness / chart-locally-constant
  uniform-atlas hypothesis) is mathematically FALSE on normal manifolds (S² etc.); never a public-signature
  hypothesis. Intrinsic `g`-inner formulations are the correct path.

### Misc conventions
- Folder depth follows mathematical containment, up to ~5 levels where warranted.
- A standard `variable` block defines the default closed Riemannian manifold context (not a bespoke
  bundled `structure`), for Mathlib compatibility. When splitting a file, reproduce the ORIGINAL's exact
  per-section `variable`/`open`/`attribute [-instance] … in` scoping — a re-declared `variable` line can
  silently drop an instance (e.g. `[CompleteSpace M]`) for later decls. When de-privatizing a lemma to
  share it across a split, first check the name is unique library-wide (a reused `private` name collides
  when made public).
- **Files carrying a non-author attribution are moved whole (`git mv`), never split** at the decl level.
- Only **true duplicates** are deleted (merged to one canonical + re-exports). `sorry`-carrying files are
  re-homed by their math content like everything else (no special quarantine).
- No `Copyright (c) …` per-file headers (the repo-root `LICENSE` covers it); module header `/-! # … -/`
  describing actual content + per-decl `/-- … -/` docstrings only; no proof-body comments / section dividers.
  Module docstrings/`/-! -/` must come AFTER the `import` block (imports must be the file's first tokens).

Future Hamilton surgery / Perelman / 3-manifold topology get homes only when the first theorem lands there.
