# DifferentialGeometry — project conventions

A Lean 4 / Mathlib formalization of **differential geometry, broadly construed** (differential
geometry + geometric analysis + the topology/Lie theory DG uses), working toward Ricci flow →
Hamilton's → Perelman's Poincaré. Two convention authorities govern the library:

- **`NAMING.md`** — naming of *declarations* (theorem/def names).
- **`STRUCTURE.md`** — organization of *files and folders* (the file/folder grammar).

This file is the loaded-every-session summary; the two docs above are the full authority.

## Four locked architectural principles

1. **Library is primary; flows are thin capstones.** Every reusable piece of math built incidentally
   for Ricci flow is promoted to its proper mathematical topic home as first-class API, never buried
   as a flow helper. Per-file test: general → topic home; genuinely flow-specific glue → thin `Flow/`.
2. **Scope = differential geometry broadly construed.** Root namespace `DifferentialGeometry` is fixed
   (no rename). Geometric analysis + the topology DG uses + Lie groups are first-class second-level
   domains. No speculative algebraic-topology / algebraic-geometry pillars (YAGNI).
3. **Geometric analysis is a first-class peer pillar `Analysis/`.** Never split into a separate package.
   Its internals are refined and mis-placed items relocated into it.
4. **`External/` is VENDORED third-party (De Giorgi–Nash–Moser).** Leave it 100% untouched — never
   move, rename, reorganize, or restyle it. It is the one exception to every other rule.

## File/folder grammar (full detail in STRUCTURE.md)

- **R1 — three granularity tiers.** Atom (one result-cluster) → a file; Concept (a definition + API +
  several clusters) → a folder; Area (a subject) → a folder of Concepts. Promote a file to a folder
  when it exceeds ~400–500 lines or mixes a definition with its deep theory.
- **R2 — Concept folder skeleton + 3-level aggregators.** `Defs.lean → Basic.lean → <Aspect>*.lean →
  Concept.lean`. Each Area has an `Area.lean`; the single root `DifferentialGeometry.lean` is the one
  place new imports are added.
- **R3 — name by content, never by effort.** Files UpperCamelCase naming the math object/conclusion.
  Forbidden suffixes: `Final/FinalClosure/Unconditional/Close/UnifiedPackaging/v2/strong/clean/assembly`.
  Mathematical qualifiers are allowed and encouraged: `_withBoundary`, `_of_closed`, `_intrinsic`.
- **R4 — loose `Defs.lean`.** Definitions plus a few immediately-needed lemmas may co-locate, but
  `Defs.lean` keeps its imports minimal (it is the low-rank anchor everyone imports).
- **R5 — one cluster per file** (cluster = one public headline + only the private lemmas serving it).
- **R6 — thin headline at the top** of its folder, assembling from sibling files.
- **R7 — re-export, never re-derive.** Each canonical definition has exactly one home; visibility
  elsewhere is a thin `export`, never a second definition.

### Variant rule (boundary, scalar/tensor, chart/intrinsic, …)
Decide by whether the **conclusion changes**:
- **Conclusion differs** (e.g. boundaryless divergence theorem `= 0` vs with-boundary `= ∫_∂`) →
  **parallel co-equal sibling files** (`Boundaryless.lean ∥ WithBoundary.lean` sharing `Defs.lean`);
  neither is a corollary of the other.
- **Same conclusion, one is a specialization** (general (r,s)-tensor ⊃ scalar) → **general-primary +
  special-corollary** (collapse).
Boundary infrastructure (outward normal, surface measure, second fundamental form, boundary manifold)
is liberated to first-class `Riemannian/Boundary/`, not duplicated per theorem. The library's center
of gravity is closed (boundaryless) manifolds (the Poincaré target).

### Layering rule
The only hard constraint is **Lean's: no file-level import cycle**. On top of that: the *foundational*
geometry that Analysis builds on (`Riemannian/{Metric,Connection,Curvature}`) must not import Analysis;
but *high-level* geometry that consumes analysis **may and should** import it (geodesics ↔ `Analysis/ODE`,
spectral geometry ↔ `Analysis/Spectral`) — geometry and analysis are intertwined. The CI guardrail is a
**per-concept (sub-directory) rank table + acyclicity check**, never path-encoded `Lnn_` prefixes.

### Misc conventions
- Namespaces follow the math object/area, **not** the full folder path (Mathlib-style decoupling).
- Folder depth follows mathematical containment, up to ~5 levels where warranted.
- A standard `variable` block defines the default closed Riemannian manifold context (not a bespoke
  bundled `structure`), for Mathlib compatibility.
- **Files carrying an author attribution are moved whole (`git mv`), never split** at the declaration level.
- Only **true duplicates** are deleted (merged to one canonical + re-exports). `sorry`-carrying files are
  re-homed by their math content like everything else (no special quarantine).
- No `Copyright (c) …` headers; module header + per-decl `/-- … -/` docstrings only; no proof-body
  comments / section dividers.

## Top-level structure (target; see STRUCTURE.md / MIGRATION_PLAN.md)

```
DifferentialGeometry/
  Bundle/        smooth vector bundles (foundations, metric-free)
  Tensor/        tensor algebra (metric-free) + Exterior (de Rham)
  Riemannian/    THE geometry pillar: Metric / Connection / Curvature / Operator / Geodesic /
                 Exponential / Comparison / Boundary / Hodge / Topology   (intra-umbrella rank lint)
  Integration/   measure (Riemannian volume) / L² / divergence theorem   (peer, below Analysis)
  Analysis/      geometric analysis: Sobolev / Elliptic / Spectral / Parabolic / Heat / ODE
  Flow/          Ricci-flow thin capstone: DeTurck / RicciFlow (ShortTimeExistence, Evolution, …)
  External/      VENDORED, untouched
```

Headline theorems live in their topic home (thin): `bonnet_myers_*` ∈ `Riemannian/Comparison`,
`ricci_flow_short_time_existence` ∈ `Flow/RicciFlow`. Future Hamilton surgery / Perelman / 3-manifold
topology get homes only when the first theorem lands there.
