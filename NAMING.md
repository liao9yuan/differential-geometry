# NAMING.md — declaration naming convention (authority)

Companion to `STRUCTURE.md` (which governs files/folders). This doc governs **declaration names**
(theorems, lemmas, defs). The orchestrator owns the master rename-map; per-file work APPLIES assigned
names, it does not invent names freely.

## Scope
- **Theorems / lemmas** (`Prop`-valued): snake_case, normalized per rules below.
- **Definitions** (`def`/`structure`/`abbrev`/`class`, incl. camelCase roots like `expMap`, `injRadius`,
  `ricciTensor`, `connLaplacian`, `heatSemigroup`, `sectionalCurvature`, `arcLength`, `surfaceMeasure`):
  **KEEP camelCase** (Mathlib uses camelCase for defs). Rename a def only if genuinely wrong/misleading,
  as a deliberate, separately-flagged change.

## Theorem-name rules
1. **snake_case** — words lowercased, `_`-separated.
2. **Classical-named results LEAD with the mathematician name in snake tokens**: `bonnet_myers_*`,
   `hopf_rinow_*`, `gauss_bonnet`, `gauss_lemma_*`, `lichnerowicz_*`, `cartan_hadamard_*`, `hamilton_*`,
   `bianchi_first_*`/`bianchi_second_*`, `koszul_*`, `reilly_*`, `weitzenbock_*`, `bochner_*`,
   `green_first_*`/`green_second_*`, `voss_weyl_*`, `harnack_*`, `weak_harnack_*`, `morrey_*`,
   `rellich_kondrachov_*`, `sobolev_*`, `de_simon_*`, `de_giorgi_*`.
3. **Otherwise describe the CONCLUSION**, reusing existing def-roots (do NOT expand them):
   `subject_conclusion_of_essentialHyps`, e.g. `expMap_isLocalDiffeomorphAt_zero`, `injRadius_pos`,
   `laplacian_eigenspace_finiteDim_of_closed`.
4. **NO history/status/scaffolding suffixes** on the final name: `_unconditional`, `_truly_unconditional`,
   `_final`, `_v2`, `_strong`, `_clean`, `_assembly`, `_of_<internal-discharge-lemma>`. The headline IS the
   clean statement. KEEP genuinely-descriptive qualifiers that are NOT history: `_pointwise`, `_seq`,
   `_of_closed`/`_of_compact`/`_of_ricci_bound`, `_with_boundary`, `_intrinsic` (only if it marks a real variant).
5. **`of_` clause** carries the essential mathematical hypothesis when it disambiguates: `_of_closed`,
   `_of_ricci_bound`, `_of_torsionFree`, `_of_metricCompatible`. Keep it short — only the load-bearing hypothesis.
6. **Namespace** = math area (UpperCamelCase), decoupled from the folder path; do not churn namespaces.

## Docstring rules (CODE is the source of truth)
- First sentence = plain statement matching the actual Lean signature.
- State non-standard hypotheses honestly (closed/compact/complete/Ric≥(n−1)K/boundaryless/smallness/
  validity-domain). If a hypothesis is a supplied structural identity, SAY it is assumed.
- DELETE leaked internal blueprint node-IDs, references to deleted scaffolding, and any claim the proof does
  something it does not. A bold lead `**Name.**` is fine but use the human result name, not a node-ID.

## Collision policy
Two distinct decls must not map to the same name. Disambiguate by the distinguishing math content
(e.g. `voss_weyl_laplacian_formula` vs `..._pointwise`).

## Worked examples
| current | new |
|---|---|
| `bonnetMyers_diameter` | `bonnet_myers_diameter_of_ricci_bound` |
| `lichnerowicz_closed_unconditional` | `lichnerowicz_eigenvalue_ge_dim_mul_curvature_of_closed` |
| `expMap_contMDiffAt_zero_truly_unconditional` | `expMap_contMDiffAt_zero` |
