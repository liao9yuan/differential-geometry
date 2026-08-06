# CurvatureCoefficientDifferenceJetTower

## 2026-07-12: fixed-frame independence elaboration

### Status

- `riemannMixedBiContrFib_eq_fixedFrame_on_nbhd`: proved and source-verified (100%).
- Its dedicated frame-independence machinery, including
  `double_frame_bilin_trace_indep`: available and reused (100%).
- This module's focused source verification and targeted build: passed (100%).
- Short-time-existence branch-alignment merge preparation: approximately 85%; the headline
  theorem is already proved, but downstream consumer and final merge-gate verification remain
  separate work.

### Simplification

The theorem differs from the nearby successful fixed-frame proofs only by an outer scalar factor
`2`. The old generic `congr 1` attempted to discover that congruence through a very large tensor
expression. It was replaced by the typed congruence
`congrArg (fun z : Real => 2 * z)`, after which the existing
`double_frame_bilin_trace_indep` theorem closes the actual geometric equality.

### Failed route and verification

The generic-congruence version hit a deterministic `whnf` heartbeat timeout and a retry with a
larger heartbeat budget consumed roughly 6 GB of memory. Increasing the budget is not a viable
route. The simplified proof passed focused verification and a targeted module build at the normal
heartbeat limit with two Lean threads. No new mathematical frontier remains in this theorem.

## 2026-07-15: antidiagonal product integral API

`grid_prod_int_le` exposes the existing antidiagonal product integration
engine.  Given a pointwise zeroth-jet bound, the top `L2` jet, and the
Gagliardo--Nirenberg intermediate estimates, it controls each product term by
the square of the top jet.  This is the reusable input needed for the
three-dimensional order-two inverse-metric estimate.

The mathematical proof was already present as the private product-term engine;
this change only gives it a public canonical name.  Verification is still
running because this module is unusually large.

## 2026-07-19: public moving-trace split

`pureTrace` gives a small public name to the canonical cometric double-trace
coefficient, and `pureTrace_split` exposes its exact decomposition into the
fixed parallel trace plus the inverse-metric-difference correction.  This is
the algebraic input for the low-regularity fixed-curvature `lieCorr0` arm; it
avoids estimating that arm as an undifferentiated whole.

These aliases are source-complete but await a focused recheck after the
exclusive shared artifact refresh.  No endpoint theorem is credited by this
source-only addition.

## 2026-07-26: THE GATE — radius-free top-separated grid integrator (UNIF item-2)

Implements the single lemma frontier of UNIF item-2 proper per the GPT Pro
ruling distilled in `ShortTime/THREEARM_RECON.md` §11.  Three new declarations
added next to the ballUniform sibling (`:14417` area):

- `antidiagonalTupleGrid_integral_radiusFree` — radius-free per-order antidiagonal
  grid integral bound.  Sibling of `antidiagonalTupleGrid_integral_ballUniform_tameWindow`
  (`:8556`).  Statement takes a FIXED zeroth-order fibre bound `Λ₀` (statement-level
  `{Λ₀} (hΛ₀0 : 0 ≤ Λ₀)`) + a per-`P` pointwise hypothesis
  `hsup : ∀ x, rfns g₀ 0 2 x (P.toSection x) ≤ Λ₀²`; output `K k · (1 + ‖∇ᵏP‖²)`
  with `K` R-free (depends only on `g₀`, `Λ₀`).  Proof is the `:8556` clone with the
  `Cemb·√(a+2)·R` embedding DROPPED (so no `a`, no ball) and the final `htop_le`
  lumping SKIPPED (top jet kept explicit).  The R^{7k} disease was a wrapper
  artifact: `grid_prod_int_le` (`:8154`) is already radius-free-capable — instantiate
  with `R := ‖∇ᵏP‖` (explicit top jet) and fixed `Λ := Λ₀`.

- `boundedFactorGridWindow_integral_radiusFree_topSeparated` — THE GATE.  Sibling of
  `boundedFactorGridWindow_integral_ballUniform_tameWindow_allOrders` (`:14417`) with
  the OPPOSITE constant choice: layers `0..i+1 → Klow i·(1 + ∑_{j≤i+1}‖∇ʲP‖²)`,
  layer `i+2 → Ktop i·‖∇^{i+2}P‖²`, both `Klow`,`Ktop` R-free (`Klow i = ∑_{k<i+3}Kt k`,
  `Ktop i = Kt(i+2)`).  Proof: window ≤ ∑ antidiagonal, integrate termwise via the
  per-order lemma, then distribute + peel top layer `k=i+2` + route low layers by
  `∑ aₖbₖ ≤ (∑aₖ)(∑bₖ)`.

- `rfns_symmS_zero_le_fibreSmall` — DELIVERABLE 1, the public δ₀ fibre-small bridge.
  Thin wrapper over the EXISTING private `rfns_symmS_zero_le_of_ball` (`:3111`, which
  is radius-free despite its name): `gFibreOpBound g₀ (ccTensorBilinSymm g₀ T) δ`,
  `δ ≤ δ₀` ⟹ `rfns g₀ 0 2 x (symmS g₀ T) ≤ ((dim E)·δ₀)²`.  Λ₀ := (dim E)·δ₀.

Design decisions (durable):
1. The GATE integrator is parametrized by ABSTRACT `Λ₀` (weakest-hypotheses), NOT
   by `δ₀`/`gFibreOpBound`.  It needs only the pointwise 0-jet bound, so it is fully
   decoupled from the bridge.  Consumer instantiates `Λ₀ := (dim E)·δ₀` and supplies
   `hsup` via `rfns_symmS_zero_le_fibreSmall` at `P := symmS g₀ T`.
2. The bridge only controls the SYMMETRIC part (`gFibreOpBound` is on the symmetrized
   form), so the honest object is `symmS g₀ T`, not raw `T`.  The committed grids use
   raw `T` (e.g. `bdOmRecover_gridWindow`); the R-free consumer must switch to `symmS T`
   grids (which is the geometrically correct perturbation, `ccTensorBilinSymm g₀ T ↔
   symmS T`).  That switch is the NEXT brick's concern.
3. HONESTY / route-viability: the top-layer subgrid argument GOES THROUGH.  At antidiagonal
   order `i+2`, `grid_prod_int_le` bounds EVERY cell (incl. the top-jet-only cell
   `n=1, e=(i+2)`) by `C·‖∇^{i+2}P‖²` with NO intermediate norm — the constraint
   `∑ eₘ = i+2` forces GN interpolation onto the top jet.  So the capped top layer is
   bounded by the pure top jet.  No resisting term.

Verification status: GREEN.  Targeted module build passed (`Build completed
successfully (9387 jobs)`, 2026-07-26).  `#print axioms` on all three new lemmas =
exactly `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

Fixes found during verification (recorded for future clones of the `:8556`/`:13180`
grid templates):
- The window lemma needs the `letI : MeasurableSpace E/M := borel …; haveI : BorelSpace …`
  block (as `:13180` has) for `integral_mono`; the per-order lemma (cloning `:8556`)
  does not.
- `Finset.single_le_sum` needs its `f` pinned explicitly `(f := fun j => ‖∇ʲP‖²)` or the
  summand stays a metavariable.
- `Finset.range_subset.mpr (by omega)` fed `omega` a metavariable-tainted (real-cast)
  goal; replaced with an explicit `intro k hk; simp only [Finset.mem_range] at hk ⊢; omega`.

## 2026-08-03: MONOLITH SPLIT — this file is now a pure umbrella

**No new mathematics.**  Pure compile-stabilization.  At 15111 lines this module
could no longer be elaborated on this machine: the single-process elaboration
demanded roughly 18 GB against ~16 GB of RAM, BSOD'd the box, and its `.olean`
was deleted and unrebuildable.  Split at section / abstraction seams following
the proven C0Core recipe (`ShortTime/UNIF_EXISTENCE_PLAN2.md` No. 91).

### What this file is now

Only a module docstring plus imports of the fifteen chunk modules under
`CurvatureCoefficientDifferenceJetTower/`.  Lean import transitivity makes the
module path `…CovGrad.CurvatureCoefficientDifferenceJetTower` re-export the whole
API, so **all eleven downstream consumers compile unchanged** — no downstream
import, `open`, or name had to move.

### Recipe (identical to the C0Core split)

1. Each chunk repeats the monolith preamble verbatim: the three `set_option`s,
   both `open` lines, `namespace DifferentialGeometry/Integral/Connection`, the
   eight namespace `open`s, the three `variable` blocks, and the
   `private local instance : CompleteSpace E`.
2. Imports form a **DAG, not a chain**; every chunk imports only what it needs.
   Chunks 1–8 are the linear spine, rooted at `Grid` which carries the original
   22 imports.  `Residual` then hangs off `Envelope` (chunk 6) rather than
   `TsRungs` (chunk 8), because nothing in the residual-integrator region
   references `TsTransport` or `TsRungs`; and `ResidualCells` is a **second root**
   on the original 22 imports alone, which is what keeps the hog
   (`ResidualFlat`, which imports only `ResidualCells`) inside the memory budget.
   `ResidualBase` imports both branches (`TsRungs` + `ResidualFree`) to rejoin
   them.  This is not cosmetic — see the memory section below.
3. `private ` is stripped from the 167 internal declarations, which are wrapped
   in an internal `namespace CurvatureCoefficientDifferenceJetTower` (Lean
   `private` is module-scoped, so cross-chunk helpers had to be promoted).  Each
   chunk `open`s that scope.  The 78 **public** declarations stay at
   `Integral.Connection` level with their exact old names, so the public API is
   byte-for-byte unchanged.
4. Namespace toggles are emitted only between declarations and never across a
   `section`/`end` line, so section nesting stays balanced.

Why the internal namespace rather than promoting to bare `Connection`: a
name-collision scan found `prodTerm_le_antidiagonalTupleGrid` and
`antidiagonalTupleGrid_mul_le` also declared publicly in
`Analysis/Sobolev/AntidiagonalTupleProductGrid.lean` (namespace
`DifferentialGeometry.Combinatorics`, not opened here, so harmless today), and
`iteratedCovGrad_smul_pt` / `_b` are exactly the alias copies queued for the
pending `iteratedCovGrad_smul` dedup.  Containing all 167 in their own scope
keeps `Connection` clean and keeps that dedup unblocked.

### Chunk map

| # | chunk | lines | pub | int | imports | contents |
|---|-------|-------|-----|-----|---------|----------|
| 1 | `Grid` | 1183 | 10 | 20 | *(orig 22)* | Ricci endo fields, order-0 curv-coeff decomposition, `tWindow`/antidiagonal counting |
| 2 | `Lowered` | 1266 | 11 | 27 | Grid | lowered Riemann background difference; conn-difference top-separated + t-grid |
| 3 | `Palatini` | 2257 | 22 | 24 | Lowered | Palatini repr, perturbation-sharp endo, diagonal product grids, mixed bi-contraction |
| 4 | `PairTrace` | 2015 | 5 | 39 | Palatini | `appCcRS` slot algebra, pure double trace, `pairTraceOp`, `pureTrace_split` |
| 5 | `TraceGrid` | 1158 | 2 | 2 | PairTrace | pair-trace difference grid, metric-factor-telescope trace conversion |
| 6 | `Envelope` | 1414 | 12 | 1 | TraceGrid | per-order L2 ball-uniform bounds and tame envelopes |
| 7 | `TsTransport` | 1658 | 1 | 42 | Envelope | `ts*` transport mirrors (cast / domDomCongr / lowering / head transport), RLD rung |
| 8 | `TsRungs` | 2306 | 4 | 10 | TsTransport | top-separated rungs: slot insert, G1 lowering split, curv + Riemann arm-0 coeffs |
| 9 | `Residual` | 191 | 1 | 0 | Envelope | opens `TopSeparatedResidualIntegrator`; ball-uniform tame window |
| 10 | `ResidualCells` | 823 | 0 | 2 | *(orig 22)* | the two product-cell integral lemmas — depend on nothing else in the module |
| 11 | `ResidualFlat` | 214 | 1 | 0 | ResidualCells, ResidualFlatSup, ResidualFlatGN, `Analysis/Sobolev/BoundedFactorGridIntegral` | `boundedFactorGrid_cappedTopLayer_integral_flat` **alone** — the former memory hog, proof-refactored 2026-08-03 |
| 11a | `ResidualFlatSup` | 146 | 0 | 2 | *(orig 22)* | `rfnsIterCont`, `jetSupLow` — pointwise fibre-norm inputs of chunk 11 |
| 11b | `ResidualFlatGN` | 112 | 0 | 1 | *(orig 22)* | `jetGNInterp` — the GN interpolation input of chunk 11 |
| 12 | `ResidualWindow` | 225 | 2 | 0 | ResidualFlat, Residual | all-orders ball-uniform grid windows (flat + tame) |
| 13 | `ResidualFree` | 401 | 2 | 0 | ResidualWindow | radius-free grid integrators, incl. THE GATE |
| 14 | `ResidualBase` | 409 | 2 | 0 | TsRungs, ResidualFree | δ₀ fibre-small bridge, radius-free base-coefficient bound |
| 15 | `ResidualAllOrd` | 439 | 3 | 0 | ResidualBase | all-orders base-coefficient bound, Koszul export |

Two sections had to be reopened across chunk boundaries
(`RiemannLoweredDifference` between chunks 2/3, `TopSeparatedResidualIntegrator`
across chunks 9–14); each continuation re-emits that section's `open`s and its
section-level `set_option backward.isDefEq.respectTransparency false`.

### Two traps worth remembering for the next split

- **A doc comment containing a blank line.**  Walking backwards from a
  declaration to find its attached prelude cannot stop at the first blank line —
  `pureTrace`'s doc comment has an internal blank, so a naive walk lands
  mid-comment and splits it.  Track block-comment depth.
- **A dangling `set_option … in` separated from its command by a blank line.**
  The monolith had one such spot (old line 7138: a duplicated
  `set_option linter.unusedVariables false in` / `set_option maxHeartbeats … in`
  pair, blank line, then the same pair again before the theorem).  Lean accepts
  it, but a boundary placed at the blank line severs the modifier from its
  command.  Absorb backwards past a blank whenever the nearest non-blank line
  above still ends in ` in`.  This was the only chunk that failed its first check.

### Cost and verification

Chunk-by-chunk bottom-up: focused check then targeted module build, single Lean
process, `-LeanThreads 1`.  Chunks 1–8 (the spine) build in 22–60 s each and peak
below about 4 GB.

**Sizing is governed by individual declarations, not by line count.**  The
residual-integrator region needed three passes to get right:

- the first draft kept all 2336 lines of `TopSeparatedResidualIntegrator` in one
  chunk; it had not finished after ten minutes and peaked near 4.8 GB;
- splitting it three ways fixed `Residual` (931 lines, 60 s) but the 803-line
  `ResidualFlat` climbed to **7.5 GB within 65 seconds**, driving free physical
  memory down to 0.22 GB, then plateaued near 6.8 GB for the rest of the file;
- the profile identifies the cause: `boundedFactorGrid_cappedTopLayer_integral_flat`
  alone accounts for the jump from ~3 GB (imports) to ~7.5 GB, and every
  declaration elaborated after it in the same process inherits that high-water
  mark.  It now sits alone in `ResidualFlat` (302 lines) and the rest of the
  region is spread over six further chunks of 191–823 lines.

Isolating the hog was necessary but not sufficient.  Alone in a 302-line chunk it
still ran the machine out of memory (free physical 0.19 GB, then 0.01 GB on a
retry).  Two further passes were needed:

- **Cut its import closure to almost nothing.**  `boundedFactorGrid_cappedTopLayer_integral_flat`
  needs exactly one thing from this module, `cappedTopLayerCell_integral_le`.
  That lemma and its sibling `productTerm_integral_tame_le_ordS` depend on
  nothing in chunks 1–8, so they were pulled out into `ResidualCells`, which
  imports only the monolith's own 22 imports.  `ResidualFlat` then imports
  `ResidualCells` alone.  Measurement: `ResidualCells` (823 lines, *both* heavy
  cell lemmas) builds in 51 s peaking at 3.5 GB — i.e. the ~3.2 GB floor is the
  module's own 22 imports and is irreducible; the chunk `.olean`s are noise
  beside it.
- **Trim working sets immediately before the build** (the standing No. 112
  protocol step).  `EmptyWorkingSet` across all processes returned about 0.5 GB
  of physical memory, and that was the difference: the guarded build then peaked
  at 7.78 GB with free physical bottoming at 0.44 GB — just above the 0.40 GB
  floor — instead of being killed at 0.34 GB.

So `ResidualFlat` sits about 0.05 GB inside the safety margin on this machine.
Anyone rebuilding it should trim first and run nothing else concurrently.

Five durable lessons, all cheap to forget:

- **Profile for the expensive declaration; do not just halve line counts.**  A
  chunk whose cost is concentrated in one theorem does not get cheaper when you
  split it in half.  Do not merge `ResidualFlat` back into its neighbours.
- **Import closure is part of the memory budget.**  A linear chunk chain is the
  easy default but it charges every chunk for everything before it.  Where the
  dependency graph genuinely branches, branch the imports too.
- **Trim before the heavy build.**  `EmptyWorkingSet` over all processes is
  non-destructive (pages go to standby and fault back in on demand); it bought
  0.5 GB the first time, and ~1.3 GB (7.6 → 8.9 GB free) once the watchdog
  processes were shut down too.
- **The watchdog must not be part of the load, and must fail safe.**  Polling
  `Get-CimInstance Win32_OperatingSystem` in a tight loop is not free, and under
  real pressure the CIM call itself throws
  `Not enough memory resources are available`.  A guard that then computes
  `$os.FreePhysicalMemory` from the resulting `$null` reads it as `0` and kills a
  build that was 14 minutes in and already past its peak — which is exactly what
  happened here once.  Sample from ONE cheap background writer, have the guard
  read that log, and treat a missing or stale reading as "no data", never as
  zero.
- **Check the dependency scanner before trusting it.**  The first cut of the
  inter-chunk scan used `([^ ({:\[]+)` to capture declaration names; for a
  declaration whose name ends the line that captures the trailing newline too,
  so every such name silently never matched.  It reported `ResidualFlat` as
  depending on nothing when in fact it calls `cappedTopLayerCell_integral_le`.
  Exclude `\r\n` from the character class, and strip block comments before
  searching for uses.

Against a monolith that wanted ~18 GB, the split is the difference between
unbuildable and routine.

## 2026-08-03 (later): the hog's proof refactor — the driver was one `ring`

Splitting could not save chunk 11.  Alone in a 302-line file with a minimal
import closure, `boundedFactorGrid_cappedTopLayer_integral_flat` still demanded
**≥ 8.7 GB** in a single Lean process (five watchdog kills, peaks
7.58 / 8.04 / 8.66 / 8.43 / 8.25 GB) against a machine whose effective runway
with the session running is about 8.7 GB.  Sizing is governed by individual
declarations; here it turned out to be governed by a single *tactic call*.

The proof was refactored (statement byte-identical, verified by diff) into
`ResidualFlatSup` + `ResidualFlatGN` + the generic
`Analysis/Sobolev/BoundedFactorGridIntegral`, and the section-level
`set_option backward.isDefEq.respectTransparency false` was dropped.  That alone
moved the peak only 8.43 → **8.25 GB**: still killed.

A `sorry`-truncation bisection then measured the body prefix by prefix
(each run ≈ 20 s):

| proof prefix | peak |
|---|---|
| statement + all `set` constants + `refine ⟨Kc, …, ?_⟩` | 3.08 GB |
| + `hΛsup_low`, `hGNv`, `set b`, integrability, `refine ⟨hgrid_int, ?_⟩` | 3.09 GB |
| + `hPT` (the `cappedTopLayerCell_integral_le` application) | 3.09 GB |
| + grid = double sum | 3.08 GB |
| + calc steps 1–3 (termwise bound, constant-sum collapse, `card_filter_le`) | 3.09 GB |
| + calc step 4, `by ring` | **7.95 GB — killed** |

The whole excess was the final `ring`, proving nothing harder than
`A * (B * C) = A * B * C`.  Replacing it with `(mul_assoc _ _ _).symm` brings
the declaration to **3.09 GB focused / 2.86 GB built, 17 s** — a 5 GB drop from
one token.

**Durable lesson: never leave `ring` next to `set`-bound locals.**  `ring`
normalizes by identifying atoms up to reducible defeq, and locals introduced by
`set` are let-bound, so they zeta-unfold during that comparison.  Here the atoms
`gcount i` and `MB i ^ (9 * (i + 2))` unfold through `MB → vol, Lam, Cgn` down to
a `dite` wrapping `Exists.choose` of the Gagliardo–Nirenberg existential, and the
symbolic exponent `9 * (i + 2)` keeps the polynomial machinery from collapsing
the result.  When the goal is a fixed rearrangement, name the lemma
(`mul_assoc`, `mul_comm`, `add_assoc`) instead of calling a normalizer.  Cheap to
check: if a proof step's goal is a one-lemma identity, it should never be the
most expensive step in the file.

Two smaller findings from the same pass:

- The section-level `backward.isDefEq.respectTransparency false` was **not**
  needed by any of the four new declarations, nor by the refactored hog.  It is
  gone from `ResidualFlat`; the other continuations of
  `TopSeparatedResidualIntegrator` still carry it and were not touched.
- The generic grid layer belongs in `Analysis/Sobolev/`, next to
  `Combinatorics.boundedFactorGrid`, as a **new sibling file** — extending
  `BoundedFactorProductGrid.lean` itself would have added Mathlib measure-theory
  imports to a module the whole tree depends on.

Content preservation was checked mechanically, not by eye: all 15051 body lines
of the monolith reappear verbatim and in order across the chunks, and the 245
declarations appear in identical order with identical names.  The generator and
checker are `.codex-scratch/ccdjt-split/{split,verify}.py`, with the pre-split
file kept at `.codex-scratch/ccdjt-split/*.before-split.lean`.
