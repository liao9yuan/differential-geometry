# DeTurckRemainderTameLipschitz

## 2026-07-16 principal coefficient extraction

The duplicate local definition of the complete Ricci--DeTurck top coefficient
was removed.  The oversized legacy assembly now imports the canonical public
definition from `DeTurckTopCoeff.lean`; no new facade was added here.

The Lie C0 field construction has now been extracted to the public
`DeTurckCoefficients/LieCorr0Field.lean` module without a Sobolev-ball or
high-order hypothesis.  The legacy private copy remains here because the
later component proof refers directly to its private construction names.

The remaining low-regularity API gap is narrower but substantial: the exact
component readout identifying that field with the raw order-zero arm and the
top-reanchoring tails.  The final readout depends on roughly sixteen thousand
lines of private normal-form algebra in this file, not only on the nearby
field construction.  A public alias here would violate the agreed module
boundary and would still not provide the no-high-order C3 estimate.  The next
honest extraction must first split that algebra into coefficient-layer modules
below the 3000-line limit.

## 2026-08-03 memory probe — NO hotspot; the weight is DISTRIBUTED

Verification status: **FAILED to build, by resource exhaustion, not by any
proof error.**  Zero errors were reported in any probe; the file simply does
not fit in this machine's ~8.7 GB effective runway.  The file was **not
edited** — no hotspot exists to fix, so nothing was changed.

The brick hypothesis was the `ResidualFlat` precedent: one runaway tactic
(there, a `by ring` under `set`-bound locals) holding several GB.  That
hypothesis is **refuted here.**  A prefix ladder (`sorry`-free truncations at
declaration boundaries, each run under `lake env lean -M <cap>` so a blowup
aborts instead of taking the box down) gives a smooth monotone climb with no
jump anywhere:

| prefix (cut line) | peak lean WS | wall |
|---|---|---|
| 116 — imports/opens only | **3.51 GB** | 24 s |
| 2546 | 4.00 GB | 57 s |
| 2609 | 4.01 GB | 65 s |
| 5079 | 4.25 GB | 105 s |
| 8988 | 4.60 GB | 154 s |
| 12984 | 4.80 GB | 170 s |
| 16002 | 5.30 GB | 186 s |
| 20010 | 5.87 GB | 211 s |
| 23997 | 6.38 GB | 211 s |
| 26340 | 6.57 GB | 227 s |
| 36051 | **> 7.60 GB** (hit cap) | 276 s |
| 46927 (whole file) | ≥ 8.20 GB, still climbing when killed | — |

Two numbers carry the ruling.  First, **the import closure alone costs
3.51 GB** — 40% of the budget is spent before a single line of this file is
elaborated (37 imports, most of the heavy CovGrad/TensorHilbert tree).
Second, the file's own content adds a near-constant **≈ 0.117 GB per 1000
lines** with no spike, projecting a total of **≈ 8.8–9.0 GB**.  That is
0.1–0.3 GB over the wall, which is why this file sits exactly at the
"sometimes builds, usually dies" boundary and why iterative memory-squeezing
plateaued.

Consequence: no local proof repair can help.  A tactic swap of the
`(mul_assoc _ _ _).symm` kind buys tens of MB here, not the ~2 GB of headroom
needed.  **This file needs the split that the 2026-07-16 entry above already
called for**; the measurement now backs that call with numbers.

### Where to cut (data-driven, for the split ruling)

The single best lever is **lines 10276–17800: 187 private `nf_*` normal-form
lemmas, 7.5k lines, containing ZERO geometric types** — verified by grep:
no `SmoothRiemannianMetric`, `SmoothCcTensor`, `TangentSpace`,
`iteratedCovGrad`, `riemannianFiberNormSq`, `appCc`, `unitModel`,
`ccTensorBilin`, `Manifold`, or `ChartedSpace` occurs in that range.  Their
signatures are pure `Fin n → Fin n → ℝ` / `→ Fin n → ℝ` / `→ Fin n → Fin n → ℝ`
index algebra (199/197/197 occurrences) with 20-hypothesis symmetry bundles and
6-fold nested `Finset.sum` rewrite chains.  Moved to a standalone algebra
module they would pay **almost none** of the 3.51 GB geometric baseline —
the same move that made `BoundedFactorGridIntegral` free in the CCDJT refactor.

Other natural boundaries, from the section skeleton: 116–3013 (Lie path-value
layer, pre-section); 3014–5074 (chart-open section); 5075–10275 (`O1Abstract`
namespaces and shells); 26571–30633 (`LieCorr0BoundsA`…`F4`, already cleanly
delimited sections — the cheapest mechanical extraction); 30633–46925 (a 16.3k
line tail carrying no section markers at all).

Sizing: with a 3.51 GB baseline and 0.117 GB/1000 lines, ~4 pieces of ~12k
lines land near 5.0/5.4/5.8/6.2 GB; ~5 pieces of ~9.4k lines land near
4.6–5.8 GB.  Pulling the `nf_*` algebra out first shrinks every remaining
piece and is the only change that lowers the baseline rather than dividing it.

### Reusable technique notes

- `lean -M <megabytes>` (i.e. `lake env lean -M …`) **works and is the right
  probe instrument**: on exceeding the cap Lean aborts with "excessive memory
  consumption detected", so an over-budget prefix costs only the time to reach
  the cap and can never take the machine down.  It does *not* name a source
  position (the message names a component, e.g. `interpreter`), so it is an
  oracle for "did this prefix exceed X", not a locator.
- **Do not trust Lean's streamed stdout as a position signal.**  Under
  `lake env lean` with redirected output the log froze at 12530 bytes while the
  process ran four more minutes and grew 4.3 GB.  Reading that literally
  ("the stall is right after line 2398") pointed at
  `deTurckRicciArm_appCc_graded_ballUniform` (:2546), which a probe then
  cleared at 4.01 GB.  Only prefix probes are trustworthy.
- Peak memory must be measured as the **sum over all `lean`/`lake` processes**.
  A `lake build` runs many module jobs in parallel, so a reported "7.60 GB
  peak" from a chain build is a whole-machine figure and does not by itself
  implicate any single module.
- A guard kill leaves `.lake/codex-locks/lean-elaboration.lock` owned by a dead
  pid; it must be removed by hand (`release -Force -Lake` clears the *Lake*
  lock, not this one).

## 2026-08-03 MONOLITH SPLIT — this file is now a pure umbrella

**No new mathematics.**  Pure compile-stabilization, executing the ruling the
probe above asked for.  All 46927 lines are unchanged in content: every
declaration moved verbatim, statement and proof, together with its
`set_option ... in` prelude.  The pre-split file is kept at
`.codex-scratch/tamelip-split/DeTurckRemainderTameLipschitz.before-split.lean`;
the generator and the mechanical checker are `{analyze,usage,split,verify}.py`
in the same directory.

### What this file is now

Only a module docstring plus imports of the fifteen chunk modules under
`DeTurckRemainderTameLipschitz/`.  Lean import transitivity makes the module
path `…DeTurck.DeTurckRemainderTameLipschitz` re-export the whole API, so all
three downstream consumers (`RHSRefoldTameH2`, `SobolevNonlinearityExistence`,
`ShortTime/LowRegRHSSymm`) compile unchanged.  All **24 public names still
resolve at their original full names** (checked by a `#check @…` scratch file),
and their signature blocks are byte-identical to the pre-split ones.

### Chunk map and measured peaks

Peak = SUM over all `lean`/`lake` working sets during a guarded targeted build,
`-LeanThreads 1`.  Wall includes ~16 s of lake start-up.

| # | chunk | src lines | peak GB | wall s | imports | contents |
|---|-------|-----------|---------|--------|---------|----------|
| 1 | `Base` | 4958 | 4.45 | 89 | *(orig 37)* | fibre-norm inputs, `deTurckRHSArmG0`, chart Lie layer |
| 2 | `O1Alg` | 1307 | **1.40** | 8 | *(7 Mathlib)* | `O1Abstract` order-one index algebra — **tensor-free** |
| 3 | `LieValue` | 3555 | 4.55 | 73 | Base, O1Alg | `LieCorr0Joint`/`Eval`/`Value` |
| 4 | `M0Defs` | 810 | **1.51** | 13 | *(7 Mathlib)* | `M0Abstract.Defs` — **tensor-free** |
| 5 | `M0Gen1` | 7046 | **2.62** | 39 | M0Defs | `M0Abstract.Gen` part 1 (`nf_*`) — **tensor-free** |
| 6 | `M0Gen2` | 7514 | **2.48** | 23 | M0Gen1 | `M0Abstract.Gen` part 2 + `m0_master` — **tensor-free** |
| 7 | `Master` | 1216 | 3.76 | 41 | LieValue, M0Gen2 | `LieCorr0MasterValue` |
| 8 | `BoundsA` | 1860 | 4.14 | 49 | Master | `LieCorr0BoundsA`–`D` |
| 9 | `BoundsB` | 2244 | **5.26** | 186 | BoundsA | `LieCorr0BoundsE1`–`F4` (the heaviest chunk) |
| 10 | `TameL2` | 2894 | 4.34 | 57 | BoundsB | graded three-arm ball-uniform coefficient bounds |
| 11 | `TameJet` | 2651 | 4.35 | 97 | TameL2 | supercritical jet embedding, covariant-`L²` tame chain |
| 12 | `Refold` | 2387 | 4.43 | 49 | TameJet | path-integral triple refold, arm-1 envelopes |
| 13 | `Dim1` | 2100 | 4.09 | 57 | Refold | one-dimensional degeneracies, fibre-norm budget |
| 14 | `Kernel` | 2606 | 4.14 | 65 | Dim1 | raised-slot / refold-kernel operator bounds |
| 15 | `Envelope` | 3646 | 4.36 | 65 | Kernel | high-order arm-0 envelopes, curvature-refold coeff sup |
| — | umbrella | 35 | 3.39 | 13 | all 15 | re-export only |

Worst single Lean process: **5.26 GB** (was ≥ 8.20 GB and still climbing when
the monolith was killed).  Whole tree, cold, serially: about 15 minutes.

### The lever that actually worked

The two index-algebra layers `O1Abstract` (1.3k lines) and `M0Abstract` (15.4k
lines) contain **zero geometric types**, so they were given modules with seven
Mathlib imports instead of the monolith's 37.  16.7k of the 46.9k lines — 36% of
the file — now pay a ~1.3 GB baseline instead of the 3.51 GB geometric one, and
elaborate in 83 s total.  This is the same win as `BoundedFactorGridIntegral` in
the CCDJT refactor, and the only move available that *lowers* the baseline
rather than dividing it.  Their namespaces (`…IntrinsicSpectral.O1Abstract`,
`…M0Abstract`) are unchanged, so the call sites in `Master` are untouched.

### Recipe and the three traps

1. Each chunk replays the scope context that was live at its first line —
   computed mechanically (`analyze.py`), not by hand: the two global `open`s,
   the eleven namespace `open`s, the three `variable` blocks, the
   `private local instance instCompleteSpaceE_tame`, any *later* namespace-level
   `open`/`set_option` (there are five such spots: `:34286`, `:34578`, `:35476`,
   `:35640`, `:39592`), and every enclosing `section` with its own `open`s and
   `set_option`s.  No `set_option` value was invented; all move with their scope.
2. **`private` was stripped only where it had to be.**  A cross-chunk usage scan
   (`usage.py`, comments stripped first) found that of 1076 private
   declarations only **262** are referenced from another chunk.  Those at
   `IntrinsicSpectral` level are wrapped in the internal namespace
   `DeTurckRemainderTameLipschitz`, which every geometric chunk `open`s; the
   ones already inside `O1Abstract`/`M0Abstract` keep their place.  The other
   814 stay `private`, so their elaboration environment is byte-identical to the
   monolith's.
3. Collision scan before promoting: 64 of the private names are also declared
   publicly elsewhere in the tree (`LieCorr0Core`, `LieCorr0LowJet`,
   `LieCorr0KappaLow`, `DeTurckCoefficients.LieCorr0NF`).  Seven of those —
   `lc0Kappa`, `lc0PbLow`, `lc0IVPerm`, `lc0VFlat`, `lieCorr0Field`,
   `lc0KappaField`, `lc0PbLowField` — sit in the *bare* `IntrinsicSpectral`
   namespace, where an imported homonym would out-rank an `open`ed internal
   namespace and silently change resolution.  The import closure was computed
   (1247 project modules) and **none of those modules is in it**, so the
   promotion is safe.  Recompute this if the imports ever change.

Traps that actually bit (all plumbing, all fixed by plumbing):

- **An `open` emitted inside the internal namespace expires at the next `end`.**
  The first draft toggled `namespace DeTurckRemainderTameLipschitz` around
  promoted declarations without forcing context commands out of it; the section's
  `open …(deTurckLieWEndo … tensor0SProdKappaFib …)` at `:6993` landed inside a
  toggle and 30 identifiers went unknown 300 lines later.  Fix: `open`,
  `variable`, non-`in` `set_option`, `attribute` and `local instance` are pinned
  to the level they had in the monolith.
- **`attribute [-instance] … in` is a one-command modifier here** (both
  occurrences, `:1231` and `:33532`), so it travels with its declaration and must
  *not* be replayed in a chunk preamble.
- **Chunk starts must absorb a `set_option … in` chain separated from its
  declaration by a blank line** (`:40671`, `:43278`) — the same trap the CCDJT
  split recorded.

### Content preservation (mechanical, not by eye)

`verify.py`: all 46794 body lines of the monolith reappear verbatim and in
order across the fifteen chunks; the 1100 declarations appear in identical order
with identical names; `private` was removed on exactly the 262 promoted names
and nowhere else; every chunk is section/namespace balanced; no declaration hides
in any generated header.

### Verification status

GREEN.  All fifteen chunks and the umbrella built (targeted, guarded, serial),
then the frozen `+LowRegOpJetWindows` chain (9593 jobs) and all three direct
downstream consumers (9730 jobs) built green with **no source change on their
side**.
`#print axioms` on four moved public endpoints
(`deTurckRemainderDiff_iteratedCovGradSum_ballLipschitz`,
`deTurckArmDiff_supercritical_pointwise_jet_le_lowerWindow`,
`appCc_topOrder_l2_twoArm_mixed_ballUniform`,
`exists_deTurckRHSArmDiff_zero_canonicalTop_curvatureRefold_coeffSup_jetEnvelope_of_symm`)
= exactly `[propext, Classical.choice, Quot.sound]`.  The file's four textual
`sorry` hits are all prose; note that the doc comment of
`rawTensorConnLapSmooth_fiberNormSq_le_secondCovGrad_jet` (`:149` pre-split)
still says "its body is `sorry`" — **that sentence is stale**, the declaration
has a real proof through `rawConnLap_fiberNormSq_le_secondCovGrad`, and the
census confirms no `sorryAx` reaches the endpoints.  Style warnings inherited
from the monolith (`linter.style.show`, `unusedVariables`) were left untouched,
since every declaration had to move verbatim.
