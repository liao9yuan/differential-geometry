# Rm04Producer — discharging the `Rm04Reduction` inputs

**Status: all three steps CLOSED.**  Step 2's single named honest input
(`hmetricReg`) was discharged on 2026-07-26 by ruling R11 — see
`Evolution/Rm04ProducerTail.lean` for the unconditional per-tail endpoints.

0 `sorry`, 1195 lines.  Targeted build `+…Evolution.Rm04Producer` GREEN (3783 jobs),
warning-clean.  `#print axioms` on every public endpoint: `propext`, `Classical.choice`,
`Quot.sound` only.

## Public API

| Declaration | Content |
|---|---|
| `rmComp S x₀` / `nab2RmComp S x₀` | canonical lowered-`Rm` and `∇²Rm` component arrays at the frame centred at `x₀` |
| `rm04SymmOfSol` | `Rm04Symm` — the four algebraic curvature symmetries |
| `rmSecondAt` | `SecondBianchiAt (nablaRm04Field S t x)` at every `t`, `x` |
| **`rm2Bianchi`** | **the once-differentiated second Bianchi identity** (tensor level) |
| `rm2SymmAt` | the three algebraic symmetries inherited by `nabla2Rm04Field` |
| `n2RicTr` / `ricTr` | `∇²Ric` (resp. `Ric`) is the first metric trace of `∇²Rm` (resp. `Rm`) |
| `rmRicciId` | the `(0,4)` Ricci identity in coordinate components at the centre |
| `rmRaise` | `christoffelCurvCoeffAt = Σ_q g^{dq} Rm04_{abcq}` at the centre |
| **`rm04LapInOfSol`** | the whole `Rm04LapIn` package (7/7 fields) |
| **`ricRicciIdAt`** | the `s = 2` Ricci identity for `Ric` (the analogue of `rm04_ricciIdentityAt`) |
| **`ricCommOfSol`** | `RicCommAt` in components — the last static input |
| **`rm04StaticOfSol`** | `rm04VarRHS = ΔRm − 2(B−B+B−B) − drift`, **unconditional** on `S`/`hS` |
| **`rm04Evol_at`** | **`∂ₜRm = ΔRm − 2(B−B+B−B) − drift` at the centre**, conditional on `gInvDt`/`hmetricReg` only |
| `coordBasisAt`, `rm04Fam`, `rm04LapFam`, `rm04BFam`, `ricUpFam` | the per-point-centred lane families |
| **`rm04EvolFam`** | **`hev`** — `Riemann04BTensorWithRicciDriftEvolutionInFrameOn`, conditional on the per-centre `hmetricReg` family |
| **`rm04Fam_real`** | **`hreal`** — unconditional |
| **`rm04LapFam_real`** | **`hL`** — unconditional |

Downstream, in `Evolution/Rm04ProducerTail.lean`:

| Declaration | Content |
|---|---|
| **`rm04EvolTail_at`** | `rm04Evol_at` on a positive-time tail, **unconditional** |
| **`rm04EvolFamTail`** | **`hev` on a positive-time tail, unconditional** |

## Step 1 — `bianchi2` and `hcomm`.  DONE

### `bianchi2` (the only genuinely missing mathematics)

The route the original brief sketched (linearity of `totalNabla0S` in the differentiated
field + `domDomCongr` naturality) was **not** needed:

1. `canRmSecond` (`Geometry/Connection/LeviCivita/Curvature/Realized.lean:542`) gives
   `SecondBianchiAt` for the canonical Levi-Civita `∇Rm` **non-existentially at every
   point**; the bridge to `nablaRm04Field` is the `canBianchiAt` `simpa` unfolding
   (`rmSecondAt`, 8 lines).
2. Restate it in **slot-function form**: `α u + α (u ∘ rotA) + α (u ∘ rotB) = 0` for the two
   3-cycles `rotA, rotB : Equiv.Perm (Fin 5)` fixing slots 3,4 (`secondCyc`).  This is the
   key move — it makes the correction sums reindexable.
3. `nabPerm`: apply `nabla0SFun_eval_smooth_slots` to `V ∘ σ` and **reindex the connection
   corrections so that the differentiated field, not its slot position, is the summation
   variable** (`Function.update_comp_equiv` + `Equiv.sum_comp`).
4. `nabCyc`: sum over `σ ∈ {1, rotA, rotB}`.  Leading terms sum to `extDerivFun 0 = 0`;
   after step 3 the corrections regroup as `Σ_c (cyclic sum at U_c) = 0`.
5. `rm2Bianchi`: smooth sections through the given vectors, `totalNabla0SFun_apply_section`,
   then `nabCyc`.

≈145 lines.  **No new Tensor-layer API.**

### `hcomm` (`ricCommOfSol`)

Built as the planner predicted.  `ricRicciIdAt` is `rm04_ricciIdentityAt` at `s = 2`: the
`Nabla20SRealizesAt` witness is *not* the one buried in `coordCommAt` (that one is a local
`let` inside a 200-line theorem and unusable) — instead `solNabRic`/`solNab2RicF` are the
plain `totalNabla0S` tower for `S.ricci t`, whose realizations come free from
`totalNabla0S_realizes`, mirroring `nablaRm04Field_realizes`.  Then `ricCommOfSol` is
`rmRicciId` at `s = 2`: `curvatureAction0SAt_eq_rm04`, `Fin.sum_univ_two`, two
`Function.update → vec2` conversions, `rmRaise` to reintroduce `christoffelCurvCoeffAt`,
`sumSwap` + `gInv` symmetry.

With this, `rm04StaticOfSol` lost its `hcomm` hypothesis: **the static identity is now
unconditional on `S`/`hS`.**

## Step 2 — the time half.  CLOSED on positive-time tails (ruling R11 applied)

`rm04Evol_at` delivers the full evolution at the centre from `S`/`hS` **plus** `gInvDt` and
`hmetricReg`.  The other four packages of `rm04Var_of_sol` discharge for free:
`coordNab2Reg` (hypothesis-free), `coordGammaMix ∘ coordGammaEvol ∘ coordMetricMix ∘
coordMetricDeriv` (a single nested term, no `simpa` needed), `rm13OfSol`, `connCurvOfSol`.

### The blocker — RESOLVED by ruling R11 (option A, implemented 2026-07-26)

`InverseMetricDerivativeComponentsOn` is kept (BlackBox still uses it, with
`Set.univ`), and the two structures now carry the `u`-local
`InvMetricDerivLocal` instead.  `InverseMetricDerivativeComponentsOn.toLocal` is
the one-line converter.  The standalone consumers
`inverseMetric_derivative_row_eq` (`Metric/Covariant.lean`) and
`inverseMetricEvolutionEquationInFrame_of_inverse_components`
(`Metric/Evolution.lean`) were weakened to the local predicate as well — their
proofs only ever used the hypothesis at the in-scope `hx : x ∈ u`.  All four
consumer sites plus both constructors adapted mechanically; **zero breakage
anywhere else in the tree.**

The discharge that this unlocks is `tailCoordFrameReg`
(`Metric/TailFrameRegularity.lean`), built from
`MetricFrameSpacetimeRegularityInFrameOnLocal.congrInv` (`Metric/Basic.lean`) +
`coordInvLocal` + the new `coordInvDerivLocal`/`coordInvDt`
(`Metric/InverseSmooth.lean`).  The consuming endpoints are in
**`Evolution/Rm04ProducerTail.lean`**: `rm04EvolTail_at` and `rm04EvolFamTail`
take `S`/`hS` on `(α, ω)`, a tail `[t₀, ω)` with `α < t₀`, and nothing else —
`hev` is now unconditional per tail.

The historical analysis is kept below for the record.

### The blocker as originally diagnosed

`MetricFrameSpacetimeRegularityInFrameOnLocal S gInv gInvDt frame u` has a field that is
**not `u`-local**:

```
inverseMetricDerivative : InverseMetricDerivativeComponentsOn gInv gInvDt
  ≡  ∀ t (x : M) i j, HasDerivWithinAt (fun s ↦ gInv s x i j) (gInvDt t x i j) D.carrier t
```

— quantified over **all** `x : M`, not over `x ∈ u`.  `localFrameInv` is *designed* around
this: its definition carries an `if hx : x ∈ u then … else 0` cut-off, so off `u` the
function is constant and `localFrameInv_time` (`Metric/LocalFrameInverse.lean:97`) proves
`ContDiffOn ℝ ∞ (fun t ↦ localFrameInv … t x i j) K` **for every `x`** while only assuming
metric smoothness on `u`.  `coordInv` (`Basic/RicciNorm.lean:157`) has **no cut-off**: it is
`inverseMetricFlatModelInChart_component (S.family.metric t) x₀ i j (extChartAt I x₀ x)`, and
off the coordinate-frame domain `extChartAt I x₀ x` leaves the chart target, so nothing is
known about it — `coordInvSmooth` only covers `D.regular ×ˢ coordinateFrameSet x₀`.

Grep-verified: there is **no** producer anywhere of `MetricFrameTimeRegularityInFrameOnLocal`
or `MetricFrameSpacetimeRegularityInFrameOnLocal` with `coordInv`, and **no** lemma anywhere
about time-regularity of `coordInv` (`fun t ↦ coordInv …`).

**Consequence: the planned `localFrameInv → coordInv` bridge cannot exist as an equality.**
The two arrays genuinely differ off `u` (0 versus chart junk), and the field that needs
transporting is precisely the one quantified off `u`.  Restricting to a positive-time tail
fixes the *other* mismatch (`frameMetricSpacetimeSmooth` on `D.carrier ×ˢ u` versus
`hS.smoothMetric.frameCompSmooth` on `D.regular ×ˢ u`) but does nothing for this one.

**Two design options, both touching files outside this one — planner's call:**

- **(A) Make the field `u`-local.**  Weaken `InverseMetricDerivativeComponentsOn` (or add a
  `…On u` variant used by `MetricFrameTimeRegularityInFrameOnLocal`) to `∀ x ∈ u`.  This is
  the mathematically honest shape — every other field of the structure is already `u`-local —
  and then `coordInvSmooth` discharges it directly on the tail.  Cost: `Metric/Basic.lean`
  plus the `localFrameInv`/tail producers that currently prove the stronger form (they would
  still prove the weaker one).
- **(B) Build global time-regularity for `coordInv`.**  Provable *in principle*: the only
  `t`-dependence is through `(S.family.metric t).inner q` at the fixed point
  `q = (extChartAt I x₀).symm y`, and `ContinuousLinearMap.inverse` is smooth at invertible
  maps.  But it needs the trivialization at `x₀` to be a fibrewise linear iso *off* its base
  set, for which there is no API.  Substantially more work than (A) and of no other use.

Recommendation: (A).  Note that under (A) the tail restriction is still needed for
`frameMetricSpacetimeSmooth`, so `rm04Evol_at`/`rm04EvolFam` would be instantiated at
`S.timeRestrict (closedOpen t₀ ω)`; their statements are already `D`-generic, so no change
here is required — only the discharge of `hmetricReg`.

**Outcome:** (A) was ruled and implemented; the prediction held exactly.  Nothing
in this file changed — the tail instantiation lives in `Rm04ProducerTail.lean`,
which had to be a separate module for an instance-spine reason, not a
mathematical one (see that file's `.md`).

## Step 3 — lane packaging.  ALL THREE DELIVERED

- `coordBasisAt y` = the coordinate frame at `y` read at its own centre as a `Module.Basis`;
  `coordBasisAt_coe` is the `@[simp]` evaluation.  **No chart plumbing was needed** —
  `IsLocalFrameOn.toBasisAt` already does it, ~6 lines total.
- `rm04Fam` / `rm04LapFam` / `rm04BFam` / `ricUpFam`: the per-point-centred families.
- **`hreal` = `rm04Fam_real`** (unconditional): one `simp`.
- **`hL` = `rm04LapFam_real`** (unconditional): `roughLap0SField → covDiv0SField →
  metricTraceFirstTwoField_apply → metricTraceFirstTwo0STensor_apply →
  metricTraceFirstTwo0SAt_eq_sum_basis`, then the identification
  `metricNabla0S g (metricNabla0S g (S.base.rm04 r)) y v = nabla2Rm04Field S r y v`, which is
  **`rfl`** (both are the same `totalNabla0S` tower once `SolutionFamily.connection` and
  `metricCov` unfold).  Stated with `vec4 (coordBasisAt y i) …`; the lane's
  `frameVec4 (fun m z ↦ coordBasisAt z m) y i j k l` unfolds to exactly that.
- **`hev` = `rm04EvolFam`**: conditional on the per-centre family
  `∀ y, MetricFrameSpacetimeRegularityInFrameOnLocal S (coordInv S y) (gInvDt y) …` — i.e. on
  the *same* single honest input as `rm04Evol_at`, applied at every centre.

`hcont`/`hPDE` are lane-side and were not attempted, as instructed.

## New imports

Two: `Geometry.Curvature.CurvatureActionLower` (for `curvatureAction0SAt_eq_rm04`) and
`Geometry.Flow.RicciFlow.Evolution.ForwardUniqueRmDiff` (for `roughLap0SField`,
`covDiv0SField`, `metricNabla0S`).  Both acyclic; the build went 3780 → 3783 jobs.

**Layering note for the planner:** `roughLap0SField`, `covDiv0SField` and `metricNabla0S` are
pure metric operators with zero forward-uniqueness content, currently misfiled in
`Evolution/ForwardUniqueRmDiff.lean`.  Their canonical home is
`Geometry/Operator/RoughLaplacian.lean`, next to `metricTraceFirstTwo0SAt` and
`metricTrace0S2InBasis`, which they already consume.  Moving them would remove the second
import above and undo the producer→lane layering inversion.

## Relocation TODOs

1. `rotA`/`rotB`/`vec5_rotA`/`vec5_rotB`/`vec5_self`/`secondCyc`/`nabPerm`/`nabCyc` are
   manifold-generic `(0,5)` covariant-derivative facts.  `nabPerm`/`nabCyc` belong next to
   `nabla0SFun_eval_smooth_slots` in
   `Tensor/RSTensor/NablaOnTensors/Regularity/Tensor0S.lean`, generalized from `Fin 5` to
   `Fin s` and from a 3-cycle to an arbitrary finite family of permutations; `secondCyc` and
   the `vec5_*` conversions belong in `Geometry/Curvature/Bianchi.lean`.
2. `Rm04LapIn.n2RicSym` is **redundant**: it is derived here from `n2RicTrace`, `n2RmPair`,
   `n2RmSwap12` and `gInv` symmetry.  Consider dropping the field from the structure.
3. `sumSwap`/`sumMulPair` are generic finite-sum reindexing helpers used by both `rmRicciId`
   and `ricCommOfSol`; they belong wherever the `Rm04Reduction` algebra layer lands.
4. At 1195 lines the file is still under the 3000-line limit but has three distinct layers
   (differentiated Bianchi / component packages / lane families).  A split at the
   `### The (0,2) Ricci identity` and `## Per-point-centred global families` headings is the
   natural boundary when it next grows.

## Lessons

- **Grep `Geometry/Curvature/CurvatureActionLower.lean` before expanding a curvature action by
  hand.**  `curvatureAction0SAt_eq_rm04` gives the fully component-level form with an
  arbitrary basis and `gInv`; the invariant `cotangentSharp_gen`/`oneFormAtSlot0S` version
  (`RmRaisingBridge.lean:172`) is much more painful in components.  This one lemma carried
  both `rmRicciId` and `ricCommOfSol`.
- **`exact` between two large defeq terms is a kernel wall.**  `rm04EvolFam`'s first proof
  ended in `exact h` where `h` and the goal differed only by unfolding `rm04LapFam`/`rm04Fam`
  and reducing `m 0` — it hit a *kernel* `deterministic timeout` after 360 s.  Replacing it
  with `simpa only [<the small defs>, <four `m q = …` rfl-lemmas>] using h` made the same
  declaration check in 16 s.  When a producer family and its centre-specific expansion are
  defeq but not syntactically equal, drive the match with `simp only` on the small defs, never
  with `exact`.
- `u ∘ (σ * σ)` for `σ : Equiv.Perm` elaborates **inconsistently** — `⇑(σ * σ)` in one
  declaration, `⇑σ * ⇑σ` (`Pi.mul`!) in the next, with a confusing "pattern not found".  Give
  the square its own named `Equiv.Perm` definition.
- The `simpa [SolutionOn.family, SolutionFamily.connection, SolutionFamily.rm04, metricCov,
  metricRm04, …]` incantation from `canBianchiAt` transports **any** `can*` lemma from
  `Realized.lean` to the solution's objects, and absorbs differing regularity witnesses by
  proof irrelevance.  Four bridges (`rmSecondAt`, `rm2SymmAt`, `n2RicTr`, and the `hnab` of
  `rm04LapFam_real` — the last one is plain `rfl`) were one-shot green with it.
- A private `def` in another module can still be *used*: re-declare it verbatim locally and
  bridge with `simpa only [myCopy] using theOtherTheorem` (`solNabRic`/`solNab2Ric` versus
  `IntrinsicDerivation.nablaRicField`; `HamiltonBaseProducer.lean:116` does the same).
- Lemmas from `Geometry/Operator/RoughLaplacian.lean` and `Tensor/RSTensor/MetricTrace/` need
  the `DifferentialGeometry.Integral.Connection.` prefix here even though sibling lane files
  use them bare — those files `open` the namespace, this one does not.
- Whole-file check ≈ 17 s.  No `fin_cases` blowup (all enumerations are over `Fin 2/4/5/6`
  slot maps, never over `CoordinateIdx`).
