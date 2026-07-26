# Rm04Producer — discharging the `Rm04Reduction` inputs

**Status: outcome B.**  Work item 1 (`bianchi2`) **CLOSED**.  Work item 2 **static half
closed**, time half not started.  Work item 3 (global packaging) **not started**.

0 `sorry`, 805 lines.  Targeted build `+…Evolution.Rm04Producer` GREEN (3780 jobs),
warning-clean.  `#print axioms` on every public endpoint: `propext`, `Classical.choice`,
`Quot.sound` only.

## Public API (what a consumer gets from `S`/`hS` alone)

| Declaration | Content |
|---|---|
| `rmComp S x₀` | canonical lowered-curvature `FourComp` array, `vec4`-written |
| `nab2RmComp S x₀` | canonical `∇²Rm` component array, `n2Rm a b c d e f = (∇_a∇_b Rm)_{cdef}` |
| `rm04SymmOfSol` | `Rm04Symm (rmComp …)` — the four algebraic curvature symmetries |
| `rmSecondAt` | `SecondBianchiAt (nablaRm04Field S t x)` at **every** `t`, `x` |
| **`rm2Bianchi`** | **the once-differentiated second Bianchi identity** (tensor level) |
| `rm2SymmAt` | the three algebraic symmetries inherited by `nabla2Rm04Field` |
| `n2RicTr` | `∇²Ric` is the first metric trace of `∇²Rm`, at the centre |
| `ricTr` | `Ric` is the first metric trace of `Rm`, at the centre |
| `rmRicciId` | the `(0,4)` Ricci identity in coordinate components at the centre |
| `rmRaise` | `christoffelCurvCoeffAt = Σ_q g^{dq} Rm04_{abcq}` at the centre |
| **`rm04LapInOfSol`** | **the whole `Rm04LapIn` package (7/7 fields)** |
| **`rm04StaticOfSol`** | **`rm04VarRHS = ΔRm − 2(B−B+B−B) − drift`, conditional on `hcomm` only** |

## Work item 1 — `bianchi2`, the only genuinely missing input.  DONE

The route the task brief sketched (linearity of `totalNabla0S` in the differentiated field
+ `domDomCongr` naturality) was **not** needed.  A cheaper route exists and is what landed:

1. `canRmSecond` (`Geometry/Connection/LeviCivita/Curvature/Realized.lean:542`) gives
   `SecondBianchiAt` for the canonical Levi-Civita `∇Rm` **non-existentially at every
   point**.  The bridge to the solution's `nablaRm04Field` is the same
   `simpa [SolutionOn.family, SolutionFamily.connection, SolutionFamily.rm04, metricCov,
   metricRm04]` unfolding that `canBianchiAt` uses (`rmSecondAt`, 8 lines).
2. Restate `SecondBianchiAt` in **slot-function form**: `α u + α (u ∘ rotA) + α (u ∘ rotB)
   = 0` for the two 3-cycles `rotA, rotB : Equiv.Perm (Fin 5)` fixing slots 3,4
   (`secondCyc`).  This is the key move — it turns a 5-argument identity into a statement
   about one slot map and makes the correction sums reindexable.
3. `nabPerm`: apply `nabla0SFun_eval_smooth_slots`
   (`Tensor/RSTensor/NablaOnTensors/Regularity/Tensor0S.lean:651`) to the permuted section
   family `V ∘ σ` and **reindex the connection-correction sum** so that the *differentiated
   field*, not its slot position, is the summation variable:
   `Σ_a α(update (f∘σ) a (D V_{σa})) = Σ_c α((update f c (D V_c)) ∘ σ)`, via
   `Function.update_comp_equiv` + `Equiv.sum_comp`.
4. `nabCyc`: sum `nabPerm` over `σ ∈ {1, rotA, rotB}`.  The leading `extDerivFun` terms sum
   to `extDerivFun 0 = 0` (`extDerivFun_add` twice, `extDerivFun_zero`).  After the
   reindexing of step 3 the corrections regroup as `Σ_c (cyclic sum at U_c) = Σ_c 0 = 0`.
5. `rm2Bianchi`: pick smooth sections through the given tangent vectors
   (`ContMDiffSection.exists_eq_at_gen`), convert `nabla2Rm04Field` to `nabla0SFun` by
   `totalNabla0SFun_apply_section`, and apply `nabCyc`.

Total ≈ 145 lines including the permutation scaffolding.  **No new Tensor-layer API was
needed** — `nabla0SFun_add` / `domDomCongr` naturality were never used.

### Relocation TODO (planner ruling R10)

`rotA`/`rotB`/`vec5_rotA`/`vec5_rotB`/`vec5_self`/`secondCyc`/`nabPerm`/`nabCyc` are
manifold-generic `(0,5)` covariant-derivative facts with no Ricci-flow content.  `nabPerm`
(the permuted-slot evaluation with the reindexed correction sum) and `nabCyc` (cyclic
vanishing propagates through `∇`) belong next to `nabla0SFun_eval_smooth_slots` in
`Tensor/RSTensor/NablaOnTensors/Regularity/Tensor0S.lean`, generalized from `Fin 5` to
`Fin s` and from a 3-cycle to an arbitrary finite family of permutations.  `secondCyc`
and the `vec5_*` conversions belong in `Geometry/Curvature/Bianchi.lean` next to
`SecondBianchiAt`.  Left here so the brick stays one reviewable file.

## Work item 2 — full discharge at the centre.  STATIC HALF DONE, TIME HALF NOT STARTED

`rm04StaticOfSol` discharges **all** of `rm04Var_eq_uhl`'s inputs from `S`/`hS` except one:

| input | discharged by |
|---|---|
| `hsym` | `rm04SymmOfSol` |
| `hgi` | `coordInvSymmOn` (pre-existing) |
| `hricsym` | `coordRicSymmOn` (pre-existing) |
| `hcon` | `coordInvLocal … .2` (pre-existing `InvMetricLocal`, second conjunct) |
| `hraise` | **`rmRaise`** (new) |
| `hRup` | `rfl` at `ricciOneUpCompInFrame S (coordInv S x₀) (coordinateFrameAt x₀)` |
| `hin` | **`rm04LapInOfSol`** (new) |
| `hcomm : RicCommAt` | **NOT DISCHARGED — the remaining static frontier** |

### `Rm04LapIn` field by field (all proved)

- `bianchi2` ← `rm2Bianchi` at frame vectors.
- `ricciId` ← `rm04_ricciIdentityAt` (`Evolution/RmRealizationBridge.lean:539`) rewritten by
  **`curvatureAction0SAt_eq_rm04`** (`Geometry/Curvature/CurvatureActionLower.lean:49`),
  which is the *component* form of the curvature action and was the find that made this
  field cheap — no `cotangentSharp`/`oneFormAtSlot0S` basis expansion is needed.  Then
  `Fin.sum_univ_four`, four `Function.update → vec4` conversions, `sumMulPair`, and a
  single `Finset.sum_comm` + `gInv` symmetry.
- `ricTrace` ← `ricciFirstTraceAt_of_rm13_section` (`Geometry/Curvature/Components/RicciTrace.lean:232`)
  at `hframe.toBasisAt hx₀`, fed by `ricciTraceOfSol` + `solution_rm04LowersRm13At` +
  `coordInvSymmOn`.
- `n2RicTrace` ← `canNabla2RicTrace` (`Realized.lean:1068`) chained with
  `coordNab2Ric_eq_nabla2RicField`.  The latter mentions the **private** `nabla2RicField`,
  so this file re-declares `solNabRic`/`solNab2Ric` verbatim and bridges with
  `simpa only [solNab2Ric, solNabRic]` — the same trick `HamiltonBaseProducer.lean:116-146`
  uses.
- `n2RmSwap12`, `n2RmPair` ← `canRm2Symm` conjuncts 2 and 3, via `rm2SymmAt`.
- `n2RicSym` ← **derived**, not an independent producer: it follows from `n2RicTrace`,
  `n2RmPair`, `n2RmSwap12` and `gInv` symmetry (swap the two trace indices, use pair
  symmetry then swap12 then the derived swap34).  So `Rm04LapIn.n2RicSym` is redundant given
  the other fields; worth removing from the structure if the planner wants a tighter package.

### What blocks the rest of work item 2

**(a) `hcomm : RicCommAt`** — the `(0,2)` Ricci identity in components:
`n2Ric j i k l − n2Ric i j k l = Σ_p Rm13_{ijkp} Ric_{pl} + Σ_p Rm13_{ijlp} Ric_{kp}`
with `Rm13 = christoffelCurvCoeffAt` and `n2Ric = coordNab2Ric S x₀ t x₀`.
The route is the *exact analogue* of `rmRicciId` at `s = 2` with `alpha = S.ricci t`:
apply `curvatureAction0SAt_eq_rm04` at `s = 2`, then convert `Σ_p Σ_q g^{pq} Rm04_{ijkq}
Ric_{pl}` back to `Σ_p Rm13_{ijkp} Ric_{pl}` using `rmRaise`.  **The one missing ingredient
is a `Tensor0SRicciIdentityAt (S.base.rm13 t) (S.ricci t x₀) (solNab2Ric S t x₀)`
producer** — the `s = 2` analogue of `rm04_ricciIdentityAt`.  `Evolution/Ricci/` has only
the *traced* commutator (`coordCommAt` → `RicciContractedCommutatorsInFrameOnLocal`), not
the raw one.  Estimated ≈ 60 lines of Ricci identity plumbing + ≈ 60 lines mirroring
`rmRicciId`.  Classification: **missing groundwork/API**, routine.

**(b) `hmetricReg : MetricFrameSpacetimeRegularityInFrameOnLocal` for `coordInv S x₀`** —
the time half (`rm04Var_of_sol`).  **The `coordMetricDeriv`/`coordMetricMix` route
recommended in the brief does NOT compose**: those produce
`MetricCovDerivDerivativeComponentsInFrameOnLocal`, a different predicate, and
`coordRicciEvol` (the "architectural gold standard") never builds `hmetricReg` at all — it
routes through `ricciEvolCore`, which takes `hGamma : ChristoffelEvolutionEquationInFrameOn`
instead.  Grep-verified: the **only** producers of
`MetricFrameSpacetimeRegularityInFrameOnLocal` from a solution are `tailFrameSpaceReg`
(`Evolution/Metric/TailFrameRegularity.lean:74`) and `tailChristoffelReg`
(`Evolution/Connection/TailChristoffel.lean:144`), both on a strictly positive-time tail and
both with `localFrameInv` as the inverse family.  The tail is *structurally* required: the
`frameMetricSpacetimeSmooth` field asks for joint `(t,x)` smoothness on `D.carrier ×ˢ u`,
while `hS.smoothMetric.frameCompSmooth` only gives it on `D.regular` — restricting to
`[t₀, ω)` is exactly what makes the old `regular` cover the new `carrier`.  So **the tail
must be paid**, and the remaining bridge is `localFrameInv = coordInv` (both are two-sided
inverses of the same Gram matrix on the same open set, so uniqueness of the inverse gives
it; `InvMetricLocal` + `coordInvLocal` are the two sides).  Classification: **route-choice
+ missing bridge lemma**, routine but the tail restriction propagates into the statement of
work items 2 and 3.

The other four packages of `rm04Var_of_sol` are free: `hnablaReg` = `coordNab2Reg`
(zero hypotheses), `hmix` = `coordGammaMix S hS x₀ (coordGammaEvol S hS x₀ hmetric)` with
`hmetric` from `coordMetricMix ∘ coordMetricDeriv` (copy `coordRicciEvol:895-950`),
`hRm` = `rm13OfSol`, `hcurv` = `connCurvOfSol`.

## Work item 3 — global packaging.  NOT STARTED

Blocked behind work item 2 in the sense that `hev` is literally "work item 2 at `x₀ := y`
for every `y`".  Nothing was attempted; `basisAt` chart plumbing was not scoped.  Note that
if (b) above is settled by the tail route, `hev` will be stated for
`S.timeRestrict (closedOpen t₀ ω)`, not for `S` on the original `D`.

## New imports

One added: `DifferentialGeometry.Geometry.Curvature.CurvatureActionLower`, for
`curvatureAction0SAt_eq_rm04`.  No cycle (it sits under `Geometry/Curvature/`).

## Lessons

- **Grep `Geometry/Curvature/CurvatureActionLower.lean` before expanding a curvature action
  by hand.**  `curvatureAction0SAt_eq_rm04` already gives the fully component-level form with
  an arbitrary basis and `gInv`; the `cotangentSharp_gen`/`oneFormAtSlot0S` version
  (`RmRaisingBridge.lean:172`) is the *invariant* one and is much more painful to use in
  components.  This turned `ricciId` from the expected hard field into a ~110-line
  bookkeeping proof.
- `u ∘ (σ * σ)` for `σ : Equiv.Perm` elaborates **inconsistently**: in one declaration Lean
  read `⇑(σ * σ)` (group multiplication), in the next it read `⇑σ * ⇑σ` (pointwise `Pi.mul`),
  and the `rw` then failed with a confusing "pattern not found".  Fix: give the square its
  own named `Equiv.Perm` definition rather than writing a product inside a `∘`.
- The `simpa [SolutionOn.family, SolutionFamily.connection, SolutionFamily.rm04, metricCov,
  metricRm04, …]` incantation from `canBianchiAt` transports **any** `can*` lemma from
  `Realized.lean` to the solution's `S.family.connection` / `S.base.rm04` /
  `nablaRm04Field` / `nabla2Rm04Field`.  It also handles the differing
  `totalNabla0S_reg`-vs-`connSmoothInf` regularity witnesses (proof irrelevance).  Three
  separate bridges (`rmSecondAt`, `rm2SymmAt`, `n2RicTr`) were one-shot green with it.
- A private `def` in another module can still be *used* through a public theorem that
  mentions it: re-declare the definition verbatim locally and bridge with
  `simpa only [myCopy₁, myCopy₂] using theOtherTheorem`.  `HamiltonBaseProducer.lean` does
  this for `nabla2RicField`; `coordNab2Eq` here repeats it.
- Whole-file check ≈ 18 s.  Nothing needed a performance workaround; no `fin_cases` blowup
  (the only enumerations are over `Fin 4`/`Fin 5` slot maps, never over `CoordinateIdx`).
