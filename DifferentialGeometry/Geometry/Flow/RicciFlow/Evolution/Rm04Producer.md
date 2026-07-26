# Rm04Producer — discharging the `Rm04Reduction` inputs

**Status: PARTIAL (outcome B).** Layer 1 partially done: one producer complete and green,
the rest of the input list re-mapped onto *existing* API. Layers 2 and 3 NOT STARTED.

Focused check green; targeted build `+…Evolution.Rm04Producer` GREEN (3779 jobs,
warning-clean). 0 `sorry`. 110 lines.

## What landed

- `rmComp S x₀ : FourComp M (CoordinateIdx (𝕜 := ℝ) E)` — the canonical lowered-curvature
  component array in the coordinate frame centred at `x₀`, written with `vec4` (rather
  than `realizedRmBase`'s `Fin 4` slot map) so the tensor-level symmetry producers apply
  to it definitionally.
- **`rm04SymmOfSol`** — `Rm04Symm (rmComp S x₀ t x)` at every regular time and every
  point, from `S`/`hS` **only**. This fully discharges the `hsym` package of
  `rm04Var_eq_uhl` and the `Rm04Symm` argument of `rmQuad_eq_b` — four of the ten
  K2-B-1 inputs (swap12 / swap34 / pair / first Bianchi).
  Built from `rm04InputSkew_regular`, `rm04PairSymm_regular`, `rm04FirstBianchi_regular`
  (`Evolution/Ricci/Trace.lean:321/346/397`), fed by `rm13OfSol` and the hypothesis-free
  `solution_rm04LowersRm13At`. `swap34` is derived (pair ∘ skew ∘ pair) since only the
  first-two-slot skew producer exists.

## THE MAIN FINDING — the planner's two "missing producers" are down to ONE

The task framing said `Rm04LapIn.bianchi2` and `Rm04LapIn.n2RicTrace` were the gaps, and
my K2-B-1 note listed `n2RmSwap12`/`n2RmPair` as needing new producers too. Reconnaissance
shows **three of those four already exist** as `can*` lemmas in
`Geometry/Connection/LeviCivita/Curvature/Realized.lean`, with slot conventions that match
`Rm04LapIn` exactly (checked index-by-index, not assumed):

| `Rm04LapIn` field | Existing producer | Match |
|---|---|---|
| `n2RicTrace` | **`canNabla2RicTrace`** (`Realized.lean:1068`) | `nabla2Ric (vec4 A B C D) = Σ_{i,j} gInv i j * nabla2Rm04 (Fin.cons A (vec5 B (basis i) C D (basis j)))` — i.e. `n2Ric a b c d = Σ_{p,q} g^{pq} n2Rm a b p c d q`. **Exact match.** |
| `n2RmSwap12` | **`canRm2Symm`** conjunct 2 (`Realized.lean:1229`) | `nabla2Rm04 (A,B,Y,X,Z,W) = −nabla2Rm04 (A,B,X,Y,Z,W)`. Exact. |
| `n2RmPair` | **`canRm2Symm`** conjunct 3 | `nabla2Rm04 (A,B,X,Y,Z,W) = nabla2Rm04 (A,B,Z,W,X,Y)`. Exact. |
| `ricciId` | **`nablaKRm04_ricciIdentityAt`** at `k = 0` (`RmRealizationBridgeAllK.lean:345`) | `Tensor0SRicciIdentityAt (S.base.rm13 t) (rm04) (∇²Rm)`, hypothesis-free from `S`/`hS`/regular `t`/`x`. Still needs the tensor→component evaluation, not new mathematics. |
| `ricTrace` | `canRicTrace` (`Realized.lean:1011`) / `RicciTensorRealizesRm04FirstTraceInFrameOnRegular` | first metric trace; slot order to be re-checked at wiring time |
| `n2RicSym` | not yet located; the first-order analogue `canNablaSymmAt` is used at `CoordinateIdentities.lean:276` | likely a small lift |
| `bianchi2` | **NONE — the one genuine gap** | see below |

**`Nabla20SRealizesAt` at `s = 4` already exists** (`nablaKRm04_nabla20SRealizesAt`, k = 0,
`RmRealizationBridgeAllK.lean:329`), hypothesis-free, along with the whole bundled
`nablaRm04Field` / `nabla2Rm04Field` / `nabla3Rm04Field` tower and their
`TotalNabla0SRealizes` witnesses (`RmRealizationBridge.lean:279-348`). **The stop gate on
"new Tensor-layer API beyond ~150 lines" is NOT triggered** — no new Tensor-layer API is
needed for the realization at all.

### The remaining gap: `bianchi2` (once-differentiated second Bianchi)

`canRmSecond` (`Realized.lean:542`) gives `SecondBianchiAt` for the canonical Levi-Civita
`∇Rm` **directly and non-existentially** (it is what `metricBianchiAt`'s existential is
instantiated with, so the `canBianchiAt` existential can be bypassed — this matters,
because the existential witness cannot be differentiated). Slot convention checked:
`SecondBianchiAt nablaRm04` is `nablaRm04(A,X,Y,Z,W) + nablaRm04(X,Y,A,Z,W) +
nablaRm04(Y,A,X,Z,W) = 0`, exactly `Rm04LapIn.bianchi2`'s cyclic pattern one derivative
down.

Intended route (NOT yet implemented): `canRmSecond` at every `x` says a specific cyclic
combination of `nablaRm04Field S t` vanishes as a **section**; differentiate that zero
section. Concretely this needs two pieces of `totalNabla0S` API that I did **not**
locate: (i) linearity of `nabla0SFun`/`totalNabla0S` in the differentiated field, and
(ii) naturality under a slot permutation (`domDomCongr`). If those exist the producer is
short; if not, they are the precise missing API to build, and they belong in
`Tensor/RSTensor/…` / `Geometry/Operator/`, not here. **This is the one item to scope
next.**

## What did NOT get done

- **Layer 2** (`rm04Evol_of_sol`, the centre-point evolution combining `rm04Var_of_sol`
  with `rm04Var_eq_uhl`): not started. Recon done, signatures collected:
  `coordNab2Reg` (zero hypotheses), `coordGammaMix` (needs `hGamma`), `rm13OfSol` /
  `connCurvOfSol` (`Evolution/Ricci/Trace.lean:215/232`). The `hmetricReg` slot is the
  awkward one: `tailChristoffelReg` (`Evolution/Connection/TailChristoffel.lean:144`)
  supplies `MetricFrameSpacetimeRegularityInFrameOnLocal` but with `localFrameInv` as the
  inverse-metric family, whereas `rm04Var_of_sol` wants `coordInv S x₀` — a
  `localFrameInv = coordInv` bridge lemma is needed, OR route (i) via
  `coordMetricDeriv`/`coordMetricMix` (`Ricci/CoordinateRegularity.lean:897/933`), which
  is what `coordRicciEvol` uses and would avoid the positive-time tail entirely. **Try
  route (i) first** — `coordRicciEvol` (`CoordinateIdentities.lean:864`) carries
  `S`/`hS`/`x₀`/`t`/`i`/`j` only, so the tail price may be avoidable.
- **Layer 3** (per-point-centred global families + `hreal` + `hL`): not started.

## Lessons

- Grep the `can*` family in `Geometry/Connection/LeviCivita/Curvature/Realized.lean`
  **before** declaring a Levi-Civita curvature identity missing. This is the fourth
  recorded instance in this project of a "framework wall" that was already built
  (`ricciflow-agents-overcount-walls`, `p13-shi-pullback-wall`, `a0prime-l1l2-false-wall`).
  The file is ~1500 lines of exactly these pointwise canonical identities.
- `canBianchiAt` returns an **existential** `nablaRm04`; anything that needs to
  *differentiate* the identity must go to the non-existential `canRmSecond` instead.
- `rw` will not see through a `def` like `rmComp` even when the two sides are defeq;
  `exact`/`neg_inj.mpr` on the underlying tensor-level lemma works and is shorter.
