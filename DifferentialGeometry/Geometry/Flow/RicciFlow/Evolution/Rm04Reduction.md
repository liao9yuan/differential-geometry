# Rm04Reduction — static reduction of `rm04VarRHS` to Uhlenbeck form

**Status: COMPLETE, 0 `sorry`, axiom-clean** (`propext`, `Classical.choice`, `Quot.sound` only).
Targeted build `+DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Rm04Reduction` GREEN
(3778 jobs). 801 lines. Brick K2-B stage 1.

## What this file is

`Evolution/Rm04Variation.lean` already proves the **time** half of the lowered-Riemann
evolution: `rm04Var_of_sol` gives `∂ₜ realizedRmBase = rm04VarRHS`, the `∇²Ric`-expanded
Christoffel-variation form. This file does the **static** half: at one fixed time and one
fixed frame centre it rewrites `rm04VarRHS` into

`Δ Rm_{ijkl} − 2(B_{ijkl} − B_{ijlk} + B_{ikjl} − B_{iljk}) − drift_{ijkl}`,

the shape of `Riemann04BTensorWithRicciDriftEvolutionInFrameOn` (`Evolution/Uhlenbeck.lean`).
No `HasDerivWithinAt` appears anywhere in the file.

## Design: two layers

**Layer 1 (bulk of the file) — bare component algebra** over `{ι : Type*} [Fintype ι]
[DecidableEq ι]`, no manifold, no metric object, no smoothness. Every array is a plain
`ι → … → ℝ`. This is what made the file cheap to check (13 s) and is the right reuse layer.

**Layer 2 (~120 lines) — solution wrapper** `rm04Var_eq_uhl`, at `CoordinateIdx (𝕜 := ℝ) E`,
instantiating layer 1 at the solution's component arrays. The three bridges
(`rm04VarRHS = rmVar`, `uhlenbeckBTensorInFrame = bComp`,
`riemann04RicciDriftInFrame = rmDrift`) are all `rfl` — the layer-1 defs were written to
match the existing defs slot-for-slot on purpose.

## Book route (MSM110 = Chow–Knopf, chapter6.tex:365–556) ↔ theorem map

| Book step | Theorem | Content |
|---|---|---|
| `RiemCurv3-1 tensor RicciFlow1`, algebraic half | `rmVar_eq_hess` | Contracting `g_{lp}` against the two `∇Γ̇` terms kills the inverse metric inside `nabGamma`, leaving the `∇∇Ric` commutator + `rmHess` + `−2·drift₄` |
| Ricci identity on `(0,2)` Ric (:474) | `comm_eq_drift` | commutator `= drift₄ − drift₃` |
| Lemma 6.14 steps 1–3 | `lapHessW` (private) | 2nd Bianchi on the inner `∇`, `∇`-commutation, differentiated traced Bianchi ⟹ `ΔRm = rmHess + rmW` |
| traced 2nd Bianchi (:421–423), differentiated | `tracedBi` (private) | `Σ g^{pq}∇_d∇_p Rm_{aqkl} = ∇²Ric_{dkal} − ∇²Ric_{dlak}` |
| Lemma 6.14 step 4 + first Bianchi merge (:441–445) | `wEq` (private) | the 8 quadratic terms `= drift₁ + drift₂ − rmQuad` |
| Lemma 6.14 (assembled) | `rmHess_eq_lap` | `rmHess = ΔRm + rmQuad − drift₁ − drift₂` |
| Lemma 6.15 proof (:533–556) | `rmQuad_eq_b` | `rmQuad = −2(B − B + B − B)` |
| Corollary + Lemma 6.15 | `rmVar_eq_uhl` / `rm04Var_eq_uhl` | final assembly |

Chain: `rmVar = comm + rmHess − 2 drift₄ = (drift₄ − drift₃) + rmHess − 2 drift₄
= rmHess − drift₃ − drift₄ = ΔRm + rmQuad − drift = ΔRm − 2(B−B+B−B) − drift`.

## Sign-convention ledger (project vs MSM110) — VERIFIED, not assumed

- `convention.md`: `Rm04(X,Y,Z,W) = g(W, R(X,Y)Z)`, `R(X,Y) = ∇_X∇_Y − ∇_Y∇_X − ∇_{[X,Y]}`.
  This is **literally** MSM110's `R_{ijkℓ} = g_{ℓm}R^m_{ijk}`. So `Rm04_proj = +Rm04_MSM`,
  no overall flip.
- `christoffelCurvCoeffAt conn x i j k p = R^p_{ijk}`; `realizedRmBase_eq_curvCoeff_lower`
  is the lowering `Rm04_{ijkl} = Σ_p R^p_{ijk} g_{lp}`. Cross-check: `rm04VarRHS`'s first
  summand is `∇_iΓ̇^p_{jk} − ∇_jΓ̇^p_{ik}`, exactly `∂ₜR^p_{ijk}` in that convention.
- MSM110 `B_{ijkℓ} = −g^{pr}g^{qs}R_{ipjq}R_{krℓs}` (**with** a minus);
  `uhlenbeckBTensorInFrame` = `Σ h^{eg}h^{fr}Rm_{aebf}Rm_{cgdr}` (**no** minus).
  Index-by-index match ⟹ `bComp = −B_MSM`.
- Hence the book's `+2(B_MSM − B_MSM + B_MSM − B_MSM)` **is** the project's
  `−2(bComp − bComp + bComp − bComp)`. The `UhlenbeckBaseProducer.md:166–215`
  "FIX APPLIED + VERIFIED" flip is exactly this bookkeeping, and this file now derives it
  dimension-generically rather than checking it at dim 3.
- `curvatureAction0SAt` carries a leading `−` and `metricTraceInput X Y tail =
  Fin.cases X (Fin.cases Y tail)` (derivative slots FIRST two) — checked in
  `Geometry/Operator/RoughLaplacian.lean:40`. This fixes the sign of `Rm04LapIn.ricciId`
  and of `RicCommAt`.

## Hypothesis packages and their stage-2 dischargers

Solution-level (`rm04Var_eq_uhl`); all evaluated at the fixed `t`, at `x₀`, in
`coordinateFrameAt x₀`:

| Hypothesis | Shape | Intended discharger |
|---|---|---|
| `hgi` | `coordInv` symmetric | `IsSmoothSolutionOn.invSymm` (field, `Basic/RicciNorm.lean`); or `invComp_symm` (`Geometry/Curvature/Basic.lean:94`) from `coordInvReal` |
| `hricsym` | `ricciCompInFrame` symmetric | `IsSmoothSolutionOn.ricciSymm`; or `ricciSymFrame_can` (`UhlenbeckBaseProducer.lean:663`) |
| `hcon` | `Σ_p g_{ap} g^{pb} = δ` | `coordInvReal` + `InverseMetricComponentsInFrame` (`Geometry/Curvature/Basic.lean:83`, second conjunct) |
| `hraise` | `christoffelCurvCoeffAt = Σ_q g^{dq} Rm04_{abcq}` | `realizedRmBase_eq_curvCoeff_lower` (lowering) + `hcon` (invert it); the raising bridge `rm13_apply_eq_rm04_raise` / `RmRaisingBridge.lean` is the tensor-level source |
| `hRup` | `ricciOneUp = Σ_q g^{bq} Ric_{aq}` | take `ricciOneUp := ricciOneUpCompInFrame S (coordInv S x₀) (coordinateFrameAt x₀)` — then `rfl` (`Basic/Components.lean:506`) |
| `hsym : Rm04Symm (Rm04 t x₀)` | swap12 / swap34 / pair / first Bianchi at components | `algebraicCurvatureSymmetries` + `first_bianchi` (`Geometry/Curvature/Bianchi.lean:358`) evaluated on `coordinateFrameAt` vectors, via `realizedRmBase_apply` |
| `hcomm : RicCommAt` | `(0,2)` Ricci identity at components | `tensor0S_ricciIdentity_of_torsionFree` (`Tensor/RicciIdentity/Tensor0S/Formula.lean:975`) at `s = 2` with `alpha = Ric`, then `curvatureAction0SAt_eq_rm04_raise` (`RmRaisingBridge.lean:172`) + `Nabla20SRealizesAt` for `nabla2Ric` |
| `hin.bianchi2` | differentiated 2nd Bianchi | `canBianchiAt` (`Evolution/Ricci/CoordinateIdentities.lean:200`) gives `SecondBianchiAt`; differentiate once (∇ of the identity) — this is the one input needing a *new* small producer (∇ of `SecondBianchiAt`), see TODO below |
| `hin.ricciId` | `(0,4)` Ricci identity | same route as `hcomm` but at `s = 4` with `alpha = Rm04` |
| `hin.ricTrace` | `Ric = Σ g^{pq} Rm_{pabq}` | `RicciTensorRealizesRm04FirstTraceInFrameOnRegular` (used in `Evolution/Ricci/Commutator.lean:982`) |
| `hin.n2RicTrace` | `∇²Ric = Σ g^{pq} ∇²Rm_{pcdq}` | trace of the previous through `∇²` — metric compatibility (`Geometry/Coordinates/MetricCompatibility/`); needs a small producer |
| `hin.n2RmSwap12`, `n2RmPair`, `n2RicSym` | `∇²` inherits the algebraic symmetries | pointwise from `Nabla20SRealizesAt` + the symmetries of `Rm04`/`Ric` as `Tensor0S` sections |

Rules honoured: (1) every hypothesis has a named plausible discharger above; (2) none of
them is the conclusion or a rewrite of it — `rmHess_eq_lap` is **proved** from
`Rm04LapIn` + `Rm04Symm`, it is not assumed; (3) 8 solution-level hypotheses + 2 packages
(`Rm04Symm`, `Rm04LapIn`), i.e. few mid-sized packages rather than many micro-hypotheses.

**Non-vacuity guard (checked, out-of-repo scratch file):** `Rm04Symm` and `Rm04LapIn` are
simultaneously satisfiable — the identically-zero curvature instance over `Fin 3`
constructs both structures. So the packages are not contradictory and the theorems are not
vacuously true. (That the packages are satisfiable *together with a nonzero `Rm`* is
exactly what stage 2's producers will establish.)

## What was hard / what worked

- **The whole thing is `Finset.sum` reindexing.** The winning move was the normal form
  `quadSum gInv X = Σ_{p,q,r,s} g^{pq} g^{rs} X_{pqrs}`: *every* quadratic curvature block
  in Lemma 6.14/6.15 is a `quadSum`, and `bComp` (= `uhlenbeckBTensorInFrame`) is one too,
  with the metric pairs already in the right slots. After that the book's index gymnastics
  reduce to three reindexing lemmas — `quadSwapPQ`, `quadSwapRS` (both need `gInv`
  symmetry), `quadSwapPR` (needs `sum4Swap`) — plus pointwise `rw [symmetry]; ring`.
  No `fin_cases`, no `decide`, no component enumeration anywhere.
- `bComp_quad` (`bComp` → `quadSum` normal form) is a pure `mul_assoc`: `bComp`'s summation
  order `e,g,f,h` already matches `quadSum`'s `p,q,r,s`. My first attempt routed it through
  `sum4Swap`, which was unnecessary — check the *order* before assuming a permutation.
- **`linarith` over sum atoms works well.** `hpt` inside `lapHessW` combines one
  `bianchi2` and two `ricciId` instances whose RHSs are big double sums; `linarith` treats
  each `∑ u, ∑ v, …` as an atom and closes it in one line. Same trick in `tracedBi` and in
  the final `wEq` assembly (`linarith [h16]`).
- **Beta-redex traps.** `quadSwapRS gInv hgi X : quadSum X = quadSum (fun p q r s => X p q s r)`
  produces a beta-redex; it composes fine in `calc`/`exact` (defeq) but a `rw` on it needs
  the *explicit* helper (`quadB`) rather than rewriting with `quadSwapPR` directly.
  Likewise `(fun u => Rm j u k l) u = -(fun u => Rm u j k l) u` cannot be closed by `rw`
  (pattern not found under the redex) but is closed by `exact hsym.swap12 j u k l`.
- `simp only [mul_add, mul_sub, mul_neg, Finset.mul_sum, mul_assoc]` closed a step
  outright, so the trailing `ring` became "no goals" — a one-line fix, but worth noting
  that these distribution `simp only`s are often already terminal.
- Whole-file check: 13 s. Nothing needed a performance workaround.

## Relocation TODOs (for the planner, not urgent)

1. The entire `section Algebra` (`Rm04Symm`, `quadSum` + reindexing lemmas, `bComp`,
   `rmQ1/rmQ2/rmQ4/rmQuad`, `rmLap`, `rmDrift`, `rmHess`, `nabGamma`, `rmVar`) is
   manifold-free component algebra. Its canonical home is next to `Uhlenbeck.lean` (which
   already has the `MatrixComp`/`FourComp` currency and `Idx` section variables) — either
   as a new `Evolution/UhlenbeckAlgebra.lean` below `Uhlenbeck.lean`, or folded into
   `Uhlenbeck.lean` itself. Left here so stage 1 stays a single reviewable file.
2. `bComp` duplicates `uhlenbeckBTensorInFrame`'s body at the bare-index level (the bridge
   is `rfl`). If the algebra layer moves next to `Uhlenbeck.lean`,
   `uhlenbeckBTensorInFrame` should be *redefined* as `bComp (hInv t x) (Rm t x)` so there
   is one definition, not two.
3. `bComp_swap` (`B_{abcd} = B_{badc}`, MSM110 (6.42)) and `rmQuad_eq_b` are generally
   useful Uhlenbeck-`B` API; they belong wherever (1) lands.
4. `Rm04Symm` overlaps `algebraicCurvatureSymmetries` at the tensor level. Once stage 2
   builds the producer, consider making `Rm04Symm` the component-level *projection* of the
   tensor-level predicate rather than an independent structure.

## Stage 2 (next brick)

Build the producers listed in the discharger table, then combine with
`rm04Var_of_sol` (`Rm04Variation.lean:64`) to get
`Riemann04BTensorWithRicciDriftEvolutionInFrameOn`. The only input with **no** existing
producer at all is `Rm04LapIn.bianchi2` (the once-differentiated second Bianchi identity)
and `n2RicTrace`; everything else has a named source. Suggested order:
`n2Rm`/`n2Ric` realization (`Nabla20SRealizesAt` at `s = 4`) first, since `bianchi2`,
`ricciId`, `n2RicTrace` and the three symmetry fields all flow from it.
