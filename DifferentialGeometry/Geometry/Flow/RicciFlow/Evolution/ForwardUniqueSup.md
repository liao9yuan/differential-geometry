# `ForwardUniqueSup.lean` — the slab-uniform input layer of the (B) endgame

Lane: `ricci_flow_forward_unique` (black box (B)).  Companion notes:
`ForwardUniqueAssembly.md` (the bundle + provenance ledger), `ForwardUniqueWiring.md` (the five
residual hypotheses), `ForwardUniqueDensReg.md` (the joint-regularity tower),
`ForwardUniqueRmBounds.md` / `ForwardUniqueRateLe.md` / `ForwardUniqueConnBound.md` (the
pointwise estimate producers).

## Outcome — 2026-07-26, third pass (SLAB-2)

**`hedge` is DISCHARGED; `fluxLe` is now produced at the constructed carrier; `hbounds` is
still short four fields.**  `forward_unique_of_gram`'s residual list drops from **two**
hypotheses to **one**.

* `energyEdgeCont` (this file) **is** the wiring's `hedge`, from (B)'s two chart-Gram fields
  alone.  Machine-checked against `forward_unique_of_gram` in a scratch `example`: the
  planner's discharge of that slot is a one-liner.
* `ricciSlabLe` (`ricciLe`) was already unconditional; `fuFluxSlab`
  (`Evolution/ForwardUniqueWiring.lean`) is now `fluxLe` at `fuUflux`, unconditional, using
  the three background sups below.
* `volLe`, `remLe`, `reactLe`, `adotLe` remain open — see §"Field-by-field discharge table"
  and §"What is still missing".

0 `sorry`; focused check and targeted module build green, warning-clean; every public endpoint
3-axiom clean.

### What the closed-edge upgrade bought

`ForwardUniqueDensReg.lean`'s brick `normSq0S_jointContMDiffOn` lost its `IsOpen J` hypothesis
(third pass, see `ForwardUniqueDensReg.md`), so it now fires on `J := Icc a c`.  The
§"The closed-edge blocker" of the previous pass is therefore **RESOLVED**, and this file adds
the sup layer it was blocking:

| new endpoint | delivers |
| --- | --- |
| `normSqSlabSup` | brick + `normSqSlabBound`: any moving fibre norm with closed-edge chart components is bounded on `Icc a c ×ˢ univ` |
| `metricSlabSup` | `B_g ≥ \|g₂\|²_{g₁}` |
| `rm04SlabSup` | `B ≥ \|Rm(∇^{gC}) lowered by gL\|²_{gN}`, three metric roles independent — `(g₁,g₂,g₂)` is `B₂`, `(g₁,g₁,g₂)` is `B_P` |
| `ricciSq_le_rm04` | `\|Ric₂\|²_{g₁} ≤ n⁴·\|Rm(∇²) lowered by g₁\|²_{g₁}` (from `metricRicci_eq_trace_cross` + `normSq0S_domDomCongr` + `traceNormSq_le`) |
| `ricciSlabSup` | `B₃ ≥ \|Ric₂\|²_{g₁}`; with `g₂ := g₁` this is `adotLe`'s `Λric` and `reactLe`'s only background norm |
| `energyEdgeCont` | the wiring's `hedge` |

### `hedge`: the route

`forwardUniqueEnergy g₁ g₂ t = ∫ dens(t,·) dμ_{g₁ t}` moves **both** the integrand and the
measure, so the edge is a moving-measure statement.  The dominated-convergence layer already
exists: `integral_family_cont`
(`Analysis/Integration/Measure/FamilyContinuity.lean:203`) takes purely `C⁰` hypotheses on an
**arbitrary compact** time set and returns `ContinuousOn (fun t => ∫ f t dμ_{g t}) K`.  So the
proof is: restrict (B)'s fields to `Icc a c` with `c := (a+b)/2`, feed
`dens_jointContMDiffOn (J := Icc a c) |>.continuousOn` as the integrand input, and widen
`ContinuousWithinAt … (Icc a c) a` to `Ico a b` through `Icc a c ∈ 𝓝[Ico a b] a`.  **No new
integration theory was needed** — the only thing that had been missing was the closed-edge
`C⁰` regularity of the *density*, which is exactly what the DensReg upgrade supplies.
`first_var_joint` / `first_variation_of_volume` are structurally unusable here: they are
hard-gated on `IsOpen U` through `exists_time_retract`.

## What is still missing (the four open fields)

* **`volLe`** — needs joint continuity of `traceTimeDerivMetric g₁` on `Icc a c ×ˢ univ`.
  Unlike every other background quantity this is *not* a chart-Gram statement: the trace is
  computed in the chart **centred at `x` itself**, and its time derivative at `t = a` is
  one-sided.  Route unchanged: port `traceTimeDerivMetricAt_eq_neg_two_scalar_of_metricDeriv`
  (`Evolution/Volume.lean`, stated in `RealizedMetricFamily` currency) into the lane's
  `ℝ → SmoothRiemannianMetric I M` currency, then use `ricciSlabSup` for the scalar-curvature
  sup.  This is now the *cheapest* of the four.
* **`reactLe`** — still needs a bound on `movingReact0S`, which is frame-pinned to
  `Module.finBasis`.  The №47 basis-free reading (`fuReactDeriv`, `private` in
  `ForwardUniqueWiring.lean`) exhibits `movingReact0S (g t) x s Q W` as
  `deriv (fun r => normSq0S (g r) x s W) t`, i.e. basis-free — so the intended shortcut is
  `HasDerivAt.unique` against the same derivative computed in a `g`-orthonormal basis, which
  transports `movingReact_le` (`Analysis/Spectral/Intrinsic/DeTurck/MovingEdgeEnergy.lean:643`,
  rank 2, for the parallel `movingMetricReact`) to `movingReact0S` at every rank.  Not
  attempted in this pass.  `ricciSlabSup` already supplies the `sup |Ric₁|²` it will consume,
  but note `movingReact_le` takes an **operator** bound `|Q(v,w)| ≤ B|v||w|`, not a
  `normSq0S` bound — a Cauchy–Schwarz step is still owed.
* **`adotLe`** — `connDiffDot_normSq_le` (`ForwardUniqueConnBound.lean:1404`, 0-sorry) is
  instantiable: its `hΓ` is `fuGamma` rewritten through `coeff_bilinOfComp`
  (`ForwardUniqueConnDot.lean:587`) and its `hA` is `connDiffVec_hasDerivAt`
  (`ForwardUniqueConnDot.lean:418`) fed by the same `fuGamma` — the previous note's claim that
  `hΓ`/`hA` are missing is **stale**.  Of its four background inputs, `Λric` and `B₃` are now
  `ricciSlabSup`.  The two genuinely missing ones are:
  - `B₁ ≥ |∇²Ric₂|²_{g₁}` — needs chart components of `metricNabla0S (g₂ t) Ric₂`, i.e. a
    `∂(chart Riemann)` layer.  `RicciDifferenceMeanValueWithin.lean` has `partChristWithin`
    (the `∂Γ` layer) but no `partRiem`/`partRicci`; adding one is the smallest brick.
  - `Λ` with `∀ v, (g₁ t)(v,v) ≤ Λ·(g₂ t)(v,v)` — a *pointwise metric comparison*, not a
    `normSq0S` sup, so `normSqSlabSup` does not produce it.  It needs a separate
    compactness argument on `Icc a c × unit sphere bundle`, or a Grönwall-type comparison from
    the two PDEs.
* **`remLe`** — unchanged and the hardest: two of `sdecRemFam`'s four summands
  (`lowOfComp g₁ b (rmDotRem …)` and `gapDot g₁ g₂ (uhlRm2Vec …)`) are built from a raw
  component array and a bare pointwise trilinear family, neither of which carries **any** norm
  bound anywhere in the tree.  This is a planner decision (re-express `sdecRemFam` through
  tensorial carriers?), not a sup problem.

## What the wiring actually asks for

`forward_unique_of_gram` (`ForwardUniqueWiring.lean:561`) leaves

```
hbounds : ∀ c ∈ Ioo a b, ∃ C_A C_R C_Ric C_V C_U C_rem,
  ForwardUniqueSlab g₁ g₂ (connSpeed g₁ g₂ (fuAvec g₁ g₂)) (fuSfield g₁ g₂)
    (fuUflux g₁ g₂) (fuRem g₁ g₂) a c C_A C_R C_Ric C_V C_U C_rem
```

and all six fields of `ForwardUniqueSlab` (`ForwardUniqueAssembly.lean:229`) quantify over the
**open** `Ioo a c`.  Two facts about that shape drive everything below.

1. `Ioo a c` accumulates at `a`, so a uniform constant on it needs control **up to the closed
   initial edge** `t = a`.  Compactness therefore has to be applied on `Icc a c`, not on an
   interior subslab.
2. The carriers are the *constructed* ones of `ForwardUniqueWiring.lean`, not the abstract ones
   the older ledger entries were written against.  In particular `Uflux = fuUflux = sdecUflux`
   and `rem = fuRem = sdecRemFam`, which are **not** `rmDiffFlux` / `lapDiffRem`.

## Field-by-field discharge table

| field | needed at | producer | sup consumed | status |
| --- | --- | --- | --- | --- |
| `ricciLe` | — | `ricciSlabLe` (here) ← `ricciDiff_eq_trace` + `normSq_ricciTraceRep` + `ricciDiffSq_le` + `rmDiffSq_le_dens` | **none** | **DONE, unconditional, `C_Ric = n⁴`** |
| `volLe` | `traceTimeDerivMetric g₁` | `volSlabLe` (here) ← `slabBound` | drift itself | **DONE modulo one regularity input** (joint continuity of the drift on `Icc a c ×ˢ univ`) |
| `fluxLe` | `sdecFlux g₁ g₂ Rm₂ P` | `fuFluxSlab` (Wiring) ← `fluxSlabLe` (here) ← `sdecFluxSq_le` (here) ← `fluxNormSq_le` + `reLowerPairSq_le` (here) + `connDiffSq_le_dens` | `rm04SlabSup` ×2, `metricSlabSup` | **DONE at the constructed carrier, unconditional given (B)** |
| `remLe` | `sdecRemFam` | **none** | — | **blocked, and not only on sups** (see §"`remLe`") |
| `reactLe` | `movingReact0S` | **none** (`movingReact_le`, plan №25, deliberately deferred) | `sup |Ric₁|²` | **blocked** |
| `adotLe` | `connSpeed … fuAvec` | `connDiffDot_normSq_le` (`ForwardUniqueConnBound.lean:1404`; **planner correction: that file is 0-sorry since β4, commit `24dc9ac50` — the ":496 live sorry" claim was read from the .md's historical disproof section, not the code**) | `Λric`, `Λ` (metric comparison), `B₁ = |∇²Ric₂|²`, `B₃ = |Ric₂|²` | **blocked** on those sups **and** on `hΓ`/`hA` (the K1 Christoffel-evolution and speed-derivative inputs, available only through `gamma_of_gram` / `connSpeed_hasDerivAt`) |

## What is in the file

### 1. The compactness engine (the piece `ForwardUniqueWiring.md` names as missing)

* `slabBound F hF : ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc a c, ∀ x, |F t x| ≤ C` from
  `ContinuousOn (fun p => F p.1 p.2) (Icc a c ×ˢ univ)`.  `IsCompact.exists_bound_of_continuousOn`
  on `isCompact_Icc.prod isCompact_univ`; the two-sided conclusion is what `volLe` needs.
* `slabBound_ioo` — the same on `Ioo a c`, the interval the bundle quantifies over.
* `normSqSlabBound` — the shape the five sub-producers consume: one constant `B` with
  `|A t x|²_{g t} ≤ B` on the whole subslab.

**Relocation TODO.**  `slabBound` / `slabBound_ioo` mention neither `I` nor any bundle; they are
pure topology (`compact × compact → bounded`).  Their canonical home is a topology layer, not
this lane.  They are kept here only because the lane is the sole consumer today.

### 2. `ricciLe`, unconditionally

`ricciSlabLe g₁ g₂ t x : |Ric₁ − Ric₂|²_{g₁} ≤ n⁴ · forwardUniqueDensity g₁ g₂ t x`.

No background norm, no compactness, no hypothesis at all.  The reason: `ricciDiff_eq_trace`
(`ForwardUniqueRatePro.lean:256`) exhibits the Ricci difference as the `g₁`-trace of a *slot
permutation* of the very carrier `S₀₄` whose norm is the curvature third of the density, and
`normSq_ricciTraceRep` says that permutation is a fibre isometry — so `ricciDiffSq_le` applies
with background coefficient `B = 0`, and `rmDiffSq_le_dens` finishes.  This is the only one of
the six fields that is genuinely free.

### 3. `volLe`

`volSlabLe g₁ hdrift : ∃ C_V ≥ 0, ∀ t ∈ Ioo a c, ∀ x, ½·traceTimeDerivMetric g₁ t x ≤ C_V`.

Exactly the route the ledger records ("compactness of `Icc a c` applied to
`traceTimeDerivMetric`").  The input is a *regularity* statement — joint continuity of the
volume drift up to the closed edge — not a restatement of the conclusion, so this is not an
adapter wrapper.

Discharging `hdrift` is a separate obligation: `traceTimeDerivMetric g_fam t x` is
`trace(G(t,x)⁻¹ · Ġ(t,x))` computed in the chart **centred at `x` itself**, so its joint
continuity is not a chart-Gram statement.  The intended route is the Ricci-flow identity
`traceTimeDerivMetric = −2·scal`, for which `Evolution/Volume.lean` has
`traceTimeDerivMetricAt_eq_neg_two_scalar_of_metricDeriv` — but only in the
`RealizedMetricFamily` / `ScalarRealizesRicciTraceInFrame` currency, not the lane's
`ℝ → SmoothRiemannianMetric I M`.  Porting that bridge is the next concrete step for this
field; it then needs the same closed-edge curvature sup as everything else.

### 4. `reLowerPairSq_le` and `sdecFluxSq_le`

`reLowerPairSq_le g T K x : |reLowerPair g T K|²_g ≤ n^{s+4} · |T|²_g · |K|²_g`.

This is the genuinely new algebraic content of the pass.  `reLowerPair` is
`metricTraceFirstTwoField g (domDomCongr (reLowerPerm2 s) (T ⊗ K))`; the bound is
`traceNormSq_le` ∘ `normSq0S_domDomCongr` (permutation is an isometry) ∘ `normSq0S_product`
(the product multiplies fibre norms *exactly*).  Nothing in the tree bounded this carrier
before, and it appears in **both** `sdecFlux` and `sdecRem`.

`sdecFluxSq_le` then gives the `fluxLe` estimate at the carrier the wiring builds:

```
|sdecFlux g₁ g₂ Rm₂ P|²_{g₁} ≤ 32·n⁵·|A₀₃|²·B₂ + 8·n¹⁰·|A₀₃|²·(B_P·B_g)
```

with `B₂ ≥ |Rm₂|²_{g₁}`, `B_P ≥ |P|²_{g₁}`, `B_g ≥ |g₂|²_{g₁}` named arguments.  Both summands
carry `|A₀₃|²_{g₁} = connDiffSq`, so `connDiffSq_le_dens` turns the whole thing into
`C_U · density`; `fluxSlabLe` does exactly that and is the `fluxLe` field verbatim, with

```
C_U = 32·n⁵·B₂ + 8·n¹⁰·B_P·B_g.
```

Its three nonnegativity side conditions are precisely what `normSqSlabBound` returns next to
each sup, so the field is one closed-edge sup away from being unconditional.

**Correction to `ForwardUniqueAssembly.md`'s ledger.**  It names `fluxNormSq_le` /
`rmFluxNormSq_le` as the producer of `fluxLe`.  That is wrong for the constructed carrier:
`rmFluxNormSq_le` bounds `rmDiffFlux`, whereas `fuUflux = sdecUflux = sdecFlux` is
`lapDiffFlux(Rm₂) − reLowerPair g₁ P (lapDiffFlux g₁ g₂ g₂)`, and the subtracted defect had no
bound at all.  Same correction applies to `remLe` (`rmRemNormSq_le` bounds `lapDiffRem`, not
`sdecRemFam`).

## ~~The closed-edge blocker (why no background sup is produced here)~~ — RESOLVED 2026-07-26

*Historical.*  The blocker below was discharged in two steps: `christoffelWithin` /
`riemannWithin` (`RicciDifferenceMeanValueWithin.lean`, ruling R12) removed the two-sided
`ContDiffAt` demand, and the third pass of `ForwardUniqueDensReg.lean` removed `IsOpen J`
from the brick and re-threaded `connChartJoint`/`rmChartJoint` against `christWithinM`/
`riemWithinM`.  The four `private` helpers named at the end of this section were **deleted**,
not made public: their `Within` replacements are public in the `Within` file.  Kept for the
record of what the obstruction was.

### The obstruction, as it stood

Every remaining field needs `sup_{Icc a c × M}` of a **curvature-type** background quantity
(`|Ric₁|²`, `|Rm₂|²`, `|∇²Ric₂|²`, `|∇²Rm₂|²`, the scalar curvature).  The route is
`normSq0S_jointContMDiffOn` (`ForwardUniqueDensReg.lean:216`) + `slabBound`.  It does not close,
for a precise reason:

* (B)'s own regularity field is `h1smooth : ContMDiffOn … (Ico a b ×ˢ baseSet)` — smoothness in
  time only **one-sidedly** at `t = a`.
* The joint Cramer chain (`chartGramDet_jointContMDiffOn`, `chartGramAdj_jointContMDiffOn`,
  `chartInvGram_jointContMDiffOn`) is stated for an **arbitrary** `J : Set ℝ`, so it survives
  the closed edge.  Good.
* The joint **Christoffel/Riemann** tower does not.  `GenJointGram`
  (`Analysis/Parabolic/RicciLinearization/RicciDifferenceMeanValue.lean:401`) demands
  `ContDiffAt` in `(s, y)` jointly at every `s₀ ∈ S`, i.e. a **two-sided** time neighbourhood;
  `gen_joint_christoffel` / `gen_joint_riemann` inherit that.  With `S = Ico a b` and `s₀ = a`
  the hypothesis is strictly stronger than `h1smooth`, so the tower cannot be fed at the edge.
* Consequently `normSq0S_jointContMDiffOn` is stated with `hJ : IsOpen J`, and the lane's own
  consumers (`connChartJoint`, `rmChartJoint`, `dens_jointContMDiffOn`) all live on `Ioo a b`.

**The smallest unblocking step** is a `ContDiffWithinAt` version of the joint Christoffel/Riemann
tower — `GenJointGramWithin`, plus `gen_joint_christoffel`/`gen_joint_riemann` restated with
`ContDiffWithinAt … (S ×ˢ interior target)`.  `Ico a b ×ˢ U` is `UniqueDiffOn`, and only the
*spatial* derivatives are taken, so the mathematics is routine; the cost is re-threading the
chain rules of `RicciDifferenceMeanValue.lean` (~700 lines of tower).  That file is outside this
lane and was not touched.

Two smaller, private-visibility obstacles sit on the same path and should be fixed when the
tower is:

* `genGram_of_joint`, `jointOnM`, `christJoint`, `riemJoint` are **`private`** in
  `ForwardUniqueDensReg.lean`.  Any background-norm sup producer outside that file needs all
  four; re-deriving them would be a straight duplication of ~80 lines.
* `gen_joint_ricci` is `private` in `RicciDifferenceMeanValue.lean` (its body is three lines over
  the public `gen_joint_riemann`, so this one is cheap to work around).

## `remLe`: blocked beyond sups

`fuRem = sdecRemFam = sdecRem g₁ g₂ P b (rmDotRem …) (uhlRm2Vec …)`, i.e. four summands
(`ForwardUniqueSdec.lean:659`):

1. `lowOfComp g₁ b R₀` with `R₀ = rmDotRem …` — a raw **component array**, not a tensor with a
   fibre norm.  Bounding `|lowOfComp g b R₀|²` needs componentwise control of `rmDotRem`, which
   is built from the Uhlenbeck component families `Rm04ᵢ`, `Bᵢ`, `ricciOneUpᵢ`.
2. `gapDot g₁ g₂ Rm2dot` with `Rm2dot = uhlRm2Vec …` — a **bare pointwise family** (`∂ₜRm₂` as a
   trilinear map).  There is no continuity, no smoothness and no norm bound available for it;
   this is the same class of object that already blocks `hpair`/`hrest`/`hrem` in the wiring.
3. `(reLower g₂ g₁ − id)(Δ₁P)` — needs a `reLower`-defect bound against `metricDiffSq`;
   `traceDiffNormSq_le` (`ForwardUniqueRmBounds.lean:641`) is the right shape but is stated for
   the trace, not for `reLower`.
4. `tr₁(reLowerPair g₁ (∇¹P) (lapDiffFlux g₁ g₂ g₂))` — **this one is now available**:
   `reLowerPairSq_le` + `traceNormSq_le`.

So `remLe` is not a sup problem: summands 1 and 2 need new estimate machinery whose inputs
(component arrays, a bare `∂ₜRm₂` family) do not carry norms yet.  Recommended next planner
decision: whether `sdecRemFam` should be re-expressed through tensorial carriers before any
bound is attempted.

## Lean lessons from this pass

* `slabBound`'s statement mentions no `I`, so Lean's automatic section-variable inclusion drops
  it: call sites must write `slabBound (M := M) …`, **not** `(I := I)`.  The error message
  ("Invalid argument name `I`") is the tell.
* `isCompact_univ (α := M)` does not elaborate in this Mathlib (the binder is `X`); the robust
  form is the ascription `(isCompact_univ : IsCompact (univ : Set M))`.
* `sdecFlux g₁ g₂ T P x = lapDiffFlux … x - reLowerPair … x` is **`rfl`**: `Tensor0SField`
  subtraction evaluates pointwise definitionally, so no `fieldSub_eval` rewrite is needed.
* Rank arithmetic across `reLowerPair`: the product has rank `s + 1 + 3` and the trace consumes
  rank `(s + 2) + 2`.  These are defeq, so `exact`/`refine` cross the gap, but a `rw` on the
  exponent would not — state the conclusion at `n ^ (s + 4)` and close with `exact`, never with
  `rw`.
* `MultilinearSection.domDomCongr_apply` is `rfl` and `@[simp]`; `normSq0S_product` is stated
  directly on `MultilinearSection.product … x`, so no `_apply` rewriting is needed on that side.
* A fourth private copy of `exists_onFrame` / `onFrame_inv` had to be made (copies now live in
  `ForwardUniqueRmBounds.lean`, `ForwardUniqueConnBound.lean`, `ForwardUniqueRatePro.lean` and
  here).  **Dedup TODO**: promote one public pair to
  `Tensor/RSTensor/Tensor0SRiemannian/` and delete the four.

## Verification

Focused check green and warning-free; targeted module build green; zero `sorry`.
`#print axioms` on every public endpoint — the original seven plus `normSqSlabSup`,
`metricSlabSup`, `rm04SlabSup`, `ricciSq_le_rm04`, `ricciSlabSup`, `energyEdgeCont` — returns
exactly `[propext, Classical.choice, Quot.sound]`.

The module is now reachable from the root aggregate **transitively**: `ForwardUniqueWiring.lean`
imports it (for `fuFluxSlab`), and the aggregate imports the wiring.  No edit to
`DifferentialGeometry.lean` was made.

## Next targets, in order of leverage

*(Re-ordered 2026-07-26 after the closed-edge upgrade; see §"What is still missing".)*

0. **`volLe`** — cheapest of the four remaining fields: port the
   `traceTimeDerivMetric = −2·scal` bridge into the lane's currency, then `ricciSlabSup`.
1. ~~The `ContDiffWithinAt` joint Christoffel/Riemann tower (closed edge).~~  **DONE** (R12 +
   the DensReg third pass).  It unblocked `fluxLe`'s three constants and `reactLe`/`adotLe`'s
   `sup |Ric|²`; `volLe`'s regularity input is *not* among them (it is not a chart-Gram
   quantity).
2. `movingReact_le` (plan №25) — the `reactLe` micro-bound.  `movingReact0S` is frame-pinned to
   `Module.finBasis`; the bound needs the change of basis to a `g`-orthonormal frame, which is
   why it was deferred.  Nothing else about `reactLe` is missing.
3. The planner decision on `sdecRemFam`'s two non-tensorial summands (§"`remLe`").
4. ~~`ForwardUniqueConnBound.lean:496` — the live `sorry` under `adotLe`.~~
   PLANNER CORRECTION: stale — ConnBound is 0-sorry since β4 (`24dc9ac50`,
   machine-verified in two full builds); `adotLe`'s real remaining inputs
   are the sups plus the hΓ/hA wiring only.
