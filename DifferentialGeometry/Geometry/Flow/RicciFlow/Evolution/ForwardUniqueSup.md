# `ForwardUniqueSup.lean` — the slab-uniform input layer of the (B) endgame

Lane: `ricci_flow_forward_unique` (black box (B)).  Companion notes:
`ForwardUniqueAssembly.md` (the bundle + provenance ledger), `ForwardUniqueWiring.md` (the five
residual hypotheses), `ForwardUniqueDensReg.md` (the joint-regularity tower),
`ForwardUniqueRmBounds.md` / `ForwardUniqueRateLe.md` / `ForwardUniqueConnBound.md` (the
pointwise estimate producers).

## Outcome

**The assignment was to produce the first `ForwardUniqueSlab` instance.  That was NOT
achieved, and cannot be from the current tree.**  Two of its six fields are landed here
(one of them unconditionally), the missing algebraic estimate for a third is landed, and the
other three are blocked on named, grep-verified gaps recorded below.  0 `sorry`; focused check
and targeted module build green; every public endpoint 3-axiom clean.

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
| `fluxLe` | `sdecFlux g₁ g₂ Rm₂ P` | `fluxSlabLe` (here) ← `sdecFluxSq_le` (here) ← `fluxNormSq_le` + `reLowerPairSq_le` (here) + `connDiffSq_le_dens` | `|Rm₂|²`, `|P|²`, `|g₂|²_{g₁}` | **field DONE in the exact `≤ C_U · density` shape**; the three sups are blocked (see §"The closed-edge blocker") |
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

## The closed-edge blocker (why no background sup is produced here)

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

Focused check green; targeted module build green; zero `sorry`.  `#print axioms` on the public
endpoints (`slabBound`, `slabBound_ioo`, `normSqSlabBound`, `ricciSlabLe`, `volSlabLe`,
`reLowerPairSq_le`, `sdecFluxSq_le`) returns exactly `[propext, Classical.choice, Quot.sound]`.

The module is **not** wired into the root aggregate — that is the planner's step, as for the
other lane files.

## Next targets, in order of leverage

1. The `ContDiffWithinAt` joint Christoffel/Riemann tower (closed edge).  It unblocks *every*
   background sup at once, hence `volLe`'s regularity input, `fluxLe`'s three constants,
   `reactLe`'s `sup |Ric₁|` and three of `adotLe`'s four.
2. `movingReact_le` (plan №25) — the `reactLe` micro-bound.  `movingReact0S` is frame-pinned to
   `Module.finBasis`; the bound needs the change of basis to a `g`-orthonormal frame, which is
   why it was deferred.  Nothing else about `reactLe` is missing.
3. The planner decision on `sdecRemFam`'s two non-tensorial summands (§"`remLe`").
4. ~~`ForwardUniqueConnBound.lean:496` — the live `sorry` under `adotLe`.~~
   PLANNER CORRECTION: stale — ConnBound is 0-sorry since β4 (`24dc9ac50`,
   machine-verified in two full builds); `adotLe`'s real remaining inputs
   are the sups plus the hΓ/hA wiring only.
