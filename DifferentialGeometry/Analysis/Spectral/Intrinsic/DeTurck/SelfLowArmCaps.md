# `SelfLowArmCaps.lean` — the last two per-arm capped windows

Created 2026-08-04 (A1-CUR-2 session 3).  **Sorry-free.**  With it,
`selfLow_jet` and `c0_jet_tower` are unconditional and the F6 estimate chain
closes.

## What is here

Two public theorems, both in the shape `selfLow_jet` consumes:

* `ricciDACap` — the transferred lower Ricci Palatini arm `ricciDALow g₀ g₁ P`;
* `lieCovCap` — the DeTurck–Lie covariant-derivative arm against its subtracted
  edge pairing, `deTurckLieCovDerivArmField − edgeLiePairFam`.

Plus the private leaf inventory both need: `sieSplit`, `endoAtgw`, `clSplit`,
`clAtgw` (Palatini arm) and `ptAtgw`, `pairCap`, `curvSmul`, `curvCap`,
`revEndoAtgw`, `omegaCap`, `lrQuadCap` (Lie arm).

Two generic calculus lemmas went into `GradCapArms.lean` instead, which is
their canonical home: `capOfP`/`capOfDP` (the perturbation and its first
derivative are themselves capped) and `capDdc0` (`domDomCongrSection` at
valence `(0,s)` is a capped-window isometry).

## `ricciDACap`

`ricciDALow g₀ g₁ P = daContr g₀ g₁ (dagLowOp g₀ g₁ ⋆ ∇P)`.  Chain:

1. `clSplit` abstracts the transparent Koszul factor.  `koszulOp` is **private
   to the read-only `DeTurckRemainderLowBaseAction.lean`**, so it is never
   named: `⟨_, fun _ => rfl⟩` lets unification fill the hole, and the resulting
   `Z : SmoothCcTensor g₀ 3 3` is state-free, which is all the estimate uses.
   `lowPerm` and `daPermA` ARE public (there are private homonyms earlier in
   the same file, but the `LowBaseInternal` copies at `:3375`/`:3379` win).
2. `endoAtgw s` — window at `bP`-offset `+1` for
   `slotInsertEndoCc g₀ s (fullRaisedEndoField g₀ g₁)`, from
   `fullRaisedEndoField_diff_split` + `slotInsertEndoCc_sub` (`sieSplit`),
   `rfns_iteratedCovGrad_slotInsertEndoCc_le_endo` and the `gInvDiff` grid
   producer.
3. `clAtgw` — window at `+1` for `connLowOp`, two `atgwFold`s at `(0,0)`.
4. `covGrad (connLowOp)` enters at `+2` via
   `rfns_iteratedCovGrad_covGrad_comm_rs` (shift the constant, not the level),
   then `capOfArm`; `dagLowOp = permCoeff ⋆ that` by `capApp`.
5. `∇P` enters by `capOfDP`, so `G = dagLowOp ⋆ ∇P` is `capApp`.
6. `refoldKernelContractionMonomialField_eq_mvPairTraceRefold` — public and
   valid for an ARBITRARY `(0,4)` argument — factors each `daMono` head as
   `mvPairTraceOp ⋆ rsDdc (Ext² (ddc G))`; `mvPairTraceOp g₀ g₀` is state-free
   (`capOfBnd`), and `capDdc`/`capIter`/`capDdc0` carry `G` through.
7. `daContr = daMono daPermA − daMono daPermB` closes by `capSub`.

## `lieCovCap`

1. `lieCov_residual` applies **directly** to the goal's
   `− edgeLiePairFam … lieRefoldQ lieRefoldEps s`: the bridge `edgeEq` of
   `DeTurckRemainderLowBaseH2Cov.lean` is `rfl`, so no rewrite is needed.
2. `lieCovPair g₀ g₁ = appCcRS g₀ 6 4 2 (pureTrace g₀ g₁ 2) (pureTrace g₀ g₁ 4)`
   is `rfl` (`bdPureDT` and `pureDoubleTraceField` are the same structure).
   `ptAtgw s` clones `pureAtgw` at generic valence from the public
   `pureTrace_split`.
3. `lieCovR4_eq` splits into the curvature head and the quadratic.
4. **The `s`-factor is load-bearing.**  `(-(s/2))•lrCurvF g₀ T` is rewritten as
   `(-(1/2))•lrCurvF g₀ P` using `curvSmul` (linearity of `lrCurvF` in its
   tensor argument) and `P = s•T`.  Without this the arm is NOT capped:
   `lrCurvF g₀ T` contains the order-zero jet of `T`, which no cap controls,
   whereas `|P| ≤ Λ` is exactly `hP0`.  `capOfP` is what consumes it.
5. `lrQuadF` decomposes as six output-slot permutations of
   `lrQA`/`lrQB = lieCovArm2 ⋆ lrOmegaHat`, and both factors carry one
   derivative of the state.

## The two public wrappers that made `lrQuadCap` possible

The private grid windows `lrOmegaHat_gridWindow` and `bdArmSlot2_rfns_le` of
`RiemannCoefficientPalatiniRefold.lean` look like the only inputs, and
promoting them is ruled out by cost (reverse closure of that module: **170
modules / ~229k lines**, including the 19.5k/13.8k/10.9k/9.6k/9.4k-line
files).  They are not needed:

* `lieCovArm2` is a **public** def equal to `armSlotEndoCc g₀ 2 (bdConnPair …)`
  and `lieCovArm2_l2` is a **public** wrapper of `bdArmSlot2_rfns_le`;
* `lrOmegaHat` is re-estimated from its own public definition, using
  `fullRev0_eq` + `omRecover_add` (both public) for the REVERSED endomorphism
  and `connLow_rfns` (public, `FlatArmCoeffConnectionDifferenceBridge.lean`)
  for the `connDiffLoweredCc` ↔ `connDiffSection` fibre-norm bridge.

That is the whole lesson of this session: **before declaring a private wall,
grep for a public wrapper of the private lemma.**  Three of the four walls
diagnosed in session 2 dissolved this way; the fourth (`koszulOp`) was
side-stepped by abstraction rather than promotion.

## Traps hit

* `set_option … in` must come AFTER `open … in`; the reverse is a parse error.
* A qualified name may not be broken across lines at the `.`.
* `le_of_eq rfl` for a `δ ≤ δ₀` argument silently unifies `δ := δ₀` and then
  the later `0 ≤ δ` argument mismatches — pass the real `hδ_le`.
* `cometricDoubleTraceField` lives in
  `PDE.RicciFlow.IntrinsicSpectral.DeTurck`, `convexPerturbation`/`realizedFam`
  in `PDE.DeTurck.RicciLinearization`; both opens are needed and are exactly
  the ones `LowRegC01JetTower.lean` already carries.
* `capOfArm` takes an offset-`+2` window; offset-`+1` producers need
  `antidiagonalTupleGridWindow_mono` first.

## Verification

Focused check green; targeted build of
`…DeTurck.LowRegC01JetTower` green (9610 jobs).  Axiom census: `ricciDACap`,
`lieCovCap`, `selfLow_jet`, `c0_jet_tower`, `c1_jet_tower`, `low1Ker_jet` and
every new declaration are `[propext, Classical.choice, Quot.sound]`.  No
`sorryAx` anywhere in the census.

# Session 4 (2026-08-04): the lieCov arm in the marked currency

## The decisive finding: the residual has NO second derivative of the state

The brick was dispatched on the reading that `lieCovR4` carries one order-two
factor `∇²T` and that the session's design question was how to mark it.  That
reading is WRONG, and checking it was the whole difficulty.

`lieCovR4 = (-(s/2))•lrCurvF T − lrQuadF g₁`, and

* `lrCurvF g₀ T = appCcRS (lrRiemW1 g₀) T + appCcRS (lrRiemW2 g₀) T`
  (`RiemannCoefficientPalatiniRefold.lean:7936`), whose evaluation
  `lrCurvF_unitModel_apply` is
  `T(Rm(g₀)(m0,m1,m2), m3) + T(m2, Rm(g₀)(m0,m1,m3))` —
  the **fixed background** Riemann tensor contracted with `T` ITSELF.  Zero
  covariant derivatives of the state, linear in the state, state-free
  coefficient.
* `lieCovPair` is `pureTrace 2 ⋆ pureTrace 4`, a pure double moving trace, also
  order zero in the state (`ptAtgw`, offset `+1`).

The `∇²T` in the neighbourhood belongs to `edgeLiePairFam`, the SUBTRACTED edge,
and it is exactly what `lieCov_residual` cancels: the `∇A`-headed arm minus the
`∇²T`-headed edge equals one product of two order-zero-or-lower factors.  So the
arm's real structure is

```
residual = (−1)•[ Pair ⋆ σ(Ext²( (−½)•lrCurvF P )) − Pair ⋆ σ(Ext²( lrQuadF g₁ )) ]
             u = 0 + 0 = 0                            u = 0 + 2 = 2
```

Over-count exhibit EIGHT.  The planner's design question ("marked treatment of a
`c = 2` factor") never arises on this arm.

## The one genuine structural point: the halves have DIFFERENT mark counts

`mkAdd`/`mkSub` need a common `u`, and no cheap demotion exists — dropping a
mark costs a level (`markGrid b (u+1) w ⊆ markGrid b u (w+1)` at best), and the
level is exactly the budget.  So the arm must be split at the TENSOR level, not
at the window level.  The split runs along the sub-linearity of the three
structural maps, all of which already exist in `PairTrace.lean`:

`slotExtend_sub_cc` (twice, through `extSub`) → `rsDomDomCongrSection_sub_cc`
→ `appCcRS_sub_right_cc`, then `neg_smul, one_smul, neg_sub` turns
`(−1)•(A − B)` into `B − A`.  The two halves are then bounded separately —
`markJet0` on the unmarked half (no `Λ₁` at all, axiom-clean) and `markJet` on
the twice-marked half — and recombined with `norm_sub_le` plus
`‖a−b‖² ≤ 2‖a‖²+2‖b‖²`.

## What landed

In `SelfLowArmCaps.lean` (import of `…TensorHilbert.TameLieCorrJets` added;
1012 → 1521 lines, well under the cap):

* `pairMark` — `lieCovPair`, `u = 0`, from `ptAtgw` at `s = 2, 4` through
  `mkOfWin` (whose input shape IS `ptAtgw`'s output shape — nothing to prove).
* `curvMark` — `lrCurvF g₀ P`, `u = 0`, from `mkOfBnd` on the two fixed
  curvature coefficients and `mkOfP` on the state.  Hypothesis: the δ-anchor
  only.
* `omegaMark` — `lrOmegaHat`, `u = 1`: `revEndoAtgw` (order zero) against
  `connDiffLoweredCc`, whose jets transfer by `connLow_rfns` to
  `connDiffSection` and are marked by `connDiffMark`.
* `lrQuadMark` — `lrQuadF`, `u = 2`, six output-slot permutations of
  `lieCovArm2 ⋆ lrOmegaHat` via `mkDdc0`; `lieCovArm2`'s jets transfer by
  `lieCovArm2_l2`.  This is the ONLY quadratic part of the residual.
* `extSub` (private) — `Ext²` is sub-linear; `slotExtendIter g₀ 0 4 2 Z =
  slotExtend 1 5 (slotExtend 0 4 Z)` is `rfl`.
* `lieCovJet` — the deliverable, in the `ricciAAJet` shape
  `(K₀ i + K₂ i·∑_{j<3}‖∇^{1+j}P‖²)·(1 + ∑_{j<i+2}‖∇ʲP‖²)`, constants chosen
  before `T`, no `R₀`, no cap, no `s`, exactly one power of `‖P‖²_{H³}`.

The `s`-factor trick is load-bearing here for the same reason as in `lieCovCap`:
`curvSmul` turns `(-(s/2))•lrCurvF T` into `(-(1/2))•lrCurvF P`, and only the
perturbation `P = s•T` has a δ-anchored order-zero jet.  `mkOfP` is what
consumes that anchor.

## What did NOT land, and the precise blocker

`ricciDALow` — the `∇A ⋆ ∇T` arm of `ricciGoodLow`
(`ricciGoodLow g₀ g₁ P = ccInputSymm (ricciAAArm + ricciDALow)`,
`LowRegC01JetTower.lean:229`) — is NOT closed.  The blocker is one missing
producer, and it is NOT combinatorial:

`ricciDALow` needs `G = dagLowOp ⋆ ∇P` at `u = 2`, level `i`.
`∇P` is free (`mkOfDP`, `u = 1`, constant `1`).
`dagLowOp = permCoeff(daPermA) ⋆ covGrad 3 3 (connLowOp g₀ g₁)`, and the ONLY
window the tree has for `connLowOp` is `clAtgw`, an `atgw bP (i+1)` window —
lossy in exactly the fatal way.  Reading it at order `i+1` gives `u = 0` at
level `i+1`, i.e. **one level over budget**, and the level cannot be recovered:
`G` would be `u = 1` at level `n+1` and the arm would integrate onto
`range (n+3)`.

What is needed is a `topSeparated`-shaped radius-free producer

```
|∇ⁱ(covGrad 3 3 (connLowOp g₀ g₁))|²(x)
    ≤ Ktop·bP(i+1) + Kc i·∑_{k<i} bP(i−k)·atg(bP)(k+1)
```

(exactly `mkOfTop`'s input), i.e. `u = 1` at level `i`.  Mathematically it is
true because `connLowOp g₀ g₀` is built from `g₀`, `g₀⁻¹` and permutations and
is therefore `∇^{g₀}`-PARALLEL, so `∇(connLowOp g₁) = ∇(connLowOp g₁ −
connLowOp g₀)` and the difference is `perm ⋆ slotIns(gInvDiff) ⋆ koszul`, whose
derivative carries an explicit `∇P`.  In Lean this needs, in order:

1. `covGrad (permCoeff g₀ ρ) = 0` and `covGrad (koszulOp g₀) = 0`
   (parallelism of the fixed permutation and Koszul coefficients);
2. `covGrad (slotInsertEndoCc s (fullRaisedEndoField g₀ g₀)) = 0` — the frozen
   half of `sieSplit`;
3. a `topSeparated` window for `covGrad (gInvDiffRaisedEndoField g₀ g₁)`, whose
   `atg bP q` (EXACT weight `q`) producer already exists at
   `rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le`.

Routes explicitly ruled out this session:

* **Demote the mark.** Costs a level; the level is the budget.
* **Leibniz through `connLow_app`.**
  `∇A ⋆ ∇T = ∇(A ⋆ ∇T) − A ⋆ ∇²T = ∇(connDiffLowered) − A ⋆ ∇²T`.  Both
  summands are individually `u = 1` at level `i+1` (each has a lone
  `|∇^{i+2}P|²` head) — strictly worse than their difference, and there is no
  cancellation identity here of the kind `lieCov_residual` supplies for lieCov.
* **A `markJet1` bridge.**  It IS cheap and worth recording:
  `markGrid b 1 n ≤ (n+1)²·atgw b (n+2)` (each `b(c+1)·atg b k ≤ atg b (c+1+k)`
  by `single_factor_mul_antidiagonalTupleGrid_le`, total weight `≤ n+1`), and
  `atgwToJet` at `w = 2` then lands on `range (n+2)` — the deliverable budget,
  with NO `Λ₁` factor.  So a `u = 1` arm at level `n` is perfectly tame.  It
  does not rescue `ricciDALow`, because the problem there is the LEVEL
  (`u = 1` at level `n+1`), not the mark count.

## Verification

Focused checks of `TameMarkWin.lean` and `SelfLowArmCaps.lean` green (the only
`sorry` warning is the declared `gridIntHigh` frontier).  Targeted builds of
`…TensorHilbert.TameLieCorrJets` and `…DeTurck.SelfLowArmCaps` green.

## Traps hit

* `open … in` must precede `set_option … in` (already recorded) — and the
  `_cc` sub-linearity lemmas (`slotExtend_sub_cc`,
  `rsDomDomCongrSection_sub_cc`, `appCcRS_sub_right_cc`) live in
  `CurvatureCoefficientDifferenceJetTower`, which this file does NOT open by
  default.  Two `open CurvatureCoefficientDifferenceJetTower in` lines.
* `lieCov_residual`'s LHS mentions
  `deTurckLieCovDerivRefoldPairTraceFamily … ![…] ![…]`, which is only DEFEQ —
  not syntactically equal — to `edgeLiePairFam … lieRefoldQ lieRefoldEps`.
  `capCongr` accepted it because the expected type drove elaboration; `rw` does
  NOT.  Restate it as a `have hres0 : <edgeLiePairFam form> = … := lieCov_residual …`
  and rewrite with that.
* `mkApp` reports its mark count as `u + v` syntactically; `simpa using` is
  needed to normalise `0 + 0`, `0 + 2`, `1 + 1` to the declared count.

## Session 5 (2026-08-04): the `covGrad connLowOp` brick + `ricciDAMark`/`ricciDAJet`

**The blocker of session 4 is gone.**  `covGrad 3 3 (connLowOp g₀ g₁)` now has a
once-marked window at its own level `i` (`clCovMk`), so `ricciDALow` closes at
`u = 2` (`ricciDAMark`) and at the deliverable jet shape (`ricciDAJet`).  All
six arm families of the tame C0 bottom are now closed.

### The route that worked (and why the dispatched one was over-priced)

The dispatch asked for `covGrad(permCoeff) = 0` and `covGrad(koszulOp) = 0`.
**Neither is needed.**  `permCoeff` never has to be differentiated at all:

* `connLowOp g₀ g₁ = permCoeff(lowPerm) ⋆ (E₁ ⋆ Z)` with
  `E₁ = slotInsertEndoCc 2 (fullRaisedEndoField g₀ g₁)`.
* The OUTER `permCoeff` is a fibre isometry of the iterated jets
  (`rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr`, the `mkDdc` idiom) — no
  parallelism, just `slotPermCLM_apply` + `toModel_ofModel` for `hrel`.
* The INNER `Z` is written out explicitly (the opacity trick used offensively a
  second time: `clZ` is `rfl`, the private `koszulOp` is still never named) as
  `(1/2)•(permCoeff ρ₁ + permCoeff ρ₂ − permCoeff ρ₃)`, and
  `appCcRS Φ (permCoeff ρ) = reindexCoeffGen Φ ρ` (`permRe`, ~12 lines) turns
  each into a SOURCE reindex, again a jet isometry
  (`rfns_iteratedCovGrad_reindexCoeffGen_eq`).
* What is left is `∇^{i+1}E₁`, and there `sieZero` (the generic-`s` sibling of
  the public `covGrad_slotInsert_fullRaised_id_eq_zero`, proved from the public
  `endoCovariantDerivative_fullRaised_id_eq_zero` + the generic
  `tensorCovDerivAt_slotInsertEndoCc_eq` — the `s = 0` proof verbatim) kills the
  frozen half, leaving the inverse-metric difference, whose jets the tree
  already delivers at EXACT weight.

So the brick is `clExact` (`|∇^{i+1}connLowOp|² ≤ C i · grid(bP)(i+1)`) plus the
new combinatorial entry `mkOfAtg`/`atgLeMark1`.  No `topSeparated` producer was
needed and no parallelism of a permutation coefficient was proved.

**Over-count exhibit NINE** (minor): `jetSmul` already exists, public, in
`DeTurckRemainderLowBaseH2VB.lean`; a duplicate was written and had to be
deleted.  Grep before declaring even a four-line helper.

### Lean notes

* `rw [hA, hB, hC] at h1 h2` applies EVERY rewrite to EVERY hypothesis and fails
  if one of them has no occurrence.  Split into `rw [hC] at hsub` /
  `rw [hA, hB] at hadd`.
* `positivity` does not read hypotheses: `0 ≤ fr^2 * Cb (i+1)` needs
  `mul_nonneg _ (hCb_nn _)`, not `positivity`.
* The `(A + B - C).toSection x` shape must be pushed through
  `SmoothCcTensor.toSection_sub` / `_add` by an explicit `rw [show … from by …]`
  before `riemannianFiberNormSq_sub_le` applies; `set`ting the three iterated
  covgrads first keeps that rewrite readable.

Verification: focused check green, targeted build green (9614 jobs).  Axiom
census: `sieZero`, `permRe`, `clZ`, `clExact`, `clCovMk`, `ricciDAMark` clean;
`ricciDAJet` carries `sorryAx` through `gridIntHigh` only (it consumes
`markJet`), exactly like `lieCovJet`.  `ricciDACap`/`lieCovCap` unchanged and
still clean.
