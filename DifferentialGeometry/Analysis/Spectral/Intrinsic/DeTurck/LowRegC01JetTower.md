# `LowRegC01JetTower.lean` — bricks A1a + A1b

Target: the `C1` and `C0` analogues of `c2_jet_tower`, i.e. the all-order `L²`
jet towers of the two coefficients that assemble `LowBaseActionData.a1`.

## What landed

* `selfLow_split` — public re-derivation of the private `selfBase_decomp`
  (`DeTurckRemainderLowBaseAction.lean:11165`) from public API only
  (`selfLow_good`, `deTurckLieCoeffField_eq_covDerivArm_add_endoArm`,
  `tail_base_split`).  This is the *cancellation-preserving* grouping

  `rhsSelfLow = (-2)•ricciGoodLow + (deTurckLieCovDerivArmField − edgeLiePairFam)
    + lc0VB + lc0AMix + lc0Riem`.

  It matters because the literal summands of `rhsSelfLow`
  (`deTurckLieCoeffField`, `lieCorr0Field`) each cost **two** derivatives of the
  state; only after the pairwise head cancellation does every summand cost one.
  A frontier stated on the literal summands would be FALSE at the tower's
  `range (i + 2)` budget.
* `c1_jet_tower`, `c0_jet_tower` — both towers, in exactly `c2_jet_tower`'s
  shape (constants before the state, `range (i + 2)` budget, `δ ≤ 1/3` the only
  smallness input, inert `H^{a+2}` ball).  Both are **proved from** the
  integrand-level frontiers below; the path-integral passage, the
  `Real.sqrt`-bookkeeping and the `phiMetCurvCoeff` constant summand are real
  and sorry-free.
* `jetNeg`, `jetAdd` in `LowRegOpJetWindows.lean` (canonical home, next to
  `jetSub`); `moserWin_add`'s inline copy of the sum bound was replaced by
  `jetAdd` and the theorem gained the now-required `omit
  [BoundarylessManifold I M]`.

## What did NOT land, and why (the route obstruction)

`low1Ker_jet` and `selfLow_jet` — the uniform-in-`s` jet windows of the two path
integrands — are stated and carry one `sorry` each.  They do **not** close on the
route prescribed by `F6_ESTIMATE_RECON.md` §7.4 ("TK1+TK2 verbatim"), and the
reason is structural rather than a missing local proof step.

**The `IsMoserWin` vocabulary cannot express these summands.**  A window carries
an order-0 fibre cap `S` alongside the affine jet envelope, and the product step
`moserWin_appRS` is `appRS_hn_sup`, which *requires a fibre cap on both factors*
(it is Gagliardo–Nirenberg interpolation: `exists_integrated_iteratedCovGrad_
diagonalProductGrid_twoArm_rs_le` takes `ΛS` and `ΛT` and no ball).  Both `C0`
and `C1` contain the **bare connection difference** `connDiffSection gm g`
(equivalently `connDiffLoweredCc`), which is `∇P` up to algebra:

* `C1`: `linearizedRicciConnDiffOrder1CoeffField g gm =
  appCcRS(ricciCometricFourTraceCastG0 g gm, linearizedRicciConnDiffOrder1KernelField g gm)`
  (`RicciConnDiffOrder1TameEnvelope.lean:116`, public) and the kernel field is a
  five-term permuted combination of
  `connDiffContrInsertionField g gm = reindex(slotExtend²(connDiffSection gm g))`.
  That split is `private` in three places (`ricci1_split`
  `DeTurckRemainderLowBaseAction.lean:12380`; `kernelField_eq_neg_arm_combination`
  `LieFieldJetL2Summed.lean:136` and `RicciConnDiffOrder1TameEnvelope.lean:738`)
  and must be promoted or re-derived.
* `C0`: even after the Palatini refold `lieCov_residual`, the residual
  `lieCovR4 ⊃ lcvQuad ⊃ lcvQA/lcvQB ⊃ lcvOmega =
  appCcRS(slotInsertEndoCc(fullRaisedEndoField gm g), domDomCongr(connDiffLoweredCc g gm))`
  still contains it.

`∇P` has **no** order-0 fibre bound from `δ ≤ 1/3` — the fibre certificate caps
`P`, not its derivative — and no ball-free substitute exists.  So the window
predicate cannot be instantiated for these families, and `moserWin_appRS` cannot
pair them with anything.

This is *not* what happened in TK3.  `topKer_jet`'s three summands are
`lieRefold2`, the `Φmet` deviation and `ricciTop`, and the C2 refold pushes every
connection difference into curvature and pair traces, leaving only objects that
are algebraic in the moving metric (hence capped by `δ`) times `symmS g T`
(capped by `δ`).  The C2 arm is the coefficient of `∇²` and is metric-algebraic;
the C0/C1 arms are quadratic in `∇P` and are not.

**What the tree actually stocks for this.**  Every family with a bare `∇P`
already has a *radius-free* per-order engine, in a different currency: the
`antidiagonalTupleGrid_integral_radiusFree` route, where the only capped object
is `P` itself and the higher jets sit inside a combinatorial grid integrated once
against `‖P‖_∞`.  Confirmed instances (all ball-free; their
`2·finrank ℝ E + 10 ≤ a` gate is on a *free internal* order parameter and is
therefore free — `moserWin_sharp` already exploits exactly this):

| producer | file:line | shape |
|---|---|---|
| `connDiffSection_lowOrder_jetL2_radiusFree` | `Sobolev/TensorHilbert/DeTurckVFJetRadiusFree.lean:581` | affine, `range (i+2)`, sharp |
| `wXi_lowOrder_jetL2_radiusFree` | same:733 | affine |
| `wOmega_lowOrder_jetL2_radiusFree` | same:1117 | affine |
| `cometricCastG0_order0sup_jetL2_radiusFree` | same:66 | cap + affine |
| `sharpFlatEndoCc_lowOrder_jetL2_radiusFree` | same:428 | cap + affine (already used by `moserWin_sharp`) |
| `mcd_l2_radiusFree` | `Sobolev/TensorHilbert/LieCorr0CoeffDiffRadiusFree.lean:2107` | — |
| `lieCorr0Field_perOrder_l2_radiusFree` | same:3104 | **top-separated**: `Atop i‖∇^{i+2}(symmS T)‖² + Alow i(1+range (i+2))` |
| `deTurckLieCoeffField_perOrder_l2_radiusFree` | `Sobolev/TensorHilbert/DeTurckLieCoeffDiffRadiusFree.lean:273` | **top-separated**, same shape |
| `ricciArmOrder0BaseCoeff_perOrder_l2_radiusFree` | `Spectral/Tensor/CovGrad/CurvatureCoeffDiffRadiusFree.lean:127` | — |

Two obstacles remain even with these:

1. The two *composite* public producers are **top-separated at `+2`**, which is
   one order above `c0_jet_tower`'s budget.  Their `Atop` terms are exactly the
   heads that `selfLow_split` cancels at the tensor level, so the assembly must
   go through `selfLow_split` and the *pieces*, not through the composites.
2. The sharp pieces are `private`: `lc0Base_perOrder_rf` (`:113`),
   `lc0Diff_perOrder_rf` (`:164`), `lc0Riem_perOrder_rf` (`:258`),
   `lc0VBAMix_perOrder_rf` (`:3061`) in `LieCorr0CoeffDiffRadiusFree.lean`, and
   `dLaField_perOrder_rf`/`dLbField_perOrder_rf` are public but only feed the
   top-separated composite.  Moreover the two `lc0*` piece lemmas are stated at
   `range (i + 3)`, i.e. **one order lossier** than the fixed-order-2 siblings
   (`lc0VB_h2_rf` reaches order 2 from `lowJetSq g 3 P`, offset `+1`), so even
   after promotion they do not directly meet the budget.

## Probe outcome (the permitted one-shot de-gating probe)

`linearizedRicciConnDiffOrder1KernelField_order0sup_perOrder_l2_tameEnvelope_generic`
(`RicciConnDiffOrder1TameEnvelope.lean:1240`): **gate is load-bearing, probe
abandoned.**  It forwards `ha_super` to
`connDiffContrInsertionField_..._generic` (`:982`), which consumes it twice —
`antidiagonalTupleGrid_integral_ballUniform_tameWindow g₀ a ha_super hR` and
`deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow g₀ a
ha_super` — and the statement is additionally **ball-based**: the hypothesis
`∀ j ≤ a+2, ‖∇ʲP‖ ≤ R` enters the pointwise constant
`Λ2 = fr²·CA 0·(1 + Cemb²(a+2)R²)`.  Not a forwarded-only gate; this is not the
`appCc_cap_hs_le` situation.

## Recommended next step

**Do not build a window algebra for `C0`/`C1`.**  In the radius-free currency
every factor is a jet of `P` and there is exactly *one* cap, on `P` itself; the
whole coefficient is written as a combinatorial grid in `P`'s jets and integrated
**once**.  A two-arm product predicate is the wrong shape here — that is why the
`IsMoserWin` route stalls and why every stocked producer for a `∇P`-carrying
family is a bespoke per-order engine rather than an algebraic composite.

The right brick is: **radius-free siblings of the existing ball-based composite
producers**, i.e. replace `boundedFactorGridWindow_integral_ballUniform_
tameWindow` by `antidiagonalTupleGrid_integral_radiusFree` in

* `connDiffContrInsertionField_perOrder_l2_topSeparated_generic`
  (`ConnDiffJetL2Summed.lean:149`) — note its conclusion is already **sharp**,
  `Ktop‖∇^{i+1}P‖² + Kc i (1 + range (i+2))`, i.e. inside `c1_jet_tower`'s
  budget; only `hPball` has to go;
* then `linearizedRicciConnDiffOrder1CoeffField` via `ricci1_split` and
  `linearizedRicciConnDiffOrder1CoeffField_eq_appCcRS`, whose outer factor
  `ricciCometricFourTraceCastG0` *is* capped
  (`cometricCastG0_order0sup_jetL2_radiusFree`, `DeTurckVFJetRadiusFree.lean:66`);
* then `deTurckLieArm1Coeff` via `deTurckLieArm1Coeff_eq_lieArm1Piece_sum`
  (14 pieces) — the radius-free sibling of
  `deTurckLieArm1Coeff_realizedFam_jetL2_perOrder_ballUniform`
  (`DeTurckLieArm1CoeffL2JetBound.lean:4917`).

Those two discharge `low1Ker_jet` (brick A1a).  For A1b, the same treatment of
the five `selfLow_split` summands, plus promotion of the four `private`
`lc0*_perOrder_rf` lemmas of `LieCorr0CoeffDiffRadiusFree.lean` and a one-order
sharpening of `lc0Riem_perOrder_rf` / `lc0VBAMix_perOrder_rf` from
`range (i + 3)` to `range (i + 2)` (the fixed-order-2 siblings already achieve
the sharp offset, so the loss is slack, not mathematics).

## Verification

`LowRegOpJetWindows.lean`: focused check green (its one new `unusedSectionVars`
warning on `moserWin_add` fixed by the required `omit`).

**Tooling blocker hit during this brick.**  The targeted olean refresh of
`LowRegOpJetWindows` failed twice: a single `lean` process on
`Spectral/Tensor/CovGrad/CurvatureCoefficientDifferenceJetTower.lean`
(15 111 lines) reached ~7 GB and free RAM hit 252 MB on this 16 GB box.  That
module needed rebuilding because the E3 brick's edit to the low module
`DeTurckRemainderDefs.lean` invalidated the downstream chain; killing the OOMing
process deleted its olean, so it had to be rebuilt before anything downstream
could be checked at all.  Budget for this when touching this subtree.

Because of that, `c0_jet_tower` is written against the *pre-existing* `jetSub`
rather than the new `jetAdd`, so this file checks against the current oleans
without waiting on the refresh.

## 2026-08-03: FIRST clean check — two pre-existing syntax errors, then green

The `TameLipschitz` split unblocked this file's first real check, and it did not
parse.  Both `low1Ker_jet` and `selfLow_jet` had their
`set_option linter.unusedVariables false in` /
`set_option linter.unusedSectionVars false in` pair placed **between** the doc
comment and the `theorem` keyword, which Lean rejects
(`unexpected token 'set_option'; expected 'lemma'` at `:65` and `:154`).  The
modifiers were moved above their doc comments, matching the correct order this
same file already uses at the `Towers` section.  No statement or proof changed.

Focused check now green: exactly the two expected `sorry` warnings,
`low1Ker_jet` and `selfLow_jet`, 19 s / 3.53 GB.  Targeted build green.

Axiom census (first time possible): `c1_jet_tower` and `c0_jet_tower` both
depend on `[propext, sorryAx, Classical.choice, Quot.sound]`, and the `sorryAx`
enters **only** through those two integrand frontiers — every other named input
was censused clean: `selfLow_split`, `c1_eq`, `c0_eq`, `selfLow_joint`,
`c2_jet_tower`, `rhsLow1_path_joint`, `path_jetL2_le`, and the four moved
`TameLipschitz` public endpoints.  So the two towers are complete modulo exactly
the two stated frontiers.

Lesson: a file written while its import chain is broken has never been parsed.
Budget a syntax pass the first time such a file is checked.

## 2026-08-03 (session N+1): C0 statement surgery LANDED; C1 currency layer built, C1 NOT closed

### Part 1 — `selfLow_jet` ball-threading (DONE, green)

The statement was **false as landed** (two of `selfLow_split`'s five summands
are quadratic in `∇P`; concentration counterexample at `i = 0`).  Repaired by
threading the `H^{a+2}` ball that `c0_jet_tower` already binds and previously
discarded at its application site.

Widened signature (constants still bound after the ball data, per the
quantifier rule):

```
theorem selfLow_jet
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (a : ℕ) (ha : 1 ≤ a)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ Kk : ℕ → ℝ, (∀ i, 0 ≤ Kk i) ∧
      ∀ (T …) (hT …) {δ} (hδ0) (hδ_le) (hδg) (hδZ),
        ‖smoothCcToTensorHs g ((a : ℝ) + 2) T‖ ≤ R₀ →
        ∀ (i : ℕ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → …
```

**Gate choice: `1 ≤ a`, ball form (not `3 ≤ a`, not a pointwise `‖∇P‖_∞`
hypothesis).**  Reasons, in order:

* `1 ≤ a` is the weakest gate the mathematics needs (`H³ ⊂ C¹` in dimension
  three) and is what the Galerkin bottom rungs can supply from an `H³` a-priori
  bound.  `3 ≤ a` would over-gate; `a ≥ 16` (the ball-based `order0sup`
  producers' gate) is forbidden and was not inherited.
* The **pointwise** form (`∀ x, |∇T|²(x) ≤ L`) was considered and rejected:
  `c0_jet_tower` would then have to *produce* a fibre-Morrey `H^{a+2} → C¹`
  bridge that does not exist in the tree, which would inject a NEW frontier
  into `c0_jet_tower` and break its "sorryAx only via `selfLow_jet`" status.
  With the ball form `c0_jet_tower` passes its own `hball` through verbatim.

`c0_jet_tower` gained `(ha : 1 ≤ a)` — it had no gate at all, and cannot
discharge `selfLow_jet` without one.  It has no consumers yet (only the axiom
census), and its eventual consumer will carry `a2_ladder`'s `3 ≤ a`, so the
change is free.  `low1Ker_jet` stays ball-free (C1 is linear in `∇P`).

**0% new mathematics.**  This is statement repair; `selfLow_jet` is still
`sorry` and is brick A1-CUR-2.

### Part 2 — A1-CUR-1 (`low1Ker_jet`): NOT closed; the currency layer is built

`low1Ker_jet` is **still `sorry`**.  What was built is the reusable machinery it
needs, verified sorry-free (see `AtgwArmFold.md`, `RicciOrder1RadiusFree.md`).

Route confirmed and unchanged: `rhsLow1Coeff = (-2)•ricciArm + lieArm`, both of
the shape `appCcRS(order-0-capped arm, connection-difference arm)`, folded in
the `antidiagonalTupleGridWindow` currency and integrated once.  **No
stop-signal was hit**: no summand of `rhsLow1Coeff` carries two connection
differences, and the Ricci kernel folds at `atgw(l + 2)`, not `(l + 3)`.

Remaining for `low1Ker_jet`, in order:

1. `ricciCometricFourTraceCastG0` pointwise `atgw` at offset `+1` — a
   valence-`(4,2)` clone of `rfns_iCG_cometricCastG0_atgw_rf`
   (`DeTurckVFJetRadiusFree.lean:824`, ~134 lines).  Its two inputs are already
   radius-free: `rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le`
   and `exists_bound_riemannianFiberNormSq_smoothCcTensor` on
   `cometricDoubleTraceField g₀ 2`.  Use
   `ricciCometricFourTraceCastG0_eq_reindex_combination` +
   `ricciArmPrincipalCoeffPure_eq_doubleTrace_add_appCcRS`.
2. Ricci arm = `atgwFold` (u = 0, v = 1) against `ricciKerAtgw`, then
   `atgwToJet` with `w = 2` — now ~60 lines, not 225, because the fold is
   generic.
3. Lie arm: `deTurckLieArm1Coeff_eq_lieArm1Piece_sum` gives three
   `lieArm1Piece(σ', ρ, Ψ)`; each is
   `reindexCoeffGen (appCcRS (deTurckLieTraceCoeff g₀ g₁ σ') (slotExtend² Ψ)) ρ`.
   Needs an `atgw` at `+1` for `deTurckLieTraceCoeff` and at `+2` for each of
   the three `Ψ`.  Note that at the tower's call site `g_bg = g₀`, so
   `lieArm1ConnDiffBgCc g₀ g₁ g₀ = connDiffSection g₁ g₀` — the *same* object
   `rfns_iCG_connDiffSection_atgw_rf` already covers; only `lieArm1PsiB`
   (`connDiffLoweredCc` against `sharpFlatEndoCc`) is genuinely new.
4. `low1Ker_jet` = `jetAdd`/`jetSmul` over 2 and 3, with the `moserWin_sharp`
   `choose`-over-`a` idiom (`LowRegOpJetWindows.lean:684`) to instantiate the
   engines' free internal order at `2 * finrank ℝ E + 10 + n` and so remove the
   `i ≤ a + 1` gate.  `IsPathPert` (`LowRegOpJetWindows.lean:547`) is the exact
   bridge: it carries `htie`, the order-0 fibre bound (`Λ₀ = finrank · δ₀`) and
   the jet domination `lowJetSq g n P ≤ lowJetSq g n T`, i.e. everything the
   radius-free engines want, and `pathPert_rad` produces it for the radial path.

### Lessons

* The tower already transitively imports `RicciConnDiffOrder1TameEnvelope` but
  **not** `LieFieldJetL2Summed`.  The A1-CUR plan's instruction to promote the
  `LieFieldJetL2Summed` copy of `kernelField_eq_neg_arm_combination` was
  therefore wrong for this consumer; the envelope copy was promoted instead (no
  new import, no duplicate).
* `permApp_eq_rs` is `private` in the READ-ONLY low-base action file, so the
  `rsDomDomCongrSection` form of the split had to be re-derived publicly
  (`permAppEqRs`).  All of its ingredients (`slotPermCLM_apply`,
  `Tensor0SSpace.toModel_ofModel`, `toModel_rsDomDomCongr_apply`) are public.
* `riemannianFiberNormSq_add_le` concludes `≤ 2*a + 2*b`, not `≤ 2*(a+b)`.
* `Combinatorics.antidiagonalTupleGridWindow` is a plain `def`; `rw` on it fails
  with "Failed to rewrite using equation theorems".  Use `rfl` on a stated
  function equality instead.

### Verification

Focused checks of every edited file passed.  `LowRegC01JetTower.lean` has
exactly **two** `sorry` (`low1Ker_jet`, `selfLow_jet`) — the brick's target of
one was not reached.  `selfLow_split`, `c1_jet_tower`'s derivation and
`c0_jet_tower`'s derivation are unchanged apart from the threaded ball.

### Addendum — promotion fallout and final build

Promoting the envelope's `slotPermCc` / `kernelField_eq_neg_arm_combination` /
seven permutations collided with `LieFieldJetL2Summed.lean`'s own `private`
copies of the same names (that module transitively imports the envelope).
**`private` hides a name from importers but does not give it a distinct
fully-qualified name**, so a same-named public import is a hard error.  Fixed by
deleting the nine duplicates there — the dedup the A1-CUR plan asked for, applied
on the other side.  Full details in `RicciOrder1RadiusFree.md`.

Final verification: full targeted build **9599 jobs, 0 errors**.  Census:
`c1_jet_tower`/`c0_jet_tower` carry `sorryAx` only through their integrands;
`selfLow_split` and all eight new/promoted declarations clean.

## 2026-08-04 (session N+2): `low1Ker_jet` CLOSED — A1-CUR-1 complete

`low1Ker_jet` is proved sorry-free.  The file's sorry census is now **one**
(`selfLow_jet`, brick A1-CUR-2), and `c1_jet_tower` is
`[propext, Classical.choice, Quot.sound]` — the first of the two low-base jet
towers to become unconditional.

### Proof of `low1Ker_jet`

The statement was **not** touched (ball-free, `∃ Kk, ∀ T`, `range (i + 2)`,
`δ ≤ 1/3` the only smallness input).  The proof is three moves:

1. **Pointwise window.**  `low1Atgw`
   (`Analysis/Sobolev/TensorHilbert/Low1KerRadiusFree.lean`, new this session)
   bounds `|∇ⁿ((-2)•ricci₁ + lieArm₁)|²(x)` by `Kw n · atgw(bP)(n + 2)`,
   radius-free and gate-free.  `rhsLow1Coeff g g T 0 hδg hδZ s` is that
   expression by `rfl` once `g₁ := realizedFam g T 0 hδg hδZ s` is read off.
2. **Perturbation data.**  `pathPert_rad` at `δ₀ = 1/3` supplies, uniformly in
   `s ∈ [0,1]`: the tie `g₁ = g + P` with `P = convexPerturbation g T 0 s`, the
   fibre bound on `P`, the order-zero cap `Λ₀ = finrank · (1/3)` (which is what
   `atgwToJet` consumes), and `lowJetSq g n P ≤ lowJetSq g n T`.  Its
   `hTsup` input is the `topKer_jet` move: `symmS g T = T` by `hT`, then
   `rfns_symmS_zero_le_fibreSmall`.  **No constant sees `s`.**
3. **Integration.**  `atgwToJet` at `w = 2` turns the pointwise window into
   `‖∇ⁿX‖² ≤ Kw n · (∑_{k<n+2} Kint k) · (1 + ∑_{j<n+2} ‖∇ʲP‖²)`; summing over
   `q ≤ i` and replacing `P`'s jets by `T`'s gives
   `Kk i = ∑_{q<i+1} Kw q · (∑_{k<q+2} Kint k)`, manifestly nonnegative — so
   the `le_abs_self` trick of `topKer_jet` was not needed.

### Summand → window map (for A1-CUR-2's benefit)

* Ricci arm = `appCcRS (ricciCometricFourTraceCastG0) (order-1 kernel)`:
  `fourTrAtgw` (`+1`) folded against `ricciKerAtgw` (`+2`) by
  `atgwFold (u := 0) (v := 1)`.
* Lie arm = 14 `lieArm1Piece`s: `dltcAtgw` (`+1`) folded against the
  slot-extended `Ψ` (`+2`) by `atgwFold (u := 0) (v := 1)`, with
  `Ψ ∈ {connDiffSection g₁ g₀ (twice, via `bgCcEqConn`), lieArm1PsiB}`.
* `lieArm1PsiB` = `appCcRS (raised κ) (sharpFlatEndoCc)`: `kappaAtgw` (`+2`)
  against `sfEndoAtgw` (`+1`) by `atgwFold (u := 1) (v := 0)`.

### Edits outside this file

One: `b4_mcd_atgw` in `Analysis/Sobolev/TensorHilbert/LieCorr0CoeffDiffRadiusFree.lean`
promoted `private` → public (docstring added).  It is the `+2` window of
`metricConnDiffLoweredCc`, which is `-lieArm1LoweredBgKappa`, which is the `Ψ`
factor of `lieArm1PsiB`.  Name collision-scanned tree-wide before promotion.
Nothing else was touched; no statement anywhere was changed.

### Verification

Focused checks of `LieCorr0CoeffDiffRadiusFree.lean` (121 s),
`Low1KerRadiusFree.lean` (24 s) and `LowRegC01JetTower.lean` (19 s): green, no
warnings beyond the expected `selfLow_jet` sorry.  Final targeted build of the
census target — which rebuilds the promoted module,
`DeTurckRemainderLowBaseAction`, `LowRegOpJetWindows` and this tower —
**completed successfully, 0 errors**.  Census: `low1Ker_jet` and `c1_jet_tower`
`[propext, Classical.choice, Quot.sound]`; `c0_jet_tower` carries `sorryAx`
only through `selfLow_jet`; all twelve new declarations of
`Low1KerRadiusFree.lean` and the promoted `b4_mcd_atgw` clean.

## 2026-08-04 (session N+3): A1-CUR-2 ASSEMBLY — `selfLow_jet` PROVED over two arm frontiers

### What landed

`selfLow_jet`'s `sorry` is GONE.  The theorem is now a complete proof whose only
remaining inputs are two `private` per-arm capped windows in this file,
`ricciDACap` and `lieCovCap`.  Three of the five `selfLow_split` summands are
fully discharged, and the fourth is discharged down to one of its two arms.

| `selfLow_split` summand | window | where |
| --- | --- | --- |
| `(-2)•ricciGoodLow` — `A·A` arm (`ricciAAArm`) | `ricciAACap` | `SelfLowCapWindows.lean`, PROVED |
| `(-2)•ricciGoodLow` — Palatini arm (`ricciDALow`) | `ricciDACap` | this file, **sorry** |
| `deTurckLieCovDerivArmField − edgeLiePairFam` | `lieCovCap` | this file, **sorry** |
| `lc0VB` | `lc0VBCapAtgw` | session 1, PROVED |
| `lc0AMix` | `lc0AMixCap` | `SelfLowCapWindows.lean`, PROVED |
| `lc0Riem` | `lc0RiemCap` | `SelfLowCapWindows.lean`, PROVED |

`ricciGoodCap` (this file) assembles the first two through `ccInputSymm`, which
is free: it is a half-sum with a product against the fixed `ccSlotSwapField`.

### The assembly (the session's main deliverable)

Structure of `selfLow_jet`, mirroring `low1Ker_jet`:

1. `gradCapOfBall hDim g a ha hR₀` fixes `Λ₁` from the threaded `H^{a+2}` ball.
2. `Λ := max 1 (max (finrank·(1/3))² Λ₁²)` — **before** the state, and it never
   sees `s`.  This single `Λ` serves both caps: `gridBase … 0 ≤ Λ` from
   `pathPert_rad`'s `hPsup`, and `gridBase … 1 ≤ Λ` from `Λ₁` after
   `P = s•T` with `s ∈ [0,1]` (the `s²  ≤ 1` contraction).
3. The five capped windows and `capJet` are obtained at that `Λ`.
4. `capSmul`/`capAdd` chain the five into a capped window of the five-term sum;
   `capCongr` transports it along `selfLow_split` (whose `let` zeta-reduces
   silently) to `rhsSelfLow`.  Constant `KS` is the explicit
   `2(2(2(2·4K₁+2K₂)+2K₃)+2K₄)+2K₅`.
5. `capJet` integrates per order; `pathPert_rad`'s `hPjet` dominates the
   perturbation's jets by the state's; `Finset.sum_mul` closes.

Landing budget: `range (i + 2)`.  Gate: `1 ≤ a`.  **Neither stop signal fired** —
no `range (i+3)`, no `a ≥ 16` gate inherited (the supercritical gate of
`lc0AMix_perOrder_rf`/`lc0Riem_perOrder_rf` comes from their
`cometricCastG0_order0sup_jetL2_radiusFree` route and is bypassed entirely).

### The `ricciAAKer` split — session 1's named blocker, dissolved

See `SelfLowCapWindows.md`.  Summary: the six pieces exist twice privately
(read-only `DeTurckRemainderLowBaseAction.lean` as `aa*`, editable
`EdgeRicciPairing.lean` as `ricQuad*`), but publicizing either set is unsafe
because the `ricPerm*` permutations are duplicated under the same names in the
same namespace inside the read-only file.  Re-derived instead in
`SelfLowCapWindows.lean` with fresh names; `aaKerSplit` is `rfl`.

### The two remaining frontiers, and how hard they look

* **`ricciDACap`** (`ricciDALow g₀ g₁ P = daContr g₀ g₁ (dagLowOp ⋆ ∇P)`).  The
  structure is right: `connLowOp` is `permCoeff ⋆ (slotInsertEndoCc
  (fullRaisedEndoField) ⋆ koszulOp)`, i.e. offset `+1` — no derivative of the
  state — so `dagLowOp = permCoeff ⋆ ∇(connLowOp)` is offset `+2` and pairs with
  `∇P` (also `+2`) exactly in the `capApp` shape.  **The structural route is
  already public and already generic**: the tame layer's *bound*
  `rfns_…_refoldKernelContractionMonomialField_topSeparated_and_lowerWindow_le`
  is hard-wired to `G = ∇²(symmS P)`, but the *identity*
  `refoldKernelContractionMonomialField_eq_mvPairTraceRefold`
  (`RicciArmResidualFieldGridWindow.lean:5945`) holds for an ARBITRARY `(0,4)`
  argument and factors the head as
  `mvPairTraceOp ⋆ ddc (slotExtendIter (ddc G))` — pure `capApp`/`capIter`/
  `capDdc` food.  What is genuinely missing is the LEAF inventory: capped
  windows for `mvPairTraceOp`, for `slotInsertEndoCc (fullRaisedEndoField)` and
  for `koszulOp` (the latter is a fixed tensor, so `capOfBnd`), plus a
  `capDdc0` sibling of `capDdc` for `domDomCongrSection` at valence `(0,s)`
  (the fibre-isometry lemma
  `riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection` already exists and
  is what `kappaAtgw` uses).  Classification: **missing API leaves**, no
  mathematical obstruction; estimated a short brick, not a session.
* **`lieCovCap`** (`deTurckLieCovDerivArmField − edgeLiePairFam`).  The route is
  identified and public at the top: `edgePair_eq` is `rfl` (re-derivable in one
  line), and `lieCov_residual` turns the difference into the single product
  `(-1) • lieCovPair ⋆ ddc (slotExtendIter (lieCovR4))`.  Two sub-frontiers:
  (a) `lieCovPair g₀ g₁ = appCcRS g₀ 6 4 2 (pureTrace g₀ g₁ 2) (pureTrace g₀ g₁ 4)`
  should be `rfl` — `bdPureDT` and `pureTrace` are the SAME field (both the
  section of `cometricDoubleTraceFib g₁ s`), so `trace_grid_rf` at the identity
  permutation supplies both factors;
  (b) `lieCovR4 = (-(s/2))•lrCurvF g₀ T − lrQuadF g₀ g₁` needs windows for
  `lrCurvF` (curvature ⋆ state — note `(-(s/2))•lrCurvF g₀ T = (-(1/2))•lrCurvF
  g₀ P` by linearity, which is what puts it into `P`'s currency at all) and for
  `lrQuadF` (six slot-permuted copies of `lrQA`/`lrQB`, a genuine `A·A`).  The
  `lrQA`/`lrQB` windows do not exist publicly; only private `bd*_gridWindow`
  producers in `RiemannCoefficientPalatiniRefold.lean`.  Classification:
  **missing API layer**, roughly a session's worth.

### Traps recorded

* `HasCapWin` is definitionally the conclusion shape of the session-1 producers,
  so `lc0VBCapAtgw` is consumed as a `HasCapWin` with no glue at all.
* `convexPerturbation g T 0 s = s • T` has NO public name; the idiom in the tree
  is `rw [convexPerturbation, smul_zero, zero_add]` (there is a local `cvxRad`
  inside `LowRegOpJetWindows.lean` but it is not exported).
* `lieCorr0AMixPerm1`/`PermQ`/`Perm2` live in
  `…IntrinsicSpectral.LieCorr0Core`, a nested namespace that
  `open …IntrinsicSpectral` does NOT bring into scope.
* `Equiv.Perm (Fin d)` is a `Fintype`: `∑ ρ, S ρ i` plus `Finset.single_le_sum`
  gives a permutation-uniform bound for `permCoeff` in two lines, avoiding a
  six-way case split.

### Verification

Focused checks green throughout, under the memory guard, `-LeanThreads 1`, no
trip.  `GradCapArms.lean` and `SelfLowCapWindows.lean` sorry-free;
`LowRegC01JetTower.lean` sorry census = exactly two (`ricciDACap`,
`lieCovCap`), both `private` and both narrow per-arm windows.  There is
currently NO downstream consumer of `c0_jet_tower`/`c1_jet_tower` in the tree
(A1c `a1_ladder` and A1d `n_diff_hm_rung` are not yet written), so the
"downstream build" is vacuous by construction.

---

## 2026-08-04 (session N+4): A1-CUR-2 CLOSED — both towers unconditional

`ricciDACap` and `lieCovCap` are proved.  Both private stubs were **deleted**
from this file; the two theorems now live publicly in the new sibling
`SelfLowArmCaps.lean` (same statements, `Integral.Connection` namespace, so
`ricciGoodCap` and `selfLow_jet` pick them up through the existing
`open DifferentialGeometry.Integral.Connection`).

**This file's sorry census is now ZERO**, and the axiom census gives
`[propext, Classical.choice, Quot.sound]` for `selfLow_jet`, `c0_jet_tower`,
`c1_jet_tower`, `low1Ker_jet`, `selfLow_split` and every capped-window
declaration — no `sorryAx` in the census at all.

### Correction to session N+3's diagnosis

Session N+3 recorded the `lrQA`/`lrQB` windows as existing "only as private
`bd*_gridWindow` producers", and estimated promotion + re-derivation at about a
session.  **Both halves of that were wrong**, in the same way three earlier
"walls" in this campaign were wrong: the private producers have PUBLIC wrappers
a few hundred lines away in the same file (`lieCovArm2_l2` wraps
`bdArmSlot2_rfns_le`; `fullRev0_eq` and `omRecover_add` wrap the recovery
decomposition), and the remaining piece, `lrOmegaHat`, is cheaper to re-estimate
from its own public definition than to promote — `connLow_rfns` in
`FlatArmCoeffConnectionDifferenceBridge.lean` is the public
`connDiffLoweredCc` ↔ `connDiffSection` bridge.  The rule to carry forward is
the one already in memory: **grep for a public wrapper of the private lemma
before declaring a wall.**

The one genuinely inaccessible name was `koszulOp` (private to the read-only
`DeTurckRemainderLowBaseAction.lean`).  It was side-stepped, not promoted:
`clSplit : ∃ Z, ∀ g₁, connLowOp g₀ g₁ = … Z` proved by `⟨_, fun _ => rfl⟩`
lets unification supply the term without ever writing its name, and the
estimate only uses that `Z` is state-free.

### Cost measurement that ruled out promotion

Reverse closure of `Analysis/Parabolic/RicciLinearization/
RiemannCoefficientPalatiniRefold.lean`: **170 modules, ~229k lines**, including
the 19.5k / 13.8k / 10.9k / 9.6k / 9.4k-line files.  Zero churn was the right
call; no file outside the three claimed ones was touched.

### Route detail

In `SelfLowArmCaps.md`.  The two new generic calculus lemmas `capOfP`/`capOfDP`
and the `(0,s)` slot-permutation isometry `capDdc0` went into
`GradCapArms.lean`, their canonical home.

### Verification

Focused checks green; targeted build of this module green (9610 jobs);
axiom census green (see above).  Memory guard armed on every run, never
tripped.  Still NO downstream consumer of `c0_jet_tower`/`c1_jet_tower`
(A1c `a1_ladder`, A1d `n_diff_hm_rung` unwritten), so a downstream build
remains vacuous.

## 2026-08-04 (session N+5): FEASIBILITY GATE `selfLow_jet_quad` — FAIL as scoped

**Outcome: the theorem was NOT added; this Lean file is unchanged.**  The gate
(CODEX audit, `CODEX_LOMASS_AUDIT.md`, "Next concrete brick handoff") asked for a
`selfLow_jet` variant whose constant is `K₀ i + K₂ i·‖T‖²_{H³}`, with the fixed
radius `R₀` removed.  It is not producible by refining the constants of the
existing capped-arm proof, and no sorry-free route to it exists in the current
currency.  **The audit's stop-condition trigger is NOT met**: the C0 arm algebra
does *not* force a higher-than-quadratic power, there is no same-rung radius
inside a Grönwall coefficient, and no cutoff-dependent inverse inequality.  The
obstruction is the CURRENCY, not the mathematics.

### Why the hinted route is provably dead

`gradCapOfBall` really is the only place `R₀` enters as a *magnitude*, and that
part is bookkeeping: `Λ₁² = c·R₀²`, `Λ = max 1 (max ((n/3)²) (Λ₁²))`, so `Λ` is
affine in `‖T‖²_{H³}`.  The radius, however, enters the CONSTANT as a
**polynomial whose degree grows with the jet order**:

* every arm window enters the capped currency through `capOfArm`
  (`GradCapArms.lean`) with constant `K i * shiftConst Λ (i+1)`, and
  `shiftConst Λ k = Σ_{m≤k} Λ^m · count m` (`GradCapAtgw.lean`) is a degree-`k`
  polynomial in `Λ`;
* `foldConst` (`AtgwArmFold.lean`) multiplies the constants of two arms at every
  product node, so **degrees add**.  In `ricciAACap` the chain
  `KIns`/`KInn` → `KIC` → `KMA`/`KMB` → `KA`/`KB` → `KQ` → final fold against
  `KFT` reaches `Λ`-degree `3(i+1)`, i.e. degree `6(i+1)` in `‖T‖_{H³}` —
  degree six already at `i = 0`.  `lc0VBCapAtgw` has the same shape, and
  `capJet`'s `Kint` adds more through `atgwCapToJet (Λ₁ := √Λ)`.

The `Λ^m` in `shiftConst` is structurally necessary, not slack.  `prodShift`
re-reads a weight-`m` tuple of the state's own jet base in the shifted (`∇P`)
base; a tuple of `m` weight-one entries is `(|∇P|²)^m`, which has weight `0` in
the shifted base and therefore appears in **no** shifted window at any level
(`antidiagonalTupleGrid b 0 = 1`).  It can only be paid by the cap.  So no
choice of constants inside `HasCapWin` is affine in `Λ`, while the target needs
`Λ`-degree `≤ 1`.  Self-application (`a := 1`, `R₀ := ‖T‖_{H³}`) removes the
fixed radius but leaves `Poly_{6(i+1)}(‖T‖_{H³})` — an explicitly forbidden
deliverable, so it was deliberately NOT written under the name
`selfLow_jet_quad`.

### Why the statement is nevertheless true (the lane's premise is sound)

The five summands of `selfLow_split` are (analytic in `P`) ⋆ (at most quadratic
in `∇P`); the docstring heading `selfLow_jet` already records which two are the
quadratic ones.  For such an arm the classical Moser tame estimate gives
`‖∇ⁱ(arm)‖_{L²} ≲ C(δ)·‖∇P‖_∞·(1 + ‖P‖_{H^{i+1}})` — **one** power of
`‖∇P‖_∞ ≲ c‖T‖_{H³}`, which is exactly the quadratic shape after squaring.  The
high-degree terms `(∇P)^{i+2}` produced by the inverse-metric expansion are NOT
charged to `‖∇P‖_∞`: Gagliardo–Nirenberg anchors every intermediate jet at
`‖P‖_∞ ≤ δ ≤ 1/3`, a FIXED constant.  The capped-grid currency cannot see this
because it bounds `|∇ⁱ(arm)|²` **pointwise**, and pointwise that term genuinely
is of size `|∇P|^{2(i+2)}`; only the `L²`-level redistribution recovers a
quadratic constant.  This confirms the paper's own claim
(`PSTOP_PROPOSITION.md`: "the C0 cap enters the rung-`k` Grönwall coefficient
QUADRATICALLY").

### The enabling primitives exist and are sorry-free (verified this session)

A fresh axiom probe on `Analysis/Sobolev/MoserTameProduct.lean` returned
`[propext, Classical.choice, Quot.sound]` — no `sorryAx` — for
`exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le` (the `L^∞`-anchored
interpolation `‖∇ʲu‖ ≤ C·Λ₀^{1−j/k}·‖∇ᵏu‖^{j/k}`, exactly the δ-anchor this
route needs), `exists_moserTameProduct_iteratedCovGrad_l2Norm_le` and
`exists_moserTameProduct_pi_iteratedCovGrad_l2Norm_le`.

**STALE-DOC WARNING (false-wall generator, the fifth in this campaign).**  That
file's docstrings still assert the GN half is blocked on a `sorry` in
`l2jet_logConvex_iteratedCovGrad` / `secondCovDeriv_unit_frame_fiberNormSq_le`.
Both are proved now (`RoughLaplacianSecondCovGradL2Bound.lean`, zero sorries);
the file contains no `sorry` term at all — every occurrence of the word is prose.
An executor reading those docstrings would wrongly conclude the tame layer is
unusable.  Flagged for separate cleanup.

### What the next brick should be told

Not a constant refactor.  The real brick is **the tame C0 bottom**: re-derive
the five `selfLow_split` summands' `L²` jets in the tame currency — one `∇P`
factor in `L^∞` (the single `‖T‖_{H³}` power), the top jet in `L²` inside the
`range (i+2)` budget, every intermediate jet interpolated at the δ-anchor by
`exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le`.  The pattern to copy is
`AppCcJetWindowTame.lean`'s tame per-order layer for the C2 coefficient
(`deTurckPrincipalCometricCoeff_perOrder_l2_tame_generic`), whose conclusion is
already `K i * (1 + ‖P‖_{H^i})`; but its own constant is a growing power of its
cap, so it must be re-derived, not instantiated.  The existing pointwise arm
windows cannot be reused as-is: already at `i = 0` they have spent the `∇P`
structure into the constant (`HasCapWin … K` at `i = 0` reads `|arm|² ≤ K 0`,
the window being `1`), so the explicit `∇P` powers must come from a fresh
per-summand Leibniz split.  Several bricks, not one.

### Percentages (honest)

`selfLow_jet_quad`: **not started, 0%** — nothing is stated in Lean.  Its
dedicated machinery: the two enabling primitives exist sorry-free but the
five-summand tame re-derivation is untouched, so ≈ 20–30%.  `lowreg_loMass` 0%
(dedicated machinery ≈ 30%); (N) 0% (stated,
`Evolution/ExtendViaUniqueness.lean:80`, `sorry` at :98); whole HCG ≈ 3%.

### Verification

No Lean source was edited, so no focused check was required.  The single probe
run (axiom census of the GN/Moser primitives) passed.  Memory guard was checked
before the run and never tripped.

## 2026-08-04 (session N+6): TAME C0 BOTTOM, brick 1 — composition layer built, no summand closed

**This Lean file is again unchanged**; the work is in the new
`Analysis/Sobolev/TensorHilbert/TameGridProd.lean` (see `TameGridProd.md`
for the full route and the Lean lessons).

What the brick delivered: the `L²`-level tame composition layer —
`gridIntUnit` (state-free per-antidiagonal grid-product integral at cap
`Λ₀ ≤ 1`), `gridIntTwo`, `gridIntGrad` (**the quadratic tame product**,
`∫|∇^{c₁}P|²|∇^{c₂}P|² ≤ K k (1+Λ₁²)‖∇ᵏP‖²`, `K` state-free),
`gridIntPull`, and `gradCapLin` (the `∇P` cap with its `H³` dependence
explicit, replacing `gradCapOfJets`'s hidden radius).  All sorry-free.

What it did NOT deliver, and why: none of the five `selfLow_split`
summands was closed.  The engine needs the per-arm Leibniz expansion in
the form `∏_j ∇^{c_j}P` with the factors EXPLICIT; every window this file
consumes (`ricciAACap`, `lc0VBCapAtgw`, `lieCovCap`, `lc0AMixCap`,
`lc0RiemCap`, `ricciDACap`) has already spent that structure into its
constant — at `i = 0` `HasCapWin … K` reads `|arm|² ≤ K 0`.  Re-deriving
those expansions is the next brick and is per-arm.

Sharper than No. 137: the tame split is **provably not pointwise**.
`∏_j |∇^{c_j}P|(x) ≤ Λ₁ · (grid at order i+1)(x)` is false whenever no
`c_j = 1` (take `|∇²P|²|∇ⁱP|²`).  So no refinement inside
`antidiagonalTupleGridWindow` can produce the quadratic constant — which
also means a `Λ₁`-prefactored pointwise window is NOT a legitimate
intermediate interface to introduce.

Remaining analytic frontier, exactly one: Leibniz terms with `q ≥ 3`
factors all of order `≥ 2` (first possible at jet order `i = 4`).  True,
but needs an interpolation between the two Gagliardo–Nirenberg scales in
the tree.  If the `(N)` jet budget is `∀ a ≤ 3`, this class never occurs
and the frontier is off the critical path — a planner call.

## Session 5 (2026-08-04): `selfLow_jet_quad` — the cap-free sibling of `selfLow_jet`

**Landed and green.**

```
selfLow_jet_quad (hDim : Module.finrank ℝ E = 3) (g : SmoothRiemannianMetric I M) :
    ∃ K0 K2 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K2 i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ x u v, ccTensorBilin g T x u v = ccTensorBilin g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound g (ccTensorBilinSymm g T) δ)
        (hδZ : gFibreOpBound g (ccTensorBilinSymm g (0 : SmoothCcTensor g 0 2)) δ)
        (i : ℕ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        lowJetSq g i (rhsSelfLow g g T hδg hδZ s) ≤
          (K0 i + K2 i * ∑ j ∈ Finset.range 3, ‖iteratedCovGrad g 0 2 (1 + j) T‖ ^ 2) *
            (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad g 0 2 j T‖ ^ 2)
```

`‖T‖²_{H³}` is spelled `∑_{j<3} ‖∇^{1+j}T‖²` — `gradCapLin`'s convention, the
same spelling every arm jet uses.  **No `R₀`, no `H^{a+2}` ball, no `a`, no `Λ`,
one power of `‖T‖²_{H³}`, constants before the state.**  Compare `selfLow_jet`,
which keeps the ball and whose constant has `Λ`-degree growing with `i`.

### Structure

New private layer, in dependency order: `ricciGoodMark` (marked sibling of
`ricciGoodCap`, from `ricciAAMark` + `ricciDAMark` at `u = 2`), `jetFold`
(sum a per-order tame bound over `range (i+1)`; constants add, the single `H³`
power survives), `jetTrans` (`P`-jets ⟹ `T`-jets, both in the `H³` factor and in
the `range (q+2)` budget, from `‖∇ᵏP‖ ≤ ‖∇ᵏT‖`), `ricciGoodJet`.

Assembly: `selfLow_split` → `jetAdd` ×4 (coefficients 16/16/8/4/2) with the
`(-2)•` handled by the PUBLIC `jetSmul` (factor 4, so arm 1 pays 64).  The
δ-anchor `|P|²_∞ ≤ 1` that all six arm jets spend is `hDim` + `δ ≤ 1/3`:
`(dim·1/3)² = 1` in dimension three, i.e. `pathPert_rad`'s `hPsup` IS the anchor
with no slack — this is why the theorem needs `hDim` and `δ ≤ 1/3` and nothing
else.

### Lean note that cost a cycle

The first version was ONE declaration and blew the default 200000 heartbeats
(`whnf` timeout on the whole declaration, plus `isDefEq` timeouts inside).  No
`maxHeartbeats` was raised: the fix is to split the local `have`s that are
really lemmas (`jetTrans`, `ricciGoodJet`) into private declarations, since the
heartbeat budget is per-declaration.  Rule of thumb for this file: a `have`
whose statement quantifies over `{r c}` or over a constant pair is a lemma.

### Census

`selfLow_jet_quad` depends on `[propext, sorryAx, Classical.choice, Quot.sound]`;
the `sorryAx` is `gridIntHigh` and nothing else (it enters through `markJet` →
`markMon`).  `selfLow_jet`, `c0_jet_tower`, `c1_jet_tower`, `low1Ker_jet`,
`selfLow_split` unchanged and still clean.

## Session 6 (2026-08-04): `c0_jet_tower_quad` — the ball-free tower sibling

**Landed, focused check + targeted build green.**  `c0_jet_tower_quad` has
`c0_jet_tower`'s conclusion with the `H^{a+2}` ball replaced by an explicit
quadratic dependence:

```
c0_jet_tower_quad (hDim : finrank ℝ E = 3) (g) :
  ∃ K0 K2 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K2 i) ∧
    ∀ T (hT : symmetry) {δ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1/3) (hδg) (hδZ) (i : ℕ),
      ‖∇ⁱ (lowBaseData g g T … ).C0‖² ≤
        (K0 i + K2 i * ∑_{j<3} ‖∇^{1+j}T‖²) * (1 + ∑_{j<i+2} ‖∇ʲT‖²)
```

No `a`, no `ha : 1 ≤ a`, no `R₀`, no `hR₀`, no ball premise — the parameters
`(a, R₀)` are GONE from the signature, not merely inert.  Constants are chosen
before the state (TK3), and `‖T‖²_{H³}` is `gradCapLin`'s spelling
`∑_{j<3}‖∇^{1+j}T‖²`, matching `selfLow_jet_quad` verbatim.

### Route

Exactly `c0_jet_tower`'s skeleton with `selfLow_jet` swapped for
`selfLow_jet_quad`; the ball entered the original ONLY through that integrand
window.  `path_jetL2_le g 2 2 i (rhsSelfLow …)` is unchanged (the joint
smoothness `selfLow_joint` and the `realizedSmallSet` inclusion do not see the
ball), and `c0_eq` + `jetSub` still peel the state-free curvature summand.

The one arithmetic step worth recording: the `Λ` fed to `path_jetL2_le` is now
the PRODUCT `(K0' i + K2' i·H3)·JS` rather than `K' i·JS`, so the constant
bookkeeping at the end is
```
K0 i := 2·(K0' i + lowJetSq g i (−phiMetCurvCoeff g g g)),   K2 i := 2·K2' i,
```
and the closing inequality is `2Φ(JS − 1) ≥ 0` — i.e. the curvature summand's
`Φ` is absorbed by the `JS ≥ 1` factor, which is why it lands in `K0` alone and
does not need a second `JS` power.  `nlinarith` closes it from
`mul_nonneg hfix hsum` plus the four nonnegativity facts.

### Census

`c0_jet_tower_quad` carries `sorryAx` — **through `gridIntHigh` and nothing
else**, exactly as `selfLow_jet_quad` does (it consumes it and nothing further).
`c0_jet_tower`, `c1_jet_tower`, `selfLow_jet`, `selfLow_split`, `low1Ker_jet`
unchanged.  When `gridIntHigh` closes, this tower becomes clean with no further
work.

### What consumes it

`lowreg_loMass`'s intended pipeline (`PSTOP_PROPOSITION.md` §6.3, tower-direct
pairing) reads the `C0` tower at `i = k−1` for the stopped rungs `k = 3,4,5`.
`c0_jet_tower` cannot serve there because its ball premise is not available on
the ball-free class; `c0_jet_tower_quad` is the statement that can.  The
`c1`/`c2` towers are already ball-free (their ball arguments are inert), so this
was the only tower needing a quadratic sibling.

## M3 — `c1JetTowerQ` (2026-08-04)

The "already ball-free (their ball arguments are inert)" claim above is now
realized in the statement, not just in the proof: `c1JetTowerQ` is
`c1_jet_tower` with the `(a : ℕ)`, `{R₀ : ℝ}`, `(hR₀ : 0 ≤ R₀)` binders and the
`‖T‖_{H^{a+2}} ≤ R₀` premise **deleted**.  Nothing else changed — the body is
the same `low1Ker_jet` + `path_jetL2_le` passage, and the deleted `hball` was
literally an unused `intro`.  `c1_jet_tower` is now a four-line wrapper of
`c1JetTowerQ`, so the ball form stays available for the ball-carrying consumers
(`a1_ladder`) with no duplicated proof.

Unlike `c0_jet_tower_quad`, no quadratic `K2·‖T‖²_{H³}` correction is needed:
the first-order integrand window is driven by `hδ_le : δ ≤ 1/3` alone, which is
what makes the binder vestigial rather than merely slack.

The `c2` sibling `c2JetTowerQ` landed the same way in `LowRegLadderRung.lean`
(its canonical home).  With that, all three coefficient towers now have
ball-free statements.  What this does **not** do is make the ladder layer above
them `H²`-only — see the M3 obstruction section of `LowRegLadderRung.md`: the
`H⁵` anchor there is spent by the `L^∞` embedding inside the operator-norm
engines, not by the towers.

Verification: focused check green; targeted module build green; census clean
(`c1JetTowerQ` and `c1_jet_tower` both `[propext, Classical.choice,
Quot.sound]`).

## 2026-08-05: operator-window add-lemma rename

The four local sum estimates now call `opJetAdd`, and the local scaling estimate
calls `opJetSmul`.  These are the renamed window-lane versions of the squared-jet
algebra.  This removes the import collision with the canonical H²-lane
declarations; the proof statements and constants are unchanged.  Focused
verification passed after both renames, and the module rebuilt successfully as
part of the adapted-package dependency refresh.
