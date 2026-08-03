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
