# `Low1KerRadiusFree.lean` — radius-free grid currency for the order-one low-base integrand

Created 2026-08-04 (brick A1-CUR-1 COMPLETION).  Status: **COMPLETE, sorry-free,
axiom-clean.**  It is the producer layer that closes `low1Ker_jet`
(`Analysis/Spectral/Intrinsic/DeTurck/LowRegC01JetTower.lean`).

## What it provides

The order-one path integrand is

```
rhsLow1Coeff g₀ g_bg T T' s
  = (-2) • linearizedRicciConnDiffOrder1CoeffField g₀ g₁
      + deTurckLieArm1Coeff g₀ g₁ g_bg,        g₁ = realizedFam g₀ T T' s
```

Both summands are **linear** in the connection difference, so each has a
pointwise `antidiagonalTupleGridWindow` bound at offset `+2` (one derivative of
the state), radius-free and gate-free.  The module produces those windows and the
combined one:

| declaration   | object                                             | offset |
| ------------- | -------------------------------------------------- | ------ |
| `pureAtgw`    | `ricciArmPrincipalCoeffPure g₀ g₁`                 | `+1`   |
| `fourTrAtgw`  | `ricciCometricFourTraceCastG0 g₀ g₁`               | `+1`   |
| `dltcEqPure`  | `deTurckLieTraceCoeff = reindex(pure)`             | —      |
| `dltcAtgw`    | `deTurckLieTraceCoeff g₀ g₁ σ`                     | `+1`   |
| `ricci1Atgw`  | `linearizedRicciConnDiffOrder1CoeffField g₀ g₁`    | `+2`   |
| `sfEndoAtgw`  | `sharpFlatEndoCc g₀ g₁`                            | `+1`   |
| `kappaAtgw`   | raised/permuted `lieArm1LoweredBgKappa g₀ g₁ g_bg` | `+2`   |
| `psiBAtgw`    | `lieArm1PsiB g₀ g₁ g_bg`                           | `+2`   |
| `bgCcEqConn`  | `lieArm1ConnDiffBgCc g₀ g₁ g₀ = connDiffSection`   | —      |
| `pieceAtgw`   | `lieArm1Piece g₀ g₁ σ' ρ Ψ` (Ψ at `+2`)            | `+2`   |
| `lieA1Atgw`   | `deTurckLieArm1Coeff g₀ g₁ g₀`                     | `+2`   |
| `low1Atgw`    | `(-2)•ricci₁ + lieArm₁`                            | `+2`   |

Every fold is one call of `atgwFold` (`AtgwArmFold.lean`); the module contains no
re-derivation of the Leibniz grid argument.

## Route, and the two facts that made it short

1. **The two outer trace factors have a common source.**  Both
   `ricciCometricFourTraceCastG0` and `deTurckLieTraceCoeff σ` are source-slot
   reindexings of the *same* object `ricciArmPrincipalCoeffPure` (the moving
   cometric double trace at valence `(4,2)`).  `dltcEqPure` is that identity —
   provable by `SmoothCcTensor.ext` / `ContinuousLinearMap.ext` /
   `reindexCoeffFibGen_apply` / `rfl` — so one window (`pureAtgw`) feeds both
   arms.  The plan (`A1CUR_PLAN.md` §9, open item 1) budgeted a ~134-line clone
   of `rfns_iCG_cometricCastG0_atgw_rf` for the Ricci factor alone; in the end
   `fourTrAtgw` is 12 lines (the existing
   `rfns_iteratedCovGrad_ricciCometricFourTraceCastG0_diagonalProductGrid_le`
   already *is* the `+1` window, since `∑_{k<n+1} atg = atgw (n+1)` by `rfl`) and
   `pureAtgw` is needed only for the Lie factor.

2. **`lieArm1PsiB` needs no new geometry.**  It is
   `appCcRS (raise ∘ domDomCongr κ) (sharpFlatEndoCc)`, and
   `κ = lieArm1LoweredBgKappa = -metricConnDiffLoweredCc` (public
   `metricConnDiffLoweredCc_eq_neg_kappa`).  The `metricConnDiffLoweredCc` window
   at `+2` already existed as `b4_mcd_atgw` inside
   `LieCorr0CoeffDiffRadiusFree.lean` — it was `private`; promoting it was the
   only edit outside this file.  Raising slot 0 and permuting slots are fibre
   isometries at every jet order
   (`rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq`,
   `riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection`), both public, so
   `kappaAtgw` is ~20 lines and the private `lieArm1_rfns_icg_raiseDomDom_eq` of
   `DeTurckLieArm1CoeffL2JetBound.lean` did **not** have to be promoted.

`lieA1Atgw` sums the fourteen `lieArm1Piece`s of
`deTurckLieArm1Coeff_eq_lieArm1Piece_sum` over the three `Ψ` factors.  At
`g_bg = g₀` two of them collapse to `connDiffSection g₁ g₀` (`bgCcEqConn`), so
only `lieArm1PsiB` is genuinely new.  The `2`-subadditivity cascade along the
recorded bracketing `((A + G₁) + G₂) + D` costs a factor `1138`; the constant is
not optimised and does not need to be.

## Traps recorded

* `foldConst_nn` has `{u v : ℕ}` **implicit and unconstrained by its
  hypotheses**.  Inside a `refine ⟨…⟩` whose expected type fixes them it
  elaborates; in a bare `have h := foldConst_nn hA hB n` it fails with
  "don't know how to synthesize implicit argument `v`".  Pass `(u := …) (v := …)`.
* There is no public `riemannianFiberNormSq_neg`.  Use the public
  `riemannianFiberNormSq_smul` through `(-X) = (-1 : ℝ) • X` (the local
  `l1IcgSmul` / `l1RfnsNeg` pair).  Trying to reach it by
  `SmoothCcTensor.toSection_neg` alone leaves the goal in the shape
  `((-s) x)` rather than `(-(s x))`; the pointwise step needs
  `ContMDiffSection.coe_neg` / `Pi.neg_apply`, exactly as the `add` case needs
  `ContMDiffSection.coe_add` / `Pi.add_apply`.
* `atgwToJet` takes `(r c n w : ℕ) (X) (K : ℝ) (hK)`.  `X` is explicit and comes
  *before* `K`; passing `_ (hK)` silently binds `hK` to the `K` slot and gives an
  "argument … has sort `Prop` but is expected to have type `ℝ`" mismatch.
* Private helper names must be unique **tree-wide**, not just per file:
  `private` hides a name from importers but does not give it a distinct
  fully-qualified name.  All local helpers here are prefixed `l1`.

## Verification

Focused check of this file: green, no warnings.  Targeted build of the census
target (which rebuilds `LieCorr0CoeffDiffRadiusFree`,
`DeTurckRemainderLowBaseAction`, `LowRegOpJetWindows`, `LowRegC01JetTower`):
completed successfully, 0 errors.  Every public declaration of this module is
`[propext, Classical.choice, Quot.sound]`.
