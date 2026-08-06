# `AtgwArmFold.lean` — the generic radius-free grid composer

Created 2026-08-03 during brick A1-CUR-1 (`low1Ker_jet`).

## Why it exists

Every radius-free per-order producer in the DeTurck / LieCorr0 layer repeats the
same two steps by hand:

1. a two-arm `appCcRS` Leibniz product whose factors each carry a pointwise
   `antidiagonalTupleGridWindow` bound in the state's own fibre jets, folded
   into a single window via `antidiagonalTupleGridWindow_mul_le`;
2. one application of the grid integral workhorse
   `antidiagonalTupleGrid_integral_radiusFree`, turning the pointwise window
   into an affine `L²` jet bound with a `range (n + w)` budget.

Before this file the argument was written out in full at
`cometricCastG0_wXi_twoArm_fold_rf`, `wCA_wOmega_twoArm_fold_rf`
(`DeTurckVFJetRadiusFree.lean`) and the eight `b4_*_atgw` folds of
`LieCorr0CoeffDiffRadiusFree.lean` — several hundred lines of duplicated
bookkeeping, and the reason `A1CUR_PLAN.md` §7 budgeted ~225 lines *per arm*.

## What it provides

* `gridBase g₀ P x j = |∇ʲP|²(x)` — the family every window is measured against.
* `foldConst u v KΦ KW n` — the fold constant, with `foldConst_nn`.
* `atgwFold` — the pointwise two-arm fold, at **generic left rank** `p`,
  generic valences `a b`, and generic offsets: windows at `i' + u + 1` and
  `l + v + 1` compose to a window at `n + u + v + 1`.
* `atgwToJet` — the integration step: a pointwise window at offset `w` gives
  `‖∇ⁿX‖² ≤ K · (∑_{k<n+w} Kint k) · (1 + ∑_{j<n+w} ‖∇ʲP‖²)`.

Both are radius-free (the only state input is the fixed order-zero fibre bound
`Λ₀`) and **gate-free**, which is what the `∀ i` jet towers need; the flat
ball-uniform producers are gated `i ≤ a` and cannot discharge them.

## Notes / lessons

* `atgwFold` was first written for left rank `0`
  (`rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_le`) and then generalised
  to arbitrary `p` using
  `rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le`
  (`MetricArmCoeffJetTower.lean:2361`).  The `p = 0` case is subsumed.  The
  generalisation was necessary: the Ricci and Lie outer arms sit at left rank
  `4` and `3`, not `0`.
* `Combinatorics.antidiagonalTupleGridWindow` is a plain `def`, so `rw` on it
  fails ("Failed to rewrite using equation theorems").  State the unfolding as a
  function equality proved by `rfl` and `rw` with that.
* Offset arithmetic: `antidiagonalTupleGridWindow_mul_le b hb a c` is
  `atgw(a+1) · atgw(c+1) ≤ MulConst a c · atgw(a+c+1)`, hence the `+1`-shifted
  parametrisation of `u` and `v`.

## Verification

Focused check passed, sorry-free, no warnings; module builds.
