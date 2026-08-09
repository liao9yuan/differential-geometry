# `SelfLowCapWindows.lean` — capped windows of the `selfLow_split` summands

Created 2026-08-04, brick A1-CUR-2 session 2 (the assembly session).

## What is here

Capped windows (`HasCapWin`, see `GradCapArms.md`) for the summands of
`selfLow_split` that live in the Lie-correction and Ricci-kernel layers:

| declaration | summand | status |
| --- | --- | --- |
| `lc0RiemCap` | `lc0Riem` | proved |
| `lc0AMixCap` | `lc0AMix` | proved |
| `aaKerSplit` + `ricciAACap` | `ricciAAArm` inside `ricciGoodLow` | proved |

`lc0VB`'s capped window is session 1's `lc0VBCapAtgw` (`Lc0VBCapWindow.lean`);
its conclusion IS `HasCapWin` unfolded, so it is consumed directly.

## The `ricciAAKer` two-arm split — session 1's named blocker

Session 1 reported that `ricciAAArm` "cannot be handled by shifting its folded
window: `ricciAAKer` is a single arm that is ITSELF quadratic, and the shift is
sharp only when every grid entry of the bound carries a factor".  Correct — and
the fix is to expose the two arms.

`aaKer_eq` and the six `aa*` pieces are `private` in the READ-ONLY
`DeTurckRemainderLowBaseAction.lean` (~:4400).  **But they are a duplicate**: the
CANONICAL home of `ricciAAKer` is `EdgeRicciPairing.lean`, where the same six
pieces already exist as `ricQuad0 … ricQuad5` — also `private`, but in an
editable file.  Even so, publicizing them there was rejected: the `ricPerm*`
permutations they are built from are ALSO privately duplicated, under the same
names and in the same namespace, inside the read-only file.  Making those public
risks an ambiguity error in a file that cannot be repaired.

So the split was re-derived here (the `ricci1Split`/`selfLow_split` precedent):
fresh private permutations `aaP****`, two public cores `aaCoreP`/`aaCore`, and

```lean
theorem aaKerSplit (g₀ g₁) : ricciAAKer g₀ g₁ = … six pieces … := rfl
```

`rfl` closes it — `ricciAAKer` is definitionally the sum, and the permutation
structures match field-by-field with proof irrelevance on the `by decide`
components.  No edit to any other file; no rebuild of the read-only tree.

## Route notes per summand

* **`lc0Riem`** — `lc0Riem_eq_app` gives `-(lc0RiemLive ⋆ lc0RiemPass)`; the
  live arm is a cometric cast (offset `+1`), the passenger is a fixed tensor.
  This summand never needed the cap; it is capped only so that all five
  summands speak one language at the assembly.
* **`lc0AMix`** — session 1 and No. 122 called this summand LINEAR.  It is not:
  `b4_amix_atgw` lands at `atgw bP (i + 3)` because `amix_refold_rf` is a
  five-factor nest `trace ⋆ trace ⋆ mcd ⋆ trace ⋆ mcd` with TWO lowered
  connection differences.  It is a quadratic summand and needs the cap.  Also
  note that the existing integrated producer `lc0AMix_perOrder_rf` carries the
  supercritical gate `2·finrank + 10 ≤ a`; that gate comes from its
  `cometricCastG0_order0sup_jetL2_radiusFree` route and is NOT inherited here —
  the capped route uses only `trace_grid_rf` and `b4_mcd_atgw`, both gate-free.
* **`ricciAAArm`** — `fourTrAtgw` (offset `+1`) folded against the six kernel
  pieces; each piece is `permCoeff ⋆ (insertion ⋆ innerInsertion)`, and both
  insertions carry exactly one derivative of the state (`insertAtgw`, and
  `connDiffContrInsertionInnerField_eq_reindex_slotExtend` over
  `rfns_iCG_connDiffSection_atgw_rf`).

## Constants

Every producer fixes its constants before seeing the state, and none sees the
path parameter `s`: the caps `Λ₀ = finrank·δ₀` and `Λ₁` are determined by the
background, the gate `1 ≤ a` and the ball radius `R₀` alone.

## Verification

Focused checks green; `lc0Riem`/`lc0AMix` on the second attempt (one namespace
fix: `lieCorr0AMixPerm*` live in `…IntrinsicSpectral.LieCorr0Core`, which has to
be opened explicitly), `ricciAACap` + `aaKerSplit` on the first.  Zero sorries in
this file.

---

## 2026-08-04 — the other two summand windows

`selfLow_split`'s remaining two arms, `ricciDALow` (inside `ricciGoodLow`) and
`deTurckLieCovDerivArmField − edgeLiePairFam`, are NOT here: their factors live
in the low-base action module and in the Palatini refold, so they were put in
`Analysis/Spectral/Intrinsic/DeTurck/SelfLowArmCaps.lean` (public `ricciDACap`,
`lieCovCap`), which sits above this file in the import order.  With them
`selfLow_jet` is unconditional; see `SelfLowArmCaps.md`.
