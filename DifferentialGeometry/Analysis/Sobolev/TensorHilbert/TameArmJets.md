# `TameArmJets.lean` — the quadratic C0 arms in the marked currency

Companion note.  Status, route, what landed, what is still blocked and where.

## Status

* **`A·A` arm (`ricciAAArm`): DONE end-to-end.**
  `connDiffMark` → `ricciAAMark` (pointwise, `u = 2`, constants state-free,
  **axiom-clean**) → `ricciAAJet` (the tame `L²` jet bound).
* **`lc0VB`: NOT started here.**  Blocked on one missing marked input; see below.

## What landed

### `connDiffMark` — the entry point

`|∇ʲ(connDiffSection g₁ g₀)|²(x) ≤ Kcd j · markGrid (bP x) 1 j`, constants
state-free, no cap.  Read off
`rfns_iteratedCovGrad_connDiffSection_topSeparated_le`
(`Spectral/Tensor/CovGrad/CurvatureCoefficientDifferenceJetTower/Lowered.lean:731`)
through `mkOfTop`: that producer already presents the arm as
`Ktop·|∇^{j+1}P|²` plus residual monomials `|∇^{j-k}P|²·grid(k+1)`, each carrying
an explicit state jet of order `≥ 1` at total weight exactly `j + 1`.

**This was the session's key find.**  The marked window that the tame currency
needs is not new geometry: it is the `topSeparated` form the tree already proves
and then throws away when it weakens to `atgw bP (j+2)`
(`rfns_iCG_connDiffSection_atgw_rf`).

### `ricciAAMark` — the arm, twice marked

`|∇ⁱ(ricciAAArm g₀ g₁)|²(x) ≤ K i · markGrid (bP x) 2 i`, `K` **state-free**: no
`Λ`, no Sobolev radius anywhere in the statement.  A one-for-one re-run of
`ricciAACap` with `capOfArm ↦ mkOfTop` and `cap* ↦ mk*`:

```
connDiffSection      topSeparated  -->  u = 1
  slotExtend ×2, reindex           -->  u = 1   (connDiffContrInsertionField)
  slotExtend ×1, reindex           -->  u = 1   (…InnerField)
permCoeff (Fin 3 / Fin 4)          -->  u = 0
aaCoreP / aaCore                   -->  u = 2   (mkApp: the marks ADD)
ricciAAKer = Σ six pieces          -->  u = 2
ricciCometricFourTraceCastG0       -->  u = 0   (fourTrAtgw, offset +1)
ricciAAArm = cast ⋆ ricciAAKer     -->  u = 2
```

The six kernel pieces are handled through the universally-quantified
`hA' ρ ρ'` / `hB' ρ`, so the `private` permutation constants of
`SelfLowCapWindows.lean` never have to be named.

### `ricciAAJet` — the deliverable shape

```
‖∇ⁱ(ricciAAArm)‖² ≤ (K₀ i + K₂ i·∑_{j<3}‖∇^{1+j}P‖²)·(1 + ∑_{j<i+2}‖∇ʲP‖²)
```

`K₀, K₂` chosen BEFORE the state (background metric + order only): no `R₀`, no
opaque cap, no `N`, exactly ONE power of `‖P‖²_{H³}`.  Inputs: `ricciAAMark`,
`markJet`, and `gradCapLin` (spent once, at the very end).  The only extra
hypothesis is the δ-anchor `|P|_∞ ≤ 1`, which at `finrank = 3` is implied by
`‖P‖_∞ ≤ finrank/3`.

Compare `ricciAACap` + `capJet`: same left-hand side, constant of `Λ`-degree
`3(i+1)`, i.e. degree `6(i+1)` in `‖P‖_{H³}`.

## `lc0VB` — precise blocker

`lc0VB = 2 • (lc0RiemLive ⋆ lc0VBPass)` (`lc0VB_eq_app`), and
`lc0VBPass = vbMcdArm ⋆ ipLowCc (wOmega g₀ g₁ g₀)` (`vbSplit`).  Marks:

| factor | needed | available |
| --- | --- | --- |
| `lc0RiemLive` | `u = 0` | ✅ `rfns_iCG_cometricCastG0_atgw_rf` at offset `+1` → `mkOfWin` |
| `vbMcdArm` (via `b4_mcd_atgw`) | `u = 1` | ❌ only `atgw bP (m+2)` |
| `ipLowCc (wOmega)` (via `b4_wOmega_atgw`, `rfns_icg_ipLow_le`) | `u = 1` | ❌ only `atgw bP (q+2)` |

Both missing inputs bottom out in the SAME place: `rfns_iCG_wXi_atgw_rf`
(`DeTurckVFJetRadiusFree.lean:1050`), whose own docstring says it goes "via the
public valence bridge `connLow_rfns` (`connDiffLoweredCc ↔ connDiffSection`
fibre-norm identity) + the connDiffSection grid bound; the `g_bg` half is a
`T`-free per-order constant folded into the window".

So the next brick is a **marked `wXi`**: re-run `rfns_iCG_wXi_atgw_rf` with
`connDiffMark` in place of `rfns_iCG_connDiffSection_atgw_rf`.  ONE thing must be
checked first, and it is a genuine mathematical question, not a Lean one: the
`g_bg` half.  For general `g_bg` it is a `T`-free constant, which is `u = 0`, NOT
`u = 1`, and would break the mark count.  In the `lc0VB` call site `g_bg = g₀`
(`b4_mcd_atgw g₀ g₀`, `b4_wOmega_atgw g₀ g₀`), where that half should vanish
identically — **verify that it does before building the marked `wXi`.**  If it
does, the rest of the `lc0VB` chain is mechanical:
`wXi` (u=1) → `mcd` (u=1, via `b4_mcd_eq` + the two `b4_app` terms, which must
also be checked to be marked) → `wOmega = cometricCast ⋆ wXi` (u = 0+1 = 1) →
`ipLowCc` (mark-preserving, `rfns_icg_ipLow_le` is a sum bound) →
`lc0VBPass` (u = 2) → `lc0VB` (u = 0+2 = 2).

## Verification

Focused checks of `TameArmJets.lean`: **passed, no errors, no warnings.**
Targeted module builds of `+…MarkedTupleGrid`, `+…TameMarkWin`,
`+…TameArmJets`: all passed (9572 jobs on the last).  Axiom census:
`connDiffMark`, `ricciAAMark` **clean**; `ricciAAJet` carries `sorryAx` through
`markJet → markMon → gridIntHigh` (the single declared class-3 frontier) and
through nothing else.

## Lessons

* Do NOT bind the six `aaKerSplit` pieces to their `private` permutation names.
  Build the window universally in `ρ, ρ'` and let unification pick them; the
  chain must then be written INSIDE the `refine mkMono … (mkAdd …)` so the
  expected type propagates.  A detached `have hsum := mkAdd …` leaves the
  permutations as unsolved metavariables.
* `rfns_iteratedCovGrad_connDiffSection_topSeparated_le` returns a CONJUNCTION
  about the split `connDiffSection = Hd + (connDiffSection − Hd)`; combine with
  `riemannianFiberNormSq_add_le` (factor 2 on each half) and state the two halves
  as `have`s already phrased in `gridBase` (they typecheck by defeq) before
  `linarith`.  `simp only [hgb]` on a `∀ l` unfolding lemma does NOT fire under
  the `antidiagonalTupleGrid` binder.
