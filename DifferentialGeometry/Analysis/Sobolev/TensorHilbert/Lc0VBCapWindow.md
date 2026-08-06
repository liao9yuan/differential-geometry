# `Lc0VBCapWindow.lean` — `lc0VB` on the `range (i+2)` budget

Smoke test of the `Λ₁`-capped currency of `GradCapAtgw.lean` (brick A1-CUR-2,
session 1).  Both declarations are sorry-free.

## What it proves

* `lc0VBCapAtgw` — `|∇ⁱ(lc0VB g₀ g₁)|²(x) ≤ Kvb i · atgw b'P (i+1)` where
  `b'P j = |∇^{j+1}P|²(x)`.  Compare `b4_vb_atgw` (same file family), whose
  window is `atgw bP (i+3)`: one grid level higher in the base that does NOT see
  the `∇P` cap, hence one derivative over budget.
* `lc0VBCapJet` — `‖∇ⁱ(lc0VB)‖² ≤ K i · (1 + ∑_{j<i+2} ‖∇ʲP‖²)`.  Compare
  `lc0VB_perOrder_rf`, which is radius-free but lands on `range (i+3)`.

The extra input is exactly the pointwise cap `|∇P|_∞ ≤ Λ`, which
`gradCapOfBall` produces from the `H^{a+2}` ball at gate `1 ≤ a` in dimension
three.  The other cap `|P|_∞ ≤ Λ` is already available from `δ ≤ 1/3`
(`pathPert_rad`).

## Route

Nothing about `lc0VB` is re-proved.  The same three arm windows that
`b4_vbPass_atgw` / `b4_vb_atgw` consume are fed in; only the base of the grid
changes, via `armShift`:

```
vbMcdArm            (vbMcdArm_rfns_le ∘ b4_mcd_atgw)      atgw bP (m+2)
ipLowCc (wOmega)    (rfns_icg_ipLow_le ∘ b4_wOmega_atgw)  atgw bP (q+2)
   atgwCapArm  +  vbSplit        ->  lc0VBPass  :  atgw b'P (n+1)
lc0RiemLive  (lc0RiemLive_rfns_le ∘ rfns_iCG_cometricCastG0_atgw_rf)
                                      atgw bP (m+1) ≤ atgw bP (m+2)
   armShift + atgwFold (0,0) + lc0VB_eq_app (the factor 2)
                                  ->  lc0VB      :  atgw b'P (n+1)
   atgwCapToJet (w = 1)           ->  range (n+2)                      ✓
```

## Cost / lessons

* Exactly ONE promotion was needed: `b4_wOmega_atgw`
  (`LieCorr0CoeffDiffRadiusFree.lean:2227`) `private → public`.  It was
  collision-scanned first (three references, all inside its own file).  The
  standing lesson applies: `private` hides a name from importers but does NOT
  give it a distinct fully-qualified name.
* The `2 •` of `lc0VB_eq_app` goes through the PUBLIC
  `iteratedCovGrad_smul_real` and `riemannianFiberNormSq_smul`; the `private`
  `b4_iCG_smul` / `b4_rfns_smul` copies did not have to be promoted.
* The window has to be re-entered at the ARM level.  Shifting the already-folded
  `b4_vb_atgw` window is one order lossy, because the shift is sharp only when
  every grid entry of the bound has at least one factor — true for a bound on an
  arm LINEAR in `∇P`, false for a bound on a quadratic one.  This is the same
  reason `ricciAAArm` is not reachable this way.
* First build passed with no iteration.
