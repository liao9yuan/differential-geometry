# DeTurckVFJetRadiusFree — radius-free DeTurck-VF jet-L² tower (brick 3b)

New leaf for brick 3b: the radius-free (R-free) siblings of the private DeTurck-vector-field jet-L²
tower that discharges brick 3's frontier `deTurckLieCoeffField_perOrder_l2_radiusFree`
(`DeTurckLieCoeffDiffRadiusFree.lean:89`, ONE sorry).  Imports
`DeTurckVFEndoInsertProducers` (re-exports the tower defs + public bottom producers) and
`CurvatureCoefficientDifferenceJetTower` (THE GATE + workhorse + symmS bridge).  The three split
parts (Tower/Producers/TopSep) are READ-ONLY and must not be modified.

## Route (confirmed against the R-dependent tower)

Each R-dependent bottom producer converts `∫ grid_q` (the antidiagonal-tuple product grid over the
P-jets) into a FLAT `R`-dependent constant via `diagonalProductGrid_rfns_integral_ballUniform_succ`
(needs `hPball : ∀ j ≤ a+2, ‖∇ʲP‖ ≤ R`).  The workhorse
`antidiagonalTupleGrid_integral_radiusFree` has the BYTE-IDENTICAL integrand and instead yields
`∫ grid_q ≤ K_rf q · (1 + ‖∇^q P‖²)` from only the order-0 fibre bound
`hsup : ∀ x, rfns g₀ 0 2 x (P.toSection x) ≤ Λ₀²` — no `R`, no `a`, no `hPball`.  Swapping it makes
the producer's `F i` a LOW WINDOW `Flow i · (1 + ∑_{j≤W} ‖∇ʲP‖²)` with `Flow` R-free.

## Producer checklist (per-item status)

| producer | status | axioms | notes |
|---|---|---|---|
| `cometricCastG0_order0sup_jetL2_radiusFree` | LANDED (session 1) | clean | flagship; all-public decomps |
| `sharpFlatEndoCc_lowOrder_jetL2_radiusFree` | LANDED (session 1) | clean | re-derived private `DiffIns+IdIns` split in-leaf |
| `raisedKoszul_order0sup` R-free | NOT NEEDED | — | head engine subsumes it (see finding) |
| `connDiffSection_lowOrder_jetL2_radiusFree` | LANDED (session 2) | clean | via R-free head engine + single_factor + workhorse |
| `wXi_lowOrder_jetL2_radiusFree` | LANDED (session 2) | clean | connDiffSection triangle + `g_bg` const |
| `rfns_iCG_cometricCastG0_atgw_rf` (pointwise) | LANDED (session 3) | clean | re-derives private cometricCastG0 grid bound, atgw currency |
| `rfns_iCG_connDiffSection_atgw_rf` (pointwise) | LANDED (session 3) | clean | head engine + single_factor, atgw currency |
| `rfns_iCG_wXi_atgw_rf` (pointwise) | LANDED (session 3) | clean | via PUBLIC `connLow_rfns` valence bridge + `g_bg` |
| `wOmega_lowOrder_jetL2_radiusFree` | LANDED (session 3) | clean | two-arm grid-mul via `antidiagonalTupleGridWindow_mul_le` + workhorse |
| `exists_rfns_connDiff_topsep_rf` (pointwise) | LANDED (session 4) | clean | head engine, top `rfns(∇^{l+1}P)` kept separate, `l·grid` remainder fold |
| `connDiff_L2_topsep_rf` | LANDED (session 4) | clean | integrate top-sep engine; workhorse window → `Flow n·(1+∑_{j<n+2})` |
| `wXi_L2_topsep_rf` | LANDED (session 4) | clean | connDiff triangle; `g_bg` half folded into window `1` |
| `cometricCastG0_wXi_twoArm_fold_rf` (pointwise) | LANDED (session 4) | clean | reusable two-arm fold → `atgw(n+2)` (extracted from wOmega_lowOrder) |
| `exists_rfns_wOmega_topsep_rf` (pointwise) | LANDED (session 4) | clean | corner-peel envelope `Kc_top·rfns(∇ⁿwXi)+Kwin·atgw`; SPLIT from L² for heartbeats |
| `wOmega_L2_topsep_rf` | LANDED (session 4) | clean | corner via `wXi_L2_topsep_rf`; lower fold via workhorse |
| `rfns_iCG_wOmega_atgw_rf` (pointwise) | LANDED (session 4) | clean | full Leibniz + fold, no `hsup` — feeds wAlphaB fold |
| `wCA_wOmega_twoArm_fold_rf` (pointwise) | LANDED (session 4) | clean | wCA(=connDiff)×wOmega fold → `atgw(i+3)` (both arms +2 offset) |
| `wAlphaB_L2_perOrder_rf` | LANDED (session 4) | clean | top-free arm; two-arm fold + workhorse → `FlowB i·(1+∑_{j<i+3})` |
| `wAlpha_L2_topsep_rf` | LANDED (session 4) | clean | TOWER TOP: wAlphaA(wOmega@i+1)+wAlphaB+triangle; top `‖∇^{i+2}P‖²` |

`clean` axioms = exactly `[propext, Classical.choice, Quot.sound]` (targeted build + `#print axioms`, 2026-07-26).

### SESSION-3 RESULT — wOmega landed; the whole low-order tier is R-free

All FOUR `_lowOrder` producers (`cometricCastG0`/`sharpFlatEndoCc`/`connDiffSection`/`wXi`/`wOmega`)
are now R-free.  `wOmega = appCc(cometricCastG0, wXi)` — the genuine two-arm composer — was folded per
term into a single `antidiagonalTupleGridWindow(n+2)`: `atgw(i'+1)·atgw(l+2) ≤ Const·atgw(i'+l+2) ≤
Const·atgw(n+2)` (via `antidiagonalTupleGridWindow_mul_le` + `_mono`, valid because `i'+l ≤ n`), then
integrated by the workhorse → low window.  No `R`, no `ΛX 0` sup — the R-dependent sup obstruction is
fully avoided.  KEY de-risk: `connLow_rfns` (`connDiffLoweredCc ↔ connDiffSection` fibre-norm identity)
is PUBLIC (`Analysis.Parabolic.TensorSpectral`, reachable via Tower), so the wXi grid bound needed NO
private valence-bridge re-derivation.  Two Lean lessons: (i) after the `l`-range extend the window
`_mono` needs `i'+l ≤ n`, so bound per-`l` on `range(n+1-i')` FIRST then extend the nonneg constants;
(ii) `set Komega := fun n => …` β/ζ-reduces under `rw [mul_assoc]` — use a `calc … := by ring` step
(ring treats `Komega q` as an atom) to keep the fold.

### SESSION-2 FINDING — the head engine subsumes raisedKoszul + sharpFlatEndoCc

`connDiffSection_lowOrder` R-free does NOT route through the R-dependent appCcRS-rankLeft + two-arm
integrator (which consumes `raisedKoszul_order0sup`/`sharpFlatEndoCc_lowOrder` and their `R`-dependent
order-0 sups).  Instead it uses the PUBLIC R-FREE head engine
`rfns_iteratedCovGrad_connDiffSection_topSeparated_le` (JetTower:1823) — constants `g₀/δ₀`-only
(`Ktop = 10·S 0`, `Kc` from `exists_..._sharpFlatEndoCc_tgrid`, no `R`), remainder in
`antidiagonalTupleGrid` currency.  The engine folds the `appCcRS(∇ʲraisedKoszul)(sharpFlatEndoCc)`
product INTERNALLY.  So the R-free `connDiffSection` needs neither a `raisedKoszul` nor a
`sharpFlatEndoCc` R-free sibling — task item 1 (raisedKoszul) is OFF the critical path, and session-1's
`sharpFlatEndoCc_lowOrder_jetL2_radiusFree` is likewise unconsumed by the connDiff/wXi/wOmega chain
(kept as a standalone public producer).  Corner `‖∇^{q+1}P‖²` and remainder
`∑_{k<q}rfns(∇^{q-k}P)·grid(k+1)` fold into the single `grid(q+1)` via
`single_factor_mul_antidiagonalTupleGrid_le`; the workhorse integrates it → low window at order `i+1`.

### wOmega (session 3) — the genuine two-arm grid-mul

`wOmega = appCc(cometricCastG0, wXi)`.  The R-dependent `wOmega_L2_topsep` (TopSep:1001) uses the
arg-corner decomposition `iteratedCovGrad_appCcRS_eq_argCorner_add_lower`: corner = cometricCastG0
order-0 (`ΛClow 0`, R-FREE) × `∇ⁿwXi` (→ top via connDiff); lower sum = two-arm integrator fed
cometricCastG0's R-free sup AND `wXi`'s order-0 sup `ΛX 0` — the latter is `R`-DEPENDENT
(`wXi ~ ∇P`).  R-free route: keep the corner (R-free, `‖∇ⁿwXi‖²` controlled by wXi_lowOrder), and
fold the lower two-arm `∑ rfns(∇^{i'}cometricCastG0)·∑ rfns(∇ˡwXi)` into single grids via
`antidiagonalTupleGrid_mul_le`, then workhorse.  NEEDS a POINTWISE cometricCastG0 grid bound
(`rfns_iteratedCovGrad_cometricCastG0_gridWindow_le`, PRIVATE in
`CurvatureArm1KoszulTopSeparation.lean:35` → re-derive in-leaf, OR extract from session-1's
cometricCastG0 internal `hstep2/hstep3` structure) + a pointwise wXi grid bound (connDiff head engine
per-`x` + `g_bg` const).  Full session; constants stay `g₀/g_bg/δ₀`-only (no `R`) via grid-mul
(no `ΛX 0` sup).

## cometricCastG0 R-free — proof shape (clone of `:834` with the workhorse swap)

`cometricCastG0 = Φ + appCcRS Φ W` (public `cometricCastG0_eq_doubleTrace_add_appCcRS`),
`Φ = cometricDoubleTraceField g₀ 1` (T-independent, R-free sup `SΦ`),
`W = slotInsertEndoCc g₀ 2 (gInvDiffRaisedEndoField g₀ g₁)`.

- **order-0 sup Λ** (R-free): `rfns(cometricCastG0) ≤ 2 SΦ0 + 2 SΦ0·(fr²·C_base 0)` — order-0 of W
  is bounded by the fibre constant `C_base 0` via `grid_0 = 1` (no P-jets); needs only
  `htie/hδ_le/hδ0/hδ`, NOT `hsup`.  Λ R-free.
- **W L² jets (workhorse swap)** `‖∇^q W‖² ≤ KW_rf q·(1+‖∇^q P‖²)`, `KW_rf q = fr²·C_base q·K_rf q`.
- **appCcRS jets** `‖∇^l(appCcRS Φ W)‖² ≤ kd l·(1+S)`, `kd l = appCcGdiag l·(∑_{i'≤l}SΦ i')·(∑_{q≤l}KW_rf q)`,
  `S = ∑_{j≤i}‖∇ʲP‖²`, via `∑_{q≤l}KW_rf q·(1+‖∇^q P‖²) ≤ (∑_{q≤l}KW_rf q)·(1+S)`.
- **assembly** `‖∇^l cometricCastG0‖² ≤ (2·aL l + 2·kd l)·(1+S)`, sum over `l≤i` →
  `Flow i·(1+S)`, `Flow i = ∑_{l≤i}(2 aL l + 2 kd l)`.  R-free.

## §6 FINDING (composers are NOT a single-integrator swap)

The two-arm composers `connDiffSection_lowOrder` / `wOmega_lowOrder` route
`∫ ∑ rfns(∇ⁿS)·∑ rfns(∇ˡT)` through `exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le`
(itself R-free — takes arg-sups, no R), fed the ORDER-0 sups of S/T.  For connDiffSection
S=raisedKoszul, T=sharpFlatEndoCc; the raisedKoszul order-0 sup `ΛK = C·(Csob·R)` is genuinely
`R`-dependent (raisedKoszul ~ ∇P is order-1 in P; its L∞ bound needs the C² Sobolev embedding of the
`a+2` ball).  So the R-free composer CANNOT feed a fixed sup — it must fold the two-factor product
into a SINGLE antidiagonal grid (`antidiagonalTupleGrid_mul_le` + `single_factor_mul_...`, present in
`AntidiagonalTupleProductGrid.lean` and already used by JetTower/Kernel) and hit the workhorse.  This
is viable (infrastructure exists — NOT a wall), but is materially more than a clone-with-swap:
SESSION 2+ scope.  cometricCastG0 avoids this because its appCcRS S-factor is Φ (T-INDEPENDENT,
R-free sup).  sharpFlatEndoCc avoids it too (its non-trivial factor is DiffIns bounded directly by a
grid — no two-arm), but needs the private `sharpFlatEndoCc = DiffIns + IdIns` split re-derived in-leaf
(Producers is read-only).

## Constant audit (STRICT: R-free)

All constants are `g₀ / g_bg / a / dim E / δ₀`-only: `C_base` (fibre decomposition, R-free),
`K_rf` (workhorse, fixed Λ₀), `SΦ` (T-independent Φ sup, R-free), `fr = finrank`, `appCcGdiag`.
NO `R`.  Confirmed by inspection — no §6 unreceivable term at the cometricCastG0/sharpFlatEndoCc level.

### SESSION-4 RESULT — the whole `_L2_topsep` layer + `wAlpha` (tower top) landed

Ten declarations LANDED green + axiom-clean.  The four public `_L2_topsep` siblings
(`connDiff`/`wXi`/`wOmega`) + the tower top `wAlpha_L2_topsep_rf`, plus the supporting private engines
(`exists_rfns_connDiff_topsep_rf`, `exists_rfns_wOmega_topsep_rf`, `cometricCastG0_wXi_twoArm_fold_rf`,
`rfns_iCG_wOmega_atgw_rf`, `wCA_wOmega_twoArm_fold_rf`, `wAlphaB_L2_perOrder_rf`).  Route = clone the
R-dependent `_L2_topsep` proofs with the ball-uniform integrator swapped for the workhorse, keeping the
top data term separate.  Shapes:
- `connDiff`/`wXi`/`wOmega _L2_topsep_rf` (n ≤ a+1): `Ktop·‖∇^{n+1}P‖² + Flow n·(1+∑_{j<n+2}‖∇ʲP‖²)`.
- `wAlpha_L2_topsep_rf` (i ≤ a): `Ktop·‖∇^{i+2}P‖² + Flow i·(1+∑_{j<i+3}‖∇ʲP‖²)`.  Top index `i+2` STILL
  sits inside the low window (range `i+3`); session 5 splits it out (frontier wants range `i+2`, top
  `i+2` — trivial `Finset.sum_range_succ` moving `Flow i·‖∇^{i+2}P‖²` into `Atop`).

KEY Lean lessons (session 4):
1. `/-- … -/` declaration docstrings go AFTER `set_option … in`, not before (else
   "unexpected token 'set_option'; expected 'lemma'").
2. **wOmega heartbeat wall + fix.** The single `wOmega_L2_topsep_rf` (corner-peel pointwise + fold +
   workhorse in one theorem) blew `maxHeartbeats` (timeout at `whnf`, LINEAR scaling 1.6M→3.2M, so
   cumulative not one pathological step). Fix = SPLIT the pointwise corner-peel envelope into a private
   lemma (`exists_rfns_wOmega_topsep_rf`) so the corner-peel and the workhorse integration keep
   SEPARATE heartbeat budgets → both fit 1.6M (51s full-file). The giant `rw [show (…).toSection x = …
   from by rw [SmoothCcTensor.toSection_add]; rfl]` was ALSO replaced by the cheaper
   `rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]` (avoids the terminal
   `rfl` whnf) — but that alone did NOT fix it; the split did.
3. `wOmega`'s pointwise atgw bound (`rfns_iCG_wOmega_atgw_rf`) needs NO `hsup` — take it from the
   FULL Leibniz fold (folding the corner in), NOT from the corner-peeled sup engine (which bundles
   `hsup` for the ΛC sup). Only the top-SEPARATED bounds carry `hsup`.
4. wAlphaB's two-arm fold lands at `atgw(i+3)` (both wCA and wOmega carry the `+2` offset;
   `atgw((n+1)+1)·atgw((l+1)+1) ≤ WMC·atgw(n+l+3) ≤ WMC·atgw(i+3)`), one higher than the wOmega fold's
   `atgw(n+2)` (cometricCastG0 is `+1`).  `norm_iCG_wAlphaA_eq_succ_wOmega` + defeq `(i+1)+1 = i+2`,
   `(i+1)+2 = i+3` let `exact (hom (i+1))` close wAlphaA after `rw […, hS'_def]`.

## Status line (2026-07-26, session 4)

The whole `_L2_topsep` layer is R-free through the TOWER TOP.  17 declarations LANDED green +
axiom-clean (`#print axioms` = exactly `[propext, Classical.choice, Quot.sound]` on all 5 session-4
publics/producer; targeted build 9433 jobs OK).  Leaf 2282 lines (< 2500, no split needed).  What
session 5 (the frontier discharge) consumes: `wAlpha_L2_topsep_rf` — top `Ktop·‖∇^{i+2}P‖²` + low
`Flow i·(1+∑_{j<i+3}‖∇ʲP‖²)` — lifted through `norm_iCG_wEndoInsert_eq_wAlpha` (private in Producers,
`‖∇ⁱwEndoInsert‖=‖∇ⁱwAlpha‖`) + the DLa/DLb split into the brick-3 frontier
`deTurckLieCoeffField_perOrder_l2_radiusFree` (`DeTurckLieCoeffDiffRadiusFree.lean:89`, ONE sorry;
its window is range `i+2`, so session 5 splits the top index `i+2` out of my range `i+3`).  Frontier
still 0% in-code (its `sorry` untouched per task).  See THREEARM_RECON §11d.4.
