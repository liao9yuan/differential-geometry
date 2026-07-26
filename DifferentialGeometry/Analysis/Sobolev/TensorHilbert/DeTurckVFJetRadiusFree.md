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
| `wOmega_lowOrder` R-free | NEXT (session 3) | — | two-arm; needs cometricCastG0 pointwise grid bound + grid-mul |

`clean` axioms = exactly `[propext, Classical.choice, Quot.sound]` (targeted build, 2026-07-26).

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

## Status line (2026-07-26, session 2)

FOUR producers LANDED green + axiom-clean (targeted build, exactly `[propext, Classical.choice,
Quot.sound]`): session 1 `cometricCastG0`/`sharpFlatEndoCc`; session 2 `connDiffSection_lowOrder`/
`wXi_lowOrder`.  Leaf ~815 lines.  Session-2 pivot: `connDiffSection` R-free came in cleanly via the
PUBLIC R-free head engine (subsuming raisedKoszul/sharpFlat — task item 1 `raisedKoszul` turned out
UNNEEDED, see finding).  Next (session 3): `wOmega_lowOrder` R-free — the genuine two-arm grid-mul
(cometricCastG0 pointwise grid bound re-derive + `antidiagonalTupleGrid_mul_le` fold + workhorse; NO
`ΛX 0` sup).  Then the `_L2_topsep` layer (`connDiff`/`wXi`/`wOmega` top-sep, mostly done R-free-ready
by the same engines) → `wAlpha` assembly → frontier discharge (final 3b session).  Base = 4 of ≈8-10
producers; frontier still 0% in-code.  See THREEARM_RECON §11d.1.
