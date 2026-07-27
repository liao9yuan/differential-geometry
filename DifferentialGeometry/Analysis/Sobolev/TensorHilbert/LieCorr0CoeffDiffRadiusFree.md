# LieCorr0CoeffDiffRadiusFree — radius-free lieCorr0 coefficient jet-L² sibling (brick 4)

Fourth brick of the Pro-ruled repair of UNIF item-2: the `lieCorr0Field` sibling of brick 3
(`DeTurckLieCoeffDiffRadiusFree.lean`), same gate/workhorse currency, same target shape.  See
`ShortTime/THREEARM_RECON.md` §11/§11d and brick 3's note (whose "brick 4 reuse spec" this
implements).

## Target

R-free sibling of the (never-stated) `lieCorr0Field_realizedFam_jetL2_summed_topSeparated`,
single-tensor (`g₁` tied to `T` via `htie`), RHS jets over `symmS g₀ T`:
```
∑_{i≤a} ‖∇ⁱ(lieCorr0Field g₀ g₁ g_bg)‖²
  ≤ Ktop·∑_{j≤a+2}‖∇ʲ(symmS g₀ T)‖² + Klow·(1 + ∑_{j≤a+1}‖∇ʲ(symmS g₀ T)‖²)
```
`Ktop/Klow` depend only on `g₀,g_bg,a,dim E,δ₀`; NO `R`, NO ball hyp.  Hyps: `ha_super`
(`2·dim E+10 ≤ a`, inherited from the DeTurck-VF tower), `gFibreOpBound g₀ (ccTensorBilinSymm g₀ T) δ`,
`δ ≤ δ₀`, `htie`.

## Status: COMPLETE — all five arm engines proved; public endpoints are axiom-clean

- `lieCorr0Field_summed_l2_radiusFree` — the deliverable, STATED + summed→per-order reduction
  PROVED (verbatim brick-2/3 summed clone).
- `lieCorr0Field_perOrder_l2_radiusFree` — the per-order engine, PROVED from the five-way split.
- Arm engines (private, in this leaf):
  - `lc0Base_perOrder_rf` — **PROVED** (the only top-carrying piece).
  - `lc0Diff_perOrder_rf` — **PROVED** (top-free).
  - `lc0Riem_perOrder_rf` — **PROVED** (top-free).
  - `lc0VB_perOrder_rf` — **PROVED** (session 3, the atgw jets assembly; see the session-3
    entry below).
  - `lc0AMix_perOrder_rf` — **PROVED** from the five-factor refold, moving-trace grid bounds,
    four pointwise product joins, and one radius-free integration.
  - `lc0VBAMix_perOrder_rf` — **PROVED** from the two axiom-clean halves.
- Both public theorems replay with `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

## The five-way split and per-arm routes

`lc0_decomp` + `insert_base` (`LieCorr0Split.lean`, all public):
`lieCorr0Field = lc0Insert g₀ + (lc0Insert g_bg − lc0Insert g₀) + lc0VB + lc0AMix + lc0Riem`,
assembled by the local `sq_le_five_add` (copied from the frozen leaf) + one
`Finset.sum_range_succ` peel of the `i+3` windows into `Atop` (brick-3 pattern).

1. **base insert (top).**  `lc0Insert g₀ g₁ g₀ = −DLb(g₀,g₁,g₀)` (`lc0Insert_base_eq_neg_dlb`,
   exposed) ⟹ brick-3's DLb arm verbatim at `g_bg := g₀`: `normSq_iCG_dlbField_le` (public
   since brick 3) + `norm_iCG_wEndoInsert_eq_wAlpha` (public) + the R-free tower top
   `wAlpha_L2_topsep_rf`.  Top `4·fr·Ktop_wα·‖∇^{i+2}P‖²` + low window `i+3`.
2. **insert difference (top-free).**  `(2,2)→(1,1)` by `normSq_iCG_lc0InsertDiff_le` (exposed);
   `slotInsertEndoCc g₀ 0 (endoDiffSection) = cometricRaise(wAlphaB g₀) − cometricRaise(wAlphaB g_bg)`
   via `slotInsertEndoCc_sub` (exposed) + the public HOIST `connDiffDVFInsert_eq_cometricRaise` ×2
   (the `endoDiffSection`-unfolded form is accepted by `exact` — defeq, session-4 lesson);
   jet isometry `norm_iCG_cometricRaiseSlot0Field_eq` (exposed) ×2 + `sq_le_two_add` →
   R-free `wAlphaB_L2_perOrder_rf` (exposed in `DeTurckVFJetRadiusFree.lean`) at `g₀` and `g_bg`.
   Result `4·fr·(2FB₀+2FB_bg)·(1+∑_{j<i+3})`.
3. **lc0Riem (top-free).**  Clone of the frozen atom's two-arm route with ONE swap: the
   ball-uniform `cometricDoubleTraceField_order0sup_jetL2_ballUniform_generic` (Λ, F both
   R-dependent) is replaced by the R-free `cometricCastG0_order0sup_jetL2_radiusFree` (tower,
   public; Λ R-free, jets → low window `Fcg i·(1+∑_{j<i+1})`).  Everything else was ALREADY
   R-free: the two-arm integrator `exists_integrated_..._twoArm_rs_le`'s constant `Cint k` is
   `g₀`/ranks/`k`-only (R entered the old atom ONLY through the cometric envelope's Λ/F); the
   fixed passenger `lc0RiemPass` is `T`-independent (sup via
   `exists_bound_riemannianFiberNormSq_smoothCcTensor`, jets = plain constants `NPass i`).
   Live-arm transports `lc0RiemLive_rfns_le`/`_l2_le` (exposed) carry sup and jets from
   `cometricCastG0` at cost `fr`.  Tail: pad `1+W₁ ≤ 1+W₃` and `NPass ≤ NPass·(1+W₃)`.
   Needs `i ≤ a+1` (the tower producer's cap) — one `omega` at the call site.
4. **lc0VB — PROVED (session 3, `lc0VB_perOrder_rf`).**  Pointwise atgw assembly:
   `lc0VB_eq_app` (live cometric arm × moving passenger, cost `4` from the `2•`) → `vbSplit`
   (passenger = `vbMcdArm` head × `ipLowCc(wOmega)` tail) → `b4_mcd_eq` (mcd = wXi + the
   two-orientation `b4Phi` correction), with the committed producers
   `rfns_iCG_{cometricCastG0,wXi}_atgw_rf` + `rfns_icg_ipLow_le`; one integration at the end.
   The window lands at `atgw(i+3)` = the `range (i+3)` low window exactly.  No `i ≤ a` cap.
5. **lc0AMix — PROVED.**  `LieCorr0AMixRefold.lean` identifies the canonical `lc0AMix` with
   the exact five-factor operator product.  `LieCorr0TraceRadiusFree.lean` bounds each moving
   trace by a radius-free low grid window.  Two slot-extended mcd bounds and four applications
   of `b4_join_atgw` land on `atgw(i+3)`, then one integration gives
   `Flow i·(1+∑_{j<i+3})`.

## Exposures (minimal `private`-removals, content unchanged; homes rebuilt green)

- `DeTurckVFJetRadiusFree.lean` (brick-3b tower): `wAlphaB_L2_perOrder_rf`.
- `DeTurckVFEndoInsertTopSep.lean`: `slotInsertEndoCc_sub`, `norm_iCG_cometricRaiseSlot0Field_eq`.
- `LieCorr0CoeffL2JetBound.lean` (frozen leaf; exposures only, NO content edits — the old
  ballUniform atoms stay untouched): `endoArm_eq_dlb`, `lc0Insert_base_eq_neg_dlb`,
  `lc0RiemLive`, `lc0RiemPass`, `lc0Riem_eq_app`, `lc0RiemLive_rfns_le`, `lc0RiemLive_l2_le`,
  `endoDiffSection`, `normSq_iCG_lc0InsertDiff_le`.

New leaf imports: `LieCorr0CoeffL2JetBound` + `DeTurckVFJetRadiusFree` +
`SobolevNonlinearityExistence` (symmS bridges).  Opens: the frozen leaf's block with `symmS`
and `cometricRaiseSlot0Field` added to the restricted `TensorSpectral` list (both live there).

## Completed frontier assessment

**UPDATE (2026-07-26, ip-engine session): the `lc0VB` half of the gap is DISSOLVED.**  The
frozen atom's `vbPass_jetL2` is discharged (frozen leaf ZERO-sorry, axiom-clean) via the new
generic engine `InteriorProductJetBound.lean` (`ipLowCc` + `rfns_icg_ipLow_le`/`norm_icg_ipLow_le`
— radius-AGNOSTIC) + the exposed `wOmega_unitModel_apply` bridge + the in-leaf split
`vbSplit : lc0VBPass = appCcRS g₀ 2 1 4 vbMcdArm (ipLowCc g₀ (wOmega g₀ g₁ g₀))` (see the frozen
note's session 9).  What discharging `lc0VBAMix_perOrder_rf` still needs (route fully mapped in
`THREEARM_RECON.md` §11d.7, no unknown frontier):

(a) `lc0VB` R-free: **DONE (session 3)** — see the session-3 entry: `b4_mcd_eq`-based mcd
producer (`b4_mcd_atgw`), the atgw jets assembly, and the single integration
(`lc0VB_perOrder_rf`), all axiom-clean.

(b) `lc0AMix`: **DONE.**  The smaller route uses the public `pureTrace` realization rather
than rebuilding three separate slot-extended cometric transports.  The exact refold still
expresses the canonical three moving traces at ranks `(4,2)/(5,3)/(6,4)` and the two mcd
chains, but the common theorem `trace_grid_rf p` handles all three ranks.

## SESSION 2 (2026-07-26, discharge session): R-free `mcd` FIBRE IDENTITY GREEN; workhorse currency decoded; jets assembly = resumption

**Landed green (in-leaf, private; the leaf's ONLY `sorry` is still `lc0VBAMix_perOrder_rf`):**

- **Workhorse currency decoded** (from the tower's wOmega proof): the R-free tower does NOT use
  the sup×L² integrator — it works in POINTWISE `antidiagonalTupleGridWindow` (atgw) polynomial
  bounds in `bP j = |∇ʲP|²(x)`, multiplies windows by `antidiagonalTupleGridWindow_mul_le`
  (`atgw(a+1)·atgw(c+1) ≤ C·atgw(a+c+1)`) + `_mono`, and integrates ONCE at the end via the
  public `antidiagonalTupleGrid_integral_radiusFree` (`∫grid(i) ≤ K i·(1+‖∇ⁱP‖²)`, `Λ₀`-only).
  This dissolves the "no R-free sup for connDiff arms" worry: sups are never needed off order 0.
- **Exposed** (`DeTurckVFJetRadiusFree.lean`): `rfns_iCG_cometricCastG0_atgw_rf`
  (`≤ Kcg l·atgw(l+1)`) and `rfns_iCG_wXi_atgw_rf` (`≤ Kwx l·atgw(l+2)`) — the per-arm pointwise
  producers.
- **`b4_mcd_eq` (THE identity):** `metricConnDiffLoweredCc g₀ g₁ g_bg = wXi g₀ g₁ g_bg +
  ½·appCc(b4Phi g₀ P b4PermA)(wXi) + ½·appCc(b4Phi g₀ P b4PermB)(wXi)` under `htie`, with
  `b4Phi g₀ P σ = appCcRS g₀ 3 5 3 (reindexCoeffGen (cometricDoubleTraceField g₀ 3) σ)
  (slotExtend³ P)` (the `ipLowCc` pattern one rank up; `b4PermA = ![2,3,0,1,4]` self-inverse,
  `b4PermB = ![2,3,0,4,1]`).  NO symmS bridge (the two orientations average to
  `ccTensorBilinSymm` directly), NO inverse-metric machinery (polynomial in `P`).
- Green supporting privates: `b4_pk3_toModel`, `b4_trace_center` (rank-3), `b4_frame_expand`,
  `b4_cons_sum_smul`/`b4_cons1_sum_smul`, `b4_mcd_unitModel`, `b4_appCc_unitModel`,
  `b4_unit_read`, `b4_unitModel_add/smul`, `b4_rank0_unit`, `b4_icg_zero`, `b4_iCG_smul`,
  `b4_rfns_smul`, `b4_trace_succ` (rank-3 ∇-parallel collapse), `b4_bP_le_grid` (positive-order
  monomial ↪ grid; the order-0 term goes through the `Λ₀` sup instead — `grid b 0 = 1`!).

**RESUMPTION (jets assembly, all committed currency, no unknown frontier):**
1. ✅ (session 3) `b4_phi_atgw`: `|∇ⁱ(b4Phi)|²`-pointwise via the rankLeft grid `(3,5,3)`.
2. ✅ (session 3) `b4_mcd_atgw`: `|∇ⁿmcd|² ≤ Kmcd n·atgw(n+2)` via `b4_mcd_eq`.
3. ✅ (session 3) `b4_wOmega_atgw`: the tower `hpt` clone, `|∇ⁿwOmega|² ≤ KΩ n·atgw(n+2)`.
4. ✅ (session 3) `b4_vbPass_atgw` + `b4_vb_atgw`: window lands at `atgw(i+3)` exactly.
5. ✅ (session 3) `lc0VB_perOrder_rf` integrated; sorry NARROWED to `lc0AMix_perOrder_rf`.
6. ✅ (session 4) `lc0AMix`: exact five-factor refold + generic moving-trace grid producer +
   two slot-extended mcd arms + four joins + one integration.

## SESSION 3 (2026-07-26, brick-4 part A): resumption items (1)–(5) LANDED GREEN; sorry now lc0AMix-only

All five items closed exactly along the itemized route, on the FIRST full check pass (no proof
repair).  New in-leaf privates (all axiom-clean, `[propext, Classical.choice, Quot.sound]`):

- `b4_pk3_rfns_le` — triple-`slotExtend` jet domination `|∇^q b4Pk3|² ≤ fr³·|∇^q P|²`.
- `b4_phi_atgw` — item (1).  Deviation from the itemized route: the trace arm uses per-order
  constants via `exists_bound_riemannianFiberNormSq_smoothCcTensor` at EVERY order (tower `hSΦ`
  pattern) instead of `b4_trace_succ` + order-0-only; mathematically equivalent (the arm is a
  fixed `T`-independent tensor), strictly simpler.  `b4_trace_succ` stays banked for step (6).
  Window absorption: `bP 0` through the `Λ₀` sup, `bP (m+1)` through `b4_bP_le_grid`; per-window
  constant `(l+1)·(1+Λ₀²)`.
- `b4_app_atgw` — item (2a), the `appCc (b4Phi σ) (wXi)` two-arm fold (`σ` generic, so A/B
  orientations are one lemma); `≤ Kap n·atgw(n+2)`.
- `b4_mcd_atgw` — item (2), `g_bg`-GENERIC (step (6) needs both `g_bg` and `g₀` mcd arms):
  `b4_mcd_eq` + rfns add ×2 + `b4_rfns_smul` (the two `½`s square to `¼`, cancelling the
  `2·2` from the two triangle bounds) → `Kmcd n = 2·Kwx n + KapA n + KapB n`.
- `b4_wOmega_atgw` — item (3), the tower `hpt` fold as a standalone pointwise lemma (no `hsup`
  needed — sups enter only at integration).
- `b4_vbPass_atgw` — item (4) head: `vbSplit` + rankLeft `(2,1,4)`; head arm
  `vbMcdArm_rfns_le` → `b4_mcd_atgw` at `g_bg := g₀` (window `i'+2`), tail arm
  `rfns_icg_ipLow_le` → `b4_wOmega_atgw` at `g_bg := g₀` (per-`m` mono into window `q+2`);
  fold at `_mul_le (i'+1) (q+1)` → `atgw(n+3)`.
- `b4_vb_atgw` — item (4) tail: `lc0VB_eq_app` + `b4_iCG_smul`/`b4_rfns_smul` (the `2•` costs
  `×4`) + rankLeft `(2,4,2)`; head `lc0RiemLive_rfns_le` → `rfns_iCG_cometricCastG0_atgw_rf`
  (window `i'+1`), tail = `b4_vbPass_atgw` (window `q+3`); fold at `_mul_le i' (q+2)` →
  `atgw(i+3)` exactly.
- `lc0VB_perOrder_rf` — item (5), the single integration (workhorse
  `antidiagonalTupleGrid_integral_radiusFree` summed over `k < i+3`); needs NO `i ≤ a` cap
  (all atgw producers are cap-free).
- `lc0AMix_perOrder_rf` — the NEW lc0AMix-only `sorry` (same hypothesis bundle and low-window
  shape as the old pair lemma, minus the `lc0VB` summand).
- `lc0VBAMix_perOrder_rf` — REWRITTEN as the sum of the two halves; public statement unchanged,
  so the downstream five-way assembly is untouched.

Lean lessons (session 3): the whole assembly is term-mode-safe against `set`-variable folding
(bounds combined by `mul_le_mul`/`add_le_add`, never cross-`linarith` on window atoms); the
tower's per-l-then-extend `_mono` pattern and the `rw [mul_assoc]`-then-`mono-left` RHS
restructure transplant verbatim; `(4+1)+q`-style literal indices unify by `exact` without any
`show` bridges (same as the session-2 machinery).

## Honest progress (denominator: (N) `ricci_flow_unif_existence` = 0%, unstated)

Item-2 proper: bricks 1-4 DONE (gate + arm0 + deTurckLie + lieCorr0, all axiom-clean).
Brick 4 is **100%**.  The item-2 smooth-core theorem itself is still **0%** until stated and
proved; its dedicated machinery is about **80%**.  Remaining: threeArm/Ψ₀ topSeparated
assembly (Fork-A), then smooth-core tame layers 2-3.  Whole `(N)` remains **0%** as a theorem;
its dedicated machinery is conservatively about **74%**.

## Verification (2026-07-26, session 3)

Focused check + targeted module build through the leaf: GREEN.  The ONLY `sorry` in the leaf is
`lc0AMix_perOrder_rf` (the lc0AMix-only private).  In-file `#print axioms` (end of leaf),
literal results:

- `lieCorr0Field_perOrder_l2_radiusFree` : `[propext, sorryAx, Classical.choice, Quot.sound]`
- `lieCorr0Field_summed_l2_radiusFree`   : `[propext, sorryAx, Classical.choice, Quot.sound]`
- `lc0Base_perOrder_rf` : `[propext, Classical.choice, Quot.sound]`  (clean)
- `lc0Diff_perOrder_rf` : `[propext, Classical.choice, Quot.sound]`  (clean — hence the exposed
  `wAlphaB_L2_perOrder_rf` / `slotInsertEndoCc_sub` / `norm_iCG_cometricRaiseSlot0Field_eq` /
  `normSq_iCG_lc0InsertDiff_le` chain is sorry-free)
- `lc0Riem_perOrder_rf` : `[propext, Classical.choice, Quot.sound]`  (clean)
- `b4_phi_atgw`, `b4_app_atgw`, `b4_mcd_atgw`, `b4_wOmega_atgw`, `b4_vbPass_atgw`,
  `b4_vb_atgw`, `lc0VB_perOrder_rf` : all `[propext, Classical.choice, Quot.sound]`  (clean —
  the whole lc0VB half is sorry-free)
- `lc0AMix_perOrder_rf` : `[propext, sorryAx, Classical.choice, Quot.sound]`  (THE frontier)
- `lc0VBAMix_perOrder_rf` : `[propext, sorryAx, Classical.choice, Quot.sound]`  (inherits
  exactly the lc0AMix sorry)

Frozen-leaf audit (unchanged this session — no frozen-leaf edits were needed; the four
session-9 exposures `vbSplit`/`vbMcdArm`/`vbMcdArm_rfns_le`/`lc0VB_eq_app` were already
public).  Session 3 compiled on the first full check pass (no proof repair was needed).

## SESSION 4 (2026-07-26, Codex takeover): lc0AMix CLOSED

Landed:

- `LieCorr0AMixRefold.lean`: a 394-line public leaf proving the exact canonical
  `amix_refold_rf`; it uses `metricConnDiffLoweredCc` directly and does not import the RED
  `LieCorr0LowJet.lean`.
- `LieCorr0TraceRadiusFree.lean`: a 203-line public leaf proving the rank-generic
  `trace_grid_rf`; the fixed trace contributes background constants and the moving
  inverse-metric difference contributes the low antidiagonal grid.
- In this file: generic slot-extension and product-window joins, the five-factor pointwise
  bound `b4_amix_atgw`, and the integrated `lc0AMix_perOrder_rf`.

Verification passed for both new leaves and this consumer.  Exact axiom replay:

- `lieCorr0Field_perOrder_l2_radiusFree`,
  `lieCorr0Field_summed_l2_radiusFree`,
  `lc0AMix_perOrder_rf`, and `lc0VBAMix_perOrder_rf`:
  `[propext, Classical.choice, Quot.sound]`.

No `sorry` remains in the three touched Lean files.  The next item-2 frontier is the
threeArm/Ψ₀ topSeparated assembly, not another `lc0AMix` transport proof.
