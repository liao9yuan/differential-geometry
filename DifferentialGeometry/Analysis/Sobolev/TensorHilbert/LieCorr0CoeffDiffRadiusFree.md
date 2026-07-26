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

## Status: HONEST PARTIAL — statement landed, 3 of 4 arm engines PROVED, ONE flagged `sorry`

- `lieCorr0Field_summed_l2_radiusFree` — the deliverable, STATED + summed→per-order reduction
  PROVED (verbatim brick-2/3 summed clone).
- `lieCorr0Field_perOrder_l2_radiusFree` — the per-order engine, PROVED from the five-way split.
- Arm engines (private, in this leaf):
  - `lc0Base_perOrder_rf` — **PROVED** (the only top-carrying piece).
  - `lc0Diff_perOrder_rf` — **PROVED** (top-free).
  - `lc0Riem_perOrder_rf` — **PROVED** (top-free).
  - `lc0VBAMix_perOrder_rf` — **THE single flagged `sorry`** (see below).
- Both public theorems therefore carry `sorryAx` from exactly this one frontier.

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
4. **lc0VB + lc0AMix — THE FRONTIER (one `sorry`, `lc0VBAMix_perOrder_rf`).**  Their pointwise
   engines do not exist in ANY currency:
   - `lc0VB`: its own ballUniform atom is still sorried at `vbPass_jetL2` (frozen leaf) — the
     moving passenger `lc0VBPass = domDomCongr(VBPerm) ∘ slotExtend(metricConnDiffLoweredCc)
     ∘ ip(deTurckVF)` lacks an `interior_product`-with-vector Leibniz jet lemma + the
     raw-deTurckVF ↔ `wOmega` g₀-lowering correspondence (frozen note, session 8).
   - `lc0AMix`: no jet atom at all (traceStep-chain fibre identity unstarted).
   Both are `∇²T`-free, so the sorried statement is the pure low window `Flow i·(1+∑_{j<i+3})` —
   exactly what their eventual engines (product of two connDiff-family arms through the
   workhorse) will deliver.  Per the brick-4 ruling the atom machinery was NOT rebuilt here.

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

## Remaining frontier assessment

**UPDATE (2026-07-26, ip-engine session): the `lc0VB` half of the gap is DISSOLVED.**  The
frozen atom's `vbPass_jetL2` is discharged (frozen leaf ZERO-sorry, axiom-clean) via the new
generic engine `InteriorProductJetBound.lean` (`ipLowCc` + `rfns_icg_ipLow_le`/`norm_icg_ipLow_le`
— radius-AGNOSTIC) + the exposed `wOmega_unitModel_apply` bridge + the in-leaf split
`vbSplit : lc0VBPass = appCcRS g₀ 2 1 4 vbMcdArm (ipLowCc g₀ (wOmega g₀ g₁ g₀))` (see the frozen
note's session 9).  What discharging `lc0VBAMix_perOrder_rf` still needs (route fully mapped in
`THREEARM_RECON.md` §11d.7, no unknown frontier):

(a) `lc0VB` R-free: expose `vbSplit`/`vbMcdArm`/`vbMcdArm_rfns_le`/`vbMcdArm_l2_le` from the
frozen leaf; build the ONE missing producer — the R-free `metricConnDiffLoweredCc` sibling via
`mcd = wXi g₀ g₁ g_bg + Pκ` (`wXi_lowOrder_jetL2_radiusFree` committed; `Pκ` = fixed-trace ∘
`slotExtend³(P)` correction, P-jets = the window, P-sup = `Λ₀`); ip arm consumes
`norm_icg_ipLow_le` + `wOmega_lowOrder_jetL2_radiusFree` (both committed) as-is; then clone this
file's `lc0Riem_perOrder_rf` integrator assembly.  ~1 session.

(b) `lc0AMix`: the 5-factor traceStep-chain fibre identity — three moving cometric traces at
ranks `(4,2)/(5,3)/(6,4)` via `reindexCoeffGen(slotExtendᵏ(cometricCastG0))` (`lc0RiemLive`
pattern, `k = 1,2,3`) + two `slotExtend`-chains over the mcd arms (`g_bg`, `g₀`) + nested grids +
integrator.  ~1–2 sessions.  Classification unchanged: missing-groundwork/API, now with all
engines committed except the R-free mcd producer of (a).

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
1. `b4_phi_atgw`: `|∇ⁱ(b4Phi)|²`-pointwise via the rankLeft grid `(3,5,3)`: trace arm =
   `rfns_iteratedCovGrad_reindexCoeffGen_eq` + `b4_trace_succ` (only order 0 survives, const by
   `exists_bound_riemannianFiberNormSq_smoothCcTensor`); `slotExtend³` arm = slotExtend jet lemma
   ×3 → `bP`-window via `b4_bP_le_grid` + `hsup`.
2. `b4_mcd_atgw`: `|∇ⁿmcd|² ≤ Kmcd n·atgw(n+2)` via `b4_mcd_eq` + rfns add/`b4_rfns_smul` +
   `appCc_iteratedCovGrad_diagonalProductGrid_le` + `mul_le`/`mono` + `rfns_iCG_wXi_atgw_rf`.
3. `b4_wOmega_atgw`: clone the tower's in-proof `hpt` (DeTurckVFJetRadiusFree:1151–1200) from
   the two exposures → `|∇ⁿwOmega|² ≤ KΩ n·atgw(n+2)`.
4. `lc0VBPass`-atgw via exposed `vbSplit` + rankLeft `(2,1,4)`: head = exposed `vbMcdArm_rfns_le`
   → item 2; tail = `rfns_icg_ipLow_le` (pointwise, radius-agnostic) → item 3.  Then `lc0VB`-atgw
   via exposed `lc0VB_eq_app` + `lc0RiemLive_rfns_le` → `rfns_iCG_cometricCastG0_atgw_rf`;
   the window lands at `atgw(i+3)`, matching the sorry's `range (i+3)` exactly.
5. Integrate per order (`antidiagonalTupleGrid_integral_radiusFree`, summed over `k < i+3`) →
   the `lc0VB` half; NARROW the sorry (VB half proved + new `lc0AMix_perOrder_rf` sorry, public
   statement unchanged).
6. `lc0AMix`: the 5-factor fibre identity (traceStep transports =
   `reindexCoeffGen(slotExtendᵏ(cometricCastG0))`, `k = 1,2,3`, the `lc0RiemLive` pattern; two
   `slotExtend`-chains over mcd with item 2 covering both) + nested grids + one integration.

Estimate: (1)–(5) ≈ 1 session; (6) ≈ 1 session.

## Honest progress (denominator: (N) `ricci_flow_unif_existence` = 0%, unstated)

Item-2 proper: bricks 1-3 DONE (gate + arm0 + deTurckLie, all axiom-clean).  Brick 4
(lieCorr0): statement + assembly + 3/4 arms done ≈ **~60% of brick 4**; the remaining 40% is
the vb/amix engine gap above.  After brick 4: the threeArm/Ψ₀ topSeparated assembly (Fork-A)
and the smooth-core tame lemma remain (item-2 proper); brick 4's sorry is on Ψ₀'s critical path
only through the lieCorr0 constituent.

## Verification (2026-07-26)

Targeted module build GREEN (9498 jobs; the three touched homes + the whole chain between them
and the leaf rebuilt clean; brick-3's leaf and both its publics replayed unaffected).  The ONLY
`sorry` in the leaf is `lc0VBAMix_perOrder_rf` (line 408).  In-file `#print axioms` (end of
leaf), literal results:

- `lieCorr0Field_perOrder_l2_radiusFree` : `[propext, sorryAx, Classical.choice, Quot.sound]`
- `lieCorr0Field_summed_l2_radiusFree`   : `[propext, sorryAx, Classical.choice, Quot.sound]`
- `lc0Base_perOrder_rf` : `[propext, Classical.choice, Quot.sound]`  (clean)
- `lc0Diff_perOrder_rf` : `[propext, Classical.choice, Quot.sound]`  (clean — hence the exposed
  `wAlphaB_L2_perOrder_rf` / `slotInsertEndoCc_sub` / `norm_iCG_cometricRaiseSlot0Field_eq` /
  `normSq_iCG_lc0InsertDiff_le` chain is sorry-free)
- `lc0Riem_perOrder_rf` : `[propext, Classical.choice, Quot.sound]`  (clean)
- `lc0VBAMix_perOrder_rf` : `[propext, sorryAx, Classical.choice, Quot.sound]`  (THE frontier)

Frozen-leaf audit (its own in-file prints, unchanged by the exposures): all prior atoms keep
their exact prior status — `endoArm_eq_dlb` … `lc0InsertDiff_realizedFam_perOrder_topSep` clean;
the pre-existing `vbPass_jetL2` sorry (`:943`) untouched.  The whole leaf compiled on the first
build pass (no proof repair was needed).
