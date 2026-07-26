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

Discharging `lc0VBAMix_perOrder_rf` = building the two missing atoms' engines (the frozen
note's resumption plan): (a) the `interior_product`-with-vector jet lemma + deTurckVF↔`wOmega`
lowering, then `vbPass_jetL2`, then an R-free re-derivation of the `lc0VB` two-arm assembly
against R-free arm producers (`metricConnDiffLoweredCc` producer is committed but BALL-UNIFORM —
an R-free sibling via the workhorse is also needed); (b) the `lc0AMix` fibre identity + the same
producer.  Estimate ~2-4 sessions; classified as missing-groundwork/API (a genuine engine gap,
not a route-choice or elaboration issue).  No wall expected: both pieces are products of two
connDiff-family arms — the same currency the workhorse already integrates.

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
