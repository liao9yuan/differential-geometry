# DeTurckLieCoeffDiffRadiusFree — radius-free DeTurck-Lie coefficient jet-L² sibling

Third brick of the Pro-ruled repair of UNIF item-2. Consumer sibling of THE GATE
(`boundedFactorGridWindow_integral_radiusFree_topSeparated`) and its per-order workhorse
`antidiagonalTupleGrid_integral_radiusFree`. Arm0 exemplar (brick 2):
`Analysis/Spectral/Tensor/CovGrad/CurvatureCoeffDiffRadiusFree.lean`. See
`ShortTime/THREEARM_RECON.md` §11/§11c.

## Target (landed)

R-free sibling of `deTurckLieCoeffField_realizedFam_jetL2_summed_topSeparated`
(`DeTurckLieCoeffL2JetBound.lean:799`), single-tensor (g₁ tied to `T` via `htie`), RHS jets over
`symmS g₀ T`, top window `a+2` / low window `a+1` (brick-2 shape):
```
∑_{i≤a} ‖∇ⁱ(deTurckLieCoeffField g₀ g₁ g_bg)‖²
  ≤ Ktop·∑_{j≤a+2}‖∇ʲ(symmS g₀ T)‖² + Klow·(1 + ∑_{j≤a+1}‖∇ʲ(symmS g₀ T)‖²)
```
`Ktop/Klow` depend only on `g₀,g_bg,a,dim E,δ₀`; NO `R`, NO ball hyp. Hyps: `ha_super`
(`2·dim E+10 ≤ a`, genuinely needed by the DeTurck-VF supercritical machinery),
`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T) δ`, `δ ≤ δ₀`, `htie`.

## Status: COMPLETE — frontier DISCHARGED (2026-07-26, session 5)

- `deTurckLieCoeffField_perOrder_l2_radiusFree` — **PROVED, `sorry` deleted.**
- `deTurckLieCoeffField_summed_l2_radiusFree` — **the brick-3 target, now unconditional** (its summed
  reduction was already proved; it just consumes the now-sorry-free per-order engine).
- Targeted build GREEN (9480 jobs).  `#print axioms` on BOTH public theorems = **exactly**
  `[propext, Classical.choice, Quot.sound]` — ZERO `sorryAx`.

### How the frontier was discharged (session 5)

`deTurckLieCoeffField = DLa + DLb`; `‖∇ⁱfield‖² ≤ 2‖∇ⁱDLa‖² + 2‖∇ⁱDLb‖²` (re-derived in-leaf from the
public `deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField` + `iteratedCovGrad_add`).  Two per-order
R-free arm engines (private helpers `dLaField_perOrder_rf` / `dLbField_perOrder_rf` in this leaf):
- **DLa** — integrates the R-free pointwise `rfns_iCG_dLaField_topsep` (top `(appCcGdiag i)²·rfns(∇^{i+2}P)`
  + `dLaGridWin (i+3)` remainder) through the workhorse `antidiagonalTupleGrid_integral_radiusFree`
  (in place of the ball-uniform tame-window integrator).  `dLaGridWin b m = ∑_{k<m} grid k` — defeq to
  the leaf's `antidiagonalTupleGridWindow`, so the exposed engine feeds the workhorse directly.
- **DLb** — `‖∇ⁱDLb‖² ≤ 4·finrank·‖∇ⁱwEndoInsert‖²` (`normSq_iCG_dlbField_le`); the insert jet equals the
  `wAlpha` jet (`norm_iCG_wEndoInsert_eq_wAlpha`), top-separated by the session-4 `wAlpha_L2_topsep_rf`.

Single-tensor bridge: `P := symmS g₀ T`, with `htie`/`hδ` transported via the PUBLIC
`ccTensorBilinSymm_symmS_apply` / `gFibreOpBound_symmS` (namespace
`…PDE.RicciFlow.IntrinsicSpectral`, qualified at the call).  Range bookkeeping: the arm engines land at
window `i+3`; one `Finset.sum_range_succ` peels the top cell `‖∇^{i+2}P‖²` out of `∑_{j<i+3}` into `Atop`
(the frontier needs only `0 ≤ Atop`), giving the target shape `Atop·‖∇^{i+2}P‖² + Alow·(1+∑_{j<i+2})`.

### Exposures (minimal, `private` removed; both home files rebuilt GREEN)

- `rfns_iCG_dLaField_topsep`, `dLaGridWin`(+`_nonneg`) in `DeTurckLieKernelL2JetBound.lean` (the DLa
  pointwise engine is ~250 lines with a deep private dep chain — infeasible to re-derive in-leaf).
- `normSq_iCG_dlbField_le` in `DeTurckLieCoeffL2JetBound.lean` (its slotInsert/reindex deps are private).

New import edge: this leaf now imports `DeTurckVFJetRadiusFree` (for `wAlpha_L2_topsep_rf`) and
`SobolevNonlinearityExistence` (for the symmS bridges).

## The fork is CLOSED (no wall, no unreceivable term)

Pro's §11 ruling ("R^{7k} is a wrapper artifact") is confirmed by direct inspection. The frontier's
proof is a **mechanical** re-derivation of the private DeTurck-vector-field tower; NO term arises that
the gate's two windows cannot receive.

### Where R enters (exactly two integrators, both with the SAME integrand as the workhorse)

1. `diagonalProductGrid_rfns_integral_ballUniform_succ` (`DeTurckVectorFieldL2JetBound.lean:996`) —
   grid `∑_{n≤i}∑_{e∈antidiagonalTuple n i}∏_m rfns(∇^{e_m}P)`; output fixed `K i`, R-dependent via
   `Lam := Cemb·√(a+2)·R`, `Gfun k := k·(max Lam R (Cgn k) 1)^{7k}` (:1023,1037).
2. `antidiagonalTupleGrid_integral_ballUniform_tameWindow` (monolith `:8556`) — SAME integrand;
   output `K i·(1 + ∑_{j≤i}‖∇ʲP‖²)` (already low-window SHAPE) but R-dependent CONSTANT via the same
   `Lam := Cemb·R` / `^{7k}` (:8584,8598).

The workhorse `antidiagonalTupleGrid_integral_radiusFree` (monolith `:14455`) has the **byte-identical
integrand** (compare :14462-14473 to :1005-1016 and :8564-8577) and output `K i·(1+‖∇ⁱP‖²)` with
FIXED `Λ₀` (`Gfun k := k·(max Λ₀ (Cgn k) 1)^{7k}`), gated on `hsup : ∀x, rfns g₀ 0 2 x (P x) ≤ Λ₀²`.
⟹ **one workhorse replaces BOTH integrators.** The tameWindow's window `∑_{k<i+1} antidiagonalTupleGrid k`
becomes `∑_{k<i+1} K_rf k·(1+‖∇ᵏP‖²)` — a low window whose top cell (`k=i`) supplies the explicit
top jet; all sub-top cells land in `1 + ∑_{j<i}‖∇ʲP‖²`.

### Index bookkeeping (why the target shape comes out exactly)

At `wAlpha` order `i` (`wAlpha_L2_topsep:4233`): residual `C i = 2·Com(i+1) + 2·appCcGdiag i·(CT i·(ΛO 0·FCd i + ΛCd 0·FO i))`.
- `Com(i+1)` (from `wOmega_L2_topsep` at `i+1`): top `‖∇^{(i+1)+1}P‖² = ‖∇^{i+2}P‖²` → absorbs into `Atop`;
  residual → low (via tameWindow→workhorse).
- `FO i` (`wOmega_lowOrder` at `i`): `wOmega = appCc cometricCastG0 wXi`; `cometricCastG0` jet at `q`
  → `‖∇^q P‖²`, `wXi` jet at `q` → `‖∇^{q+1}P‖²` (wXi ≈ ∇P). ⟹ `FO i` → `1 + ∑_{j≤i+1}‖∇ʲP‖²`.
- `FCd i` (`connDiffSection_lowOrder` at `i`): `connDiffSection = appCcRS raisedKoszul sharpFlatEndoCc`;
  both jets stay ≤ order `i` ⟹ `1 + ∑_{j≤i+1}‖∇ʲP‖²`.

Net per-order `i`: `Atop i·‖∇^{i+2}P‖² + Alow i·(1+∑_{j≤i+1}‖∇ʲP‖²)` — EXACTLY the target (top `i+2`,
low `i+1`), with `P := symmS g₀ T`. No cross-contamination.

## The frontier's proof (brick 3b), bottom→top

The private tower (all in `DeTurckVectorFieldL2JetBound.lean` unless noted):

**Bottom producers** (each: swap its integrator/ball step, keep the low window explicit).
The pointwise decomposition helpers they need are ALL PUBLIC:
- `rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le`
  (`InverseMetricRaisedEndomorphismJetBound.lean:1316`)
- `rfns_iteratedCovGrad_slotInsertEndoCc_le_endo` (`MetricArmCoeffJetTower.lean:2863`)
- `cometricCastG0_eq_doubleTrace_add_appCcRS` (`RemainderCoeffPerOrderJetEnvelopes.lean:1519`)
- `appCc_iteratedCovGrad_diagonalProductGrid_le` (`OperatorFieldFibreNormJet.lean:918`)
- `rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le` (`MetricArmCoeffJetTower.lean:2360`)
- `connDiffSection_eq_appCcRS_raisedKoszul_sharpFlatEndoCc` (`ConnectionDifferenceJetTower.lean:451`)

| R-dep producer (private) | line | integrator | R-free plan |
|---|---|---|---|
| `raisedKoszul_order0sup_jetL2_succ_generic` | 1294 | none (pointwise) | mechanical: keep `‖∇^{n+1}P‖` (not `≤R`); `F i → (9/4)∑_{n≤i}‖∇^{n+1}P‖²` |
| `wXi_lowOrder_jetL2_succ_generic` | 2280 | via cometricCastG0 | compose R-free cometricCastG0 (+ `T`-free `g_bg` const) |
| `cometricCastG0_order0sup_jetL2_succ_generic` | 1388 | `ballUniform_succ` (:1410) | swap → `radiusFree`; `KW q → fr²·C_base q·K_rf q·(1+‖∇^q P‖²)`; `F i` → low window |
| `sharpFlatEndoCc_lowOrder_jetL2_succ_generic` | 1868 | `ballUniform_succ` (:1891) | swap → `radiusFree` |

**Residual generics** (compose bottom producers; already only sum/pointwise algebra R-free):
- `wOmega_lowOrder_jetL2_succ_generic` (2516) — uses cometricCastG0 (`FC`), `cometricCastG0_rfns_lowOrder_le`
  (`ΛClow`), wXi (`FX`); `F i` becomes a low window.
- `connDiffSection_lowOrder_jetL2_succ_generic` (1999) — uses raisedKoszul (`FK`), `raisedKoszul_rfns_lowOrder_le`,
  sharpFlatEndoCc (`FS`); FULLY over public objects.

**Top-separated generics** (swap tameWindow→workhorse; top jet already isolated R-free):
- `connDiff_L2_topsep` (3765), `wXi_L2_topsep` (3890), `wOmega_L2_topsep` (3936).

**Assembly:**
- `wAlpha_L2_topsep` (4233) → R-free `wAlpha_..._radiusFree`: `Ktop·‖∇^{i+2}P‖² + Klow i·(1+∑_{j≤i+1}‖∇ʲP‖²)`.
- lift via `norm_iCG_wEndoInsert_eq_wAlpha` (2960, private) → `deTurckLieWEndoInsert` per-order R-free.
- `deTurckLieDL{a,b}CoeffField` per-order (`DeTurckLieCoeffL2JetBound.lean`) → combine via
  `normSq_iCG_deTurckLieCoeff_le` (:714, private; re-derivable from public
  `deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField` + `iteratedCovGrad_add`) → the frontier.

### Home decision for brick 3b

The tower needs the PRIVATE defs `wAlpha`/`wOmega`/`wXi`/`wCA` ⟹ the R-free tower must live IN the VF
file (or those defs get exposed). `DeTurckVectorFieldL2JetBound.lean` is already 4596 lines (>3000-line
limit): per CLAUDE.md, SPLIT before adding. Recommended: expose `wAlpha`/`wOmega`/`wXi`/`wCA` +
`norm_iCG_wEndoInsert_eq_wAlpha` as thin public wrappers, build the R-free tower in a new leaf that
imports the VF file (this leaf then imports THAT). Bottom producers over PUBLIC objects (cometricCastG0,
raisedKoszul, sharpFlatEndoCc) can live in that leaf too. Est. ~1200-1500 lines, ~3-5 sessions.

## Brick 4 (lieCorr0) — mechanizable from this pattern?

YES, with the same three ingredients. `lieCorr0` (`LieCorr0CoeffL2JetBound.lean`) is another
DeTurck-Lie-flavoured (2,2) coefficient; its R-dependent summed bound routes through the SAME two
integrators (`ballUniform_succ`, `tameWindow`) via the SAME g₁⁻¹/connDiff machinery. Once brick 3b's
R-free tower + the exposed wrappers exist, brick 4's leaf is a mechanical clone: same
`_perOrder_l2_radiusFree` engine shape (sorry→proved via the shared R-free tower) + the same summed
reduction (verbatim from here). No new integrator, no new frontier expected.

## Honest progress (denominator: (N) `ricci_flow_unif_existence` = 0%, unstated)

- Item-2 proper (the main math risk of a 15-25-session (N) discharge): bricks 1-2 (gate + arm0)
  green; **brick 3 (DeTurckLie) is now DONE — theorem PROVED, axiom-clean, no `sorry`.**  The full
  brick-3b R-free DeTurck-VF tower (sessions 1-4, `DeTurckVFJetRadiusFree.lean`) + this leaf's DLa/DLb
  arm engines + the exposed pointwise engines discharge it end-to-end.
- Remaining item-2 after brick 3: brick 4 (lieCorr0's sibling — mechanical clone of this pattern, ~1-2
  sessions, pending the coordinator's re-assessment of the lieCorr0 freeze), the threeArm/Ψ₀
  topSeparated assembly (Fork-A, ~3-5 sessions), and the smooth-core tame lemma (layers 2-3, ~4-8
  sessions).  Brick 3 no longer on the critical path.

## Lessons

- The two "ballUniform" integrators are NOT a wall: both share the workhorse's integrand; only their
  CONSTANT is R-poisoned (`Cemb·R` before the `^{7k}` grid). The workhorse's fixed-`Λ₀` + `hsup` is
  the drop-in. Confirmed by byte-comparing the three integrands.
- The single-tensor target (RHS over `symmS g₀ T`, `htie`) is SIMPLER than the R-dependent `realizedFam`
  original — no convexPerturbation/two-tensor plumbing; the generic-`g₁` producers (`wAlpha_L2_topsep`
  etc. take `g₁`+`htie`) already support it. The `realizedFam` specialization only happens at/above
  `deTurckLieWEndoInsert_realizedFam_*` (:4384).
- Summed proof is a verbatim clone of brick 2's — the two deliverables share the identical
  summed→per-order envelope algebra. Reuse, don't re-derive.
