# ROUTE_C_PLAN.md — route (c): direct smoothing for `bg_packet_of_solve`

Created 2026-08-07 by the planner from the (c-A) scope-scout dossier.
Authority: user ruling `UNIF_EXISTENCE_PLAN7.md` №227 (route (c) adopted;
№220/№222 packet + lift ports superseded).  Ledger context: №225 ((c)
feasibility), №226 (gate-constant probe), №227 (ruling), №228 (this plan).
This file is the lane's running source of truth: update the brick STATUS
column and the status log as bricks land; do not restart settled bricks.

## Goal

Discharge the ONE sorry on (N)'s axiom chain:
`bg_packet_of_solve` (`LowRegBgBootstrap.lean:215`, sorry :225):
given `hK : IsLowBoundsAt g g_bg K` and
`hsol : IsLowSolveBg g g_bg K hK hT hT1 u gforce` on `T ≤ 1`, produce
`Nonempty (BgSmoothPacket g g_bg K T)` — the order-two closed-slab packet
on the SAME horizon.

Route (amended by the Pro overall ruling, ledger №235 — C1 + reorder):
the frontier is RESTATED as `bg_packet_of_adapt`
(`ha : IsAdaptedLowBg g g_bg K hK hT hT1 u gforce` →
`Nonempty (BgSmoothPacket g g_bg K T)`), replacing
`bg_packet_of_solve` (unprovable as posed: the absorption inequality
is not derivable from arbitrary `IsLowBoundsAt K`; adaptation is
solve-PRE calibration, not a free post-certificate).  Phases, in
EXECUTION ORDER:
- **(c-C0)** fixed-metric feasibility gate: the DIAGONAL
  `bg_packet_of_adapt` prototype on the proved diagonal ladder —
  from `IsAdaptedLowSolve` alone (no `IsRealizedTwo`), build the
  packet fields (H² forcing rep, order-2 carrier, `mode_smooth`,
  `mode_mass`, `mode_eq`, bounds).  Zero widening; tests the
  route-specific risk FIRST.  Its consumption map DEFINES minimal
  (c-A).
- **(c-A)** minimal widening of the adapted-solve/rung/gate/mass
  chain `(g,g)` → `(g,g_bg)` (per-`g` statements only — NOT uniform);
- **(c-B)** the ABSORPTIVE gate only: split `IsLowGateOrd` into
  absorptive small coefficients vs metricwise high-rung bookkeeping;
  class-uniformize ONLY Ā/B̄/δ/state-cap and PROVE they read ≤3 jets
  of the varying `g` (STOP condition below); build
  `lowreg_adapt_unif` (class-first: uniform gate bounds + literal
  common `K` before `g`).
- **(c-C)** final assembly: `bgreg_allOrderJet` → `bg_packet_of_adapt`,
  and RETHREAD `lowreg_dt_unif`'s PROOF BODY (uniform solve →
  uniform adapted solve; its THEOREM STATEMENT and (N)'s statement
  stay unchanged — "untouched" claims in earlier entries were
  interface-level only).
The lift layer (`IsBgLiftAt`, `bgLift_of_radial`,
LowRegBgLift/A1Refold/C2Small/A2Time, G3 `_unif` nodes) stays in
place UNUSED until (c-C) lands (rollback point); do not delete or
edit it in this lane.

## Slot semantics (scout-verified ground truth)

Universal convention at every definition site: **slot 1 = state/spectral
metric** (Sobolev scale, eigenbasis, state ball, fibre bounds,
realization); **slot 2 = DeTurck background/coefficient metric**, entering
only through `deTurckRicciRHS g_bg` / `deTurckSmoothRemainder`.  Widening
= free slot 2; every space stays on `g₀`.  No definitional identity forces
the slots equal — the diagonal is pinned only in THEOREM statements.
Substrate already two-metric (class A, no work): `deTurckSmoothRemainder`,
`deTurckSmoothN`, `coreN`, `lowRegN`, `lowregNfun`, `coreN_tame`,
`lowRegSeedMass`, `nZero_eq_static`, `lowregGalSol`, `lowBaseData`,
`lowData_split`, `topKernel_eq`, `c0_eq/c1_eq/c2_eq`, `rhsRefoldTop(_joint)`,
`rhsLow1PathIntegral`, `moserWin_phiDev`, `phiMet_cap`, `lowregGateAbsorb`,
`IsAllRungPath`, `lowregMassOfEnergy`, and the whole
`LowRegBoundData`/`IsLowBoundsAt`/`IsLowSolveBg`/`lowreg_sol_of_data`
input layer.  Scout verdict: **zero verified class-C (genuine
diagonal-use) items; zero monolith edits needed** (all monolith producers
public and two-metric).

## Phase (c-A): the widening bricks (≈13–17 sessions)

One executor at a time (heavy DT checks import the 13.8k monolith).
| # | brick | files | class | est | STATUS |
|---|---|---|---|---|---|
| 1 | `IsBgSolveAt` bundle: fields = (`bounds : IsLowBoundsAt`, `solve : IsLowSolveBg`, `hTτ`, `hcap`); projection lemmas named/shaped like `IsLowSolveAt`'s fields (slot 2 freed) so rung mirrors port near-verbatim.  NOT a 17-field re-statement. | NEW `ST/LowRegBgSolveAt.lean` (231) | B | 0.5–1 | **DONE** (№231: green, warning-free, axiom-clean; 15 projections; zero statement-level deltas) |
| 2a | DT tower spine, in-place widen: `topKerJetSharp`, `c2JetTowerSharp/Q`, `c2_jet_tower` (proof edits = re-instantiations `moserWin_phiDev g g_bg`, `topKernel_eq g g_bg`, `rhsRefoldTop_joint g g_bg`, `lowData_split g g_bg`); fix 2–6 diagonal call sites per lemma (extra `g` argument). | `DT/LowRegC2JetTower.lean` (387), `DT/LowRegLadderRung.lean` (957, C2 part) | B | 1 | **DONE** (№233: green, axiom-clean, zero class-C; 3 diagonal call sites fixed: `topKer_jet` :370, `a2LadderQ` :371, `c2SupJet` A2PerIndex:206) |
| 2b-i | Window-layer C-point repairs (№232): free-bg A1 window, sharp AMix background difference, and combined Lie residual. | `Analysis/Sobolev/TensorHilbert/Low1KerRadiusFree.lean`, `…/TensorHilbert/TameLieCorrJets.lean`, `DT/LowRegC01JetTower.lean` | **C-repair** | 1–2 | **DONE** (№240: `bgCcAtgw`/`low1AtgwBg`, `mcdBgAtgw`/`amixBgAtgw`/`lc0AMixJetBg`, and `lieBgJet` green) |
| 2b-ii | Exact C0 split, sharp insertion difference, and arbitrary-background C0/C1 quadratic towers with diagonal wrappers. | `…/TensorHilbert/Lc0InsertDiffWindow.lean`, `DT/LowRegC01JetTower.lean` | **C-repair**+B | 1–2 | **DONE** (№240: `lc0InsDiffAtgw`, `insBgJet`, `selfLowJetQBg`, `c0JetTowerQBg`, `c1JetTowerQBg`; focused checks and targeted refreshes green) |
| 2c | A2 per-index: `c2SupJet`, `a2PerIdxJet/Lin`. | `DT/LowRegA2PerIndex.lean` (499) | B | 1 | **DONE** (№234: green, axiom-clean, zero class-C; consumers fixed diagonally: `armLadder3` RungThree:311, `armOrder3` RungFour:88, `armOrder4` RungFive:85) |
| 2d | A1 per-index: `a1Arm0/1`, `a1PerIdxJet/Lin` (engines cleared B by №232 probe). | `DT/LowRegA1PerIndex.lean` (1049) | B | 1–2 | **DONE** (№241: `a1PerIdxJetBg`/`a1PerIdxLinBg` focused-green, axiom-clean, targeted refresh green) |
| 2e | Ladder assembly: `a2/a1_ladder`, `a2/a1LadderQ`, `nDiffHmQ`, widen `IsHmRungOrd` (:935 `deTurckSmoothRemainder g g`) + `lowregHmPack`. | `DT/LowRegLadderRung.lean` | B | 1 | **DONE** (№241: six Bg declarations focused-green and axiom-clean; targeted refresh green) |
| 3 | Rung-3 Bg siblings: `galN_evalBg`, `galArmIdBg`, `armLadder3Bg`, `galArmVecBg` (№232: the diagonal `galArmVec` DEF bakes `lowBaseData g₀ g₀` in its body — bg-slotted analog def needed), `galArmMassOrdBg`, `galForceArmBg` (ForceArms:368 restatement); then `lowregRung3OrdBg`/`IsRung3OrdBg`/pack (Grönwall closure verbatim; `lowRegSeedMass g g_bg` is A). Diagonal `LowRegRungThree.lean` stays byte-stable. | NEW `ST/LowRegBgRung3*.lean` | B | 2–3 | **DONE**: all five rung-three declarations and `galArmVecBg` are focused-green; both direct modules refreshed; ordered `Kcap` is selected by `lowData_split g₀ g_bg` before `δ` |
| 4 | Rung-4/5 Bg: mechanical mirrors of brick-3 template. | NEW `ST/LowRegBgRungFour.lean`, `ST/LowRegBgRungFive.lean` | B | 2 | **DONE**: both five-declaration siblings are focused-green and targeted-refreshed; their `.olean`s are fresh and the diagonal files remain unchanged by the ports |
| 5 | Gate pack Bg: `IsLowGateOrdBg` + `lowregGatePackBg`. | NEW `ST/LowRegBgRungPack.lean` | B | 0.5 | **DONE**: metricwise Bg gate package focused-green and targeted-refreshed; reuses unchanged `rungGate_le`; makes no class-first uniformity claim |
| 6 | `IsAdaptedLowSolveBg` (= brick-1 bundle ∧ `IsRung3OrdBg` ∧ gateBg + absorption budget) + producer from a GIVEN solve.  **DESIGN FLAG** below. | NEW `ST/LowRegBgAdapt.lean` | B | 1 | **DONE (metricwise)**: package, projections, absorption lemma, and given-solve producer are focused-green/refreshed; the distinct class-first absorptive producer remains 0% |
| 7 | HigherRung Bg: `lowregRung5PathAtBg`, `lowregHighRungsBg` (+ `galArmMassHmBg` HigherRung:40), `lowregAllRungsAtBg`, `lowregAllMassAtBg` (reuse `IsAllRungPath`, `lowregMassOfEnergy` unchanged; №232 cleared the bodies B).  Also restate: `IsRung5Path` (RungClosure:42, pins `lowregNfun g₀ g₀` :65), `lowregFatouE3At` (FatouIdent:385), `lowreg_projMode_at` (GalerkinIdent:308). | NEW | B | 2 | **DONE (conditional/metricwise)**: Galerkin, Fatou/path closure, higher rungs, `lowregAllRungsAtBg`, `lowregAllMassAtBg`, and `lowreg_loMassBg` are focused-green and refreshed; this does not produce the adapted certificate class-first |
| 8 | Direct endpoint seam: `direct_jet_of_mass` consumes primitive two-metric solve data plus the exact `lowreg_loMassBg` output; `bg_packet_of_mass` packages it as `BgSmoothPacket`, and `bg_packet_of_adapt` supplies that mass from an adapted solve. | `ST/LowRegDirectJet.lean`, `ST/LowRegBgBootstrap.lean` | B | 1–2 | **DONE (metricwise)**: direct core, every-exponent background mass, and adapted-to-packet consumer are focused-green and refreshed; class-first adapted-solve production/rethreading remains outside this seam |

Consumption anchor (proved Brick 0): `direct_jet_of_mass` consumes primitive
two-metric solve data plus one `hspatial` hypothesis in exactly the shape of
`lowreg_loMassBg`.  `bg_packet_of_mass` supplies every `BgSmoothPacket` field
from that result, and `bg_packet_of_adapt` now closes this metricwise endpoint
chain.  The remaining lane is the class-first production of an adapted solve
and rethreading the uniform consumer through it; no completed A1/A2 lift maps
or high-scale realization certificate are endpoint inputs.

## Phase (c-B): energy-pairing-first Rung 3 (current binding redesign)

The former closed-slab all-rung `IsLowGateOrdBg` uniformization is superseded.
Its stop audit remains valid as a refutation of that architecture, but it is not
a stop condition for the new route.  Keep the class-first low fixed point,
background Galerkin identification, Rung-3 Fatou framework, metricwise direct
smoothing, gauge removal, and the checked adapted-to-mass-to-packet consumers.
Do not resume G3/adjacent-scale lifting or put Rungs 4/5 into the class-first
gate.

The binding producer chain is now:

1. **Full Lie background correction — DONE.**  `lieBgCorr_unif` in
   `LowRegBgC1Pair.lean` is proved and focused-check green.  It controls all
   three exact `lieBgCorr_eq` pieces on every preselected intrinsic `H2` radius;
   its function bound is selected before `g` and reads varying-metric jets only
   through order three.  It has no metricwise small radius, `H3` cap, or
   fourth-jet coefficient.
2. **Actual C1 path correction — DONE.**  `lowC1CorrBg` is the low-base
   coefficient difference
   `lowC1CorrBg := (lowBaseData g gBase ...).C1 -
   (lowBaseData g g ...).C1`.  `lowC1Corr_unif` proves its `H2` bound by the
   existing radial
   path integral (`LowBaseInternal.c1_eq`, `rhsLow1PathIntegral`,
   `exists_convex_jets`, `path_jetL2_le`, and
   `convexPerturbation_gFibreOpBound_abs`).  The path integrand is the full
   background-self `rhsLow1Coeff` difference; its Ricci arm cancels and the
   remaining Lie arm is discharged by `lieBgCorr_unif`.  The producer is
   focused-check green with its function bound selected before `g`.
3. **Complete Galerkin correction — DONE.**  In the new ShortTime module
   `LowRegA1FixedPairBg.lean`, `galA1FixVecBg` and `galA1FixPairBg` are complete
   public definitions; both carry the realization hypothesis `hreal` required
   by `galRepFib`/`lowregFibZero`.
4. **Direct Rung-3 pairing — DONE.**  `galA1FixPair3_le` is proved and
   focused-check green with the class-first order
   `eta -> g -> G`.  Pair using `appCc_h2_h3_h2`, `galRepHs_le g 3`,
   `cc_partial_le_norm`, and `two_abs_cross_le_eps`, obtaining
   `eta * E4 + G * E3`.  Preserve the mandated scalar order by quantifying the
   actual state radius after `G` together with `0 <= R` and `R <= 1`; apply
   `lowC1Corr_unif` at radius `1`.  The solver supplies this cap through
   `lowregStateRad_le_cap`, so `G` depends on `g` but not on the inner `R`.
   An uncapped arbitrary-radius variant would instead have to return `G R`.
5. **Signed C1 consumer split — DONE.**  `galA1RestVecBg` retains the
   fixed-background `C2/C0` action but uses the self-background `C1` action;
   `galArmVecBg_split` and `galArmPair3_split` isolate exactly the complete C1
   correction.
6. **Rest-only Rung-3 bound — CONTINUE-WITH-CORRECTIONS at the sharp post-peel
   estimates.**  The arbitrary-passenger frozen adapter
   is permanently rejected.  The source orientation is

   ```text
   ricciTop(..., U) applied to nabla^2 P
   curvatureKernel(U) applied to nabla^2 P,
   ```

   where `P` is the path/coefficient state.  The proposed frozen operator used
   the opposite orientation `ricciTop(..., P) (nabla^2 U)` and
   `curvatureKernel(P) (nabla^2 U)`.  These agree on the diagonal `P = U`, but
   are not equal for arbitrary independent jets.  Existing `edgeRiem_cancel`
   already accepts an arbitrary acted field **provided** the correctly
   oriented `hrefold` is supplied; the diagonal Palatini producer cannot
   supply the proposed reversed `hrefold`.  Therefore no duplicate
   `edgeRiem_cancel_bi` wrapper and no false `rhsSelf_refold_bi` theorem is to
   be added.

   The corrected route now keeps state=acted=`T` throughout.  It has the
   following focused-green exact and analytic producers:

   - `lowBase_path_nf` rewrites the actual `AB.a2 T + AB.a1 T` as the complete
     diagonal path action with order-zero, order-one, and top-deviation
     coefficients.  It uses `lowData_split`, `rhsArm_sub_eq_paths`, and
     `edgeTop_split`; it asserts no off-diagonal operator identity.
   - `appD2_pair_h2` and `appD2_pair_h4` prove the finite rank-two principal
     form estimate directly, without converting an `H4` tensor into a uniform
     covariant four-jet.
   - `top_pair_h2_unif`, `top_pair_h4_unif`, and `top_pair_abs_unif` specialize
     this estimate to the path-top deviation.  The last theorem selects the
     `H2` cap before `g` and absorbs
     `2 * |<L^2 T, Phi(T) nabla^2(LT)>|` into `eta * H4^2` using only the `C3`
     metric class.
   - `exists_edgeLieJoint`, public `edgeLiePair_joint`, and
     `threeArmJoint_const`/`threeArmJoint_comp` retain the joint-smooth exact
     data needed by a subsequent directed-Green expansion.
   - `low0_path_refold`, `b02_raw_nf`, and `b02_center_nf` perform the honest
     diagonal raw refold and center the complete order-zero/top block.  The
     off-diagonal raw-pair values enter only by algebra; no false
     arbitrary-passenger low-base identity is asserted.
   - `edgeTopPairInt`, `edgeTopPartnerInt`, and `edgePath_inner_bi` provide the
     path-integrated formal-partner layer.  `edge_swap_h4_unif` and
     `edge_diag_h4_unif` give class-first cross-sum and diagonal estimates with
     only the `C3` metric class and the `H2` state cap.
   - `edgeLow0_split` and `edge_center_s_nf` give the focused-green fixed-path
     centered normal form

     ```text
     J_s = L(E0_s T) + (L(D_s T) - D_s(LT))
             - (K_s-K_0)(LT) - Cross_s.
     ```

     After composition with `b02_center_nf`, the explicit Cross sum cancels
     exactly; it must not be estimated a second time.

   The principal-symbol calculation is positive: the canonical raw top pair
   reduces to six surviving monomials, and its two literal fourth-order
   orientations are exactly those carried by `Cross_s`.  Covariantly, however,
   the exact argument-corner theorem stops at `Delta(nabla^2 T)`.  Replacing
   that by `nabla^2(Delta T)` produces

   ```text
   edgeTopPairG_s (
     nabla(pointwiseTensorCurv g 2 T)
       + pointwiseTensorCurv g 3 (nabla T)),
   ```

   whose first summand contains `(nabla^2 Rm(g)) * T`: the first-order
   curvature commutator already contains `(nabla Rm) * T`, so the outer
   derivative cannot be dropped from the ledger.  A complete normal-frame
   symbol check shows that the resulting transparent `q/Phi/ricciTop` block
   is generally nonzero.  Cancellation to zero is therefore neither available
   nor required.

   The representation/orientation audit is now closed rather than assumed:
   focused-green `appCcPsi_diag` and `cometricTrace_appCcRS` expose the mixed
   Leibniz/trace corner, while focused-green `edgeTopPairG`, `edge_arg2_nf`,
   `phiMet_fold_comm`, and `edgeTopG_apply` show exactly what survives.  With
   the canonical arrays, `edgeTopG_apply` turns the q block into
   `rhsRefold2` acting on an arbitrary rank-four argument while keeping the
   passenger equal to `T`.  Combining the coefficient definitions leaves

   ```text
   (lieRefold2 + (Phi_s - Phi_0) - 2s * ricciTop)
     (nabla(pointwiseTensorCurv g 2 T)
       + pointwiseTensorCurv g 3 (nabla T)).
   ```

   The prior STOP inference confused two different quantifier requirements.
   The caps `delta2,R2` are chosen before `g`, but the lower Gårding constant
   is chosen afterward:

   ```text
   eta -> exists delta2,R2 -> forall g in C3 -> exists G_g.
   ```

   Consequently a fourth jet of the fixed smooth `g` may enter `G_g` provided
   it multiplies a genuinely lower state term.  Only the dangerous
   `(nabla^2 Rm(g)) * T` cell is zeroth order in state derivatives; the full
   curvature defect is linear in `T` and uses state jets through order two.
   The complete coefficient vanishes at `T = 0`; paired with `L^2 T` the block
   has size `C_g * H2(T)^2 * H4(T)` (or,
   under a coarser bound, at worst `C_g * H2(T) * H4(T)`), not
   `C_g * H4(T)^2`.  Young's inequality sends it to
   `eps * H4^2 + G_g * H3^2` using `H2 <= 1` and `H2 <= H3`, without making
   either cap depend on `g`.

   The principal-head-isolating non-Green peel `edge_center_peel` is now
   focused-verified and directly refreshed; the false zero theorem
   `edge_qk_comm` remains rejected.  The verified peel exposes the centered
   block as the sum of:

   ```text
   L(A_s T)
     + (B_s-C_s) nabla^2(LT)
     - B_s G_T
     - P20_s - P11L_s - P11R_s
     - Cross_s,
   ```

   where `A_s = rhsSelfLow_s + K_0`,
   `B_s = lieRefold2_s + C_s - 2s * ricciTop_s`,
   `G_T = nabla(pointwiseTensorCurv g 2 T)
     + pointwiseTensorCurv g 3 (nabla T)`, and the three `P` terms are the
   explicit `2+0` and `1+1` Leibniz corners, not an opaque remainder.  Its
   supporting public diagonal projection `LowBaseInternal.self_refold` is also
   focused-verified and exactly refreshed.  An arbitrary-passenger version
   remains forbidden.

   The class-first top-kernel fibre bound and the principal-face pairing are
   now focused-verified and directly refreshed.  The nonzero `B_s G_T`
   curvature-defect pairing is also focused-verified and directly refreshed.
   The next substantive inequalities are the sharp paired bounds for `P20`,
   `P11L/P11R`, and `L(A_s T)`.
   Their class-uniform `H4^2` heads
   must have shapes `C(R+R^2) H4^2` and `C R H4^2`; fixed-metric derivative
   corners may additionally contribute only lower terms such as
   `C_g(H3*H4 + r^2*H4)`, where `r = H2(T)` is the actual homogeneous state
   norm, not merely its radius cap `R`.  The curvature-defect term has the
   latter shape.  `Cross_s` is retained in the peel only to align the exact
   identities: it
   cancels against the Cross added by `b02_center_nf` and is not charged a
   second time in the final bound.  The already verified Cross estimate remains
   a valid independent fallback, not a required loss in the final assembly.
   The route must STOP only if the peel leaves a naked or
   metricwise `C_g * H4^2` coefficient, an uncapped fourth state derivative,
   a cap that must be chosen after `g`, or a derivative of the test requiring
   `H5`.

   Consequently the homogeneous diagonal residual estimate

   ```text
   2 * (
     <L^2 T, L (AB.a2 T + AB.a1 T)>
       - <L^2 T, Phi(T) nabla^2 (L T)>)
     <= eps * H4^2 + G(g,eps) * H3^2.
   ```

   remains unavailable, but its stop condition has not fired merely because
   `nabla^2 Rm(g)` occurs in a lower coefficient.  `lowbase_full3_unif` itself is
   still unstated and remains 0%; its
   required eventual statement remains:

   ```text
   eta > 0
     -> exists delta2 R2,
        0 < delta2 < 1/3 and 0 < R2 <= 1,
        forall g in the C3 class, exists G >= 0,
        forall 0 <= delta <= delta2, 0 <= R <= R2, ...,
          2 * fullSlopePair3 g gBase ...
            <= eta * H4^2 + G * H3^2.
   ```

   The later raw/rest consumer adds the static seed and routine lower pieces,
   and only there weakens the lower term to
   `G * (1 + E3)^2` in the bound for `galA1RestPairBg`.  Thus the
   cap/constant order is
   `eta -> exists delta2, R2 -> g -> exists G`; both small caps are selected
   uniformly before the varying metric, while the lower-energy Gårding
   constant may depend on `g`.  This is distinct from the completed C1 theorem
   `galA1FixPair3_le`, whose correct order remains `eta -> g -> G` and whose
   solver radius is capped afterward by `R <= 1`.

   The spectral/Galerkin transport is also closed at the exact level.
   `finite_pair_split` gives the Rung-3 split and `finite_symm_scale` carries
   the radial scalar.  `galArmPair3_diag` states the resulting
   `theta * rawPair = diagonalPair` identity, while `galRepHs_scale` retains
   the exact `theta` factor in every Sobolev norm.  No inverse of `theta` is
   introduced, but the eventual inequality proof must still split
   `theta = 0` from `0 < theta`: the zero branch proves the acted arm is zero;
   the positive branch cancels the common factor with
   `mul_le_mul_left`.  The polarized monomial APIs `edgePair_l2_bi`,
   `edgePair_inner_bi`, and `edgePair_green_bi` remain valid lower-level tools,
   but they do not identify the whole low-base kernel with `edgeTopPair`.

   The exact diagonal theorem now lives in the Analysis-layer
   `LowBaseFullSlopePairing.lean`; the eventual class-first cap theorem still
   belongs in `LowRegBgC2Pair.lean`, and the final rest consumer may live in
   `LowRegA1RestPairBg.lean`.  Rungs 4+ remain deferred until after solution
   construction, where metricwise interior/corner smoothing may use metricwise
   high-rung constants.

The arbitrary-acted-field stop condition has now fired: the proposed
pointwise frozen C0+C2 refold reverses the actual derivative orientation and is
false off the diagonal.  This is a wrong-statement/design obstruction, not a
verification failure.  The old three-route audit still rules out (1) a direct
high-state-jet `C2` action bound, (2) the derivative-short raw weight-three
duality route, and (3) treating the closed-edge `edgeTopPair` as the complete
low-base C2 kernel.  A corrected diagonal form-level route has now been adopted
and its exact path normal form and principal absorption are proved.  The
completed `lieBgCorr_unif`,
`lowC1Corr_unif`, `galA1FixPair3_le`, signed C1 split, complementary spectral
split, `finite_symm_scale`, diagonal Galerkin pairing, radial scale bound,
principal form absorption, polarized raw-pair estimates, and the exact
fixed-path centered normal form are
theorem-level 100%; the
unstated rest-only theorem is 0%; the dedicated fixed-background
direct-smoothing machinery is approximately 96%; the remaining denominator is
the post-peel corner and carrier estimates
and the ensuing diagonal residual Gårding estimate;
`ricci_flow_unif_existence` remains 0%; whole HCG remains approximately 3%.

## Phase (c-C0) result + (c-C): synthesis and endpoint

(c-C0) — **DONE**.  The implemented feasibility gate is
`lowreg_directJet` in the new `ST/LowRegDirectJet.lean`.  It starts
from the existing diagonal `IsAdaptedLowSolve` and directly produces
the complete order-two forcing/carrier data needed by the smoothing
endpoint.  The actual checked chain is:

1. `lowreg_loMass` feeds a direct order-one forcing driver based on
   `lowReg_force_smooth`;
2. the driver produces a single smooth coordinate family with all
   time-jet/spatial masses;
3. spectral synthesis promotes that family to an order-two
   time-`L²` forcing;
4. `duhamel_mode_pin` identifies the promoted carrier with the
   order-one `duhamelCross` representative;
5. `direct_state_bound`, `direct_force_coeff`, and `direct_radius`
   provide the closed-slab state cap, the exact smooth forcing
   identity, and the realization radius.

This route does **not** consume a calibration tuple, completed A1/A2
maps, `IsRealizedTwo`, `liftForceHi`, `liftHiN`, or
`lowregLiftHorizon'`.  The earlier №236 `liftHiN` prototype was a
false detour and is superseded.  `carrier_coeff_pmConv` was promoted
from private to public without changing its statement or proof.
Focused verification is green and the axiom audit is exactly
`[propext, Classical.choice, Quot.sound]`.

The consumption map now fixes (c-A): parameterize only the diagonal
adapted-solve/low-mass/rung path actually read by `lowreg_directJet`.
Do not resume the adjacent-scale A1/A2 completion lane.

(c-C): the `(g, g_bg)` assembly `bgreg_allOrderJet` →
`bg_packet_of_adapt`, then rethread `lowreg_dt_unif`'s proof body
through `lowreg_adapt_unif` (statement unchanged).
The next serial task is the smallest background-aware adapted-solve
producer exposed by this checked consumption map.

## Design flags

1. **RESOLVED → C1 (№235, Pro ruling)**: the frontier is
   `bg_packet_of_adapt` over `IsAdaptedLowBg`; the calibration lives in
   the class-first `lowreg_adapt_unif` (uniform gate bounds + literal
   common `K` before `g`); `lowreg_dt_unif`'s proof body rethreads,
   statement unchanged.  Brick 6 builds `IsAdaptedLowBg` to exactly
   this consumption shape.
2. **RESOLVED → the №235 layering + STOP condition** (supersedes the
   №226 "widen (N) if it bites" remedy): only the absorptive slice is
   uniformized, with a mandatory ≤3-jet audit; if the audit fires,
   HALT and escalate — (N)-hypothesis changes are theorem-level user
   rulings.
3. **B? bodies — RESOLVED (№232 probe)**: four of five clean B
   (A1PerIndex engines; RungClosure:79; HigherRung:110; AllOrderJet
   :761/:1099 — force abstract, no `lowregNsec`/`coreN`/`lowregNfun`
   touched).  The fifth (C01 towers) held the one genuine C cluster —
   now scoped as bricks 2b-i/2b-ii with identified repairs (the
   `sub_self` insertion-difference at C01JetTower:211; the Ψ-collapse
   windows `lieA1Atgw`/`low1Atgw`; the C0 caps).  (c-A) total re-priced
   ≈14–19 sessions; order 2a → 2c → 2b-i → 2b-ii → 2d → 2e.

## Verification discipline

`./scripts/lake-locked.ps1 claim/check/release`; focused checks
`-NoLakeLock -LeanThreads 4 -LeanMemoryMB 6144`; ONE Lean process at a
time (DT checks import the 13.8k monolith — slow, plan sessions
accordingly); no `set_option`/`maxHeartbeats` (split declarations); names
≤ 20 letters; files ≤ 3000 lines; no monolith edits; no git commits; new
Bg siblings in NEW `ST/LowRegBg*` files, diagonal lane byte-stable except
the in-place DT widenings of bricks 2a–2e.

## Status log

- 2026-08-07 (№228): plan created from the scope-scout dossier; brick 1
  dispatched.
- 2026-08-07 (№231): brick 1 DONE and accepted — `IsBgSolveAt` +
  15 diagonal-shaped projections (`ST/LowRegBgSolveAt.lean`, 231 lines),
  green/warning-free/axiom-clean; constructible from `lowreg_sol_of_data`
  via `⟨hK, hsol, hTτ, hcap⟩`; zero statement-level field deltas (details
  in `LowRegBgSolveAt.md`).  Brick 2a dispatched.  B?-bodies probe
  (design flag 3) still in flight.
- 2026-08-07 (№232): B?-probe adopted — 4/5 bodies clean B; the C01
  towers hold the ONE genuine class-C cluster (three points, repairs
  identified, shelf originals exist); brick 2b split into 2b-i/2b-ii and
  re-priced; brick 3/7 rows enriched with the probe's work-list
  additions; (c-A) ≈14–19 sessions; order 2a → 2c → 2b-i → 2b-ii →
  2d → 2e.  Brick 2a still in flight.
- 2026-08-07 (№233): brick 2a DONE and accepted — the four C2-tower
  declarations widened in place, zero class-C surprises, three diagonal
  call sites fixed, targeted builds green incl. transparent downstream
  rebuild of SelfLowArmCaps + C01JetTower.  TOOLING: `lake-locked.ps1
  claim -Files` needs COMMA-separated paths (space-separated binds only
  the first; `.md` paths silently ignored).  Brick 2c dispatched.
- 2026-08-07 (№234): brick 2c DONE and accepted (A2 per-index
  two-metric; zero class-C).  Brick 2b-i (window C-repairs) dispatched.
- 2026-08-07 (№235): PRO OVERALL RULING reconciled and adopted — C1
  (frontier → `bg_packet_of_adapt` + `lowreg_adapt_unif`;
  `lowreg_dt_unif` proof-body rethread), (c-B) re-scoped to the
  absorptive slice with the ≤3-jet audit + STOP condition (№226's
  7-family scope refuted by the `e^{2f_n}` counterexample), phase
  order rearranged **c-C0 → c-A(minimal) → c-B → c-C**.  Plan
  sections rewritten accordingly.  2b-i continues (in every minimal
  set); c-C0 scout dispatched.  Pro sections 五–七 arrived garbled —
  re-paste requested before acting on them.
- 2026-08-07 (№236): c-C0 scout GO — verdict (ii): shelf + 2 new
  lemmas (`duhamel_mode_pin`, `lowreg_forceHi2`) + the calibration
  amendment, ≈3–4 sessions; the `IsRealizedTwo`-escape risk
  DISSOLVED (identification = shelf `force_hi_id` route; `fHi` via
  Nemytskii evaluation on `solFieldAtOrder`, not forcing mass).
  (c-C0) section rewritten with sub-bricks; remaining (c-A) bricks
  paused pending c-C0's consumption map.  Queue after 2b-i lands:
  c-C0-1 → c-C0-2 → c-C0-3.
- 2026-08-07 (Codex takeover): c-C0/Brick 0 DONE.  The proved public
  theorem is `lowreg_directJet`; focused verification and the axiom
  audit are green.  The proof uses a direct order-one forcing driver
  plus spectral H² promotion and contains none of the forbidden lift
  dependencies or equivalent high-scale certificates.  The №236
  calibration/`liftHiN` design is superseded.  Background widening is
  now restricted to this theorem's actual adapted-solve/low-mass/rung
  call graph; the older broad 2b-i queue is not resumed automatically.
- 2026-08-07 (№238): the direct endpoint was factored at the exact background
  seam.  `direct_jet_of_mass` is proved with primitive `(g,g_bg)` solve data
  plus all-order spatial mass; `lowreg_directJet` is now its diagonal wrapper.
  `bg_packet_of_mass` is proved and constructs `BgSmoothPacket` on the same
  horizon from `IsLowSolveBg` plus that mass.  The first background forcing
  leaf `galN_evalBg` is also green in new `LowRegBgForceArms.lean`.  The sole
  remaining endpoint input is therefore `lowreg_loMassBg`; its first genuine
  non-mechanical obstruction remains the A1/C01 insertion-difference seam at
  `armLadder3Bg`.  Headline `(N)` remains 0%; route-(c) background/adapted
  lane is approximately 40%.
- 2026-08-07 (№239): the mechanical background force-arm front is complete.
  `galN_evalBg`, `galArmIdBg`, `galArmCapBg`, and `galForceArmBg` all pass
  focused verification in `LowRegBgForceArms.lean` without new assumptions.
  The next declaration `armLadder3Bg` is intentionally not stated yet: its
  A1 input still depends on the diagonal C01 cancellation by `sub_self`.
  The serial next producer is the fixed-offset background A1/C01 estimate in
  brick 2b-i, followed by the retained insertion-difference bound in 2b-ii.
- 2026-08-07 (№240): bricks 2b-i/2b-ii DONE.  The previously identified C01
  seam is now closed by sharp `range (i + 2)` AMix and insertion windows,
  `lieBgJet`, the exact seven-term `selfLow_split_bg`, and the proved
  `selfLowJetQBg`/`c0JetTowerQBg` towers.  The old diagonal C0 endpoints remain
  compatibility wrappers.  All focused checks and the required targeted
  refreshes are green.  Brick 2d source port is in flight; the next serial
  producer after it is the background ladder/rung assembly, not another C0
  estimate.  Headline `(N)` remains 0%; route-(c) background endpoint lane is
  approximately 50%.
- 2026-08-07 (№241): bricks 2d/2e DONE.  `a1PerIdxJetBg`/
  `a1PerIdxLinBg` and the six arbitrary-background ladder declarations pass
  focused checks, axiom probes, and targeted refreshes; diagonal declarations
  retain their exact former types as wrappers.  The conditional per-metric
  Rung 3/4/5 ports are now in flight in separate Bg siblings.  This is still
  infrastructure: `lowreg_loMassBg` is unstated (0%) and headline `(N)` is 0%.
- 2026-08-07 (Codex rung-three brick): brick 3 DONE.  `galArmVecBg`,
  `armLadder3Bg`, `galArmMassOrdBg`, `lowregRung3OrdBg`, `IsRung3OrdBg`, and
  `lowregRung3PackBg` pass focused verification; the two direct modules were
  refreshed serially.  The ordered cap proof calls `lowData_split g₀ g_bg`
  directly, so `Kcap` remains outside the later `δ` binder.  Rung three is
  100%; the verified rung-3/4/5 subphase is about 33%; `lowreg_loMassBg` and
  headline `(N)` remain unstated/unproved (0%).
- 2026-08-07 (Codex rung-four/five bricks): brick 4 DONE.  The five public
  declarations in each of `LowRegBgRungFour.lean` and
  `LowRegBgRungFive.lean` pass focused verification and targeted refresh;
  both export files are fresh.  The ports preserve the ordered absorption
  binders and change only the fixed-background slots and their already proved
  Bg dependencies.  The verified rung-3/4/5 subphase is now 100%, while
  `lowreg_loMassBg` and headline `(N)` remain unstated/unproved (0%); the
  broader route-(c) background/adapted machinery is approximately 60%.
- 2026-08-07 (Codex metricwise gate brick): brick 5 DONE.
  `IsLowGateOrdBg` stores the exact rung-3/4/5 and arbitrary-background
  high-rung certificates for one `(g,g_bg)`, while `lowregGatePackBg` selects
  their two scalar sum envelopes.  Focused verification and the targeted
  refresh are green.  This is 100% of the metricwise bookkeeping brick but 0%
  of the still-unstated class-first absorptive gate theorem;
  `lowreg_loMassBg` and headline `(N)` remain 0%.
- 2026-08-07 (Codex Galerkin-identification brick): the production APIs
  `lowreg_proj_atBg` and `lowreg_projMode_atBg` are focused-green and the
  direct module refresh is green.  All spectral spaces, projections, heat
  operators, and eigenmodes stay on the state metric; only `lowregNfun` uses
  the independent background.  Compatibility-only endpoints were not ported.
  This identification brick is 100%, while brick 7 remains partial;
  `lowreg_loMassBg` and headline `(N)` remain unstated/unproved (0%).
- 2026-08-07 (Codex higher-rung brick): `galArmMassHmBg` and
  `lowregHighRungsBg` are focused-green; the single-thread targeted refresh is
  green and fresh. The exact path consumes `IsRung5PathBg`; no AllRungs
  endpoint was added. The minimal HigherRung brick is 100%, while brick 7
  remains partial; `lowreg_loMassBg` and headline `(N)` remain 0%.
- 2026-08-07 (Codex adapted-packet endpoint): brick 8 is DONE metricwise.
  `bg_packet_of_adapt` consumes one `IsAdaptedLowSolveBg`, obtains
  `lowreg_loMassBg`, and calls the proved `bg_packet_of_mass` with the stored
  bounds and solve projections.  Focused verification and the single-worker
  targeted refresh are green.  The old bare-solve `bg_packet_of_solve` sorry
  remains visible; the class-first adapted-solve producer/rethreading and
  headline `(N)` remain 0%.
- 2026-08-07 (Codex class-first absorption audit): **STOP CONDITION FIRED**.
  The complete metricwise adapted-to-packet chain is green, but its current
  rung-three absorption envelope already depends on the fourth jet of the
  varying metric through `fixCdAtgw 3`; rung four/five depend on still higher
  jets.  The C3 class therefore cannot supply one common `A,B` for
  `IsLowGateOrdBg`.  The next honest frontier is a redesigned
  absorption-only gate, not scalar shrinkage, time shrinkage, or another
  wrapper.  `lowreg_adapt_unif` and headline `(N)` remain 0%.
- 2026-08-07 (Route-(c) energy-pairing redesign): the preceding STOP applies
  only to the abandoned all-rung gate architecture.  The user adopted the
  energy-pairing-first Rung-3 replacement recorded in the current phase-(c-B)
  section.  Its first producer `lieBgCorr_unif` is stated, proved, and
  focused-check green in `LowRegBgC1Pair.lean`: arbitrary preselected `H2`
  radius, bound-before-`g`, complete three-piece correction, and no varying
  fourth metric jet.  The path-integrated actual `lowC1CorrBg` bound is now
  also stated, proved, and focused-check green as `lowC1Corr_unif`.  The next
  complete Galerkin vector/pair module, `galA1FixPair3_le`, and the signed
  forcing-level C1 split are now stated, proved, and focused-check green.  The
  then-recorded second STOP at an absolute-value C2-only pairing is
  **historical and superseded** by the corrected step 6.  The failed
  top-deviation and raw-duality attempts remain useful negative results, but
  the live route recombines C0+C2 and asks for a one-sided full-slope
  commutator/Gårding estimate.  The complementary spectral split and
  polarized monomial Green identity are complete; the exact low-base
  full-slope adapter and analytic estimate remain unstated.  Headline `(N)`
  remains 0%.
  The superseded absorption review remains in `ROUTE_C_ABSORB_CONSULT.md`;
  the current full-slope Gårding handoff is `ROUTE_C_GARDING_CONSULT.md`.
- 2026-08-08 (arbitrary-passenger whole-slope audit):
  **STOP-AND-REDESIGN.**  Existing `edgeRiem_cancel` already accepts an
  arbitrary acted tensor once supplied a correctly oriented refold, but its
  available producer is diagonal.  The true off-diagonal terms have orientation
  `ricciTop(..., U) (nabla^2 P)` and `curvatureKernel(U) (nabla^2 P)`; the
  proposed frozen operator reverses the roles to coefficient `P` acting on
  `nabla^2 U` and is false for independent jets.  No Lean declaration, wrapper,
  stronger hypothesis, or new frontier file was added, and no Lean check was
  run because the obstruction was established before elaboration.  The next
  theorem-level choice is a paired cross-oriented directed-Green normal form or
  a genuinely diagonal form-level proof.  `lowbase_full3_unif`, the rest-only
  Rung-3 theorem, and headline `(N)` remain 0%; dedicated fixed-background
  machinery is revised from approximately 92% to approximately 90%; whole HCG
  remains approximately 3%.
- 2026-08-08 (diagonal form-level correction): the route no longer waits on a
  design choice.  Focused-green `lowBase_path_nf` connects the actual low-base
  action to its three path coefficients; `appD2_pair_h2`/`appD2_pair_h4` and
  `top_pair_h2_unif`/`top_pair_h4_unif`/`top_pair_abs_unif` prove and absorb the
  class-first principal form with only `C3` metric data.  Focused-green
  `galArmPair3_diag` and `galRepHs_scale` retain the Galerkin radial factor;
  the downstream proof uses an explicit zero/positive `theta` split but no
  inverse.  Joint-smooth exact support is public through
  `exists_edgeLieJoint`, `edgeLiePair_joint`, and
  `threeArmJoint_const`/`threeArmJoint_comp`.  The sole remaining analytic
  frontier is the homogeneous diagonal residual estimate after subtracting
  `<L^2 T, Phi(T) nabla^2(LT)>`.  `lowbase_full3_unif`, the rest-only theorem,
  and `(N)` remain 0%; dedicated machinery is approximately 92%; whole HCG
  remains approximately 3%.
- 2026-08-08 (centered complete-edge gate): the diagonal route was advanced
  through focused-green `low0_path_refold`, `b02_raw_nf`, `b02_center_nf`,
  `edgePath_inner_bi`, `edge_swap_h4_unif`, `edge_diag_h4_unif`,
  `edgeLow0_split`, and `edge_center_s_nf`.  The canonical fourth-order
  principal orientations cancel exactly against the two raw Cross terms.
  Nevertheless the exact covariant corner differs by a `q`-shaped Hessian /
  rough-Laplacian curvature commutator containing `nabla^2 Rm`; the tree has
  no identity canceling it with the `K_s-K_0` curvature fold.  Separate tame
  bounds require a radius chosen after `g`, generic commutation reads metric
  jet four, and Green reads `H5`.  The binding STOP condition is therefore
  fired at the missing complete-edge `edge_qk_comm` identity.  The target
  `lowbase_full3_unif`, rest-only Rung-3 theorem, and headline `(N)` remain 0%;
  dedicated Route-(c) machinery is approximately 94%; whole HCG remains
  approximately 3%.
- 2026-08-08 (arbitrary-Hessian audit closed): focused-green
  `appCcPsi_diag`, `cometricTrace_appCcRS`, `edgeTopPairG`, `edge_arg2_nf`,
  `phiMet_fold_comm`, and `edgeTopG_apply` close the remaining representation
  and orientation questions.  They expose the exact surviving complete
  q/K curvature block rather than canceling it.  The missing
  `edge_qk_comm`/complete-edge component identity remains unstated (0%);
  `edge_center_h4_unif`, `lowbase_full3_unif`, the rest-only Rung-3 theorem,
  and headline uniform existence all remain 0%.  Dedicated machinery stays
  approximately 94%; whole HCG stays approximately 3%.
- 2026-08-08 (Pro response audited; quantifier correction):
  **CONTINUE-WITH-CORRECTIONS.**  The response correctly declined to infer a
  complete cancellation from the q-six symbol, but it undercounted
  `nabla(pointwiseTensorCurv g 2 T)`: the exact term does contain
  `(nabla^2 Rm(g)) * T`.  It then incorrectly required the lower constant to
  be uniform over the C3 class.  The target selects `G_g` after `g`, so this
  fixed-metric fourth jet is admissible when it occurs with only one `H4`
  factor and at least one actual lower state norm, and is absorbed into
  `G_g * H3^2`.  A full symbol screen indicates that the transparent curvature
  block is generally nonzero; the historical
  `edge_qk_comm = 0` target is therefore superseded.  The non-Green
  principal-head-isolating `edge_center_peel` and its diagonal self-refold
  projection are now focused-green and directly refreshed.  The live frontier
  has passed the class-first top-kernel/principal-face and curvature-defect
  estimates.  The live frontier is the sharp `P20/P11` estimate, followed by
  the self-low carrier pairing estimate.
  `edge_center_h4_unif`, `lowbase_full3_unif`, the rest-only theorem, and
  headline `(N)` all remain
  unstated at 0%; dedicated machinery is approximately 96%; whole HCG
  remains approximately 3%.

- 2026-08-08 (post-peel analytic faces): `dagTop_cap_unif`,
  `ricciTop_cap_unif`, and `topKer_cap_unif` now give the class-first
  homogeneous fibre packet.  `bcD2_pair_h4_unif` and
  `bcD2_pair_abs_unif` close the explicit principal face, while
  `bg_pair_abs_unif` closes the nonzero curvature defect without an `H5`
  state norm.  All of these declarations are focused-green and directly
  refreshed.  The sharp `P20/P11` corner theorem, self-low carrier theorem,
  `edge_center_h4_unif`, `lowbase_full3_unif`, rest-only theorem, and headline
  `(N)` remain 0%.
