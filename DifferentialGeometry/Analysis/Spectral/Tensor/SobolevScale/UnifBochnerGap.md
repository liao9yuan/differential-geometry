# UnifBochnerGap — item-6 spine S1, stage α note

Session 4 (Opus 4.8, LANE C), branch `codex/analytic-producers-e87b`.
Ratified route: item-6 packet S1 (`UNIF_ITEM6_RECON.md §S1, §7`), curvature taken
ABSTRACTLY (Finding C, `HCGCompactness/UnifCurvatureJetBound.md`).

## What landed (stage α) — GREEN, axiom-clean

`bochner_step_unif` — the `Λ`-uniform single Bochner step, the uniform sibling of
the private `iteratedCovGrad_l2NormSq_succ_le_rawConnLap_base_add_lower`
(`DirichletSpectralBochnerGap.lean:1220`).  EXPLICIT constant `Cbase + Fc 0`
(no `Classical.choose`).

Statement (rank `s`, inner order `k`):
`∀ u, ‖∇^{k+2}u‖²_{L²} ≤ ‖∇^{k}(Δ_∇u)‖²_{L²} + (Cbase + Fc 0)·(∑_{a≤k+1}‖∇^a u‖)²`.

Abstract hypotheses (both discharged downstream — NOT `Classical.choose`):
- `hcurv` : `∀ r p (S : SmoothCcTensor g₀ 0 r), ‖∇^p(pointwiseTensorCurv g₀ r S)‖ ≤
  Fc p · ∑_{a≤p+1} ‖∇^a S‖` — the uniform Weitzenböck-defect bound, order/rank-generic,
  with explicit `Fc : ℕ → ℝ` (`hFc : ∀ p, 0 ≤ Fc p`).  This is the conclusion of
  `exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le` (`AllOrderGardingConstant.lean:193`)
  with `Fc` in place of the choose-witness `K`.  It is the "curvature-jet sup in
  consumable currency"; brick 2a discharges it from `sup_x‖∇^{g₀,a}Riemann(g₀)‖ ≤ F(Λ,n)`.
- `hbase` (constant `Cbase`) : the uniform commutator base+lower bound, uniform sibling of
  `rawConnLap_iteratedCovGrad_l2NormSq_le_iteratedCovGrad_rawConnLap_base_add_lower`
  (`:1085`).  Expressing `Cbase` through `Fc` is stage β (see below).

`0 ≤ Cbase` was DROPPED (weakest-hypotheses rule): the `nlinarith` certificate does
not use it — `hbase` already carries `+Cbase·SUM²` on the correct side.  (Callers get
`0 ≤ Cbase + Fc 0` from their own `hbase`/`hFc` when needed.)

Proof = structural mirror of `:1220`: `weitzenbock_integrated_covGrad_l2_normSq`
(`IntegratedOrder2Weitzenbock.lean:196`, PUBLIC) + Cauchy–Schwarz on the curvature
pairing.  Only the two curvature-dependent `obtain`s of the private original are
replaced by `hcurv`/`hbase`.  Uses PUBLIC API only (the leaf imports just
`DirichletSpectralBochnerGap`; no private symbol referenced).

## Verification
Whole-file `lake env lean` (`buildDir = C:/dgb2/e87b`; new file ⟹ genuine
elaboration, not cached-stale): **EXIT 0, zero errors/warnings.**  Axiom audit
(`#print axioms bochner_step_unif`, then stripped): exactly
`[propext, Classical.choice, Quot.sound]`.  Verified in a quiet Lean window
(lanes A/B active; wait-poll protocol).

## Stage β step 1 (session 5) — commutator LANDED; `:1085` BLOCKED on covDivergence tower

**`roughLapComm_unif` — GREEN, axiom-clean.**  The class-uniform `m`-fold
rough-Laplacian/covGrad commutator, uniform sibling of the `private`
`iteratedRoughLapGrad_commutator_l2Norm_le_local` (`DirichletSpectralBochnerGap.lean:616`).
Structural mirror of the original induction on `m`, with `hcurv` (the same stage-α
hypothesis) in place of its `Classical.choose` witness `K`; constant family built by the
recursion `Cfun p = Fc p + Cfun_{m-1}(p+1)` — EXPRESSED THROUGH `Fc`, no choose.  The one
private dep, the reindex `norm_iteratedCovGrad_comp_local` (`:443`, ~25 lines), was inlined
verbatim as `private norm_iterCovGrad_comp` (pointwise input `rfns_iteratedCovGrad_comp`,
public).

**`:1085` (base+lower) is BLOCKED — STOP-and-request per the session-5 mandate.**  Turning
`roughLapComm_unif` into `bochner_step_unif`'s `hbase` requires the uniform sibling of
`rawConnLap_iteratedCovGrad_l2NormSq_le_iteratedCovGrad_rawConnLap_base_add_lower` (`:1085`),
whose IBP cross-term uses `covDivergence_l2Norm_le_covGrad_local` (`:599`).  Unlike the
reindex helper, this is NOT a ≤40-line inline: it sits atop a **~130-line `private` tower**
(`:479–597`: `contract_eq_covGradBundleEquiv_symm_local`,
`riemannianFiberNormSq_eq_sum_contract_orthoFrame_local`,
`riemannianFiberNormSq_contract_le_succ_local`,
`covDivergenceRaw_eq_sum_contract_covDeriv_local`,
`riemannianFiberNormSq_covGrad_eq_sum_frame_local`,
`riemannianFiberNormSq_covDivergence_le_local`).  No PUBLIC `covDivergence ≤ covGrad` bound
exists anywhere in the tree.  The IBP identity itself
(`tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence`, `TensorCovDivergence.lean:1095`)
and `exists_rawConnLap_l2Norm_le_secondCovGrad_l2Norm_gen` (`:537`) ARE public.

**Requested ruling:** publicize `covDivergence_l2Norm_le_covGrad_local` and its `:479–597`
support tower in `DirichletSpectralBochnerGap.lean` (drop `private`; a benign,
`covDivergence`-standard, foundational-file change), OR authorize a >130-line inline copy
in this leaf (forbidden-parallel-API territory — not recommended).  With the publicize,
`:1085` → `hbase` is a short assembly (commutator `roughLapComm_unif` + `:759`-analog +
public IBP + public rawConnLap≤2ndCovGrad + the now-public covDivergence bound).

## Stage β steps 2–3 (unchanged, after `hbase`)
2. **Uniform strong induction** (mirror `:1439`): iterate `bochner_step_unif`, folding in
   the uniform Sobolev-jet constant from `hsJet_le` (`IteratedCovGradHsJetBound.lean:834`
   — audit its constant is curvature/dimension = uniformizable; expected yes, §7.3).
3. **Coefficient-one gap** (mirror `cc_dirichlet_gap`, `:1539`) ⟹ `covsum_hs_unif`; the
   easy direction (`hs_covsum_unif`) mirrors `exists_smoothCcToTensorHs_le_iteratedCovGrad_sum_general`.

## Status
- 2026-07-24 (session 5): STEP 0 authoritative build of `UnifBochnerGap` GREEN ("Build
  completed successfully (9342 jobs)").  STEP 1: `roughLapComm_unif` + inlined
  `norm_iterCovGrad_comp` LANDED, both public theorems (`bochner_step_unif`,
  `roughLapComm_unif`) axiom-clean `[propext, Classical.choice, Quot.sound]`; full-file
  authoritative rebuild GREEN.  `:1085`→`hbase` BLOCKED on the ~130-line private
  covDivergence tower — STOP-and-request the publicize ruling (above).  STEP 2 (induction)
  awaits `hbase`.  No plan edits; no commit.
- 2026-07-24 (session 4): stage α `bochner_step_unif` GREEN + axiom-clean.  Curvature
  abstracted as `hcurv` (consumable currency); commutator base abstracted as `hbase`.
