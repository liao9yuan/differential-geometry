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

## Stage β — what remains for the coefficient-one Gårding pair

Goal: `hs_covsum_unif` / `covsum_hs_unif` (recon §S1) — the two-sided
spectral↔covariant equivalence with `Λ`-uniform constant, at a generic order.
The chain mirrors `DirichletSpectralBochnerGap.lean`:

1. **Discharge `hbase` (express `Cbase` through `Fc`).**  Re-derive the `m`-fold
   commutator `iteratedRoughLapGrad_commutator_l2Norm_le_local` (`:616`, private) with
   `hcurv` in place of its `K`, then `rawConnLap_iteratedCovGrad_…_base_add_lower`
   (`:1085`, private).  BLOCKER: both use the private reindex helper
   `norm_iteratedCovGrad_comp_local` (`:443`) and the private
   `covDivergence_l2Norm_le_covGrad_local` (`:599`) — need public equivalents or a
   short inline re-derivation.  The commutator constant is then explicit in `Fc`
   (`Cfun p = ∑_{i} Fc(p+i)`-shape).  `exists_rawConnLap_l2Norm_le_secondCovGrad_l2Norm_gen`
   (`RoughLaplacianSecondCovGradL2Bound.lean:537`, PUBLIC, dimension-only) and the
   Weitzenböck IBP are consumable directly.
2. **Uniform strong induction** (mirror `exists_iteratedCovGrad_l2NormSq_le_spectralModeMass_succ_add_lower`,
   `:1439`): iterate `bochner_step_unif`, folding in the uniform Sobolev-jet constant
   from `hsJet_le` (`IteratedCovGradHsJetBound.lean:834` — audit whether its constant
   is curvature/dimension = uniformizable; expected yes, §7.3).
3. **Coefficient-one gap** (mirror `cc_dirichlet_gap`, `:1539`) ⟹ `covsum_hs_unif`;
   the easy direction (`hs_covsum_unif`) mirrors `exists_smoothCcToTensorHs_le_iteratedCovGrad_sum_general`.

Effort: step 1 is the immediate next brick (~150–250 lines incl. the two reindex/divergence
helpers); steps 2–3 are the induction assembly.  No new mathematical frontier —
structural mirroring with `hcurv` threaded.

## Status
- 2026-07-24 (session 4): stage α `bochner_step_unif` GREEN + axiom-clean.  Curvature
  abstracted as `hcurv` (consumable currency); commutator base abstracted as `hbase`.
  Stage β = discharge `hbase` (commutator re-derivation, blocked on 2 private helpers)
  then the induction to `hs_covsum_unif`/`covsum_hs_unif`.  No plan edits; no commit.
