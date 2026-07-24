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

## Stage β step 1 CLOSED (session 6) — `hbase` assembled; publicize granted

Planner GRANTED the publicize (minimal form): `private` dropped from
`covDivergence_l2Norm_le_covGrad_local` (`DirichletSpectralBochnerGap.lean:599`) ONLY (the
`:479–597` support tower stays `private` — a public theorem freely uses same-file privates).
This is the sole one-token edit in that foundational file.

Three theorems added to this leaf (verification: authoritative `lake build +…UnifBochnerGap`,
which refreshes the edited DirichletSpectralBochnerGap olean — status recorded in Status log):
- `rawConnLapIter_unif` — uniform `:759` (`∇^a∘Δ_∇` bound): public dimension-only
  `exists_rawConnLap_l2Norm_le_secondCovGrad_l2Norm_gen` + `roughLapComm_unif`.
- `baseAddLower_unif` — uniform `:1085`, **the `hbase` provider**: its conclusion is EXACTLY
  `bochner_step_unif`'s `hbase`; explicit constant `(Cfun 0)² + 2·Crc·√finrank·Cfun 1`
  (`Fc`-explicit heads + dimension), IBP via public
  `tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence` + the now-public covDivergence bound.
- `bochner_step_hcurv` — **`hbase` DISCHARGED**: combines `baseAddLower_unif` +
  `bochner_step_unif` so the only remaining hypothesis is the abstract `hcurv` (with explicit
  `Fc`).  Induction-ready form for step 2.

## `hsJet_le` audit (session 6, for step 2) — PASSES, no non-Λ quantity

`hsJet_le` (`IteratedCovGradHsJetBound.lean:834`) → `jet_even:603` / `jet_odd:667`:
- `jet_even` constant `= (2k+1)·Cg·(k+1)` — order factors × `Cg` from
  `exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter` (the SAME Bochner elliptic recursion
  `∇^j ≤ ∑ Δ^i` this file uniformizes).
- `mode_le_jet:438` constant `= (Cfun 0)²`, `Cfun` from
  `exists_iteratedCovGrad_rawConnLapIter_l2Norm_le` (iterated Δ = curvature commutator + dim).
**Verdict: entirely curvature-commutator + dimension + order factors — NO spectral gap,
injectivity radius, or `λ₁`.  Λ-controllable via the same `hcurv`/`Fc` mechanism.** (Its
UNIFORM version is not free — it requires re-deriving `exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter`
through `bochner_step_hcurv`, which is step-2 work — but the audit finds no blocker.)

## STEP-2 route MAPPED (session 7) — fully specified for a mechanical write

**KEY finding:** the endpoints `covsum_hs_unif`/`hs_covsum_unif` ARE uniform
`hsJet_le`/`hs_le_jet` (`IteratedCovGradHsJetBound.lean:834/855`).  The hard one routes
through the elliptic `exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter`
(`AllOrderGardingConstant.lean:918`, `∑‖∇^j‖ ≤ C·∑‖Δ^i‖`).  Its ORIGINAL proof peels a
DEEPER curvature atom `exists_integrated_curvatureCrossBound` (via the order-2 step
`exists_secondCovGrad_l2NormSq_le_rawConnLap_rankGen:122`, constant `2+2·Ccross`) that my
`hcurv` (the `pointwiseTensorCurv` defect) does NOT capture.  **The planner's route sidesteps
it:** re-derive `:918`'s CONTENT via `bochner_step_hcurv` (whose curvature is already
`hcurv`-packaged), NOT by uniformizing `:918`'s subs.  All pieces are now identified.

### STEP 2.1 — uniform elliptic `elliptic_lapSum_unif` (`∀ j, ‖∇^j S‖ ≤ C_j·∑_{i≤j}‖Δ^i S‖`)
STRONG induction on the jet order `j` (rank `s` fixed; `hcurv` rank-generic ⇒ reusable):
- **`j=0`:** `‖S‖ = ‖Δ^0 S‖`, `C_0 = 1`.
- **`j=1` (base, curvature-FREE):** `‖∇S‖² ≤ ‖ΔS‖·‖S‖` — the Dirichlet-energy IBP
  `covGrad_norm_sq_le_rawConnLap_mul_self` (`AllOrderGardingConstant.lean:843`, private,
  ~9 lines — INLINE; atom `covGrad_l2NormSq_le_rawConnLap_mul_self_gen`).  ⇒ `‖∇S‖ ≤
  ‖S‖+‖ΔS‖ = ∑_{i≤1}‖Δ^i S‖`, `C_1 = 1`.  No `Fc` (curvature-free, Λ-independent).
- **`j≥2` (either parity):** `bochner_step_hcurv` at `k=j-2`:
  `‖∇^j S‖² ≤ ‖∇^{j-2}(ΔS)‖² + C·(∑_{a≤j-1}‖∇^a S‖)²`.  Bound `‖∇^{j-2}(ΔS)‖` by strong-IH
  at `j-2` applied to `ΔS`, reindex `Δ^i(ΔS)=Δ^{i+1}S` (inline the private
  `rawTensorConnLapIter_rawTensorConnLapSmooth:520`, ~6 lines; `Δ^i,Δ^{i+1}` public
  `rawTensorConnLapIter_zero/_succ`); bound each `‖∇^a S‖` (`a≤j-1`) by strong-IH.  Take
  `√`: `C_j = C_{j-2} + √C·∑_{a≤j-1}C_a`, `Fc`-explicit.
- Then wrap to `hsJet_le` shape: even orders `jet_even`-style
  (`∑_{j≤2k}‖∇^j‖ ≤ C·‖Hs^{2k}‖`) via `elliptic_lapSum_unif` + the curvature-FREE
  `rawIter_even`(`‖Δ^i S‖ ≤ ‖Hs^{2i}‖`)/`ccToHs_norm_mono` (both consumable); odd via `jet_odd`.
  ⟹ `covsum_hs_unif`.  Easy direction `hs_covsum_unif` mirrors `hs_le_jet:855`/`mode_le_jet:438`
  (curvature via `exists_iteratedCovGrad_rawConnLapIter_l2Norm_le` — iterate `roughLapComm_unif`).
- Effort: `elliptic_lapSum_unif` ~100–130 lines (+ 2 inlined helpers ~15); wrappers ~120.
  Genuinely a multi-lemma brick; NOT one clean landing under the wait cadence.

### STEP 2.2 — uniform strong induction (mirror `:1439`)
Once uniform `hsJet_le` (2.1) exists: iterate `bochner_step_hcurv`, fold the uniform
Sobolev-jet constant (as `:1439` does at `:1465`).  Prereq = 2.1.

### STEP 2.3 — coefficient-one gap + endpoints
Mirror `cc_dirichlet_gap:1539` (uses 2.2) → `covsum_hs_unif`; easy → `hs_covsum_unif`.

## Status
- 2026-07-24 (session 7): STEP-2 route fully MAPPED (no Lean landed — a deep mapping of the
  elliptic chain).  KEY: `bochner_step_hcurv` route sidesteps the deeper
  `curvatureCrossBound` atom `:918` uses; the `j=1` base is curvature-FREE
  (`covGrad_norm_sq_le_rawConnLap_mul_self:843`); every sub-lemma + inline identified above.
  STEP 2.1 (uniform elliptic `elliptic_lapSum_unif` → uniform `hsJet_le`) is a specified
  ~250-line multi-lemma write; recommended as the next focused dispatch.  No plan edits; no
  commit.
- 2026-07-24 (session 6): publicize GRANTED + applied (one token: `private` dropped from
  `covDivergence_l2Norm_le_covGrad_local:599`; DirichletSpectralBochnerGap rebuilt GREEN,
  63s — NO downstream breakage).  `hbase` ASSEMBLED + DISCHARGED: `rawConnLapIter_unif`,
  `baseAddLower_unif` (the `hbase` provider), `bochner_step_hcurv` (only `hcurv`/`Fc` remain)
  — all three axiom-clean `[propext, Classical.choice, Quot.sound]`; authoritative
  `lake build +…UnifBochnerGap` GREEN ("Build completed successfully (9342 jobs)", 46s).
  One fix en route: `baseAddLower_unif` needed `set_option maxHeartbeats 1600000 in` (default
  200000 timed out at the IBP `nlinarith`).  `hsJet_le` audit for step 2: PASSES (no non-Λ
  quantity).  STEP 2 (strong induction) is next.  No plan edits; no commit.
- 2026-07-24 (session 5): STEP 0 authoritative build of `UnifBochnerGap` GREEN ("Build
  completed successfully (9342 jobs)").  STEP 1: `roughLapComm_unif` + inlined
  `norm_iterCovGrad_comp` LANDED, both public theorems (`bochner_step_unif`,
  `roughLapComm_unif`) axiom-clean `[propext, Classical.choice, Quot.sound]`; full-file
  authoritative rebuild GREEN.  `:1085`→`hbase` BLOCKED on the ~130-line private
  covDivergence tower — STOP-and-request the publicize ruling (above).  STEP 2 (induction)
  awaits `hbase`.  No plan edits; no commit.
- 2026-07-24 (session 4): stage α `bochner_step_unif` GREEN + axiom-clean.  Curvature
  abstracted as `hcurv` (consumable currency); commutator base abstracted as `hbase`.
