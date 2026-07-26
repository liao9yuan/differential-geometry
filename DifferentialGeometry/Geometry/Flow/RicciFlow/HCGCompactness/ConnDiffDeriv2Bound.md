# ConnDiffDeriv2Bound — the `hAcc` (m ≥ 2) frontier: recon + state-before-prove

Companion to `ConnDiffDeriv2Bound.lean`.  Sibling of `ConnDiffDerivBound.md` (the a=1 / B2 note) and
`UNIF_ITEM6_RECON.md` (the B2 route).  This note RULES the a ≥ 2 route, records the single stated
lemma, and gives the honest size estimate for the campaign.  **This was a RECON brick: the deliverable
is the route + a stated frontier lemma, not a proof.**

## 0. STATUS (2026-07-26)

- **UPDATE (a=2 campaign session 10 = `covStep2_diffStep_eval` core, session 3, 2026-07-26): the
  session-9 IPS-`NormedSpace` wall is CURED — LINEARITY SPLIT (iii) COMPLETE, green + axiom-clean.**
  The remedy is `set_option backward.isDefEq.respectTransparency false in` on the two `mdiff` lemmas
  (the project's known cure for `Tensor0SModel`-`NormedSpace` synthesis in
  `contMDiffAt_section_apply_gen` — the same option this file already carries for `covDConnDiff2_g1_le`,
  L565).  **This SUPERSEDES the session-9 "BLOCKED / placement-refactor" conclusion:** no move to
  `MetricCovDerivLinear.lean` and no relocation of `covDerivConnDiff_contMDiff` was needed; the
  differentiability + split live cleanly IN this IPS leaf.  Landed green + `#print axioms` =
  `[propext, Classical.choice, Quot.sound]` (all three): `covStep2_branch1_mdiff`,
  `covStep2_branch2_mdiff` (`MDifferentiableAt` of the T1/T2 summands, via
  `TensorMultilinear.contMDiffAt_section_apply_gen` + `.mdifferentiableAt`, packaging the `∇₂A`/`A`
  slots as `ContMDiffSection`s), and `covStep2_diffStep_split`
  (`extDerivFun(−∑T1 − ∑T2) = −∑ₐ extDerivFun T1ₐ − ∑ₐ extDerivFun T2ₐ`, via `extDerivFun_sub_at` as a
  defeq-checked `have` + `extDerivFun_neg_at`/`extDerivFun_finset_sum_at`, the a=1 `hDF` technique).
  Targeted module build GREEN (9519 jobs); file's ONLY `sorry` stays `covStepDiff2_mixedComm_le`.
  - **Composition ready:** `covStep2_diffStep_peel` ▸ `covStep2_diffStep_split` ▸ (per slot)
    `covStep2_diffStep_branch1`/`branch2` now expands `PieceA` up to the `H`-correction (OC) sum.
  - **Durable lesson (CORRECTS session-9):** section-apply differentiability
    (`contMDiffAt_section_apply_gen` → `.mdifferentiableAt`) IS available in IPS files after all —
    guard the lemma with `set_option backward.isDefEq.respectTransparency false in`, which lets
    `NormedSpace ℝ (Tensor0SModel s ℝ E)` synth.  (Local/global `NormedSpace` providers and
    `synthInstance.maxHeartbeats` do NOT help; the transparency option is the specific cure.)
  - **Remaining for the eval core:** (ii) the OC eval (`s+2` `diffStep_leibniz_eval` applications on the
    `∇₂_U`-updated tuples — wall-free, packaging `∇₂_U W`/`∇₂_U V`/`∇₂_U(Vslots a)` as `covApply`
    sections via `covApply_contMDiffOn`), then (iv) the `PieceA−PieceB` ∇₂²S-cancellation assembly and
    the norm CS.  Core now ~65% (peel + both branches + split; OC + assembly remain).

- **UPDATE (a=2 campaign session 9 = `covStep2_diffStep_eval` core, session 2, 2026-07-26): the T2
  BRANCH landed green + axiom-clean; the LINEARITY SPLIT (iii) was reported BLOCKED — SUPERSEDED by
  session 10 (the transparency option cures it).**  Targeted module build GREEN (9519 jobs); file's
  ONLY `sorry` stays `covStepDiff2_mixedComm_le`.
  - **`covStep2_diffStep_branch2`** (per slot `a`; `#print axioms` = `[propext, Classical.choice,
    Quot.sound]`).  Differentiates the T2 summand `y ↦ (∇₂S) y (cons (W y)(update (Vslots·y) a
    (A_y(Vslots a,V))))` (field `∇₂S = covStep g₂ s S`, rank `s+1`) by `covStep_eval_smooth_slots`
    (deriv `U`) into four branches: the leading **`∇₂²S`** term
    `covStep g₂ (s+1)(covStep g₂ s S) x (cons U (cons W (update (Vslots·x) a (A_x(Vslots a,V)))))`, the
    `p=0` **`∇₂_U W`-into-`W`** insertion, the diagonal **`covDerivConnDiff g₂ g₁ U V (Vslots a)`**
    branch (`∇₂_U(A(Vslots a,V))` via the connection-difference product rule `hfact`, mirroring a=1
    `diffStep_leibniz_eval`'s `hFact1` one variable over: `covDerivConnDiff + A(Vslots a,∇₂_U V) +
    A(∇₂_U(Vslots a),V)`), and the off-diagonal `∇₂_U(Vslots b)` insertions.  Proof idioms: typed
    `set ρ := Fin.cons W (update Vslots a Asec)`, `hρpt` pointwise, `Fin.sum_univ_succ` +
    `Fin.update_cons_zero` + `← Fin.cons_update` for the `p=0`/`p=succ` split, `Function.update_idem` +
    `hfact` + `Finset.sum_congr` for the diagonal/off-diagonal.
  - **(iii) LINEARITY SPLIT — BLOCKED (reverted).**  `covStep2_diffStep_split` (split
    `extDerivFun(−∑T1 − ∑T2) = −∑ₐ extDerivFun T1ₐ − ∑ₐ extDerivFun T2ₐ`) and its two required summand
    differentiability lemmas `covStep2_branch1_mdiff`/`covStep2_branch2_mdiff` were fully drafted and
    are mathematically correct — the split lemma itself elaborates green — BUT the `mdiff` proofs need
    `MDifferentiableAt (fun y => (T y)(slots·y)) x` via `TensorMultilinear.contMDiffAt_section_apply_gen`
    + `ContMDiffAt.mdifferentiableAt`, which triggers **`NormedSpace ℝ (Tensor0SModel s ℝ E)`
    synthesis that FAILS in this `InnerProductSpace`-based file** (the documented CMM-`NormedSpace`
    wall).  **VERIFIED not a timeout** (`synthInstance.maxHeartbeats 1000000` did not help) and **not
    fixable by a same-file provider** (the global `Tensor0SBundle.tensor0SModel_normedSpace` instance,
    a file-level `private instance`, and proof-local `letI` on both the folded `Tensor0SModel` and the
    unfolded `ContinuousMultilinearMap` forms all failed) — the diamond is at the `E`-`NormedSpace`
    level (IPS-derived vs the CMM instance's expected one).  Every WORKING use of the section-apply
    smoothness route (`Tensor0SInnerSectionSmooth`, `NablaComponents/Basic`, `CurvatureCoefficient…`)
    is in an explicit-`[NormedSpace ℝ E]` file, never an IPS one.  **FIX PATH (session 3):** place the
    two `mdiff` lemmas + the split in a `NormedSpace`-based file (e.g. `MetricCovDerivLinear.lean`,
    next to `diffStep_leibniz_eval`'s own working `hdiff`); this needs `covDerivConnDiff_contMDiff`
    (currently in this IPS leaf) moved to its documented HOME-DEBT target
    `RicciConnDiffPalatini.lean` (a `NormedSpace` Integral.Connection file) — a placement refactor, not
    new mathematics.
  - **(ii) `H`-correction (OC) eval — NOT attempted** (wall-free: it applies `diffStep_leibniz_eval`
    one level down on the `s+2` `∇₂_U`-updated tuples as a black box, packaging `∇₂_U W`/`∇₂_U V`/
    `∇₂_U(Vslots a)` as `covApply`-sections, so it dodges the tensor-model `NormedSpace` wall).  Its
    per-`q` shape differs (`q=0` deriv slot, `q=1` slot-1, `q=succ·succ a` a Vslot) so it is `s+2`
    `diffStep_leibniz_eval` applications — a genuine `hFib`-scale expansion, deferred.
  - **Honest size:** the `covStep2_diffStep_eval` core is now ~55% done (peel + BOTH branches
    materialised; OC eval + linearity split + assembly remain).  Revised estimate to
    `covStepDiff2_mixedComm_le` GREEN: **~3 more focused sessions** (mdiff/split placement refactor ≈ 1,
    OC eval ≈ 1, eval assembly + norm CS ≈ 1).
  - **Durable lesson:** section-apply differentiability (`contMDiffAt_section_apply_gen` →
    `.mdifferentiableAt`) is UNAVAILABLE in IPS files — `NormedSpace ℝ (Tensor0SModel s ℝ E)` will not
    synth there regardless of local/global providers or heartbeats.  Keep differentiability of
    `y ↦ T y (slots·y)` in `NormedSpace` files.

- **UPDATE (a=2 campaign session 8 = `covStep2_diffStep_eval` core, session 1, 2026-07-26): the outer
  PEEL and the fully-materialised T1 BRANCH landed sorry-free + axiom-clean.**  Both new theorems in
  `ConnDiffDeriv2Bound.lean`, targeted module build GREEN (9519 jobs), `#print axioms` =
  `[propext, Classical.choice, Quot.sound]` (no `sorryAx`); the file's ONLY `sorry` stays at
  `covStepDiff2_mixedComm_le` (unchanged).
  - **`covStep2_diffStep_peel`** (correct-by-construction, no differentiability hypothesis).  The eval
    `PieceA = covStep g₂ (s+2)(covStep g₂ (s+1)(diffStep g₁ g₂ s S)) x [cons U (cons W (cons V Vslots))]`
    equals, verbatim as landed:
    ```
    extDerivFun (fun y => (−∑ₐ (S y)(update (Vslots·y) a (covDerivConnDiff g₂ g₁ W V (Vslots a) y)))
                          − ∑ₐ covStep g₂ s S y (cons (W y)(update (Vslots·y) a (A_y(Vslots a, V))))) x (U x)
      − ∑_{q:Fin(s+2)} (covStep g₂ (s+1)(diffStep g₁ g₂ s S)) x
          (update (fun b => RR b x) q ((leviCiv g₂ (fun y => RR q y) x)(U x)))
    ```
    where `RR = Fin.cons W (Fin.cons V Vslots)`, `A_y(P,Q)=difference (LC g₁)(LC g₂) y P Q`.  Proof =
    outer `covStep_eval_smooth_slots` peel + pointwise `diffStep_leibniz_eval` on the inner scalar field
    (`hInner`, funext + rw hRRpt + `exact diffStep_leibniz_eval …`).  The inner `−T1 − T2` is kept as ONE
    `extDerivFun` (the linearity split is deferred to the branch layer); the `H`-correction sum is left
    unevaluated (session-2 target).
  - **`covStep2_diffStep_branch1`** (per slot `a`; materialises `covDerivConnDiff2`).  Differentiates the
    T1 summand `y ↦ (S y)(update (Vslots·y) a (∇₂A(W;V,Vslots a) y))` via `covStep_eval_smooth_slots`
    (field `S`, deriv `U`) into three branches: leading `∇₂S`-into-`∇₂A`, **diagonal**
    `(S x)(update (Vslots·x) a (covDerivConnDiff2 g₂ g₁ U W V (Vslots a) x + 3 covDerivConnDiff
    corrections))`, and the off-diagonal `∑_{b≠a} … (∇₂_U(Vslots b)) …`.  `covDerivConnDiff2` is
    materialised on the diagonal by `covDerivConnDiff2_eq` (its DEF is `covApply(∇₂) U (∇₂A-sec) − 3`
    slot corrections; `covDerivConnDiff_contMDiff` supplies the section smoothness).
  - **Session-2 frontier for `covStep2_diffStep_eval` (the full clean identity) + the bridge:**
    (i) the **T2 branch** — differentiate `∑ₐ covStep g₂ s S y (cons W (update (Vslots·y) a (A_y(Vslots a,V))))`
    by `covStep_eval_smooth_slots` (field `covStep g₂ s S = ∇₂S`, rank `s+1`, deriv `U`) → the `∇₂²S`
    leading terms + a `covDerivConnDiff` branch (via the `∇₂_U(A(Vslots a,V))` product rule, the a=1
    `hFact1` one variable over); (ii) the **`H`-correction (OC) eval** — apply `diffStep_leibniz_eval`
    ONE level down to `covStep g₂ (s+1)(diffStep S)` on each of the `s+2` `∇₂_U`-updated tuples (an
    `hFib`-scale reindex, three `Fin.cases`-style cases q=0/1/succ·succ); (iii) the peel's single
    `extDerivFun (−T1−T2)` linearity split (needs `MDifferentiableAt` of T1/T2 at `x`, mirroring a=1
    `hdiff`); (iv) the `∇₂²S`-cancellation of this `PieceA` against `PieceB = diffStep_leibniz_eval` at
    rank `s+1` (field `∇₂S`) inside `∇₂(mixedComm S) = PieceA − PieceB`, then the per-slot CS norm
    assembly (`covDConnDiff2_g1_le` + `covDerivConnDiff_gJet_le`, `normSq0S_le_card_of_component_bound`)
    to discharge `covStepDiff2_mixedComm_le`.
  - **Honest size:** the `covStep2_diffStep_eval` reusable core is ~40% done (peel + 1 of 2 branches, both
    fully materialised; T2 branch + OC eval + linearity split + assembly remain).  `covStepDiff2_mixedComm_le`
    (the norm bound consuming the eval) is a further, separate step.  Revised estimate to
    `covStepDiff2_mixedComm_le` GREEN: **~2–3 more focused sessions** (T2+OC ≈ 1, eval assembly ≈ 1,
    norm CS ≈ 1), down from the session-7 "300–450 lines, 2-session core" for the eval identity alone.
  - **Lean lessons (this session):** (a) a **section-valued `Fin.cons` tuple** `Fin.cons W (Fin.cons V Vslots)`
    written inline in a statement/`have` leaves the `Fin.cons` motive a metavar (`Function expected at
    Fin.cons ?m b`); fix = a **typed `set RR : Fin (s+2) → ContMDiffSection … := …`** (mirrors a=1's `VV`),
    whose annotation both elaborates and lets `set` fold the statement's OC into `RR`-form so the final
    `rw [hInner]` closes.  (b) **`covDerivConnDiff2` materialisation** = `rw [covDerivConnDiff2_eq]` then
    `simp only [covApply, LeviCivita_eq_leviCivitaConnectionOfMetric]; abel`: `simp` beta-reduces
    `(fun z=>U z) x → U x` and bridges the `LeviCivita g₂ = leviCivitaConnectionOfMetric g₂` **defeq**
    (which `abel` alone treats as distinct atoms), and `abel` cancels the `−cᵢ + cᵢ` corrections.  (c)
    diagonal collapse uses `Function.update_idem` (double update at `a`); off-diagonal `σ b → Vslots b`
    (`b≠a`) via `Finset.sum_congr` + `Function.update_of_ne (Finset.ne_of_mem_erase hb)`.  (d)
    `ContMDiffSection.mk`-coe is `rfl`-reducible after unfolding the `set` (a=1 `hDval` pattern), so
    `rw [hCDCdef]; rfl` closes the section-coe `have`.

- **UPDATE (a=2 campaign session 7, 2026-07-26): the `covStepDiff2_mixedComm_le` eval-identity route
  was AUDITED empirically; the plan's implied "clean one-order-up of `diffStep_leibniz_eval`" is
  DISPROVEN — the frontier is larger than the ~100-line estimate.  KEY FINDING (verified in Lean via a
  disposable test lemma, now removed; file is back to its clean single-`sorry` baseline, GREEN):**
  - **`mixedComm S` has NO clean single-`covDerivConnDiff`-insertion eval.**  Evaluating
    `mixedComm S = covStep g₂ (s+1)(diffStep g₁ g₂ s S) − diffStep g₁ g₂ (s+1)(covStep g₂ s S)` on
    `Fin.cons (W x)(Fin.cons (V x)(Vslots·x))` via `diffStep_leibniz_eval` (rank `s`) + `diffStep_eval`
    (rank `s+1`, field `∇₂S`) gives, **verbatim from the Lean goal**:
    ```
    mixedComm S x [W,V,Vslots] = −term1clean − term2 + diffStepEval
      term1clean   = ∑ₐ S(update Vslots a (covDerivConnDiff g₂ g₁ W V (Vslots a)))          -- ∇₂A into S
      term2        = ∑ₐ (covStep g₂ s S)(cons W (update Vslots a (A(Vslots a, V))))          -- A-dir V, ∇₂S leading W
      diffStepEval = ∑_{q:Fin(s+1)} (covStep g₂ s S)(update (cons V Vslots) q (A((cons V Vslots) q, W)))
      A = (LC g₁).difference (LC g₂) x
    ```
    The clean identity `mixedComm = −term1clean` requires `term2 = diffStepEval`; **`abel` leaves the
    residual `−term2 + diffStepEval = 0`, which is FALSE** (`s=1`: `term2 = ∇₂S([W,A(Vs0,V)])`;
    `diffStepEval = ∇₂S([A(V,W),Vs0]) + ∇₂S([V,A(Vs0,W)])` — one term vs two, distinct arguments).  So
    `mixedComm S` carries genuine `∇₂S`-insertion terms; it is NOT `(∇₂A)⋆S` at the naive eval level.
  - **Consequence for the a=2 bridge.**  `∇₂(mixedComm S)` is therefore a genuine NESTED second
    differentiation.  It IS feasible — the tensor identity
    `∇₂(mixedComm S) = (∇₂²A)⋆S + (∇₂A)⋆∇₂S` (product rule; airtight) guarantees the `∇₂²S` symbols
    cancel — but the realization needs the eval of `Piece A = covStep g₂ (s+2)(covStep g₂ (s+1)(diffStep S))`
    (`= ∇₂²(A⋆S)`, an outer `covStep_eval_smooth_slots` peel of the `diffStep_leibniz_eval` RESULT, with
    the two inner sums each differentiated), then subtract
    `Piece B = covStep g₂ (s+2)(diffStep g₁ g₂ (s+1)(covStep g₂ s S))` (`= diffStep_leibniz_eval` at rank
    `s+1`), with the `∇₂²S` terms (`Piece A`'s `∂(term2)` branch vs `Piece B`'s `D2 = A-into-∇₂²S`)
    cancelling.  Structurally this IS "`diffStep_leibniz_eval` one order up": `covDerivConnDiff2` emerges
    from differentiating `term1clean`'s `covDerivConnDiff` insertion (its DEF is exactly
    `covApply(∇₂) U (covDerivConnDiff-sec) − 3 slot corrections`, and `covDerivConnDiff_contMDiff`
    supplies the smoothness), exactly as `diffStep_leibniz_eval`'s `hFact1` produced `covDerivConnDiff`
    from `∂A`.  Honest size: **~300–450 lines** with 3–4 `hFib`-scale Finset re-indexing / cancellation
    blocks (the a=1 `diffStep_leibniz_eval` is 230 lines for ONE peel + ONE cancellation; a=2 adds a
    second peel and the `∇₂²S` cancellation) — a multi-session core, NOT the ~100-line port §3.2/the
    `sorry` docstring imply.  The plan's FINAL target shape (covDerivConnDiff2-insertion +
    covDerivConnDiff-insertion) is likely still correct AFTER the `∇₂²S` cancellation, but the
    intermediate `mixedComm`-clean assumption that would make it a short port is false.
  - **Smallest next lemma (the reusable core):** `covStep2_diffStep_eval` — the eval of `Piece A`
    (`∇₂²(diffStep S) x [cons U (cons W (cons V Vslots))]`).  Build it as an outer
    `covStep_eval_smooth_slots` peel (field `H = covStep g₂ (s+1)(diffStep S)`, deriv `U`), rewrite the
    inner `fun y => H y (rest·y)` by `diffStep_leibniz_eval` pointwise, then differentiate the two sums
    (`term1clean` → covDerivConnDiff2 via its DEF + `covDerivConnDiff_contMDiff`; `term2` → `∇₂²S` + a
    covDerivConnDiff branch), mirroring `diffStep_leibniz_eval`'s `hEDF`/`hFib`/`hFact1`/`hYY'` idioms.
    Then `covStepDiff2_mixedComm_le`'s norm assembly mirrors `covStepDiff_norm_le`
    (`UnifCovSumCross.lean:711`) with the g₂-fibre atoms `covDerivConnDiff_gJet_le` (for the
    covDerivConnDiff insertion) and a g₁→g₂-converted `covDConnDiff2_g1_le` (for the covDerivConnDiff2
    insertion), assembled by `normSq0S_le_card_of_component_bound`.
  - Verified: baseline `ConnDiffDeriv2Bound.lean` GREEN, single intended `sorry` at
    `covStepDiff2_mixedComm_le`.  No API change; `covDConnDiff2_g1_le`/`koszul2_clean` still axiom-clean.

- **UPDATE (a=2 campaign session 6, 2026-07-26): `covStepDiff2_exists_const` is PROVED conditional on a
  SINGLE minimal bridge; the a=2 fibre assembly is COMPLETE modulo one flagged realization lemma.**
  - **Reduction (the honest, minimal frontier).**  Applying `covStep g₂` to `diffStep_leibniz`
    (`MetricCovDerivLinear.lean`) + `covStep_add` splits
    `∇₂²(A⋆S) = covStep g₂ (covStep g₂ (diffStep g₁ g₂ s S))` into
    `covStep g₂ (diffStep g₁ g₂ (s+1)(covStep g₂ s S))` (**piece 1** — the a=1 base-Leibniz jet of `∇₂S`,
    bounded by the COMMITTED `covStepDiff_of_jets` at level `s+1`, `S := ∇₂S`) PLUS
    `∇₂(mixedComm S) = covStep g₂ (covStep g₂ (covStep g₁ S) − covStep g₁ (covStep g₂ S))` (**piece 2** —
    the a=2 mixed commutator, realizing `(∇₂²A)⋆S + (∇₂A)⋆∇₂S`).  The two fibre norms combine by
    `sqrt_normSq0S_add_le` (triangle); constant `max 0 (K₁ + C_bridge)`, uniform in `S, x`.
  - **The ONE flagged bridge = `covStepDiff2_mixedComm_le`** (new theorem in this file, `sorry`): bounds
    `√normSq0S(g₂, s+3, ∇₂(mixedComm S) x) ≤ C·(|S| + |∇₂S|)` under the exists_const hypotheses.  This is
    a genuinely NEW Tensor-layer realization lemma, NOT a recombination: its proof needs the **evaluated
    a=2 mixed-commutator Leibniz** (a=2 analogue of `diffStep_leibniz_eval`, materialising
    `∇₂²A = covDerivConnDiff2` and `∇₂A = covDerivConnDiff` at the eval level, where `∇₂³S` has cancelled)
    then per-slot Cauchy–Schwarz against the proved dual core `covDConnDiff2_g1_le` (for `∇₂²A`) and
    `covDerivConnDiff_gJet_le` (for `∇₂A`), assembled component-wise via
    `normSq0S_le_card_of_component_bound` exactly as `covStepDiff_norm_le` does one order down.
    **Flagged for the next planner decision.**
  - **Import.**  This file now imports `UnifCovSumCross` (no cycle — `UnifCovSumCross` does not import this
    file; its `hAcc` is an abstract `Racc` hypothesis discharged only in the final assembly downstream),
    to reuse the committed a=1 operator jet
    `DifferentialGeometry.PDE.RicciFlow.covStepDiff_of_jets`.
  - Verified: targeted module build GREEN (9519 jobs).  `#print axioms`:
    `covStepDiff2_exists_const` = `[propext, Classical.choice, Quot.sound, sorryAx]` (the `sorryAx` is
    inherited SOLELY from `covStepDiff2_mixedComm_le`); `covStepDiff2_mixedComm_le` = same with `sorryAx`;
    `koszul2_clean` and `covDConnDiff2_g1_le` remain axiom-clean `[propext, Classical.choice, Quot.sound]`.
  - Lean lessons: `ContMDiffSection.coe_add` as a bare `rw` lemma fails instance synth
    (`NormedSpace ℝ (Tensor0SModel ?n)`, metavar valence) in this IPS file — but the field-sum eval
    `(f + g) x = f x + g x` is DEFINITIONAL, so `rw [hop]; rfl` closes it without the lemma.  Fold
    `covStepDiff_of_jets`'s constant into the exists_const witness with
    `simp only [show s+1+2 = s+3 from rfl, ← hK1def]`.
  - **a=2 ledger — what remains before the `hAcc m=2` glue (`UnifCovSumCross.lean`, out of scope):**
    ONLY `covStepDiff2_mixedComm_le` (the evaluated a=2 mixed-commutator Leibniz realization).  Once it is
    proved, `covStepDiff2_exists_const` becomes axiom-clean automatically, and `Racc 2 := C₂`,
    `hRnn 2 := ·.1` feed `iterCovG1_le` at `m = 2` directly.

- **UPDATE (a=2 campaign session 5, 2026-07-26): `koszul2_clean` is PROVED sorry-free; the a=2
  differential-geometric content is COMPLETE.**  The ~200-line term-by-term absorption landed exactly
  as the §2.1.a derivation predicted — no statement change was needed (the corrected term-5 survivor
  shape held up in Lean).  Verified: targeted module build GREEN (9482 jobs); `#print axioms
  koszul2_clean` = `[propext, Classical.choice, Quot.sound]` AND `#print axioms covDConnDiff2_g1_le` =
  `[propext, Classical.choice, Quot.sound]` (the dual core's inherited `sorryAx` is discharged — both
  are now axiom-clean).  Proof route (all as planned): (i) package `∇₂_V` of `W,X,Y,Z` as sections
  `DVW/DVX/DVY/DVZ` (`covApply_contMDiffOn`) and `Q = ∇₂A(W;X,Y)` as `Qsec`
  (`covDerivConnDiff_contMDiff`); (ii) `hmaster := connDiff_koszul_deriv2`; the four
  `hkW/hkX/hkY/hkZ := connDiff_koszul_deriv` on the slot corrections; expand the master LHS by
  `metric_leibniz_extDeriv` + `extDerivFun_const_mul`; (iii) normalise EVERYTHING to `metricCovDeriv`
  currency in staged simps: `[nabla4_eq_mcd3, nabla3_eq_mcd2, nabla2_eq_mcd1]` first, THEN
  `field2_eq_mcd2` (before `field1_eq_mcd1` — else `field₁` inside `field₂` breaks the match), THEN
  `field1_eq_mcd1`, THEN `Fin.sum_univ_*` + `hup*`/`e4x`/`e2x`/`hcons*` + `hDVWval…`; (iv) split the
  master `∇₂_V(A-sec)` correction by `hAvec` (covDerivConnDiff-def rearrange + `abel`) and
  `hmcd1_add3` (slot-1 additivity via `Tensor0SSpace.map_update_add`); (v) unfold the a=2 jet with a
  defeq `hcdc2` (`covDerivConnDiff2_eq` + `rfl`), split by `g_sub`, `linarith`.  New reusable helper:
  `nabla2_eq_mcd1` (order-1 sibling of `nabla3_eq_mcd2`, from `metricCovDeriv_one_apply_section`).
  KEY Lean lessons: (a) the coe-vs-eta trap — `covDerivConnDiff g₂ g₁ (fun b=>W b)… x` (from
  `covDerivConnDiff2`/statement) vs `covDerivConnDiff g₂ g₁ ⇑W … x` (from `connDiff_koszul_deriv`) are
  defeq but `linarith` sees DIFFERENT atoms; unify to `⇑` by stating `hAvec`/`hQxval` in section-coe
  form and `rw [show (fun b=>W b)… = W … from rfl]` on the goal survivors.  (b) `e2x` (Fin-2
  section-tuple evaluator) is required, not just `e4x`, or the LHS-Leibniz `∑ c:Fin 2` and the `NV`
  term stay unnormalised.  (c) `hcdc2` needs an explicit `rfl` AFTER `rw [covDerivConnDiff2_eq]` (the
  reducible auto-rfl won't cross `covApply`↔coe / `Qsec`↔`cdc` / `DVW`↔`covApply`).  (d) `open … in`
  goes BEFORE the docstring, not between docstring and `theorem`.
  - **Remaining in this file:** only `covStepDiff2_exists_const` (the deliverable-3 fibre assembly).

- **UPDATE (a=2 campaign session 4, 2026-07-26): the dual core `covDConnDiff2_g1_le` is PROVED.**
  The drafted CS+division proof was finished with the three diagnosed fixes plus one more:
  - `clear_value B2 D5 D6 Avec` right after the `set`s (tames the 1.6M-heartbeat unfolding of the
    heavy `covDerivConnDiff2`/`covDerivConnDiff`/`difference` vectors);
  - vector norms kept **literal** (`√(g₁.inner x ··)`, no `set` on Pv/Qv/Rw/Su/SB) — this removes the
    `set`-folding vs literal-assoc mismatch that broke `hSD5`/`hSD6`;
  - each CS bound **pre-combined** with its atom bound (`hTA`/`hTD5`/`hTD6` via
    `mul_le_mul_of_nonneg_left` + `nlinarith`), keeping the final `nlinarith` low-degree.
  - **NormedSpace/IPS diamond fix (the real blocker):** `covDerivConnDiff_g1_le` lives in an IPS-only
    context (`ConnDiffDerivBound`, NormedSpace from `InnerProductSpace.toNormedSpace`); calling it from
    a file that declared BOTH explicit `[NormedSpace ℝ E]` and `[InnerProductSpace ℝ E]` created two
    incompatible `NormedSpace` instances, cascading to a spurious `FiniteDimensional ℝ E` synth
    failure.  Fix: drop the explicit `[NormedSpace ℝ E]` from the file's base variable block — IPS
    provides it — so the whole file is now **IPS-based** (matching `ConnDiffDerivBound`).  Consequence:
    the earlier `[NormedSpace]`-only decls (`covStepDiff2_opLeibniz`, the currency bridges,
    `covDerivConnDiff2`, `covDerivConnDiff_contMDiff`) are now IPS-typed; this is unavoidable given the
    diamond and is consistent with the a=1 `ConnDiffDerivBound` pattern (its NormedSpace-content helpers
    also live in the IPS file).  All consumers of these decls are in the IPS a=2 chain, so nothing
    breaks.
  - **Coefficient (proved):** `|∇₂²A|_{g₁} ≤ (3/2·M₃ + M₂·NA + 2·M₁·(3/2·M₂ + M₁·NA)) · |v'||v||w||u|`
    with `M₃/M₂/M₁ = √normSq0S(g₁, 5/4/3, mcd3/2/1)`, `NA = √normSqRS(g₁,1,2)(connDiff)`.
  - Axioms of `covDConnDiff2_g1_le`: `[propext, Classical.choice, Quot.sound, sorryAx]` — the `sorryAx`
    is inherited from `koszul2_clean` (still `sorry`); the dual core's own CS+division logic is complete
    and becomes axiom-clean the moment `koszul2_clean` is proved.  Targeted module build GREEN (9482).
  - **Remaining:** `koszul2_clean` (the ~200-line absorption, §2.1.a — the genuine content, now with the
    dual core validating its survivor shape is CS-usable) and `covStepDiff2_exists_const` (assembly).

- **UPDATE (a=2 campaign session 3, 2026-07-26): infra proofs landed; clean form + dual core STATED
  (corrected); §2.1 term-5 error found & fixed.**  Verified progress:
  - `ConnDiffDerivBound.lean`: **de-privatized** `sqrt_normSq0S_comp` and `covDerivConnDiff_g1_le`
    (both now `public`, docstrings added; whole file GREEN, sorry-free).  The dual core reuses both.
  - `ConnDiffDeriv2Bound.lean`: **`covDerivConnDiff_contMDiff`** — section-smoothness of the a=1 jet
    `p ↦ covDerivConnDiff g₂ g₁ W X Y p` (the sub-frontier for the LHS metric-Leibniz), PROVED
    sorry-free from `covApply_contMDiffOn` + `diffSec_contMDiff`.
  - **`koszul2_clean` STATED** (the clean a=2 Koszul identity, `sorry`) with the CORRECTED RHS.
  - **`covDConnDiff2_g1_le` STATED** (the dual core, `sorry`; statement + explicit coefficient
    `3/2·M₃ + M₂·NA + 2·M₁·(3/2·M₂ + M₁·NA)` validated by elaboration).  The full CS+division proof is
    banked in a block comment in the file; it needs finishing iteration on the wall cluster
    (1.6M-heartbeat → `clear_value` on B₂/D5/D6/Avec/M*/NA; `set`-folding of vector norms → keep them
    literal, do NOT `set` Pv/Qv/Rw/Su/SB; final `nlinarith` → pre-combine each CS bound with its atom
    bound as in `hTA`/`hTD5`/`hTD6`).
  - **§2.1 CORRECTION (a real hand-derivation error, caught during Lean prep):** the two `∇₂g₁·∇₂A`
    survivors carry the **clean** `covDerivConnDiff g₂ g₁ V X Y` (a=1 jet, deriv `V`, slots `X,Y`),
    NOT the raw `∇₂_V(A-sec)`.  The raw `∇₂_V(A-sec) = covDerivConnDiff g₂ g₁ V X Y + A(Y,∇₂_V X)
    + A(∇₂_V Y, X)`; the `A(Y,∇₂_V X)` / `A(∇₂_V Y,X)` pieces (uncontrolled `∇₂_V X`) cancel exactly
    against the quadratic slot-corrections produced by the a=1-Koszul absorption of the input-slot
    corrections (verified term-by-term below), so only the clean jet survives.  Without this the dual
    core would be UNBOUNDED — the fix is load-bearing.  §2.1.a updated accordingly.
  - Still `sorry`: `koszul2_clean` (the ~200-line absorption), `covDConnDiff2_g1_le` (CS finish),
    `covStepDiff2_exists_const` (deliverable-3 assembly, gated).

- **UPDATE (a=2 campaign session 2, 2026-07-25): infrastructure + object landed sorry-free; dual-core
  route fully de-risked.**  In `ConnDiffDeriv2Bound.lean`, all axiom-clean
  `[propext, Classical.choice, Quot.sound]`, targeted module build GREEN (9482 jobs):
  - `covStepDiff2_opLeibniz` — **deliverable 2 (operator form)**: `∇₂²(A⋆S)` expanded via
    `diffStep_leibniz` (twice) into `A⋆∇₂²S` (`= diffStep g₁ g₂ (s+2)(covStep g₂ (s+1)(covStep g₂ s S))`)
    plus the mixed commutator on `∇₂S` and the base derivative of the mixed commutator on `S`.  This
    reduces the `covStepDiff2_exists_const` frontier to the fibre norm of `∇₂(mixedComm(S))` (whose
    `(∇₂²A)⋆S` part is the a=2 atom).  `[NormedSpace]`-only (pure `covStep`/`diffStep` algebra).
  - `field1_eq_mcd1`, `field2_eq_mcd2`, `nabla3_eq_mcd2`, **`nabla4_eq_mcd3`** — the order-1/2/3
    metric-jet currency bridges; `nabla4_eq_mcd3` is the requested new order-3 sibling
    (`nabla0SFun 4 (LC g₂) V field₂ = metricCovDeriv g₁ g₂ 3` with `V x` leading).  `[NormedSpace]`-only.
  - `covDerivConnDiff2` (+ `covDerivConnDiff2_eq`) — the **clean a=2 object** `∇₂²A`
    (`= ∇₂_V[(∇₂A)(W;X,Y)] − (∇₂A)(∇₂_V W;X,Y) − (∇₂A)(W;∇₂_V X,Y) − (∇₂A)(W;X,∇₂_V Y)`), the dual-core
    target output vector.  Definable via `covApply`/`covDerivConnDiff`; typechecks, `_eq` is `rfl`.
    HOME DEBT: canonical home is next to `covDerivConnDiff` in `RicciConnDiffPalatini.lean`.
  - **The a=2 dual core `covDConnDiff2_g1_le` is NOT yet stated in Lean** (deliverable 1's bound): its
    proof needs the clean Koszul-2 identity `2 g₁(covDerivConnDiff2, Z) = RHS_clean` (§2.1 below),
    which is a genuine ~200-line absorption proof (the a=1 `connDiff_koszul_deriv` proof one order up).
    The route + the exact `RHS_clean` are now fully worked and de-risked below; the term-by-term
    correction cancellation is verified by hand.  Deliverable 3 (`covStepDiff2_exists_const`) stays
    `sorry` (gated on the dual core).  IPS note: the dual core will inherit `[InnerProductSpace ℝ E]`
    from `connDiff_koszul_deriv2` (forced, confined to that theorem); `UnifCovSumCross.lean` is an IPS
    file so it consumes it fine.

- **UPDATE (a=2 campaign session 1, 2026-07-25): the FRONTIER identity `connDiff_koszul_deriv2` is
  PROVED sorry-free** in `Geometry/Connection/LeviCivita/ChristoffelDiffKoszulDeriv2.lean` (with its two
  reusable engines `metricField_totalReg2` + `nablaMetric_combo_extDeriv2`, all axiom-clean
  `[propext, Classical.choice, Quot.sound]`).  It is the master differentiated form
  `∂_V[2 g₁(∇₂A(W,X,Y), Z)] = [three ∇₂³g₁ combos + slot corrections] − 2[∇₂²g₁·A + ∇₂g₁·∇₂A + corr]`,
  proved by "differentiate the a=1 statement" (`congrArg ∂_V` + linearity + the two combo engines; the
  quadratic reuses the a=1 engine verbatim).  Note: it carries `[InnerProductSpace ℝ E]` (inherited from
  the a=1 `connDiff_koszul_deriv`, which is not IPS-`omit`ted); the two engines are NormedSpace-only.
  See `ChristoffelDiffKoszulDeriv2.md`.  This discharges §3.1's ingredient 1.  **Still open for the
  `covStepDiff2_exists_const` sorry:** ingredient 2 (the a=2 base-Leibniz operator identity + fibre CS
  assembly) AND the a=2 dual core (analogue of `covDerivConnDiff_g1_le`, isolating `|∇₂²A|` in metric-jet
  currency from the master identity via the clean `covDerivConnDiff2` collapse).
- Ruling: **route (i) — iterate the differentiated Koszul identity** — RULED IN.  Routes (ii) and (iii)
  ruled OUT (reasons in §2).
- Stated: `covStepDiff2_exists_const` (the a=2 base-Leibniz jet atom) — elaborates GREEN, one `sorry`,
  `[NormedSpace ℝ E]`-only (standing ruling honoured).  Focused check: no errors, only the intended
  `declaration uses sorry`.
- a=2 NOT proved: it is **not** a direct extension of committed pieces — it needs a genuinely new
  differential-geometric identity (`connDiff_koszul_deriv2`, §4).  Per the brick's task 3, machinery
  NOT built; exactly what is missing is recorded (§3, §4).
- Files: created `ConnDiffDeriv2Bound.lean` + this note.  UNTOUCHED: `UnifCovSumCross.lean`,
  `AllTimesBounds.lean`, `ConnDiffDerivBound.lean`, `Evolution/*`.

## 1. THE REDUCTION — `hAcc m` forces `∇₂^a A`, unavoidably

`hAcc m` (`UnifCovSumCross.lean`, `iterCovG1_le`) bounds the **base** covariant derivative of the
telescoping accumulator:
```
√normSq0S(g₂, r+m+1, covStep g₂ (r+m) (telescAccum g₁ g₂ r T m))  ≤  Racc m · ∑_{k≤m+1} |iterCov g₂ r T k|_{g₂}.
```
Tower vocabulary (`MetricCovDerivLinear.lean`): `covStep g₂ = ∇₂`, `covStep g₁ = ∇₁`,
`diffStep g₁ g₂ = ∇₁ − ∇₂ = A ⋆ ·` (algebraic, `A = Γ₁ − Γ₂`), and
`telescAccum (m+1) = ∇₁(telescAccum m) + (∇₁ − ∇₂)(∇₂ᵐ T)`, `telescAccum 0 = 0`,
`telescAccum 1 = A ⋆ T`.

Expanding `∇₂(telescAccum(m+1))` with `∇₁ = ∇₂ + A⋆`:
```
∇₂(telescAccum(m+1)) = ∇₂²(telescAccum m) + ∇₂(A ⋆ telescAccum m) + ∇₂(A ⋆ ∇₂ᵐT).
```
The `∇₂²(telescAccum m)` term forces a **second** base derivative; iterating pushes the derivative
order up while the accumulator level comes down, so the honest object is the whole family
`∇₂^j(telescAccum m)`.  The `∇₂^j(A ⋆ S)` terms that appear are the **base-Leibniz jets of a single
connection-difference step**, and

  `∇₂^j(A ⋆ S) = Σ_{i≤j} (binom j i) (∇₂^i A) ⋆ (∇₂^{j−i} S)`   (Leibniz / Faà-di-Bruno),

so `∇₂^a A` appears with an S-independent coefficient.  **The star-product structure means `∇₂^a A`
cannot be avoided**: any recursion on `A ⋆ S`-shaped objects spawns `(∇₂A)⋆S`, `(∇₂²A)⋆S`, …, i.e. the
individual connection-difference jets.  This is why route (iii) (recurse on the accumulator, never
isolate `∇₂^a A`) does NOT dissolve the frontier (§2).

### The concrete m = 2 decomposition (what the next brick assembles)

`telescAccum 2 = ∇₁(A ⋆ T) + (A ⋆ ∇₂T)`, and `∇₂(telescAccum 2)` splits into three pieces:
```
∇₂(telescAccum 2) = ∇₂²(A ⋆ T)            -- I.a  a=2  ← THE NEW ATOM (covStepDiff2_exists_const)
                  + ∇₂(A ⋆ (A ⋆ T))        -- I.b  a=1, S = A⋆T   (covStepDiff_of_jets, committed)
                  + ∇₂(A ⋆ ∇₂T).           -- II   a=1, S = ∇₂T    (covStepDiff_of_jets, committed)
```
Derivation: `∇₂(telescAccum 2) = ∇₂(∇₁(A⋆T)) + ∇₂(A ⋆ ∇₂T)`; expand `∇₁ = ∇₂ + A⋆` inside the first:
`∇₂(∇₁(A⋆T)) = ∇₂²(A⋆T) + ∇₂(A ⋆ (A⋆T))`.  Only **I.a** is new.  I.b needs `|A⋆T|_{g₂}` (a=0 norm of
`diffStep`, available/derivable) and `|∇₂(A⋆T)|_{g₂}` (= `covStepDiff_of_jets` at S = T); II needs
`|∇₂T|, |∇₂²T|` (= `iterCov g₂` jets).  So **the sole new mathematics at m = 2 is `∇₂²(A ⋆ S)`**, which
this file's `covStepDiff2_exists_const` isolates (with S = T, s = r it is exactly term I.a).

## 2. ROUTE RULING (≤ a page)

**Route (i) — iterate the differentiated Koszul identity. RULED IN.**
B2 landed the a=1 identity `connDiff_koszul_deriv` (`ChristoffelDiffKoszulDeriv.lean:227`):
```
2 g₁(∇₂A(W,X,Y), Z) = [∇₂²g₁ combos] − 2 (∇₂_W g₁)(A(X,Y), Z),
```
with `∇₂²g₁ = nabla0SFun 3 (LC g₂) W (totalNabla0S 2 (LC g₂)(mtf g₁))` = `metricCovDeriv g₁ g₂ 2`.
**Key check (the recon's central question): does the Koszul RHS stay in `metricCovDeriv` currency at
order a+1?  YES.**  Differentiating once more along `V` (metric-compat Leibniz):
- the `∇₂²g₁`-combo terms become `∇₂³g₁`-combo terms = `metricCovDeriv g₁ g₂ 3` (order 3 = a+1); and
- the quadratic `(∇₂g₁)·A` term becomes `(∇₂²g₁)·A + (∇₂g₁)·(∇₂A)` (order-2 jet × a=0 atom + order-1
  jet × a=1 atom).
So route (i) is a clean **recursion in the metric-jet currency**:
`|∇₂^a A| ≲ |∇₂^{a+1}g₁| + Σ_{j<a} |∇₂^{a−j}g₁|·|∇₂^j A|`, base a=0 = `lcDiff_norm_le`, a=1 =
`covDerivConnDiff_gJet_le` (both committed).  This is why the stated lemma's metric jets reach **order 3**
and carry the **role asymmetry** (∇g₁ w.r.t. g₂ in `hJet1/2/3`; ∇g₂ w.r.t. g₁ in `hJet1'`, sharing Λ').
Shortest correct route; reuses the committed a=1 machinery verbatim; the general-`s` comparability
`sqrt_normSq0S_comp` already covers the higher orders.

**Route (ii) — bundle A as a tensor field, run generic `tensorRSCovariantDerivative`/`covGrad` Leibniz.
RULED OUT.**  `∇₂^a A` would be iterated `covGrad g₂` of `connDiffSection g₁ g₂`.  But A is not a product
of g-jets *as a bundled object*; to bound `covGrad^a (connDiffSection)` you still need the Koszul formula
`A ~ g₁⁻¹∇₂g₁` and to differentiate it — i.e. route (i)'s content — packaged through the bundled
covariant derivative.  This is exactly the bundled-`covGrad connDiffSection` fibre bound (P2.d) that B2
**deliberately bypassed** via the dual/eval route (see `ConnDiffDerivBound.md` §"ROUTE DECISION").
Resurrecting it is strictly more work, not less.

**Route (iii) — recurse on the accumulator re-expansion, bounding whole products.  RULED OUT.**  As §1
shows, `∇₂(telescAccum(m+1))` needs `∇₂²(telescAccum m)` (the full derivative tower), and each
`∇₂^j(A ⋆ S)` term spawns `∇₂^a A` via the Leibniz expansion.  Route (iii) therefore needs the SAME
`∇₂^a A` content as route (i) **plus** a two-index induction on `(j, m)`.  Strictly more work; it
reorganises the frontier without dissolving it.

## 2.1 THE DUAL-CORE ROUTE — clean Koszul-2 identity + CS (session 2, de-risked)

The a=2 dual core `covDConnDiff2_g1_le` mirrors the a=1 `covDerivConnDiff_g1_le`
(`ConnDiffDerivBound.lean:306`) one order up.  Two steps:

### 2.1.a The clean Koszul-2 identity `koszul_deriv2_clean` (the genuine frontier, ~200 lines)

**Statement (target).**  For sections `V W X Y Z` and `x`, with `A(a,b) = difference (LC g₁)(LC g₂) x a b`,
`mcd_k = metricCovDeriv g₁ g₂ k` (this is the CORRECTED RHS — see §0 session-3 note; both `∇₂g₁·∇₂A`
slots carry the CLEAN a=1 jet `covDerivConnDiff`, **not** the raw `∇₂_V(A-sec)`):
```
2 g₁(covDerivConnDiff2 g₂ g₁ V W X Y x, Z x)
  =  mcd3 x ![V,W,X,Y,Z] + mcd3 x ![V,W,Y,X,Z] − mcd3 x ![V,W,Z,X,Y]      -- ∇₂³g₁ combos (leading)
   − 2 · mcd2 x ![V,W, A(Y,X), Z]                                          -- ∇₂²g₁·A
   − 2 · mcd1 x ![W, covDerivConnDiff g₂ g₁ V X Y x, Z]                    -- ∇₂g₁·∇₂A  (clean; deriv V, slots X Y)
   − 2 · mcd1 x ![V, covDerivConnDiff g₂ g₁ W X Y x, Z]                    -- ∇₂g₁·∇₂A  (clean; deriv W, slots X Y = Q)
```
This is exactly the `koszul2_clean` statement in `ConnDiffDeriv2Bound.lean` (elaborates GREEN).
Here the `mcd3/mcd2` slots use the `nabla4_eq_mcd3`/`nabla3_eq_mcd2` bridges, and `mcd1 ![·,vec,·]`
uses `field1_eq_mcd1` (`(∇₂_V g₁)(a,b) = mcd1 ![V,a,b]`).  Note `Z` appears **only evaluated** — the
`∇₂_V Z` terms cancel (verified below).

**Proof route (all cancellations verified by hand — the `linarith` closes them, as in a=1):**
1. Start from the master `connDiff_koszul_deriv2 g₁ g₂ V W X Y Z x`
   (`ChristoffelDiffKoszulDeriv2.lean:141`): `∂_V[2 g₁(Q, Z)] = RHS2` (RHS2 = 3 `nabla0SFun4 V field₂`
   combos + their 3 `∑_{a:Fin 4}` slot-correction sums − 2·[quad: `nabla0SFun3 V field₁ ![W,A,Z]` +
   W-slot corr `field₁![∇₂_V W,A,Z]` + A-slot corr `field₁![W,∇₂_V A,Z]` + Z-slot corr `field₁![W,A,∇₂_V Z]`]).
2. Expand the LHS by the metric-compat Leibniz (`metric_leibniz_extDeriv` on `![Q_sec, Z]`, needs `Q`
   as a smooth section — a smoothness lemma for `p ↦ covDerivConnDiff g₂ g₁ W X Y p` is a small
   sub-frontier):
   `∂_V[2 g₁(Q,Z)] = 2(∇₂_V g₁)(Q,Z) + 2 g₁(∇₂_V Q, Z) + 2 g₁(Q, ∇₂_V Z)`.
3. `covDerivConnDiff2 = ∇₂_V Q − [(∇₂A)(∇₂_V W;X,Y) + (∇₂A)(W;∇₂_V X,Y) + (∇₂A)(W;X,∇₂_V Y)]`, so
   `2 g₁(covDerivConnDiff2, Z) = 2 g₁(∇₂_V Q, Z) − 2 g₁([3 corr], Z)`.
4. Combine 1–3: `2 g₁(covDerivConnDiff2, Z) = RHS2 − 2(∇₂_V g₁)(Q,Z) − 2 g₁(Q, ∇₂_V Z) − 2 g₁([3 corr], Z)`.
5. **Cancellations (each verified term-by-term):**
   - **`∇₂_V Z` (ζ) terms cancel.**  `−2 g₁(Q, ζ)` via a=1 `connDiff_koszul_deriv W X Y (ext ζ)` gives
     `−mcd2![W,X,Y,ζ] − mcd2![W,Y,X,ζ] + mcd2![W,ζ,X,Y] + 2·field₁![W,A(Y,X),ζ]` (note
     `nabla0SFun3 W field₁ ![a,b,ζ] = field₂ x ![W,a,b,ζ]`, an **order-2** `field₂` eval — same object
     as RHS2's Z-slot corrections).  The three `field₂![W,·,·,ζ]` cancel RHS2's Z-slot corrections of
     the 3 combos (coeffs +,+,−); the `+2 field₁![W,A,ζ]` cancels RHS2's quadratic Z-slot corr
     `−2 field₁![W,A,ζ]`.  Net ζ = 0.
   - **`∇₂_V W/X/Y` (input-slot) corrections cancel.**  `−2 g₁((∇₂A)(∇₂_V W;X,Y), Z)` via a=1 Koszul
     (deriv-dir `∇₂_V W`) gives 3 `mcd2(∇₂_V W;·,·,Z)` combos + `2 field₁![∇₂_V W, A(Y,X), Z]`.  The 3
     `mcd2` combos cancel RHS2's W-slot corrections of the 3 combos; the `2 field₁![∇₂_V W,A,Z]` cancels
     RHS2's quadratic W-slot corr `−2 field₁![∇₂_V W,A,Z]`.  Same for X, Y.  Net = 0.
6. **Survivors** = RHS_clean (the 6 terms above): 3 `mcd3` combos (RHS2's leading `nabla0SFun4`, via
   `nabla4_eq_mcd3`), `−2 mcd2![V,W,A,Z]` (RHS2's quadratic leading, via `nabla3_eq_mcd2`),
   `−2 mcd1![W, ∇₂_V A-sec, Z]` (RHS2's quadratic A-slot corr, via `field1_eq_mcd1`), and
   `−2 mcd1![V, Q, Z]` (the LHS `−2(∇₂_V g₁)(Q,Z)`, via `field1_eq_mcd1`).

### 2.1.b The dual-core CS + division (mechanical, ~150 lines, mirrors a=1)

Instantiate `koszul_deriv2_clean` at `Z = smoothExtensionTangent x (covDerivConnDiff2 …)`, so LHS
`= 2 g₁(B₂, B₂) = 2|B₂|²_{g₁}` (`B₂ = covDerivConnDiff2 g₂ g₁ (ext v')(ext v)(ext w)(ext u) x`).
Cauchy–Schwarz each RHS_clean term with `abs_apply_le_sqrt_normSq0S g₁` (ranks 5/4/3 for mcd3/mcd2/mcd1)
at an internal `g₁`-ON basis; re-expand `|A(Y,X)|` by `connDiffVec_norm_le` and the two `∇₂A`-vector
factors (`Q` and the raw `∇₂_V A-sec`) by the a=1 dual core `covDerivConnDiff_g1_le` (or its fibre form
`covDerivConnDiff_fibreNorm_le`); collect the common `|v'||v||w||u||B₂|_{g₁}`, divide by `|B₂|_{g₁}`
(rcases `eq_or_lt` of `Real.sqrt_nonneg`, then `le_of_mul_le_mul_left`, exactly as
`covDerivConnDiff_g1_le` step 7).  Result — the a=2 dual core bound in `metricCovDeriv 3/2/1` currency
(fibre norms `M₃ = √normSq0S(g₁,5,mcd3)`, `M₂ = √normSq0S(g₁,4,mcd2)`, `M₁ = √normSq0S(g₁,3,mcd1)`,
`NA`, and the a=1 vector bound `Nq`):
```
√(g₁ B₂ B₂) ≤ (3/2·M₃ + M₂·NA + [M₁·Nq-form terms]) · √(g₁ v'v')·√(g₁ vv)·√(g₁ ww)·√(g₁ uu).
```
The endpoint then converts `g₁→g₂` by `sqrt_normSq0S_comp` (private in `ConnDiffDerivBound`; re-derive
or promote) and folds `M_k ≤ √(Λ^{k+2})·Λ^{(k)}`, giving the a=2 `Λ`-polynomial that feeds
`covStepDiff2_exists_const` (existential `C₂`).

### 2.1.c Sub-frontiers exposed (for the next session)
- **Smoothness of `p ↦ covDerivConnDiff g₂ g₁ W X Y p` as a section** (for step 2's
  `metric_leibniz_extDeriv`).  Small; `covDerivDiff` is built from `cov.toFun (diffSec …)` + `covApply`,
  all with existing `contMDiff` producers (`diffSec_contMDiff`, `covApply_contMDiffOn`).
- `sqrt_normSq0S_comp` is `private` in `ConnDiffDerivBound.lean`; either re-derive (short:
  `exists_diagInv_of_metricUniformEquivalentOn` + `normSq0S_diag_le` + `Real.sqrt_mul`) or de-privatise.
- The a=1 vector bounds `covDerivConnDiff_g1_le` (private) / `covDerivConnDiff_fibreNorm_le` (public):
  use the public fibre form to bound the two `∇₂A`-vector slots in RHS_clean terms 5–6.

## 3. THE STATED LEMMA (the interface)

`covStepDiff2_exists_const` (`ConnDiffDeriv2Bound.lean`, namespace `DifferentialGeometry.HCGCompactness`):
```
(hEq  : MetricUniformEquivalentOn K g₂ g₁ Λ)
(hJet1 : MetricCovDerivOrderBoundOn K 1 g₁ g₂ Λ')     -- ∇g₁ / g₂
(hJet2 : MetricCovDerivOrderBoundOn K 2 g₁ g₂ Λ'')    -- ∇²g₁ / g₂
(hJet3 : MetricCovDerivOrderBoundOn K 3 g₁ g₂ Λ''')   -- ∇³g₁ / g₂   (order a+1 = 3, the new jet)
(hJet1': MetricCovDerivOrderBoundOn K 1 g₂ g₁ Λ')     -- ∇g₂ / g₁   (role asymmetry)
⊢ ∃ C₂ ≥ 0, ∀ (S : Tensor0SField … s) (x ∈ K),
    √normSq0S(g₂, s+3, ∇₂²(A ⋆ S) x)
      ≤ C₂ · (|S x| + |∇₂S x| + |∇₂²S x|)     [ ∇₂²(A⋆S) = covStep g₂ (covStep g₂ (diffStep g₁ g₂ s S)) ]
```
Constant is **existential** (honest state-before-prove): C₂ depends only on `Λ,Λ',Λ'',Λ''',finrank E,s`,
uniform in `S` and `x∈K` — the a≥2 campaign has not pinned its explicit polynomial, only its structure
(order-3 metric jets, order-2 S-jets, role asymmetry).  A downstream `hAcc`-facing consumer reads
`Racc 2 := C₂` and `hRnn 2 := ·.1` (this matches `iterCovG1_le`'s abstract `Racc : ℕ → ℝ`, `hRnn`).
Placement: NEW sibling leaf, not `ConnDiffDerivBound.lean`, so the committed sorry-free B2 file stays
pristine and its axiom audit stays meaningful; the a≥2 campaign gets a dedicated home.  `[NormedSpace ℝ E]`
only — the atom uses only fibre data, and both dependency layers (`MetricCovDerivLinear:42`,
`AllTimesBounds:560`) are NormedSpace-only, so the InnerProductSpace consumer can still use it.

### What discharges the `sorry` (two ingredients, one genuinely new)

1. **THE FRONTIER — `connDiff_koszul_deriv2` (does NOT exist; grep-confirmed).**  The a=2 differentiated
   Koszul identity of §2, plus its a=2 dual core (analogue of `ConnDiffDerivBound`'s private
   `covDerivConnDiff_g1_le`) yielding `|∇₂²A|` in metric-jet currency.  This is a new
   differential-geometric identity of the same character/size as `connDiff_koszul_deriv` (B2 session 5,
   ~150–300 lines, needed the differentiation engines `metric_leibniz_extDeriv`,
   `nablaMetric_combo_extDeriv`, `nabla0SFun_eval_smooth_slots`).  Canonical home upstream:
   `Geometry/Connection/LeviCivita/` next to `connDiff_koszul_deriv`.
2. **MECHANICAL — the a=2 base-Leibniz operator identity** `∇₂²(A⋆S) = (∇₂²A)⋆S + 2(∇₂A)⋆∇₂S + A⋆∇₂²S`
   (a=2 analogue of `diffStep_leibniz`, `MetricCovDerivLinear.lean:516`, pure `covStep`/`diffStep`
   algebra), then the fibre Cauchy–Schwarz product bound composing the a=0 atom `|A| ≲ √(Λ³)Λ'`
   (`lcDiff_norm_le`), the a=1 atom `|∇₂A| ≲ Λ⁴(Λ''+ΛΛ'²)` (`covDerivConnDiff_gJet_le`), and the a=2 atom
   from (1).

## 4. a = 2 VERDICT — not a direct extension

Task 3 asked to prove a=2 **iff** it is a direct extension of committed pieces.  It is NOT: the only new
atom (§1, term I.a) is `∇₂²(A ⋆ S)`, whose bound needs `|∇₂²A|`, whose only route needs the new identity
`connDiff_koszul_deriv2` (§3.1).  That identity is genuinely new machinery (grep confirms no
`covDerivConnDiff2` / `koszul_deriv2` / iterated-connection-difference-jet exists in the tree).  Per the
brick's instruction, machinery NOT built; the `sorry` in `covStepDiff2_exists_const` is the single
remaining visible frontier.

## 5. HONEST SIZE ESTIMATE

- `hAcc` is the LAST mathematical piece of **UNIF item 6**; item 6 is one lane of the multi-week HCG
  compactness project.  So `hAcc a≥2` is a small fraction (~1–2%) of the whole HCG project, but it gates
  item 6's completion.
- **a=2 alone (this atom):** the `connDiff_koszul_deriv2` identity + dual core dominate; mirrors B2
  session 5. Estimate ~2–4 focused sessions.  The base-Leibniz assembly (§3.2) and the `hAcc m=2`
  glue (in `UnifCovSumCross.lean`, the NEXT brick, out of scope here) are each ~1 session of bookkeeping.
- **General a ≥ 2 (all orders / uniform-in-a):** substantially more.  Cleanest is a general-`a`
  `covDerivConnDiffN` object + a Faà-di-Bruno schematic + the per-order Koszul recursion (§2).  This is a
  genuine multi-session-to-multi-week infrastructure project.  Reaching order 2 (this atom) is the first,
  gating step and validates the recursion currency.
- **Theorem vs machinery (per CLAUDE.md honest split):** the `hAcc a≥2` frontier is **0% proved**; its
  dedicated machinery for a=2 is **~0% built** (the differentiated-Koszul-2 identity does not exist).
  The RECON + interface (route ruled, atom stated green, reduction pinned) is complete — but that is the
  scaffolding, not the theorem.

## 6. INFRA-MAP CROSS-CHECK — no false wall

`ConnDiffDerivBound.md`'s "Infra map verdict" flagged as genuinely missing "∇ of `connDiff` as a tensor
field fed through `tensorRSCovariantDerivative`/`covGrad`" — i.e. route (ii)'s bundled object.  This recon
**agrees** it is missing AND shows route (ii) is the wrong route (B2 bypassed it).  **No existing engine
was found that the map missed**: the a=2 atom `∇₂²A` (route i's object) is genuinely absent
(grep-confirmed).  The useful nuance the recon adds: the missing piece is SMALLER/cleaner than route (ii)
implied — a per-order Koszul-differentiation identity that reuses the committed a=1 engines and stays in
`metricCovDeriv` currency, **not** a bundled-tensor covariant-derivative Leibniz theory.  Route (i) makes
`∇₂^a A` a clean recursion rather than a new fibre-norm bundle project.

## 7. ENV / Lean lessons

- **Working-checkout cwd trap (cost 3 tool calls).**  `E:\testdifferential-geometry` (the DEFAULT cwd of
  both the Bash and PowerShell tools) is STALE; the primary tree is `E:\testdifferential-geometry-ste-align`.
  File ops must use absolute ste-align paths; Bash needs `cd /e/testdifferential-geometry-ste-align`;
  **PowerShell/lake needs `Set-Location E:\testdifferential-geometry-ste-align` first** or `lake env lean`
  reports "no such file" and `lake-locked.ps1 check` reports "No existing Lean files to check" (its
  Test-Path guard fails in the stale tree).  The `lake-locked claim` succeeds even in the wrong tree (it
  does not Test-Path), which masks the mistake — always `Set-Location` before lake.
- The atom statement elaborates `[NormedSpace ℝ E]`-only.  Confirms `covStep`/`diffStep`/`normSq0S`/
  `MetricCovDerivOrderBoundOn` are all InnerProductSpace-free; `ConnDiffDerivBound.lean` carries
  `[InnerProductSpace ℝ E]` only for its `covGrad`/`connDiffSection` P1 machinery, which the atom avoids.
- Existential-constant (`∃ C₂ ≥ 0, ∀ S x∈K, …`) is the right honest interface for a state-before-prove
  frontier whose constant is not yet derived: it asserts uniformity (C₂ independent of S, x) without
  committing to a wrong polynomial, and still supplies the consumer's `Racc`/`hRnn`.  An
  existential-at-a-fixed-point would be vacuous — the `∀ S x∈K` inside is load-bearing.
