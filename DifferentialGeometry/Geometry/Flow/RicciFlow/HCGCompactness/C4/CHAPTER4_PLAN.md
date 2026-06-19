# MSM135 Chapter 4 (Theorem 3.9 / `metricCompactness`) — backlog

**Endpoint:** discharge `metricCompactness` (`MetricCompactness.lean:309`, the lone
`sorry` = the whole Cheeger–Gromov construction) by assembling Steps A→D.

**Rule:** one Lean declaration per book result, in book order. Honest-input fields
ONLY where the book itself cites an external theorem (`lbl384`, the Rauch comparison
in `lbl387`, the Hessian comparison `lbl413`). Everything the book proves, we prove.
Build via `& .\scripts\lake-locked.ps1 build +<Module>`; no `sorry`/admissions;
`#print axioms`-clean.

Legend: `[x]` done & verified · `[~]` honest-input (book-external) · `[ ]` todo.

> **Maintenance note (2026-06-11):** done items are collapsed to a one-line
> `→ file:decl` pointer; full build history lives in each file's same-name `.md`.
> The old `ApproximateIsometry.lean` monolith was deleted — its green interface is
> in `ApproxIsometryDefs.lean`, its broken proofs in `ApproximateIsometryArchive.md`.
>
> **Relocation (2026-06-17):** the 21 Ch4-exclusive modules now live in
> `…/HCGCompactness/C4/` (git renames; targeted-build-only, as before — the umbrella
> imports none of them). **Stay in the parent `HCGCompactness/`** (Ch4-content but
> shared with the active Ch3 chain, so not moved): `MapConvergence`, `ArzelaAscoli`,
> `Lemma45Engine`(+`CovariantAbstract`/`SumLemmas`/`Constants`), `MetricCompactness`,
> plus the foundational layer (`Basic`, `PointedRiemannian`, `PointedConvergence`,
> `BoundedGeometry`, `InjectivityRadius`) and the Ch3 P-track. `C4/` is therefore not
> self-contained: it imports up to the parent for those shared engines.
>
> **Dependency-graph fact (2026-06-17):** item-3a is **UNCONDITIONAL** — proved via
> normal coordinates (`Comparison/ExpBallDiffeo.lean:exp_isLocalDiffeomorphOn_ball` →
> `exists_expBall_diffeo_of_lt`), NOT via the Jacobi/Grönwall route. So the
> nonsingularity tower (`Comparison/Variation/CovariantGronwall.lean:covGronwall_ne_zero`,
> `Comparison/ExpNonsingular.lean`, `Metric/InnerExpansion.lean`, and the ∞→finite-order
> parallel-transport refactor in `Comparison/Variation/ParallelTransport.lean`) is **OFF
> the Theorem 3.9 critical path** — reusable global-geometry analysis (no-conjugate-points
> Grönwall), the natural native route to Step B `lbl395` metric bounds, NOT an item-3
> dependency. Do not re-couple it to item-3.

---

## DONE — where to find it

**Approx-isometry interface (F1-def, F1-metric).** `ApproxIsometryDefs.lean`:
`PullbackMetricTensorData`, `PreApproxIsometryData`, `BookApproxIsometryData`,
`IsApproxIsometryOn`, `IsTwoSidedApproxIsometryOn`, `metricCovDerivNormWith`, the
`ConnDiff*` realization vocabulary, and the dimension constants
(`connDiffOneConst`/`connDiffTwoConst`/`connDiffEpsConst_two`/`_three`/`connDiffCoeff`).

**F1 norm comparison (Cor *Norms of tensors*).** Superseded by the `(0,s)` metric-
equivalence factor: `Comparison.lean:sqrt_normSq0S_le_of_metric_equiv` (the book's
`(1+ε)^{(r+q₂)/2}` = `√(C^s)`) over `normSq0S_le_of_metric_equiv`. The old broken
`bookNormRS_compare` (needed the never-ported `normRS`) is archived.

**F2 — Prop *Distances*.** `Distances.lean`: `pathComp_tangent`, `dist_le_tangent`,
`image_ball_tangent`, `edist_le_of_path_comp`, `lipschitz_sqrt_of_dist_le`,
`image_ball_subset_of_lipschitz_sqrt`.

**F3 — Lemma *Norms of cov. derivs, I*** (`|∇_g^r T|_g ≤ |∇_h^r T|_g + εCΣ_{k<r}|∇_h^k T|_g`).
`Lemma45Engine.lean:lemma45_F3` (component-`compL2` form, sorry-free). Engine:
`hkoszul_of_leviCivita`, `claim1_eps_koszul`, `lemma45_component_bdd` (same file);
`Lemma45CovariantAbstract.lean:lemma45DoubleBdd`; `KoszulDifference.lean:koszul_difference`;
consumes the Claim-1 machinery in `AkMFold.lean` (`claim1`, `P(m)`).

**Good-frame / tower bridge** (the gate for F3→F4's intrinsic lift AND ric_bound R4).
`RicBoundGoodFrame.lean`: `exists_trivONBasis` (smooth gRef-ON-at-a-point frame),
`exists_goodFrame_compBound`, **`compL2_tower_le`** (bounded-Gram `compL2 ↔ √normSq0S`
inequality over a small domain), `gramInv_near_id`;
`KroneckerQuadForm.lean`: `quad_lb_of_near_id`, `quadForm_id_le_pow`,
`sum_posSemidef_mul_posSemidef_nonneg`. (Parallel-session, sorry-free, committed.)

**F5-const / F5 (C⁰) / F6 (scalar).** `Lemma45Constants.lean:compApproxConst`;
`ApproxIsometryComp.lean`: `metricEquiv_trans`, `metricEquiv_comp_eps` (book additive
form), `compEpsAccum`.

**F8tool — Arzelà–Ascoli (Lemma 3.14).** `ArzelaAscoli.lean:arzelaAscoli_subseq_…`;
now also the vector-target core `arzelaAscoli_isCompact_closure` + sequential
`arzelaAscoli_subseq_vec` (proper normed target, used by the F8-engine).

**F9–F13 — direct limit (`lbl379`–`lbl381`).** `Geometry/Topology/DirectLimit.lean`:
`SeqSystem`, `Lim`, `incl`, `incl_injective`, `incl_isOpenMap`, `isCompact_exists`,
`sigmaCompact`, `t2Space` (+ universal property `lift`/`continuous_lift`).

**B0 (normal-coord bounds) stages 1–2.** `Exponential/JacobiVariation.lean:exists_radial_jacobi_radius`,
`Analysis/Calculus/SmoothClamp.lean:exists_smooth_clamp`; smooth exp diffeo
`NormalCoordinates.expMapDiffeo`/`normalChartAt`. See `B0NormalCoordBounds.md`.

**Honest-input fields (book-external).** `GeometricInputs.lean`/`StepAInputs.lean`
(A0 `lbl384` inj-radius decay, A0' Rauch/volume); `StepBInputs.lean` (S6 `lbl418`
exp⁻¹ deriv — `ExpInverseDerivBoundInput`, temporary).

---

## ACTIVE FRONTIER (Track α, no §5 geometry)

- [~] **F4 — Cor *Norms of cov. derivs, II* (`lbl370`).** STRUCTURE done
      (`Lemma45Covariant.lean:lemma45_cor_II_of_intrinsic`, Cor II from the intrinsic
      Lemma I `hF3` + the `√(C^{q₂+r})` factor). **LIFT FRONTIER SOLVED at the lemma
      level (2026-06-11, green, `Lemma45Intrinsic.lean`):** `compL2_tower_eq_gen` (the
      decoupled tower-norm identity — the g-norm of the *gRef*-tower, which the
      parallel matched-metric `B5`/`compL2_tower_le` can't express) + `hF3_term` (one
      `compL2` Lemma-I ineq → intrinsic `hF3` at a g-ON point). So
      `lemma45_F3 → hF3_term → hF3 → lemma45_cor_II_of_intrinsic → Cor II` is now all
      at the lemma level. REMAINING = mechanical assembly (apply `exists_goodFrame_compBound`
      with `gRef:=g` for the g-ON frame; ∃-collection into `lemma45_cor_II_of_intrinsic`),
      gated on the lake lock / live parallel session. See `Lemma45Intrinsic.md`. ⟸ F3, good-frame.
- [~] **F5 (C^p part)** — Prop *Composition of approx isometries, I* derivative side.
      **GREEN sorry-free (2026-06-11): `ApproxIsometryCompHigher.lean:comp_cov_le`** —
      `|∇_{g₀}^r(δ₀+δ₁)|_{g₀} ≤ ε₀ + ε₁·C_p` (same-domain). Fiber Minkowski at a g₀-ON
      basis (`exists_gOrthonormalBasis` + `metricInverseInBasis_of_orthonormal` +
      `sqrt_normSq0S_add_le`) splits the composed tower; the `δ₁` term via
      `lemma45_corII` (F4) + `iterCov_add`. (`[~]` because it rests on F4's one
      assembly-`sorry`; F5 itself is sorry-free.) ⟸ F4.
- [~] **F6 — Cor *Composition, II* (`lbl372`).** **GREEN sorry-free:
      `ApproxIsometryCompHigher.lean:comp_cov_accum`** — the `n`-fold accumulation
      `e n ≤ C·Σ_{i≤n} εᵢ` via the scalar fold `compEpsAccum` (ApproxIsometryComp.lean). ⟸ F5.
- [ ] **F2-book** — Prop *Distances*, pre-approx-isometry form: feed `image_ball_tangent`
      from `PreApproxIsometryData` (no invented pullback-metric constructor). ⟸ F1-c0, F2.
- [x] **F7** — Def *Cᵖ-convergence of maps* + *C^∞-conv. on compacts* (`lbl373`).
      **GREEN sorry-free (2026-06-11): `MapConvergence.lean`** — `mapDerivNorm`,
      `MapCPConvOn`, `MapCInfConvOnCompacts` (Euclidean `iteratedFDeriv` form, parallel to
      `PointedConvergence`'s `Metric*` names) + order/subset/subseq API + the bridges
      `mapCPConvOn_of_tendstoUniformly`, `tendstoUniformlyOn_of_cPConv`, `tendsto_of_cInf`.
- [~] **F8** — Cor *Compactness of a sequence of isometries* (`lbl374`).
      **ASSEMBLED sorry-free (2026-06-11): `IsometryCompactness.lean`** —
      `isometry_seq_cInf` (convergence core) + `comp_eq_id_of_cInf` (invertibility, fully
      proved) + `isometry_seq_diffeo` (full `lbl374`, incl. the `C^∞` diffeomorphism limit
      via the symmetry argument). With the F8-engine now PROVED, `lbl374` is reduced to
      ONLY the honest-input `IsometryDerivBounds` (the `lbl375`→[H6] §5 derivative
      bounds). The plan's "apply F8tool" understated it: the scalar `ArzelaAscoli` tool is
      not directly enough. ⟸ **F8-engine** (done), F8-input.
- [x] **F8-engine** — *Arzelà–Ascoli for maps* (`MapConvergence.exists_cInf_subseq`).
      **PROVED sorry-free + axiom-clean (2026-06-11)**: smooth `Φₖ` with all `∇ʳΦₖ`
      bounded on compacts ⇒ `C^∞`-on-compacts convergent subsequence + smooth limit.
      Actual route (deviations recorded in `MapConvergence.md`): equicont/MVT →
      vector AA (`arzelaAscoli_isCompact_closure`, proper target; NEW
      `cmm_finiteDimensional` fills the Mathlib gap for `ContinuousMultilinearMap`) →
      diagonal-free compact countable product over all orders →
      `hasFDerivAt_of_tendstoUniformlyOn` on unit balls assembling a full
      `HasFTaylorSeriesUpTo ⊤` of the limit. ⟸ F8tool(scalar+vector).
- [~] **F8-input** — honest-input `IsometryDerivBounds` (`lbl375`→[H6] §5): isometry +
      bounded uniformly-Euclidean metrics ⇒ all `∇ʳΦₖ` bounded on compacts (book externalizes
      the polynomial recursion to [H6] §5).

---

## §5 Supporting: distance / exp⁻¹ derivatives — PARKED

Blocked on GlobalGeometry `sorry`s (minimal geodesics `HopfRinow.lean:119`; Gauss
lemma `GaussLemma.lean:687`) + no Mathlib cut-locus/Riemannian-gradient/exp API.
Leave as-is; merge external global-geometry code later, then revisit.

- [ ] S1 `lbl411` ∇d² · S2 `lbl412` Hess d² · [~] S3 `lbl413` Hess comparison (honest-input)
      · S4 local convexity · S5 `lbl417` convex balls · [~] S6 `lbl418` exp⁻¹ deriv (honest-input).

---

## §2 Step A — good coverings (`L783–1369`) — METRIC CORE DONE

**Done (2026-06-08/09, verified + axiom-clean; see `ch4-thm39-stepA` memory +
`GoodCovering.md`/`GoodCoveringOrdered.md`):** A1 (λ), A2 Zorn net + the book's
distance-ORDERED greedy net (`GoodCoveringOrdered.lean`, abstract
`[MetricSpace][ProperSpace]`), A3 cover/count, A4 finite cover, A5/A6, A7 `lbl390`
window, A8 `lbl391` radii, A9–A13, and the **capstone
`GoodCoveringSeq.lean:exists_stableNetData`** = `lbl383` items 1,2,4,5,6,7 on a
diagonal subsequence. ONE deferred `sorry`: `GoodCoveringOrdered.lean:
exists_proper_realization` (the user-approved Hopf–Rinow black box). Honest inputs:
A0 `lbl384` CGT decay, A0' PackingBound/ratio-ballMult (Bishop–Gromov), RealizesEdist.

- [ ] **A-item3 — `lbl383` item 3** (exp∘L diffeo at λ-scale + geodesic convexity):
      the ONLY remaining Step A content. UN-PARKED 2026-06-11 (user: full 3a+3b);
      brick plan + status in `Geometry/Comparison/ConvexBalls.md`. **DONE sorry-free
      (2026-06-11):** B1 (`ConvexBalls.lean:isConvexWith_smallNormalBall`, lbl417) ·
      B2 (`ExpBallDiffeo.lean:exists_diffeo_of_injOn` [Mathlib-TODO glue] +
      `exists_expBall_diffeo`) · B3-pieces: ODE heart
      (`SecondOrderGronwall.lean:gronwall_sub_linear`/`gronwall_ne_zero`) ·
      ℓ²/ON-frame (`InnerExpansion.lean`) · frame producer
      (`PerpFrame.lean:exists_parallel_frame`) · KEYSTONE
      (`CovariantGronwall.lean:covGronwall_ne_zero`) · the **∞→finite-order
      refactor** of the parallel-transport chain (5 thms in `ParallelTransport.lean`
      + callers) so the clamped radial curve (ContMDiff 8) qualifies · injectivity
      reduction (`ExpNonsingular.lean:mfderiv_exp_injective_of_jacobi`).
      **B3 RESOLVED 2026-06-13 — item-3a COMPLETE & UNCONDITIONAL.** The Jacobi/Grönwall
      nonsingularity tower was UNNECESSARY for `hloc`: `ExpBallDiffeo.lean:
      exp_isLocalDiffeomorphOn_ball` discharges it directly from
      `NormalCoordinates.expMapDiffeo` (exp IS a partial diffeo via normal coords;
      source ⊇ ball), and `exists_expBall_diffeo_of_lt` is the unconditional item-3a
      ball-diffeo producer. **3b** = `ConvexBalls.lean:isConvexWith_smallNormalBall`
      (lbl417 assembly) modulo the §5 honest-inputs (Hopf–Rinow join selector + lbl416
      d²-Hessian-convexity, both = the plan's approved §5/`lbl413` boundary).
      **B5 DONE 2026-06-13 — ITEM 3 COMPLETE at the brick level.**
      `GoodCoveringItem3.lean`: `PointedRiemannianManifold.exists_expBall_diffeo` (layer
      bridge net-manifold → exp ball diffeo) + `Item3RadiusInput` (honest-input, book's
      "`D` large enough" §5 scale) + `exists_seqItem3Diffeo` (net-level `lbl383` item 3:
      every live center carries the exp ball diffeo). So item 3 = 3a
      (`exists_expBall_diffeo_of_lt`, unconditional) + 3b (`isConvexWith_smallNormalBall`,
      §5 honest-inputs) + net wiring (`exists_seqItem3Diffeo`, §5 radius honest-input).
      Optional: fold `exists_seqItem3Diffeo` into the `exists_stableNetData` capstone as a
      field (presentation only). The Jacobi/Grönwall bricks (keystone, ExpNonsingular, ∞→N
      refactor) are reusable analysis, now relevant to Step B `lbl395`, not item 3.
      **⟹ STEP A (faithful, book-benchmark) = COMPLETE modulo the declared black boxes**
      (Hopf–Rinow, A0/A0' decay+volume, §5 `lbl413`/`lbl416` convexity + C²-radius scale).

## Convergence spine — canonical analytic interface (RULING 2026-06-17)

One convergence API across Steps B/C/D; do NOT spawn a parallel hierarchy.

- **State every new Step B/C/D convergence/limit fact `U`-relative** on
  `MapConvergence.MapCInfConvOnCompacts U` (the maps/metrics live on bounded Euclidean
  balls, not `Set.univ`), produced by the localized engine
  `MapConvergence.exists_cInf_subseq_on` (B-loc). Use the global
  `exists_cInf_subseq`/`MapCInfConvOnCompacts Set.univ` only for genuinely total maps.
- **Diffeomorphism limits** (transition maps, gluing) go through
  `IsometryCompactness.isometry_seq_diffeo` — its output (`PartialDiffeomorph` + the
  `Ψ∘Φ=id` cocycle) IS the `lbl394` transition-limit shape. No new isometry-compactness
  machinery.
- **Metric limits**: a metric in chart coords is a `MapCInfConvOnCompacts U` of the
  Gram-form-valued map `E → (E →L E →L ℝ)`; reuse the map engine, no metric-AA.
- **The pointed-CG-source vocabulary** (`MetricCompactness.lean`'s `MetricSourceCPConvOn`/
  `MetricCGConvergenceData`) appears ONLY at the **D5 endpoint**, reached by ONE bridge
  from the assembled local Map-convergence. The metric-side (`MetricCPConvOn`, LC
  covariant deriv) and map-side (`MapCInfConvOnCompacts`, Euclidean `iteratedFDeriv`)
  stay **parallel + bridged**, never unified (CLAUDE.md variant rule: different concept).
- Reusable Euclidean-analysis engines (`MapConvergence`, `MapConvergenceDeriv`,
  `ArzelaAscoli`, `DiagonalSubseq`) are promotion candidates to `Analysis/` post-completion
  (principle 1, "liberate buried byproducts"); deferred while Step B/C/D are in flight.

## §3 Step B — local metrics & transition maps (`L1370–1882`)

B0 stages 1–2 done (above); B0 stages 3–5 (x-derivative Grönwall) remain. **Spine:** use
the convergence-spine ruling above (B-loc `exists_cInf_subseq_on` + `isometry_seq_diffeo`).
`lbl395` (normal-coord metric bounds) is honest-input (book cites [H6] Cor 4.12); the
Jacobi/Grönwall tower (now off the item-3 path) is the native-discharge candidate for it.

- [ ] B1 `lbl397` approx-iso on a large ball ⟸ A14, S6/A0', B0', F1 · B2 `lbl399` ·
      B3 `lbl402` · B4 `lbl403` · B5 `lbl404` · B6 `lbl405` (`F_{kℓ,r}` is (ε,p)-pre-approx). ⟸ F1–F6.

## §6 Step C — nonlinear averages (`L2638–end`)

- [ ] C1 `lbl429` center of mass ⟸ S5 · C2 `lbl430` · C3 `lbl434` averaging maps ·
      C4 `lbl436` average-of-→id-maps →id. ⟸ B6.

## §4 Step D — directed system, limit, assembly (`L1883–2102`)

- [ ] D1 `lbl406` · D2 `lbl407` ⟸ F8 · D3 build `M_∞` ⟸ F9–F13 · D4 completeness ·
      **D5 ASSEMBLY: discharge `metricCompactness`** from D1–D4 + maps + convergence.

---

## Critical path (updated 2026-06-17)

**DONE:** Step A (metric core + item 3, modulo black boxes) ; F-track F1/F2/F3/F5/F6 green,
F7/F8 done (F8 needs only the honest-input `IsometryDerivBounds`), F4 carries one mechanical
assembly-`sorry`. **LIVE frontier:** `B1→…→B6  →  C1→…→C4  →  D1→D2→D3→D4→D5` (D5 = discharge
`metricCompactness`), all on the convergence-spine ruling above. Remaining non-B/C/D todo:
F2-book, F4-assembly.

**Off the critical path (reusable analysis, do NOT re-couple to Thm 3.9):** the
Jacobi/Grönwall nonsingularity tower (`CovariantGronwall`/`ExpNonsingular`/`InnerExpansion`
/∞→finite parallel-transport) — item-3a is unconditional without it; it is instead the
native-discharge candidate for Step B `lbl395`.

**§5 status:** item-3's §5 dependence collapsed (item-3a unconditional via normal coords).
The remaining §5 surface is honest-input only.

Honest-input boundary (total): A0 `lbl384`, A0' Rauch/volume, `lbl395` ([H6] Cor 4.12
normal-coord metric bounds), S3 `lbl413` / `lbl416` (convexity + C²-radius scale), S6
`lbl418` (`ExpInverseDerivBoundInput`), F8 `lbl375`/[H6] §5 (`IsometryDerivBounds`), Step A
Hopf–Rinow (`exists_proper_realization`). *(Open question for Step B: whether S6 is
derivable from `lbl395` + the F8 bound-propagation, shrinking this set.)*

**Shared with Chapter 3:** the good-frame producer (`RicBoundGoodFrame.lean`) is the
same gate as ric_bound's R4 (`RicBound.lean` endpoint, `RicBoundAssembly.aN_intrinsic_point`);
and the convergence spine (`MapConvergence`/`exists_cInf_subseq`/`isometry_seq_diffeo`) is
consumed by Ch3's P3 metric-preconvergence too.
