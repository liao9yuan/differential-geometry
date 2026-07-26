# FORWARD_UNIQUE_PLAN — filling black box (B) `ricci_flow_forward_unique`

Planner: the (B)-lane Fable session (charter: `FORWARD_UNIQUE_CHARTER.md`, 2026-07-24).
Branch `codex/analytic-producers-e87b`, worktree
`C:\Users\liao9\.codex\worktrees\e87b\testdifferential-geometry`, buildDir `C:/dgb2/e87b`.
Coordination contract with the (N) session: charter §4 (binding).

## Target

`DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/ExtendViaUniqueness.lean:201`
(`ricci_flow_forward_unique`): two flows `g₁ g₂ : ℝ → SmoothRiemannianMetric I M` on
`Ico a b`, closed `M` (CompactSpace, boundaryless, finite-dim, dimension-GENERIC),
chart-Gram jointly C∞ on `Ioo a b ×ˢ baseSet`, chart-Gram C⁰ on `Ico a b ×ˢ baseSet`,
both satisfy `HasDerivWithinAt (fun s => (g s).inner x v w) (−2·ricciTensor (g t) x v w)
(Ici a) t` for `t ∈ Ico a b`, and `g₁ a = g₂ a` ⟹ `g₁ t = g₂ t` on `Ico a b`.

Honest numbers: theorem 0% (sorry live). Dedicated machinery: `ricciEdgeMetric`
VERIFIED; `RicciEdgeBounds.lean` 07-19 additions + `DeTurckUniqueWindow.lean` +
four TMR drafts source-only (0% until real build — in verification now).

Sole consumer: `MaximalTime.lean:264` (`extends_of_rmBounded`, which is stated with
`hdim : finrank ℝ E = 3`). Instantiation there: `a := t_star`, `b := omega`,
`g₁ := g_fam` (ambient flow; jointly smooth TWO-SIDEDLY near `t_star` whenever
`t_star > α` — but (A) currently only guarantees `t_star ∈ Ico α omega`, so `t_star = α`
is possible and must be excluded by a Brick-V strengthening, see §Surgery),
`g₂ := rr(·−t_star)` (the (N)-box restart; edge regularity = whatever (N) outputs).

## Mathematical position (established 2026-07-24, planner recon)

1. **The C⁰ edge is the entire difficulty.** GSM77's RDT uniqueness
   (tex `chapter7.tex:2047`) runs in the class `A⁻¹g̃ ≤ g ≤ Ag̃`,
   `|∇̃g| + √t|∇̃²g| ≤ A`; its RF corollary (tex `chapter2.tex:1609–1657`) needs the
   harmonic-map heat flow gauge and is stated for flows smooth up to the initial
   time. For flows smooth on `Ico a b` slabs, all class bounds are free on compact
   sub-slabs. The stated (B) grants only interior-C∞ + C⁰-at-`a` + pointwise PDE at
   the edge; no derivative rates at `a` follow logically from these (the pointwise
   PDE yields only per-direction improper-integral convergence of Ric — far below
   `√(t−a)`-weighted C² control). Prior audits agree (`ExtendViaUniqueness.md`
   §VERIFIED item 1; `RicciEdgeBounds.md` routes 1–3 + Burkhardt-Guim comparison).
2. **(B) as stated is faithful only to Burkhardt-Guim-type regularizing-flow
   uniqueness** (arXiv:1907.13116 Thm 5.4), whose formalization is costed in
   `RicciEdgeBounds.md` as a new Koch–Lamm-type parabolic foundation (rough C⁰
   RDT solver with common horizon + C⁰ stability + limiting-isometry bridge).
   Not a citation-sized adapter. The four TMR drafts + `MovingMass.md` record that
   even the low-regularity gauge carrier does not close at the C⁰ edge.
3. **The consumer does not need the C⁰-edge class.** `rr` is produced by the (N)
   DeTurck box; for SMOOTH initial data the DeTurck construction genuinely yields
   joint smoothness UP TO t = 0 (`Ico`-slab chart-Gram C∞), strictly stronger than
   the C⁰ field (N) currently promises. `g_fam` is smooth two-sidedly at any
   interior `t_star > α`. Hence a statement surgery (below) makes (B) the honest
   textbook smooth-class theorem with no loss to any consumer.

## Statement surgery (Option 1 — REQUIRES user + (N)-session sign-off)

- **(N) `ricci_flow_unif_existence`**: strengthen the output regularity field from
  `ContMDiffOn … (Ioo 0 τ₀ ×ˢ baseSet)` (+ separate `Ico`-C⁰ field) to
  `ContMDiffOn … (Ico 0 τ₀ ×ˢ baseSet)` (C⁰ field then derivable, may keep or drop).
  Faithful: standard DeTurck short-time existence from smooth data is C∞ on
  `[0,τ₀) × M` (GSM77 vocabulary; no compatibility obstruction at a smooth initial
  corner). OWNER: (N) session — needs their ack; it can only make their box match
  the textbook MORE closely, and (N) is currently a `sorry`, so no proof breaks.
- **(A) `ricci_flow_interior_restart`** (my file, Brick V is proved): conclusion
  `t_star ∈ Ioo α omega` (strict interior; proof: max with the midpoint `(α+ω)/2` in
  the `t_star` choice — all four constraints still met), and thread the `Ico`-C∞
  field for `rr`. Mechanical repair of the existing proof.
- **(B) `ricci_flow_forward_unique`**: hypotheses become chart-Gram
  `ContMDiffOn … (Ico a b ×ˢ baseSet)` for both flows (C⁰ fields dropped as
  subsumed); PDE + initial equality unchanged. This is the textbook smooth class.
- **`MaximalTime` rewiring**: `h1smooth` on `Ico t_star omega` from `hsmooth_left`
  restricted (needs `t_star > α` from new (A)); `h2smooth` on `Ico` from the
  strengthened (N) field. Mechanical.

Consumer-supply check done 2026-07-24: with `t_star ∈ Ioo α ω`, `Ico t_star ω ⊂ Ioo α ω`
so the `g_fam` side restricts; the `rr` side is exactly the strengthened (N) output
shifted; `extend_construction_of_restart` (Brick U) needs NO change (its `Ioo`/`Ico`
fields are weaker than the strengthened supply).

**Honest cost accounting for the (N) strengthening (2026-07-24).** Today (N) is a
`sorry`, so the edit is free; but the (N) lane is ACTIVELY discharging it
(`UNIF_EXISTENCE_PLAN.md`), and `Ico`-C∞ output adds a real future obligation:
smoothness up to the initial corner in the maximal-regularity framework (classical
time-derivative/compatibility bootstrap at `t = 0` for smooth data — standard but
not free). No half-measure suffices: Route K needs coefficient bounds
(`sup |Rm_i|, |∇Rm_i|, |∇²Rm|`, metric equivalence) UNIFORM down to `t = a` on the
`rr` side, i.e. ~C⁴-up-to-edge at minimum; mere C¹-in-time at the edge does not
close the Gronwall constant. And no consumer-side dodge exists: applying (B) at
`[t_star+η, ω)` requires `g_fam(t_star+η) = rr(η)`, which is what uniqueness is
supposed to prove — circular. So the real choice is (N)-strengthening (+ smooth-class
(B)) vs Route BG (no statement change, far larger new parabolic foundation on the
(B) side). Both sessions + user must weigh; Pro consult asked to rule.

## Route decision — RESOLVED 2026-07-25 (GPT Pro ruling, user-relayed)

**Ruling** (full archive + verbatim + K1 kickoff prompt =
`FORWARD_UNIQUE_PRO_RULING.md`): statement surgery APPROVED (exact minimal
signature changes; KEEP the redundant C⁰ fields); Burkhardt-Guim rough-C⁰
route REJECTED; proof route = **(K) Kotschwar energy with MOVING g₁(t)
carrier** (fixed-ḡ ruled sound-but-wrong-formulation), dimension-generic;
brick board K1 (∂ₜΓ-difference, pure subtraction) → K2
(divergence-form Rm-difference evolution with flux U — the dominant brick) →
K3 (triple-energy exact differentiation) → rate estimate → edge-Gronwall →
integral-zero-to-equality. (N)-lane corner bootstrap ruled standard/medium
(a-posteriori bootstrap on the fixed horizon; NEVER shrinking per-order
horizons; fallback = finite edge-order contract for K, never rough-C⁰).
Stop gates: (N)-gate (shrinking horizons) and K2-gates (global representation
change / Shi-architecture modification / IBP cannot pair div₁U against S
invariantly) — details in the ruling file.

**MERGE COMPLETE — FREEZE LIFTED (2026-07-25).** e87b was fully merged into
ste-align at `8a3ce03e8` (whole-branch merge; parent chain includes the lane
tip `d52850842`). Merge fidelity verified by the (B)-lane planner: zero e87b
commits missing, all nine lane files byte-identical, the merge-adaptation
commit (`acdac880a`) touched no lane file. The lane's PRIMARY TREE is now
`E:\testdifferential-geometry-ste-align`; this copy of the plan is canonical
(the e87b copy is an archive). Root-aggregate wiring done here: the three
GREEN leaves (`RicciEdgeBounds`, `TimeLocalNemytskii`, `RadialMixedBound`)
imported into `DifferentialGeometry.lean`; the broken (`TimeTameFixedPoint`,
`MovingMass`) and blocked-upstream (`DeTurckUniqueWindow`, `MovingEdgeEnergy`)
leaves deliberately NOT in the aggregate. Next action = Stage-1 surgery, then
dispatch the K1 kickoff prompt from the ruling file.

*(Historical freeze note, superseded: implementation was frozen on e87b
pending this merge.)*

**ste-align overlap verification (2026-07-25, planner)**: file-level overlap of
this lane's work with ste-align ≈ ZERO — the four TMR drafts, RicciEdgeBounds,
DeTurckUniqueWindow, MovingEdgeEnergy, StrongSolutionUniqueness, HarmonicTension,
DeTurckNaturality, and the three broken modules do not exist there (declaration
grep zero hits); the two (0,2) Duhamel lemmas are identically hard-coded in
both trees. The one real precursor: ste-align's `SHORTTIME_MERGE_PLAN.md` §3
U-track ((B) via gauge, "keep the statement as cited") + its 07-14 audit
(gauge = real analytic frontier) — both now SUPERSEDED by this ruling
(surgery + Route K). The U-track's "statement stays as-is" decision is
explicitly overturned by the ruling; note this during the merge so the merge
plan's §3 is updated rather than resurrected.

## Route options considered (historical record; superseded by the ruling above)

Candidate proofs of smooth-class (B), ranked by expected formalization cost here:

- **Route K (LEAD): Kotschwar-style L² energy, ungauged, dimension-generic.**
  Fix `b' < b`; both flows smooth on the compact slab `Icc a b' × M`; fixed
  background `ḡ := g₁(a)`; `h := g₁−g₂`, `A := Γ₁−Γ₂` (difference tensor),
  `S := Rm₁−Rm₂`; `E(t) := ∫_M (|h|² + |A|² + |S|²)_ḡ dμ_ḡ`.
  `Ė ≤ C·E + (S-equation: 2∫⟨S, Δ_{g₁}S⟩ + cross terms)`; the `Δ₁` term yields
  `−2∫|∇₁S|²` after IBP; all `∇̄A`- and `∇S`-cross terms absorb by Cauchy–Schwarz
  into `ε∫|∇₁S|² + C_ε E`; Gronwall + `E(a) = 0` (h(a)=0 forces A(a)=S(a)=0 since
  `g₁ a = g₂ a` as SmoothRiemannianMetric, so all spatial jets agree) ⟹ `E ≡ 0` on
  `[a,b']`; sup over `b' < b`. Needs NO parabolic solver, NO harmonic-map heat flow,
  NO maximum principle — only: evolution identities (∂ₜΓ, ∂ₜRm = ΔRm + Q — Shi lane
  has the Rm heat equation), covariant difference calculus, integration layer
  (0-sorry), differentiation under ∫ over compact M, IBP/divergence, Gronwall
  (mathlib). Source: Kotschwar, "An energy approach to the problem of uniqueness
  for the Ricci flow" (closed case needs no weight). Deviation from GSM77's proof
  route (statement unchanged) — flag to user per house rule.
- **Route G (book route): HMF gauge + RDT uniqueness + ODE gauge-back.**
  RDT-uniqueness half exists source-only (`DeTurckUniqueWindow.lean`:
  `chartRD_local`/`chartRD_forward` + continuation; no known math obstruction).
  Missing: short-window HMF existence w.r.t. a time-dependent domain metric
  (the `TimeTameFixedPoint` (r,s)=(1,0) lane was built toward it; geometric
  tension-field producer MISSING), the gauge PDE identity (pushforward of RF by
  HMF is RDT), diffeo persistence/regularity package, then the (existing) ODE
  uniqueness. Three substantial missing producers.
- **Route BG: Burkhardt-Guim regularizing-flow uniqueness** — proves (B) AS STATED
  (no surgery) but requires the rough-C⁰ RDT foundation; costed largest by the
  07-19 audit. Keep as the fallback if surgery is REJECTED.

Decision inputs pending: (i) real-build verdicts on the six source-only files;
(ii) Explore-agent asset maps (gauge side; energy-side evolution identities);
(iii) GPT Pro consult ruling; (iv) user sign-off on surgery + route.

## Asset map (2026-07-24 Explore-agent recon; verify-before-trust per charter §4)

**Gauge side** (all proof-sorry-free; status = per same-name `.md`):
- `Evolution/DeTurckUniqueWindow.lean` [SOURCE-ONLY]: `metric_eq_chartGram`,
  `metric_eq_leftLim`, `chartRD_local`, `chartRD_forward` — full RDT-uniqueness
  continuation from an interior equal time, same fixed background; consumes
  `SmoothStrongPair`/`metricRD_local` (max-reg lane) + `ExtendedSolutionRegularity`.
- `Pullback/HarmonicTension.lean` + `Pullback/DeTurckNaturality.lean` [SOURCE-ONLY]:
  tension algebra complete — `idTension g h = −deTurckVF g h`, `tension_eq_push`,
  `tension_eq_DT`, `connDiff_push`, `deTurckVF_push`, `hmf_neg_gauge`/`hmf_target_gauge`.
- `HamiltonDeTurckPullback(.Flat).lean` [SOURCE-ONLY, conditional]: RDT→RF pullback
  proved MODULO `RawVariationalIdentity`/`h_total_eval` hypotheses (the Φ-family
  ODE-generation is hypothesis, not construction). `DeTurckVFTimeFamily.lean`:
  DeTurck-VF time-continuity for the ODE-solve.
- `ShortTime/DeTurckInitialDataExistence.lean:164`
  `deturck_ricci_flow_parabolic_short_time_existence` — **PROVED sorry-free**
  (per-datum, Sobolev order `4·finrank+10`); caveat: endpoint regularity capped at
  C²/k≤2 in its current statement (per `DeTurckHandoff.md`).
- HMF short-time existence + diffeomorphism persistence: **0%** (the true Route-G
  frontier); `NearIdentity`/`InverseFamily`/`PushforwardVF` source-written support.
- `HCGCompactness/SolutionPullback.lean:484` `isSolutionOn_pullback` +
  `WindowDataPullback.lean:389` `solWindowData_pullback` — **VERIFIED** (2026-06-30)
  but serve the P4/convergence lane, not uniqueness.

**Energy side** (Explore-agent recon 2026-07-24):
- ∂ₜΓ identity EXISTS sorry-free, dim-generic, frame-level:
  `Evolution/Connection/Christoffel.lean` — `christoffelMetricVariation_hasDerivWithinAt`
  (:119), RF-specialized `christoffelEvolutionEquationInFrameOn_of_pairing` (:397);
  intrinsic companions under `Geometry/Connection/LeviCivita/Variation/`.
- Single-flow ∇ᵏRm heat tower EXISTS sorry-free (`NablaRiemannHeatFull.lean` :391,
  `IteratedRmTowerHeatEq.lean`), BUT downstream reaction/commutator bound files
  still carry sorries (`NablaRiemannReactionBound` 1, `NablaRiemannCommutatorBound` 3,
  `NablaRiemannT1Bound` 2, `IteratedRmTowerSolution` 1, `CinftyLimitGlue` 19).
- **NO difference-tensor Rm evolution** (∂ₜ(Rm₁−Rm₂) = Δ(Rm₁−Rm₂)+…) and **NO
  fixed-background (g,Γ,Rm) triple energy** — the true Route-K gap.
- **BUT the DeTurck-gauge metric-difference energy skeleton EXISTS sorry-free**
  (`Analysis/Spectral/Intrinsic/DeTurck/MovingEdgeEnergy.lean`): `movingDiffEnergy`
  (:924, ∫|g₁−g₀|² dμ_{g₀(t)}), `movingEnergy_rate` (:1378, exact HasDerivAt —
  differentiation under ∫ DONE), `movingEnergy_zero` (:1412, Gronwall closure,
  hypotheses = joint smoothness + DeTurck-Ricci PDE both + equal at edge + THE OPEN
  GAP `movingRate ≤ K·movingDiffEnergy`); pairing toolkit toward that gap:
  `edgeArm_energy_le`, `edgePrincipal_half`, `edgeLower_pair_le`, `edgeCore_pair_le`,
  `edgePair_inner` (EdgeDifferenceEnergy/EdgeLowerPairing/EdgeRefoldPairing).
- Infrastructure all sorry-free: differentiation under ∫ over compact M
  (`Analysis/Integration/Measure/FiniteParametricIntegral.lean:24`), tensor IBP
  (`Analysis/Elliptic/ConnectionLaplacian/GreenIdentityAndIBP/TensorConnLapLoweredIBP.lean:252`),
  integral Gronwall (`Analysis/ODE/IntegralGronwall.lean:77`; scalar endpoint form
  `edgeGronwall_zero` at `DeTurck/EdgeStrongData.lean:56`), fixed-background tensor
  norms (`normSq0S`, `metricDiff02Field`, `metricCovDerivNorm`), sharp
  connection-difference Cauchy–Schwarz (`connDiffVec_norm_le`, `diffStep_norm_le`).
- Consequence: the repo's live (Codex-lane) design for (B) was DeTurck-gauge
  single-metric-difference energy (RDT is strictly parabolic ⟹ no triple needed);
  Kotschwar's triple exists precisely to compensate the ungauged degeneracy. The
  route comparison is therefore: (G′) finish RDT-energy coercivity + build HMF
  gauge vs (K) build the triple/difference-evolution layer with no gauge. Both
  need the surgery — the surgery decision is ROUTE-INDEPENDENT and can go to the
  user/(N)-session immediately.
- G′-coercivity decomposition (2026-07-24, planner): under the smooth class the
  gap `movingRate ≤ K·movingDiffEnergy` splits into (i) an integral coercivity
  assembly over the built pairings (`edgePrincipal_half` + `edgeArm_energy_le` +
  reaction bounds), taking the GSM77-class constants (`A⁻¹g̃ ≤ g ≤ Ag̃`,
  `|∇̃g|, |∇̃²g₀| ≤ A`) as explicit hypotheses — pure integral algebra; and
  (ii) a slab-constant producer from the smooth-class fields — TRIVIAL post-surgery
  (compactness on `Icc` sub-slabs; the `RicciEdgeBounds.md` route-1 objection
  applies only when smoothness stops short of the edge). Verified reading of
  `movingEnergy_zero` (:1412): only `Ioo`-smoothness + `Icc`-continuity + PDE +
  `hinit` + `hbound` are consumed, so the closure itself is class-agnostic; ALL
  edge difficulty concentrates in `hbound`'s uniform `K`. Hence G′'s only real
  frontier = HMF existence + diffeo persistence; K's = Rm-difference evolution.

## Stages (RATIFIED by the 2026-07-25 ruling; FROZEN until the ste-align merge)

Post-merge order: Stage 1 (surgery, exact edits per ruling §1) → K1
(`ForwardUniqueConnectionDiff.lean`, kickoff prompt in the ruling file) →
K1-corollary (pointwise |∂ₜA₀₃|² bound) → K2 (`rmDiffLowered_evolution_div_bound`,
the dominant brick, watch the K2 stop gates) → K3 (`forwardUniqueEnergy(_hasDerivAt)`
/`forwardUniqueRate`) → `forwardUniqueRate_le` → edge-Gronwall →
integral-zero-to-equality → K6 endgame (discharge `:201`, shared-file protocol).
(N)-side corner bootstrap proceeds in the sibling lane per ruling §"(N) cost";
their co-sign condition: trace/linear-regularity APIs bootstrap on a fixed
horizon. The draft stage list below is the pre-ruling record.

## Stages (pre-ruling draft; superseded)

- **Stage 0 — verification triage (RUNNING).** Real `lake build` of
  `TimeLocalNemytskii`, `TimeTameFixedPoint`, `MovingMass`, `RadialMixedBound`;
  then `RicciEdgeBounds`, `DeTurckUniqueWindow`. Hygiene repairs mine; statement
  or proof failures → planner ruling (charter №20-style).
- **Stage 1 — surgery sign-off + execution.** User + (N)-session ack; then (N)/(A)/(B)
  statement edits + Brick-V repair + MaximalTime rewiring in ONE coordinated commit
  (shared-file protocol: git status check first, endgame-style edit).
- **Stage 2 — Route K bricks (if ratified):**
  - K1 solution-package bridge: from (B)'s `Ico`-C∞ + PDE fields to the Shi-lane
    solution predicates on `Icc a b'` sub-slabs (reuse `metricFamilySmoothOn_of_chartGram`,
    `isSolutionOn`-builders; NO new predicate).
  - K2 difference calculus: `h`, `A`, `S` as ḡ-tensor fields; pointwise expansions
    `Ric₁−Ric₂`, `∇₁Ric₁−∇₂Ric₂`, `Δ₁Rm₁−Δ₂Rm₂` in terms of `h, A, S, ∇A, ∇S` with
    slab-uniform coefficient bounds (`ricciEdgeMetric` gives metric equivalence).
  - K3 evolution identities: `∂ₜh = −2(Ric₁−Ric₂)` (from the PDE field);
    `∂ₜA = −(g₁⁻¹∇Ric₁-comb − g₂⁻¹∇Ric₂-comb)` (NEW: ∂ₜΓ lemma — check Shi lane);
    `∂ₜS` via the two Rm heat equations (EXISTS in Shi lane — generality check).
  - K4 energy: `E(t)` via the integration layer; `Ė` by differentiation under ∫;
    IBP absorption of `∫⟨S,Δ₁S⟩` and the `∇A`, `∇S` cross terms.
  - K5 Gronwall + continuation: `E ≡ 0` on `[a,b']`, all `b' < b`; conclude
    `g₁ t = g₂ t` via `metric_eq_chartGram`-style extensionality (exists source-only).
  - K6 endgame: discharge `:201` in the shared file per charter §4.
- **Stage 2′ — Route G bricks (if consult overrules):** tension-field producer →
  HMF short-window existence ((r,s)=(1,0) tame fixed point) → gauge identity →
  diffeo persistence → wire `chartRD_forward` → ODE gauge-back.

## Ownership (charter §4; grows as claimed)

- This plan file; `FORWARD_UNIQUE_CHARTER.md` (read-only inherited).
- The four TMR 07-19 drafts (verify/repair): `TimeLocalNemytskii.lean`,
  `TimeTameFixedPoint.lean`, `MovingMass.lean`, `RadialMixedBound.lean`.
- `Evolution/RicciEdgeBounds.lean`, `Evolution/DeTurckUniqueWindow.lean`
  (verification + (B)-lane evolution).
- `ExtendViaUniqueness.lean`: ONLY sorry `:201` + (A)/Brick-V under Stage 1,
  endgame-style, git-status-checked (shared with (N) session — their sorry `:92`).
- `MaximalTime.lean`: Stage-1 rewiring only (coordinate — check (N) in-flight state).

## Dispatch log (planner = Fable auditor; executors = Opus 5, never commit)

- №8 (2026-07-25, ACCEPTED — **K2.4+K2.5 OUTCOME (A)**): **Agent-K2E delivered
  `Evolution/ForwardUniqueRmBounds.lean`** (898 lines, 8 public + 11 private,
  0 sorry; planner re-audit clean). `fluxNormSq_le` (|U|² ≤ s²n^{s+1}|A₀₃|²|T|²,
  instance `rmFluxNormSq_le` 16n⁵) via the proven algebraicity `lapDiffFlux_eval`;
  `remNormSq_le` (two-carrier split, instance `rmRemNormSq_le` 50n¹²/2n¹⁰) with
  the №5-recorded backgrounds as NAMED arguments (`hB₁` |∇²T|², `hB₂` |∇²∇²T|²)
  and one-sided `Λ`-comparison in `ricciEdgeMetric` shape only where needed.
  Inverse-metric difference done frame-wise (no cometric/matrix layer).
  SYSTEMIC CLEANUP ITEM (3rd occurrence): `diffStep_norm_le`/`connDiffVec_norm_le`
  /`MetricBounds.lean` are `[InnerProductSpace ℝ E]`-tainted at the producer —
  a producer-side `omit` on `normSqRS_eq_normSq0S_lowerAllSpace` + the CS lemma
  would delete three private re-proofs now in the tree (add to campaign-end
  dedup list with №3's items). Minor anomaly logged: executor's claim was
  already cleared at release time (registry cleaned concurrently?) — harmless,
  watch for recurrence.
- №7 (2026-07-25, IN FLIGHT → K2E accepted above; K1C still running): third wave, two Opus builders.
  **Agent-K2E** — `Evolution/ForwardUniqueRmBounds.lean`: K2.4 flux bound
  (Cauchy–Schwarz-shaped, |U|² ≤ C·|A₀₃|²·background) + K2.5 remainder bound
  (conn-diff + inverse-metric-diff summands; background norms incl. the
  №5-recorded ∇²∇²T factor as EXPLICIT hypothesis arguments; no hidden metric
  equivalence). **Agent-K1C** — `Evolution/ForwardUniqueConnDot.lean`:
  K1C-a `connDiffDot` invariant-speed adapter (per-x chart-frame route,
  hypothesis-taking like K1 + metric PDEs; feeds K3's `hA` exactly) then
  K1C-b the ruling's |∂ₜA₀₃|² bound (Bianchi/trace bridges; sorry+classify
  allowed). Both: standard protocol, LEAN_NUM_THREADS=3.
- №6 (2026-07-25, ACCEPTED — **K3 OUTCOME (A)**): **Agent-K3 delivered
  `Evolution/ForwardUniqueEnergy.lean`** (414 lines, 10 decls, 0 sorry;
  planner re-audit clean). Exact first variation of the triple energy on an
  open window: `forwardUniqueEnergy/Rate/Density(+Dot)`, `metricDiffDot :=
  −2(metricRicciAt₁ − metricRicciAt₂)` PROVED from the two RF PDEs
  (`metricDiff_hasDerivAt`), rank-s invariant moving-norm repackaging
  (`movingReact0S`, `normSq0S_moving_deriv`) re-derived from GREEN producers
  (`Tensor0SMetricDeriv.lean:828` + `first_var_joint` at
  `Analysis/Integration/Measure/FamilyLocal.lean:223`). AUDITOR RULING R3
  (fork resolved by executor, ratified): the rate carries the A/S speeds as
  plain arguments (`forwardUniqueRate g₁ g₂ Adot Sdot t`) with ∀-shaped
  invariant slot-vector hypotheses `hA`/`hS`; K1/K2 owe the frame→invariant
  adapter producing `Adot`/`Sdot`. APPROVED substitution `metricRicciAt` for
  `ricciTensor` (avoids the model-space `InnerProductSpace` spray; endgame
  bridge = `metricRicciAt_apply_eq_ricciTensor`). NEW LANE DEBTS RECORDED:
  (i) `hdens` — joint (t,x)-smoothness of the density (the chart-Gram → Γ →
  Rm joint tower does NOT exist; honest producer, also needed at K5);
  (ii) relocation TODO: `movingReact0S`/`normSq0S_moving_deriv` → canonical
  home `Tensor0SMetricDeriv.lean`. STATUS CORRECTION: `MovingEdgeEnergy.lean`
  is un-compilable IN ITSELF (16 hypotheses spell `𝒰` U+1D4B0 for `𝓘`
  U+1D4D8) — independently of its broken imports.
- №5 (2026-07-25, ACCEPTED — **K2.3 PROBE OUTCOME (A): GO**):
  **Agent-K2P delivered `Evolution/ForwardUniqueRmDiff.lean`** (369 lines,
  21 public decls, 0 sorry; planner re-audit: `--no-build` up-to-date + axiom
  re-check of `lapDiff_eq_div_flux`/`rmLapDiff_div_flux`/`lapDiffFlux_self`
  clean). **Neither Route-K gate fired.** APPROVED DESIGN SUBSTITUTION: flux
  representative `U₀₅ := (∇¹−∇²)T` (algebraic in A₀₃, `|U| ≤ C|A₀₃|`) instead
  of the ruling's literal `(g₁⁻¹−g₂⁻¹)∇²Rm₂ + g₁⁻¹(∇¹−∇²)Rm₂` — the literal
  form is what would have forced a raised (1,4) intermediate + cross-variance
  module (the Gate-1 shape was an artifact of the representative); the
  difference term moves into the remainder. Divergence-form point PRESERVED
  (no ∇S₀₄ anywhere in U or R). RECORDED COST for K2.4/K2.5: the remainder
  bound now needs the background `|∇²∇²T|` (one extra covariant derivative of
  curvature) — free in the smooth class but must be an explicit slab
  hypothesis. Key identity: `Δ_{g₁}T − Δ_{g₂}T = div_{g₁}U + R` with
  `Δ_g = div_g ∘ ∇^g` and both R summands manifestly differences
  (conn-difference term + inverse-metric-difference term); `rm2Low_eq_sub`
  ties T to the FIELDS carriers (`metricRm04At g₁ − rmDiffLowAt g₁ g₂`).
  DEFERRED (planner-logged): (i) the generic (0,s) operator layer
  (`metricNabla0S`, `covDiv0SField`, `roughLap0SField`, `_sub`/`_zero`
  companions) has canonical homes in `NablaOnTensors/`, `RoughLaplacian.lean`,
  `MetricTrace/NablaTraceGen.lean`, `TotalNabla0SLinear.lean` — relocate when
  a second consumer appears or at campaign end (protocol forbade editing
  existing files); (ii) K2.7 still owes `covDiv0SField` ↔ bundled
  `covDivergence` identification for the IBP hookup (conventions pre-checked
  to agree). NEXT: K2.4+K2.5 estimates dispatched (№6).
- №4 (2026-07-25, IN FLIGHT → K2P accepted above; K3 still running): second wave, two Opus builders in parallel.
  **Agent-K2P** — `Evolution/ForwardUniqueRmDiff.lean`: K2.0 flux `U₀₅` (div
  index slot 0) + the K2.3 go/no-go probe `lapDiff_eq_div_flux` (pointwise,
  two fixed metrics, no time), timeboxed, outcomes A/B/C with Gate-1 shape in
  (C); hazards pre-briefed ((1,3)/(1,2)-variance lowering bridges, three-way
  representation reconciliation). **Agent-K3** — `Evolution/ForwardUniqueEnergy.lean`:
  `forwardUniqueEnergy`/`forwardUniqueRate`/`forwardUniqueEnergy_hasDerivAt`
  (exact differentiation only) consuming the FIELDS Sq-functions; A₀₃/S₀₄
  time-derivatives taken as plain ∀-shaped hypotheses (no new predicates);
  MovingEdgeEnergy as design evidence only (no import — closure broken);
  STOP-fork discipline on hypothesis packaging. Both: LEAN_NUM_THREADS=3,
  wait-poll, no commits, planner acceptance loop.
- №3 (2026-07-25, ACCEPTED): **Agent-F "FIELDS" delivered and accepted** —
  `Evolution/ForwardUniqueFields.lean` + `.md`, 16 public decls, 0 sorry,
  planner-independent re-verification: `--no-build` up-to-date + axiom re-audit
  of the three `_self` lemmas = exactly the standard set. Design NOTE (approved
  deviation): carriers are METRIC-indexed (`g₁ g₂ x`), not solution-indexed —
  weakest honest form (SolutionFamily's only field is `metric`; connection/rm
  are defs of it) and matches the ruling's K3 signature. `S₀₄` needed NO new
  lowering machinery (canonical `riemannCurvature04At g₁ ∇ⁱ` difference —
  representation stop-signal did not fire); only `A₀₃` lowers via
  `lowerAllUpperIndices`. Deferred dedup items (planner-logged, not acted):
  (i) `RSLoweringNorm.lowerAllSpace` needs an `omit [InnerProductSpace ℝ E]`
  at the producer, after which `connDiffOutAt` collapses to it (no consumers
  today, cheap); (ii) private `covDiff_self` is more general than
  `DeTurck.connDiff_self` and belongs in the connection layer. Durable lesson
  (in the .md): `rw` fails on `Tensor0SSpace` fiber algebra via the FunLike
  coercion of a non-reducible def — use term-form
  `have h := Tensor0SSpace.sub_apply … v` instead.
- №2 (2026-07-25, ACCEPTED): **Agent-R "K2-RECON" report accepted** (planner
  spot-grep-verified the two decisive claims verbatim; both files 0-sorry).
  Findings that AMEND the ruling's §6 consume-list: `TensorConnLapLoweredIBP`
  is DIRECTIONAL (fixed vector field) — the correct, hypothesis-free pairing
  theorems are `tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence`
  (`Analysis/Elliptic/ConnectionLaplacian/GreenIdentityAndIBP/TensorCovDivergence.lean:1095`,
  exactly `⟨∇T,V⟩_{L²} = −⟨T, div V⟩_{L²}` at (0,s)/(0,s+1), no integrability/
  frame hypotheses, one metric for connection+inner+measure) and
  `tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs`
  (`…/TensorDirichletCurrentGreenIdentityRS.lean:709`, the −2D principal term).
  **K2 Gate 2 (IBP invariant pairing): CONFIRMED-SAFE.** Divergence convention:
  slot 0 (`contract_covariant`), so U₀₅ carries its divergence index in slot 0.
  Single-flow tensor Rm₀₄ evolution: dim-generic PROVEN version does NOT exist
  (dim-3 only via Kulkarni–Nomizu, banned; `rm04Var_of_sol` is ∇²Ric-form);
  the dim-generic INTERFACE exists: `Riemann04BTensorWithRicciDriftEvolutionInFrameOn`
  (`Evolution/Uhlenbeck.lean:727`) — the repo's own named 06-08 frontier
  (`BBSAllKBundledRoute.md:869`), with the proven dim-generic Ricci analogue
  `coordRicciEvol` (`Evolution/Ricci/CoordinateIdentities.lean:864`) as precedent.
  **PLANNER RULING R1**: K2 proceeds HYPOTHESIS-TAKING — K2.1 takes the
  Uhlenbeck interface (one per flow) as hypotheses, mirroring K1's pattern;
  the endpoint discharge therefore carries the single-flow Rm₀₄ evolution as a
  standing named input until brick **K2-B** (the ~900-line second-Bianchi
  conversion "Lemma 6.1", local to Evolution/Ricci/* + Curvature/Bianchi.lean)
  is separately commissioned. This is an EXPLICIT recorded decision (same
  standing-input status as the BBS pillar), not a silent wrapper. K2-B is
  mathematically unavoidable for the (B) endpoint under Route K — sequence it
  after the K2 difference calculus banks.
  **PLANNER RULING R2**: K2.3 `laplacianDiff_eq_div_flux` goes FIRST, timeboxed,
  as the go/no-go probe (Gate-1 risk lives there: three-way representation
  reconciliation, (1,3)-vs-(0,4/5) lowering bridges). If it demands a new
  cross-variance connection-difference module spanning Geometry/Curvature +
  Analysis/Elliptic, Gate 1 fires → stop and re-consult.
  Full K2.0–K2.7 decomposition (target file `Evolution/ForwardUniqueRmDiff.lean`)
  archived in the recon report; K2.7 bridge = `unitScalarRSLiftCₛ` +
  `HasCompactSupport.of_compactSpace`.

- №1 (2026-07-25, IN FLIGHT): **Agent-F "FIELDS"** (build) — new file
  `Evolution/ForwardUniqueFields.lean`: the three g₁-lowered carriers
  `h₀₂/A₀₃/S₀₄` per ruling §"Recommended tensor variances" + vanishing-at-equal-
  metrics lemmas + normSq evaluation names. Pointwise carriers acceptable;
  hard stops = new curvature representation, new mixed-tensor machinery,
  bundle-dedup instance failures. **Agent-R "K2-RECON"** (read-only) — inventory
  the single-flow tensor Rm evolution identity (tensor-level, not norm-heat),
  roughLap/div operators at (0,4)/(0,5), TensorConnLapLoweredIBP pairing
  readiness, verdicts on the two K2 STOP gates, K2 lemma decomposition proposal.
  Acceptance loop: planner spot-checks (grep sorry/axioms, diff scope,
  protocol discipline), wires the aggregate, commits.

## Status log

- 2026-07-25 (STAGE 1 DONE + K1 DONE, on ste-align): **Statement surgery landed
  per ruling §1** — (N) C∞ field `Ioo 0 τ₀ → Ico 0 τ₀` (C⁰ field kept; docstring
  records the bootstrap contract + anti-pattern); (A) `t_star ∈ Ioo α omega` +
  `Ico 0 TT` field threaded (Brick-V proof repaired: `t_star` gains the midpoint
  arm `(α+ω)/2`, `hαω` now used); (B) `h1smooth`/`h2smooth` on `Ico a b`
  (docstring rewritten: smooth class faithful, ruling pointer). `MaximalTime`
  rewired (ht0 strict bound, `Ico` shift maps, Brick-U `.mono` back to `Ioo`).
  Verification: focused checks green; stale-olean false-fail on MaximalTime
  resolved by the prescribed targeted upstream refresh; authoritative targeted
  builds GREEN (`ExtendViaUniqueness` 136s — only the two black-box sorries;
  `MaximalTime` 140s; downstream `ExtendShiInputs` + `BBSLimitProducer` rebuilt
  green — no other consumer broke). **K1 `ForwardUniqueConnectionDiff.lean`
  VERIFIED**: `christoffelEvolutionDiffInFrameOn` (pure `.sub`) +
  `christoffelDiff_coeff` (coeff `map_sub` identification); first-attempt green,
  linter-clean after `omit` hygiene, axiom audit = exactly
  `[propext, Classical.choice, Quot.sound]` both; wired into the root aggregate;
  neither ruling STOP signal fired (common frame instantiates as-is; no
  global-frame need). Details in `Evolution/ForwardUniqueConnectionDiff.md`.
  NEXT: K1-corollary (pointwise `|∂ₜA₀₃|²` bound), then K2
  (`rmDiffLowered_evolution_div_bound` — the dominant brick, watch its STOP
  gates), then K3. (N)-lane co-sign of the bootstrap contract still expected
  (ruling §"(N) cost"; the strengthened statement is now live in the shared
  file).

- 2026-07-25 (RULING + FREEZE): GPT Pro ruling received via user and archived
  (`FORWARD_UNIQUE_PRO_RULING.md`): surgery approved, BG rejected, Route K with
  moving g₁-carrier, K1/K2/K3 brick board, stop gates. USER DIRECTIVE: e87b
  merges back into ste-align — do NOT implement; K1 kickoff prompt banked for
  post-merge dispatch. ste-align overlap verification done (≈zero file overlap;
  U-track precursor superseded — see §Route decision). Lane state at freeze:
  verified green = `RicciEdgeBounds` (axiom-clean) + `TimeLocalNemytskii` +
  `RadialMixedBound` + the banked Shi/∂ₜΓ/pairing layers; broken-parked =
  `TimeTameFixedPoint`, `MovingMass`; blocked-upstream = `DeTurckUniqueWindow`,
  `MovingEdgeEnergy` (behind `SmoothEmbedInj`/`SmoothPathHs`/`MetricDiffJoint`
  — now only "design evidence" for K3 per the ruling, so the bottleneck is no
  longer route-critical; it matters only if the merge wants those files green).
- 2026-07-25 (Stage 0 wave 3, MovingEdgeEnergy verification attempt): the build
  BANKED a large newly-verified layer directly useful to both routes —
  `Evolution/Ricci.{GammaAlgebra,GammaCoord,Trace,Bianchi,Commutator,
  CoordinateRegularity,CoordinateIdentities,Lichnerowicz}` (the ∂ₜΓ/Ricci
  evolution family), the full Shi tower (`BernsteinShi(Higher)`,
  `NablaRiemann{Heat,HeatFull,TimeDeriv,Commutator(Bound),T1Bound,T2Bound,
  ReactionBound,OrthoFrame,HeatFrameInvariant}`, `IteratedRmTower{HeatEq,
  Producer}`, `Uhlenbeck`, `RmRealizationBridge(AllK)`), plus
  `EdgeDifferenceEnergy`, `DeTurckPrincipalArmEnergyPairing`,
  `Tensor0SMetric{Deriv,…}`, `DeTurckChartRegularityFromJoint` — all ✔ green.
  BUT `MovingEdgeEnergy` itself NEVER ELABORATED: blocked by the SAME three
  broken committed modules as `DeTurckUniqueWindow` (`SmoothEmbedInj` — own
  funext proof bug; `SmoothPathHs` — `NormedSpace ℝ (TensorRSModel …)`
  synthesis failures, the in-flight-dedup signature; `MetricDiffJoint` — missing
  identifiers + parse error, written against a not-yet-existing API, possibly
  the API the dedup is about to introduce). **LANE BOTTLENECK: these three
  modules block BOTH RDT-uniqueness assets.** Per charter §4 the instance-
  flavored breakage is (N)-dedup coordination territory — planner rules:
  DO NOT PATCH; flag to user + (N) session. If the (N) dedup does not repair
  them, negotiating ownership transfer of the three files to this lane is the
  next option.
- 2026-07-25 (Stage 0 wave 2): **`RicciEdgeBounds.lean` GREEN + AXIOM-CLEAN**
  (two mechanical `.symm` repairs by planner; all four public theorems on
  exactly `[propext, Classical.choice, Quot.sound]`) — the edge-bridge family
  (`ricciEdgeMetric/ChartPDE/Integral/Improper`) is settled verified API.
  **`MovingMass` STRUCTURALLY BROKEN** (identifier-level: unknown `tensorHs`,
  free `Ha`/`ET`, `MaxRegSolutionSpace` arity — a sketch against a nonexistent
  API shape; verdict in its .md; PARKED, off every live route).
  **`DeTurckUniqueWindow` BLOCKED-UPSTREAM**: never scheduled — its closure
  hits three broken committed modules `SobolevScale/SmoothEmbedInj`
  (`funext` unification at `:41`), `DeTurck/MetricDiffJoint` (unknown
  identifiers `ccTensorModel_sub`/`contMDiffOn_clm_section_of_pointwise_jointMR`,
  parse error `⟮`, FiberBundle synthesis failures), `DeTurck/SmoothPathHs`
  (`NormedSpace ℝ (TensorRSModel 0 2 ℝ E)` synthesis failures — the charter's
  in-flight bundle-dedup signature). COORDINATION FLAG for the (N) session:
  these live in their Intrinsic/DeTurck lane; per charter §4 I do not patch
  them. `MovingEdgeEnergy` closure also never built (probe: its three direct
  imports missing) — verification build IN FLIGHT (route-critical for G′).
- 2026-07-25 (Stage 0, first authoritative build — ~3h, charted a large
  never-built spectral/TMR subtree into the shared cache): **2/4 drafts GREEN**
  (`TimeLocalNemytskii`, `RadialMixedBound` — .md notes flipped to verified);
  **2/4 FAILED**: `TimeTameFixedPoint` (`:428`, `:644` — its (r,s)-generalization
  calls `timeL2Inclusion_maxRegDuhamelSolField` and `maxRegDuhamelSolField_zero_zero`,
  both hard-coded `(0,2)` in the (N)-lane engine file
  `DeTurckQuasilinearExistence.lean:155/:237`; the draft .md's variance-genericity
  claim is FALSE for these), `MovingMass` (error scrolled; re-running with full
  log). PLANNER RULING: both failures PARKED pending the route decision — they
  are Route-G engine parts (HMF fixed point; mass perturbation), off the
  Route-K path entirely; repair options recorded in `TimeTameFixedPoint.md`.
  Second build in flight: MovingMass (full log) + `RicciEdgeBounds` +
  `DeTurckUniqueWindow` (the two committed source-only Evolution leaves).
  Consult prompt READY (`FORWARD_UNIQUE_PRO_PROMPT.md`) but submission BLOCKED:
  no Chrome browser connected (per protocol, report rather than improvise login).
- 2026-07-24 (session start): charter absorbed; target + consumer read; audits read
  (`ExtendViaUniqueness.md` §VERIFIED + 07-18 execution record; `RicciEdgeBounds.md`
  full; `DeTurckUniqueWindow.md`). GSM77 passages located and read (chapter7.tex:2047
  RDT uniqueness; chapter2.tex:1609 RF corollary via HMF). Mathematical position +
  surgery proposal + route ranking written (above). Stage 0 build launched
  (four TMR drafts). Two Explore agents dispatched (gauge-side + energy-side asset
  maps). NEXT: agent reports → consult prompt → browser submission → user sign-off
  package.
