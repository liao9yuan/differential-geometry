# FORWARD_UNIQUE_PLAN — filling black box (B) `ricci_flow_forward_unique`

Planner: the (B)-lane Fable session (charter: `FORWARD_UNIQUE_CHARTER.md`, 2026-07-24).
Branch `codex/analytic-producers-e87b`, worktree
`C:\Users\liao9\.codex\worktrees\e87b\testdifferential-geometry`, buildDir `C:/dgb2/e87b`.
Coordination contract with the (N) session: charter §4 (binding).

## Target

`DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/ExtendViaUniqueness.lean:189`
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

- №45 (2026-07-26, Agent-WIRE — **K7 OUTCOME (B): THE WIRING PASS LANDED;
  12 OF 16 BUNDLE MEMBERS DISCHARGED; endpoint `:189` DELIBERATELY UNTOUCHED**):
  new file `Evolution/ForwardUniqueWiring.lean` (612 lines, 0 sorry,
  warning-free; focused check + targeted module build GREEN, 9534 jobs; all 9
  public decls 3-axiom clean).  The five `ForwardUniqueInputs` carriers are now
  CONSTRUCTED from (B)'s own fields (`fuAvec`/`fuSvec`/`fuSfield`/`fuUflux`/
  `fuRem`).  Discharged: `gamma` (`gamma_of_gram`), `rm` (`rm_of_uhlenbeck` +
  `rm04EvolFamTail` at the midpoint tail), `sdec` (`sdec_of_uhlenbeck`), `car`
  (by construction), and all seven density-regularity members.  **Two recorded
  walls fell.**  (i) `ForwardUniqueSdec.md`'s "a smooth (0,4) field realizing
  `metricRm04At` is not available as a producer" is WRONG — `metricRm04 =
  rm04Section g (metricCov g)` (`Curvature/Riemann/Basic/Sections.lean:528`)
  is exactly it, and `rm04Section g₁ (metricCov g₂)` builds the second term of
  S₀₄, so `car`/`hT₁`/`hT₂` are `rfl` (6th false wall).  (ii) the `hcont`
  input of `rm_of_uhlenbeck`/`sdec_of_uhlenbeck` (time-continuity of the raised
  curvature), treated as standing everywhere, is PROVED unconditionally on the
  tail (`fuRmContAt`): `raiseAt_lower` + `metricRm04At_inner` make the raised
  curvature the inverse Gram applied to `fuRm04`; `fuEvolTail` gives the
  components' differentiability, `hpde` gives the Gram's, and Mathlib's
  `continuousAt_matrix_inv` + `basisInvMetric_real` close it.  Design note: the
  `RealTimeInterval` index of `rm04Fam`/`rm04LapFam`/`rm04BFam`/`ricUpFam`/
  `solOfMetric` is a PHANTOM (`rfl`-transport, `fuRm04_eq` … `fuRicUp_eq`),
  which is what lets ONE fixed `Svec` serve every interior time while the
  producers only exist on tails.  **Endpoint status**: `forward_unique_of_gram`
  = (B)'s statement + exactly five named hypotheses in three families —
  (1) `hbounds` (the six `ForwardUniqueSlab` estimates; NO producer of that
  structure exists in the tree, and the five named sub-producers all consume
  slab-uniform background norms nothing supplies; `reactLe`'s `movingReact_le`
  still deferred per №25) — DOMINANT; (2) `hpair`/`hrest`/`hrem` (spatial
  continuity of the constructed speed families — tensoriality of a
  per-point-centred frame construction, not a density question); (3) `henergy`
  (closed-edge continuity of the energy).  Three families > the two-gap
  threshold, so `:189` was left intact rather than half-replaced.  Full record:
  `Evolution/ForwardUniqueWiring.md`; discharge record appended to
  `Evolution/ExtendViaUniqueness.md`.  Module NOT wired into the root aggregate
  (planner's step).
- №44 (2026-07-26, α5 ACCEPTED+COMMITTED — **R11 SURGERY LANDED TREE-GREEN;
  K2-B MACHINERY COMPLETE**): the field weakening executed exactly per
  ruling (`InvMetricDerivLocal` added, global predicate KEPT for BlackBox,
  `.toLocal` converter, both structure fields u-local, spacetime
  `congrInv`); consumers/constructors adapted across 8 Evolution files;
  discharge chain `coordInvDt`/`coordInvDerivLocal` (InverseSmooth) +
  `tailCoordFrameReg` (TailFrameRegularity) landed; unconditional tail
  endpoints `rm04EvolTail_at`/`rm04EvolFamTail` in NEW
  `Evolution/Rm04ProducerTail.lean` — the file split forced by the
  IPS-vs-NormedSpace SolutionOn instance-spine mismatch (same reason
  TailChristoffel is a separate file; `Rm04Producer.lean` byte-identical).
  VERIFICATION: α5's full locked build + the planner's INDEPENDENT full
  locked build both green (10654 jobs); whole-tree sorry set = baseline
  MINUS ForwardUniqueConnBound (β4's closure) — NO new sorries, surgery
  cascade fully contained; root aggregate rebuilt green with the tail
  file wired (:1356); tail endpoints 3-axiom by direct lean.  **The K2-B
  brick's machinery is COMPLETE**: hev (per-tail, unconditional from
  S/hS) + hreal + hL all delivered.  REMAINING for the (B) endpoint = the
  single final WIRING PASS at `:189`: build S := solOfMetric g from (B)'s
  fields (IsSolutionOn via the joint producers, K6b precedent), pick the
  midpoint-trick tail, instantiate `rm_of_uhlenbeck`/`sdec_of_uhlenbeck`
  with the Rm04ProducerTail families, discharge `forwardUniqueRate_le`'s
  hAdot from `connDiffDot_normSq_le` (+ hΓ via
  `christoffelEvolution_of_solution` on the same tail), assemble
  `ForwardUniqueInputs`, and replace the `:189` sorry with
  `forward_unique_of_inputs`.
- №43 (2026-07-26, α4 ACCEPTED+COMMITTED — **hcomm CLOSED (static side
  unconditional on S/hS); all three lane-interface items delivered;
  hmetricReg root-caused to an over-quantified structure field; RULING
  R11**): `Rm04Producer.lean` 805→1195 lines, 0 sorry, warning-clean;
  planner re-audit: 6 endpoints 3-axiom.  Delivered: `ricRicciIdAt`/
  `ricCommOfSol` (s=2 Ricci identity via the plain `totalNabla0S` tower —
  `coordCommAt`'s s=2 instance is an unusable local `let`);
  `rm04Evol_at` (∂ₜRm = ΔRm − 2(B-comb) − drift at the centre, from
  S/hS + gInvDt/hmetricReg ONLY; tail NOT paid — statements D-generic);
  `rm04EvolFam` = hev (conditional on per-centre hmetricReg),
  `rm04Fam_real` = hreal (UNCONDITIONAL), `rm04LapFam_real` = hL
  (UNCONDITIONAL; `metricNabla0S∘metricNabla0S = nabla2Rm04Field` by rfl);
  `coordBasisAt` via `IsLocalFrameOn.toBasisAt` — no chart plumbing.
  BLOCKER root cause: `MetricFrameTimeRegularityInFrameOnLocal.
  inverseMetricDerivative` (= `InverseMetricDerivativeComponentsOn`)
  quantifies ALL x : M — the one non-u-local field; `localFrameInv`'s
  off-u cutoff satisfies it vacuously, `coordInv` (no cutoff) cannot; the
  localFrameInv→coordInv bridge CANNOT exist as an equality.  Planner
  consumer audit (4 code sites): Covariant:186, Evolution:53/108,
  Producers:129 all use it at x ∈ u only; BlackBox uses u=univ (trivial
  adaptation).  **RULING R11 (option A approved)**: weaken the TWO
  structure fields (base + spacetime) to u-local (∀ x ∈ u), KEEP the
  standalone global predicate for BlackBox, adapt the ~5 consumer/
  constructor sites (mechanical; constructors get strictly easier), then
  discharge hmetricReg for coordInv on the tail via `coordInvSmooth` —
  making hev per-tail unconditional.  Layering note (campaign-end):
  `roughLap0SField`/`covDiv0SField`/`metricNabla0S` belong in
  `Geometry/Operator/RoughLaplacian.lean` (producer→lane inversion via
  the ForwardUniqueRmDiff import, acyclic).  `Rm04LapIn.n2RicSym`
  redundant (derived) — prune the structure field at relocation time.
  Durable lesson: never close a producer-family-vs-centre-expansion
  match with `exact` on large defeq terms (360s KERNEL timeout);
  `simpa only [small defs + rfl-lemmas] using h` (16s).  **α5 dispatched
  (fresh executor): the R11 surgery + tail discharge.**
- №42 (2026-07-26, β4 ACCEPTED+COMMITTED — **CONNBOUND 0-SORRY: the
  Kotschwar |∂ₜA₀₃|² bound is PROVED on the repaired honest interface;
  K1C-b 100%**): fresh executor closed `htrace` — realizer uniqueness
  ALREADY EXISTED (`totalNabla0SRealizes_unique`,
  `Tensor/RSTensor/NablaDomDomCongr.lean:184`; duplicate in
  `HCGCompactness/ProductMFoldNorm.lean:82` — relocation TODO to
  deduplicate), and the ∇-past-reindexing half needed no realizer at all
  (`totalNabla0SFun_domDomCongr` fibre-level + `metricNabla0S` rfl).
  Planner re-audit: hygiene clean, ZERO tactic sorries, both endpoints +
  `nablaRicDiff_trace_le`/`connSpeedRHS_self` 3-axiom by direct lean.
  Final interface: `[I.Boundaryless]` per-theorem (5 sites; availability
  at the consumer verified by planner — ExtendViaUniqueness.lean:58);
  PRUNED `Rm₂/hRm₂/hRF₁/hRF₂/B₂/B₄` (verified by proof inspection AND
  the unusedVariables linter); RHS group `(B₁+B₃)`; constant `200(n⁶+1)`
  honest.  1472 lines.  Durable lesson: `n+k` vs literal is defeq for
  `exact` but NOT for `rw`/`simp only` (dependent index positions fail
  outright) — fix the house form of the derivative rank (`s+2+1`) and
  let `exact` do arithmetic.  **β of the №31 bundle: DONE.**  Explicitly
  NOT done (final-wiring-pass items, not this brick): the lemma
  discharging `forwardUniqueRate_le`'s `hAdot` from
  `connDiffDot_normSq_le` (0%), and the solution-level discharge of hΓ
  (`christoffelEvolution_of_solution` + regularity triple — same tail
  machinery α4 is building).
- №41 (2026-07-26, α3 ACCEPTED+COMMITTED — **bianchi2 CLOSED without new
  Tensor API; static side complete bar hcomm; K2-B ≈55%**): fresh executor
  extended `Rm04Producer.lean` 110→805 lines, 0 sorry; planner re-audit
  clean (4 endpoints 3-axiom).  `rm2Bianchi` (once-differentiated second
  Bianchi, ~145 lines): restating `SecondBianchiAt` in slot-function form
  over two `Equiv.Perm (Fin 5)` 3-cycles lets `nabla0SFun_eval_smooth_slots`'s
  correction sum be reindexed by the differentiated field
  (`Function.update_comp_equiv` + `Equiv.sum_comp`) — the two predicted
  missing lemmas were NOT needed.  `rm04LapInOfSol` = the full 7-field
  package from S/hS (`n2RicSym` derived — redundant field).
  `rm04StaticOfSol` = the static identity with every `rm04Var_eq_uhl`
  input discharged EXCEPT `hcomm`.  Cheap-`ricciId` find:
  `curvatureAction0SAt_eq_rm04` (`Curvature/CurvatureActionLower.lean:49`)
  is the component form directly.  TWO PRECISE BLOCKERS (both
  grep-verified by executor): (1) recon §6 partially WRONG — 
  `coordMetricDeriv`/`coordMetricMix` produce a DIFFERENT predicate
  (`MetricCovDerivDerivativeComponentsInFrameOnLocal` ≠
  `MetricFrameSpacetimeRegularityInFrameOnLocal`); `coordRicciEvol` never
  builds hmetricReg (routes through `ricciEvolCore` on
  `ChristoffelEvolutionEquationInFrameOn`); the ONLY solution-producers
  are `tailFrameSpaceReg` (`Metric/TailFrameRegularity.lean:74`) /
  `tailChristoffelReg`, tail-restricted with `localFrameInv` — **the tail
  is structurally forced** (carrier-vs-regular joint smoothness) and will
  propagate into items 2-3; needs the routine `localFrameInv → coordInv`
  bridge (Gram-inverse uniqueness); (2) `hcomm` needs the s=2
  `Tensor0SRicciIdentityAt` producer for Ric (~120 lines mirroring
  `rmRicciId`) — Evolution/Ricci has only the TRACED commutator.
  Relocation TODOs: `nabPerm`/`nabCyc` →
  `Tensor/RSTensor/NablaOnTensors/Regularity/Tensor0S.lean`; `secondCyc`
  → `Curvature/Bianchi.lean`.  **α4 dispatched (same executor)**: hcomm
  producer → time half on the PAID tail (bridge lemma + tailFrameSpaceReg)
  → `rm04Evol_at` → item-3 packaging.
- №40 (2026-07-26, β PASS 3 ACCEPTED+COMMITTED `a0474e367` — **Φ-defect +
  Hamilton half CLOSED; ONE sorry left = htrace, fully scoped**):
  `lowerBilin_metric_le` (the R9(b) new API): one-sided hΛ ⟹ Λ²
  slot-precomposition bound via Parseval + Cauchy–Schwarz in a
  g₁-orthonormal frame, division avoided by an N=0/N>0 split — in-lane
  with relocation TODO, `Comparison.lean` untouched.  Hamilton half
  end-to-end (`lowerHamRHS_comp`/`lowerHam_eq_perm`/`hamSum_sub`/
  `hamSum_normSq_le`, slot isometry costs 10).  Planner re-audit: hygiene
  clean, 5 public endpoints 3-axiom clean (6th is private), single
  tactic sorry `:1244`.  Remaining = `htrace`
  `|∇¹(Ric₁−Ric₂)|² ≤ n⁵|∇¹S₀₄|²`: route fixed (`ricciDiff_eq_trace` →
  DFunLike.ext → `nablaRealizes_metricTraceFirstTwo` + `traceNablaShuffle`
  → realizer-uniqueness → `traceNormSq_le` s=3 + `normSq0S_domDomCongr`);
  ONE small missing lemma = realizer uniqueness for `TotalNabla0SRealizes`.
  R9(a) `[I.Boundaryless]` deliberately deferred to the closing pass
  (unused hypothesis would be noise).  FINAL prune list (R9(c), safe —
  htrace mentions none): DROP `B₂`,`B₄`,`hRF₁`,`hRF₂`,`hRm₂` (content
  arrives via hΓ); constant now `200(n⁶+1)` (the +1 kills the finrank=0
  split).  Lean lessons recorded (typed-wrapper defs for Tensor0SSpace
  sums — ascription does NOT force elaboration; keep nlinarith away from
  tensor atoms — isDefEq/whnf timeout, factor into pure-real lemmas;
  explicit mul_le_mul chains beat 17-variable nlinarith).  β executor
  retired at ~500k tokens; **β4 (closing pass) dispatched to a FRESH
  executor**: add Boundaryless, build realizer-uniqueness, close htrace,
  prune, restate capstone, 0-sorry target.
- №39 (2026-07-26, ACCEPTED+WIRED — **α2 PARTIAL (B) + SCOPE-CORRECTING
  FINDING: 5 of the "missing" K2-B inputs have EXISTING producers**):
  Agent-K2B1's second pass delivered `Evolution/Rm04Producer.lean`
  (110 lines, 0 sorry; `rmComp` canonical FourComp array + `rm04SymmOfSol`
  = `Rm04Symm` from S/hS ONLY, discharging 4 of the 10 static-identity
  inputs; planner re-audit clean, 3-axiom).  FINDING (planner
  grep-verified every location): `canNabla2RicTrace`
  (`LeviCivita/Curvature/Realized.lean:1068`) = n2RicTrace EXACT;
  `canRm2Symm` (:1229) conj 2/3 = n2RmSwap12/n2RmPair; `canRmSecond`
  (:542) = NON-existential SecondBianchiAt for the canonical field;
  `nablaKRm04_ricciIdentityAt` (`RmRealizationBridgeAllK.lean:345`, k=0)
  = ricciId; `nablaKRm04_nabla20SRealizesAt` (:329) = the s=4 realization
  WITH the nablaRm04Field/nabla2Rm04Field tower — zero new Tensor-layer
  API needed for realization.  Rule reconfirmed AGAIN (grep the can*
  family before declaring Levi-Civita pointwise identities missing).
  **The only genuine gap = `bianchi2`** (once-differentiated second
  Bianchi), reduced to TWO precise missing lemmas: (i) linearity of
  `nabla0SFun`/`totalNabla0S` in the differentiated field, (ii) its
  naturality under a `domDomCongr` slot permutation — then differentiate
  `canRmSecond`'s pointwise-zero cyclic section.  Layer-2 note: try
  `coordMetricDeriv`/`coordMetricMix` for hmetricReg FIRST (may avoid the
  positive-time tail; `tailChristoffelReg` gives `localFrameInv`, needs a
  bridge to `coordInv`).  Layers 2-3 (discharge + packaging) NOT built —
  dispatched as α3 to a FRESH executor (α executor at ~379k tokens,
  signatures collected in Rm04Producer.md).  RULING R10: the two bianchi2
  lemmas go IN-LANE (Rm04Producer.lean) with a relocation TODO naming the
  Tensor/Operator canonical home.
- №38 (2026-07-26, ACCEPTED+WIRED — **α1 OUTCOME (A): THE STATIC REDUCTION
  IS PROVED, MSM110 6.14 CORE INCLUDED, 0 sorry**): Agent-K2B1 delivered
  `Evolution/Rm04Reduction.lean` (801 lines; endpoint `rm04Var_eq_uhl` =
  rm04VarRHS → ΔRm − 2(B−B+B−B) − drift at the frame centre, bridges to
  `rm04VarRHS`/`uhlenbeckBTensorInFrame`/`riemann04RicciDriftInFrame` all
  rfl).  Planner re-audit: hygiene clean, 4 endpoints 3-axiom clean by
  direct lean, zero tactic sorries (three STALE docstring "carries a
  sorry" mentions from the mid-flight state fixed by planner, focused
  check re-run green).  Chain `rmVar_eq_hess → comm_eq_drift →
  rmHess_eq_lap (6.14) → rmQuad_eq_b (6.15)`; enabling technique =
  `quadSum` normal form (every quadratic block is Σ g⁻¹g⁻¹X with metric
  pairs pre-aligned; book index gymnastics collapse to 3 reindexings +
  symmetry rw); `linarith` with double-sums-as-atoms.  Sign ledger now
  DERIVED dim-generically (bComp = −B_MSM ⟹ book +2 = project −2),
  upgrading the dim-3 spot-check.  Non-vacuity guard: hypothesis packages
  constructible (zero-curvature witness).  Hypothesis inventory: 10, each
  with a named stage-2 discharger in the .md; the ONLY producer gaps =
  `Rm04LapIn.bianchi2` (once-differentiated second Bianchi) and
  `n2RicTrace`; suggested build order = `Nabla20SRealizesAt` at s=4
  first, everything else flows.  Relocation TODO: the manifold-free
  `section Algebra` → beside `Uhlenbeck.lean`; on relocation REDEFINE
  `uhlenbeckBTensorInFrame := bComp` (bridge rfl) rather than keep two.
  Wired into the root aggregate (`DifferentialGeometry.lean:1354`).
  **K2-B-2 dispatched** (same executor): discharge the 10 inputs at the
  coordinate frame (coord*/canBianchiAt families + the two new
  producers), then per-point packaging into the predicate + the
  consumers' hreal/hL realization shapes.
- №37 (2026-07-26, β PASS 2 ACCEPTED+COMMITTED `119c86055` — **statement
  repaired per R8; Layer A proved; 1 sorry on a strictly reduced goal**):
  restated `connSpeedLow_normSq_le` + capstone carry hΓ (verbatim
  `ChristoffelEvolutionEquationInFrameOn` currency), hA as realization
  link, B₃/B₄, supplied `Ric₁`+`hRic₁` (needed for `Ric₁−Ric₂` to be a
  differentiable object — flagged addition, approved), constant 100n⁶
  provisional.  GREEN axiom-clean (planner re-audited): `coeff_adot_eq`
  (HasDerivAt.unique pins Adot's frame coefficients — the structural
  discharge of the falsity), `lower_raise_cancel`, `connSpeedLow_eq`
  (splitting needs NO inverse metric), `connSpeedRHS_self`.  RatePro
  trace bridge fit exactly — `ricciDiff_eq_trace` has NO residual h₀₂
  term, so B₄/B₂ turned out UNUSED on this route (executor's own defect-2
  prediction partly wrong, recorded).  Remaining sorry = two reductions:
  (1) contracted trace — plumbing (nabla_metricTraceFirstTwo0S needs
  `[I.Boundaryless]`, not yet in the file's variable block); (2) Φ-defect
  — ONE new slot-precomposition norm bound; one-sided hΛ suffices at Λ².
  Durable lesson: `lake build` runs linters the focused `check` does not
  — warning-cleanliness must be certified by the targeted build.
  **RULINGS R9** for pass 3: (a) adding `[I.Boundaryless]` to the file /
  endpoint theorems AUTHORIZED (ExtendViaUniqueness's variable block
  already carries it — honest at wiring); (b) the new norm lemma goes
  IN-LANE (this file or ReLower) with a relocation TODO pointing at
  `Tensor0SRiemannian/Comparison.lean` — do NOT edit the shared canonical
  file mid-campaign; (c) after the proof closes, DROP whichever of
  B₂/B₃/B₄ the final proof does not consume (weakest-assumptions rule);
  keep the flagged `Ric₁` field.  Pass 3 dispatched (same executor).
- №36 (2026-07-26, ACCEPTED+COMMITTED `002d5766c` — **γ OUTCOME (A): hdens
  TOWER COMPLETE**): Agent-DENS closed all four steps + the flagged
  closed-edge delta, 0 sorry, warning-free; planner re-audit clean
  (hygiene grep: only the №29-precedented borel block; direct-lean axiom
  audit on 6 endpoints = 3-axiom clean).  Key moves: (1) the brick's
  component hypothesis WEAKENED to pointwise `ContMDiffAt` — dissolves the
  good-set-vs-baseSet mismatch with no re-localization; (2) the mixed-object
  chart lemma `rm04ChartComp` proved in 11 lines — the recon had missed the
  OFF-CENTRE Riemann basis identity (`RiemannBasisIdentityOffCentre.lean:426`);
  mini-instance of the grep-the-producer lesson; `g₂ := g₁` covers the
  diagonal, so S₀₄ needed no separate treatment; (3) `dens_continuous`/
  `dcont_idens` UNCONDITIONAL at every t (constant-family trick: fixed-time
  density is static, chart-Gram hypothesis degenerates to spatial) — the
  Ioo-vs-Icc "second gap" is CLOSED, `dcont_idens_of_joint` removed as
  subsumed; (4) the R6 import was already in the transitive closure —
  module graph unchanged.  7 of 11 hdens-tower `ForwardUniqueInputs`
  fields now producible from the file (dens/densCont/densInt/lapInt/
  divInt/nabInt/disInt); the 4 left (energyCont/pairInt/restInt/remInt)
  pair bare pointwise speed families — not density-regularity questions.
  Interface fit verified BY CONSTRUCTION in a scratch probe.  Relocation
  TODOs in the .md (6 decls in wrong layer, deferred to campaign end).
  γ of the №31 bundle: DONE.
- №35 (2026-07-26, **α RECON ACCEPTED → K2-B-1 DISPATCHED**): recon findings
  (planner-verified where load-bearing): (1) the target predicate's sign
  `−2(B…)` with minus-FREE `B` is the project's own 2026-06-09 verified
  reconciliation (`UhlenbeckBaseProducer.md:166-215`) — the old consult's
  `2|Ric|²` mystery is RESOLVED, not open; (2) citation pinned: **Chow–Knopf
  MSM110 Lemma 6.15 p.179** (chapter6.tex:518; Morgan–Tian flowbasics.tex:368
  attributes it; GSM77 = Lemma 2.51) — the plan's "Lemma 6.1" was a
  project-internal label colliding with MSM135's entropy Lemma 6.1: STOP
  using it, say "MSM110 6.15"; (3) NO producer of the predicate exists —
  every occurrence is hypothesis-side; (4) dim-3 pointwise evolution is
  DONE+discharged (`rm04Base_of_sol`, `rm04HrmProducer`) but (B) is
  dim-GENERIC (variable block re-checked: no finrank hypothesis) so K2-B
  must be general; dim-3 serves as sign/algebra reference only; (5) the
  time side is banked dim-generically (`rm04Var_of_sol`, ∇²Ric-expanded
  `rm04VarRHS`), so K2-B's real content = the STATIC MSM110-6.14-style
  reduction (differentiated-traced second Bianchi + rank-4 Ricci identity
  + first-Bianchi B-algebra); (6) consumer mismatch "centre-only producers
  vs every-y predicate" DISSOLVES by per-point centred coordinate frames
  (the component family takes the point as argument; instantiate x₀ := y);
  (7) regularity black boxes (hmetricFrame/hmix/hswap) all discharge on
  the coordinate route (`coordRicciEvol` precedent carries ZERO regularity
  hypotheses) and consumers only use t ∈ Ioo ⊆ D.regular.  **K2-B-1
  dispatched** (new file `Evolution/Rm04Reduction.lean`, hypothesis-taking
  static identity `rm04VarRHS = roughLap − 2(B-comb) − drift` mirroring
  `ricciVariationExpandedRHS_eq_evolutionRHS_of_commutators`; outcome (B)
  = B-algebra+swap green with ΔRm core as ONE named sorry is a legitimate
  landing).  K2-B-2 (coord* discharge + per-point packaging + hreal/hL
  realizations) queued after α1 lands.
- №34 (2026-07-26, **β OUTCOME (C) — FRONTIER STATEMENT FALSE; RULING R8**):
  Agent-CONNBOUND DISPROVED `connSpeedLow_normSq_le` as stated: the RHS is
  difference-only, so at `g₁ t = g₂ t` it forces `Adot = 0`, but `hA` +
  single-time pointwise `hRF₁/hRF₂` cannot exclude a Schwarz failure
  (`w(r,y) = r³y/(r²+y²)` family: `∂ᵣw(0,·) ≡ 0` yet `∂ᵣ∂_y w(0,0) = 1`);
  the RHS-collapse half is machine-checked (`connSpeedRHS_self`, green,
  axiom-clean).  Planner verified the argument + zero external consumers.
  Durable lesson: audit every pointwise-estimate frontier by collapsing all
  difference carriers FIRST; `ℝ → SmoothRiemannianMetric` carries NO joint
  (t,y) regularity — any ∂ₜ(spatial-derivative object) statement must take
  joint regularity/∂ₜΓ as input.  Defect 2 (weaker, derivation-level): RHS
  needs zeroth-order background norms `B₃ ≥ |Ric₂|²`, `B₄ ≥ |Rm₂|²`.
  **RULING R8**: repair per the executor's .md §"The repair" — keep the
  conclusion shape; ADD `hΓ` (Hamilton ∂ₜΓ-difference in the
  `ChristoffelEvolutionEquationInFrameOn` frame currency, = K1's output,
  dischargeable via `christoffelEvolution_of_solution`/`tailChristoffel` +
  midpoint trick exactly like K6b's gamma); keep `hA` as realization link
  (`HasDerivAt.unique` pins components); ADD `B₃`/`B₄`; constants free;
  reuse K4P's `ricci_eq_trace_rm04`/`ricciDiff_eq_trace`
  (`ForwardUniqueRatePro.lean`) for the (1,3)→(0,4) trace bridge BEFORE
  building any new Curvature-layer API; restate the in-file capstone
  `connDiffDot_normSq_le` accordingly; downstream `adotLe` absorbs the new
  norms into slab constants at wiring time (no downstream edits now).
  Re-dispatched to the same executor (context intact).
- №33 (2026-07-26, IN FLIGHT — **α/β/γ wave, user go received**): three
  parallel dispatches on disjoint files.  **Agent-CONNBOUND (β)**: fill
  `ForwardUniqueConnBound.lean:496` (`connSpeedLow_normSq_le`) — route =
  (i) identify `Adot` components against the PROVEN frame producer
  `christoffelEvolution_of_solution` via `HasDerivAt.unique` (no invariant
  Koszul re-derivation), (ii) trace bridge `∇¹(Ric₁−Ric₂) = tr_{g₁}(∇¹S₀₄)
  + l.o.·bg` via `nabla_metricTraceFirstTwo0S` + `traceNablaShuffle`
  (Bianchi NOT on path); constants may grow (downstream is ∃-shaped).
  **Agent-DENS (γ)**: execute DensReg .md §3 steps 1–4 (GenJointGram
  repackage → christoffel transport → good-set chart evaluation of A₀₃ →
  S₀₄ chain + THE one new mixed-object chart lemma
  `riemannCurvature04At g₁ (metricCov g₂)`); R6 import pre-authorized;
  Icc-edge gap deliver-or-report; ≤150-line escape hatch = one documented
  frontier sorry. **K2-B RECON (α stage 1, read-only Explore)**: A-half
  inventory (`realizedRmBase_timeDeriv` exact shape + olean), 3D-KN residue
  reuse, static-identity assets (curvSecondBianchi shape, ∇∇-commutator
  API, ∂ₜRm04 lowering, coordRicciEvol architecture), consumer instance
  shapes (Lifts/Sdec/Assembly), book citation pin (the "Lemma 6.1" number
  vs actual LaTeX), regularity side-conditions (hmetricFrame/hmix/hswap
  status for Ico-smooth flows). Main α dispatch AFTER recon lands.
- №32 (2026-07-26, **WINDOW WRAP — FULL LOCKED BUILD GREEN**): final
  `lake-locked build` of the autonomous window completed successfully
  (10649 jobs, 0 errors).  Whole-tree sorry set audited from the full log =
  exactly the documented frontiers: lane's ONE frontier `ForwardUniqueConnBound`
  (decl `:455`, sorry `:496`), endpoint `ExtendViaUniqueness` `:79` (N) /
  `:189` (B), plus pre-existing non-lane sorries (HopfRinow ×3,
  NoncollapseInjectivity, Exterior/Basic ×4, MetricCompactness,
  HamiltonCompactness, CurvTowerBridge, Rellich, Weyl, CinftyLimitGlue,
  HamiltonPositiveRicci ×2).  All 19 lane/canonical modules in the root
  aggregate compile inside the green tree.  Resume point for the next
  session = №31's α/β/γ/δ bundle (Task: K2-B + adotLe producer + dens
  completion, then one wiring pass instantiating `forward_unique_of_inputs`
  at `:189`).  Note: (N)-lane commits (`6c98d9738`, `eda2c3a36`) landed on
  the branch during the build window; their in-flight dirty files left
  untouched per charter §4.
- №27 (2026-07-26, ACCEPTED — **K6a OUTCOME (A): ENDGAME ASSEMBLY DONE**):
  **Agent-K6A delivered `Evolution/ForwardUniqueAssembly.lean`** (509 lines,
  11 public decls, 0 sorry; planner re-audit clean). `forward_unique_of_inputs`
  proves the (B)-shaped conclusion at (B)'s EXACT interface from a minimal
  fully-labelled standing bundle (5 data carriers + 16 Prop fields,
  satisfiability-audited). Discharged from (B)'s own fields: hgram, both PDEs
  (with the `metricRicciAt_apply_eq_ricciTensor` currency bridge), hinit,
  hA/hS DERIVED at the canonical chart frame, concrete Young parameters.
  Bundle provenance: K2-B (`gamma`/`rm`/`sdec`; rm+sdec composable-later
  pending the QUADRILINEAR frame→invariant lift and the SolutionOn bridge —
  both missing-API, dispatched as K6b №28), realization (`car`), slab bounds
  (`∃`-per-subslab, deliberate), hdens tower (`dens` + 10 of 16 fields
  collapse to `dens` alone once the tower lands). `adotLe`'s producer still
  carries the ConnBound `:496` frontier; `ricciLe`/`reactLe` now feedable
  from RatePro (№25). Endpoint `:189` untouched by design.
- №31 (2026-07-26, ACCEPTED — **K6c OUTCOME (A): COMPOSITION PROGRAM
  COMPLETE**): **Agent-K6C delivered `Evolution/ForwardUniqueSdec.lean`**
  (1008 lines, 25 public decls, 0 sorry; planner re-audit clean). The
  metric-argument SWAP on `reLower` makes the gap operator's trace metric AND
  connection both g₁ → `lapComm_reLower_eq` yields a g₁-divergence directly
  (the ∇A-cost risk of R7 dissolves entirely); `nabla1_metric2` free by the
  same swap; gap ∂ₜ by pointwise product rule; `sdecUflux`/`sdecRemFam`
  CONSTRUCTED (four-summand remainder, all difference×background);
  `sdec_of_uhlenbeck` residual = exactly R1 + K6b's carried hypotheses + two
  unavoidable field realizations (`hT₁`/`hT₂`, same papering as
  `Sfield`/`car`); `rm` and `sdec` share `uhlRmDiffSpeed` bit-for-bit.
  **THE ASSEMBLY BUNDLE NOW COLLAPSES TO**: (α) K2-B — the two own-lowered
  `Riemann04BTensorWithRicciDriftEvolutionInFrameOn` interfaces (+ per-flow
  PDE + benign realization/continuity auxiliaries) — THE mathematical
  frontier (Lemma 6.1, ~900-line second-Bianchi conversion; `coordRicciEvol`
  precedent; `curvSecondBianchi` proved); (β) `bounds` — slab constants,
  producers banked except `adotLe` ← `ConnBound:496` (invariant ∂ₜΓ);
  (γ) `dens` — the 4-step completion + ONE mixed-object chart lemma
  (`riemannCurvature04At g₁ (metricCov g₂)` reading); (δ) benign
  realization slots. Relocation TODOs logged.
- №30 (2026-07-26, ACCEPTED — **K6b OUTCOME (A) beyond spec** + **PLANNER
  RULING R7**): **Agent-K6B delivered `Evolution/ForwardUniqueLifts.lean`**
  (630 lines, 19 public decls, 0 sorry; planner re-audit clean).
  Quadrilinear lift (`quadOfComp` family + `rmDiffVec_hasDerivAt_of_basis`);
  `uhlRmDiffSpeed` CONSTRUCTS `Svec`; `rm_of_uhlenbeck` collapses `rm` to
  EXACTLY the R1 standing inputs. **`gamma` FULLY DISCHARGED from (B)'s own
  fields** (`gamma_of_gram`): the Assembly ledger's K2-B label was WRONG —
  the pairing route is DEAD (zero producers of
  `ConnectionPairingDerivativeInFrameOn`, a 5th false-path finding) but
  `solutionOn_of_joint → tailChristoffel` bypasses it; `solOfMetric g = ⟨⟨g⟩⟩`
  trivial; tail restriction paid by the midpoint trick; `Avec` constructed.
  **RULING R7 (`sdec`)**: the executor's carrier fork is ALREADY RESOLVED by
  the R4 bridge — key identity `∇¹h₀₂ = −∇¹g₂ = A-algebraic` (mirror of
  `nabla2_metric1`), so `Δ₁` of the lowering gap div-organizes (Leibniz:
  `(Δ₁h)·Rm₂ = div₁(∇¹h·Rm₂) − ∇¹h·∇¹Rm₂`, all A-flux shapes); `sdec`
  composes from K2A's generic capstone + K2.3 + K2.6b/c + this identity —
  NO carrier change, NO input beyond R1's pair. K6c dispatched (№31).
  Lesson: IPS/NormedSpace split must be a SECTION split.
- №29 (2026-07-26, ACCEPTED — **TOWER OUTCOME (B) strong; 4TH FALSE WALL
  CORRECTED**): **Agent-TOWER delivered `Evolution/ForwardUniqueDensReg.lean`**
  (20 decls, 0 sorry; planner re-audit clean — borel `private local instance`
  block = №12-precedented idiom). RECON CORRECTION: №6's "the joint
  chart-Gram→Γ→Rm tower does NOT exist" was FALSE — `GenJointGram`
  (`Analysis/Parabolic/RicciLinearization/RicciDifferenceMeanValue.lean:401`),
  `gen_joint_invGram` (:476), `gen_joint_christoffel` (:619),
  `gen_joint_riemann` (:683) + transports EXIST, generic over metric families.
  Delivered: joint moving-fibre-norm brick; `metricDiffSq_jointContMDiffOn`
  UNCONDITIONAL; **four of eight Integrable slots discharged with NO
  hypotheses** (typing fact) + `inner0S_smooth`; `hdcont`/`hidens` from
  `hdens` on the open window. RESIDUAL (classified): conn/rm density joint
  smoothness reduced to the chart-frame components of A₀₃/S₀₄ — four steps
  (~250–450 lines; 1–3 routine composition of located lemmas; STEP 4 = the
  ONE new lemma: chart reading of the mixed object
  `riemannCurvature04At g₁ (metricCov g₂)`), plus the Icc-edge variant
  blocked on the same object. **RULING R6**: `Evolution/` MAY import
  `Analysis/Parabolic/RicciLinearization` at endpoint altitude (K2.7's
  Analysis/Elliptic import is precedent; same R5 rationale). Ledger DEFECT:
  `Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure` is
  declared TWICE in the same namespace; 4 relocation TODOs in the .md.
- №28 (2026-07-26, IN FLIGHT): **Agent-K6B** (`Evolution/ForwardUniqueLifts.lean`
  — `quadOfComp` lift + `rm_of_uhlenbeck` collapse + the SolutionOn/`gamma`
  bridge; `sdec` collapse only if carrier-decision-free) and **Agent-TOWER**
  (still running).
- №26 (2026-07-26, IN FLIGHT): **Agent-K6A** (endgame assembly
  `Evolution/ForwardUniqueAssembly.lean` — `forward_unique_of_inputs` at (B)'s
  exact interface + minimal labeled standing bundle) and **Agent-TOWER**
  (`Evolution/ForwardUniqueDensReg.lean` — the hdens joint-regularity
  producer, recon-first, priority: metricDiffSq joint → Integrable slots →
  conn/rm layers; expected outcome (B) with the connection/curvature joint
  tower classified).
- №25 (2026-07-26, ACCEPTED — **K4P OUTCOME (B) strong**): **Agent-K4P
  delivered `Tensor0SMetricCongr.lean` (canonical, NormedSpace-only:
  `inner0S_domDomCongr`) + `Evolution/ForwardUniqueRatePro.lean`**
  (`ricci_eq_trace_rm04` tensor-level, slot permutation (0,1,2,3)↦(0,2,3,1),
  cross-pair gate discharged; **`ricciDiff_eq_trace` matches K4's `htr`
  VERBATIM with B = 0** — Ric-difference is EXACTLY the g₁-trace of S₀₄,
  same-norm representative). Discharges K4's `htr` AND K1C-b blocker (ii).
  Correct layering: instantiation left to the consumer side to keep both new
  files IPS-free. `movingReact_le` deferred with a SOLID classification:
  `movingReact0S` is frame-pinned by definition (hard-codes `finBasis` +
  `basisInvMetric`); K4's ~80-line estimate was WRONG; smallest unblocker =
  `movingReact0S_orthoBasis` via a new slot-composition layer (~250–400
  lines, optional-upgrade brick — `hreact` stays a named slab hypothesis, no
  sorry anywhere). Ledger: `domDomCongr_sub` → `RSTensor/Defs`;
  `exists_onFrame`/`onFrame_inv` now 4 copies; rw-on-Tensor0SSpace lesson now
  SYSTEMATIC (calc/rfl/congrArg/term-form only). 9 decls axiom-clean; both
  wired.
- №24 (2026-07-26, ACCEPTED — **K5 OUTCOME (A): CLOSURE CHAIN COMPLETE**):
  **Agent-K5 delivered `Evolution/ForwardUniqueClosure.lean`** (480 lines, 8
  public decls, 0 sorry; planner re-audit clean). `gronwall_zero_on` →
  `energy_zero_on` → `metric_eq_of_energy_zero` (measure-positivity producer
  EXISTS: `riemannianVolumeMeasure_isOpenPosMeasure`) → `metrics_eq_on` /
  `metrics_eq_ico`. **The capstone's named package IS K6's input inventory**
  (K3+K4 verbatim on Ioo + `hidens`/`hdcont` on Icc + `hinit`/`hcont`; only
  two inputs new vs K3+K4, both hdens-tower debt). RATIFIED: (1) Gronwall
  restated off Mathlib with zero DG imports — **`EdgeStrongData.lean`
  UNMASKED AS FALSE-GREEN** (no olean in this checkout; only consumer is the
  un-compilable MovingEdgeEnergy; proof uses `le_of_tendsto` where
  `ge_of_tendsto` is required — does not elaborate as written). Flag to the
  (N)/DeTurck lane. (2) `metricExtInner` = 3rd smooth-metric-ext copy —
  promote to `Geometry/Metric/Basic` at campaign end; merge the two Gronwall
  statements under `Analysis/ODE/`; add `normSq0S` positive-definiteness next
  to `normSq0S_nonneg`.
- №23 (2026-07-26, ACCEPTED — **K2.6c OUTCOME (A): K2.6 CLOSED**):
  **Agent-K26C delivered `Evolution/ForwardUniqueReLower.lean`** (992 lines,
  33 public decls, 0 sorry, warning-free; planner re-audit clean, olean
  fresh). `reLower g₁ g₂ T = tr_{g₂}(domDomCongr (rotation-by-2) (T ⊗ g₁))`
  (slot layout PINNED in its .md — reuse, never re-derive); covariant defect
  `∇²(reLower T) = reLower(∇²T) + reLowerPair g₂ T (∇²g₁)` — bilinear, no
  ∇A; with `nabla2_metric1` algebraic in the A₀₃ flux; the concrete
  divergence-form commutator instantiates `lapComm_eq_div_flux` with BOTH
  carriers algebraic in (A₀₃-flux, T, ∇²T) — abstract defect carriers
  RETIRED, **K2.6 complete**. `trace_reLower` was the one extra piece
  (four-fold basis-sum exchange; no framework, no gate). Ledger: 8 Lean traps
  in the .md (worst: `Fin.cons` motive mis-guess manifests as a bogus
  `ChartedSpace H (Fin n)` instance failure); 5 local helpers with
  Tensor-layer relocation TODOs (`traceField_eq_sum`, `nablaProd_eval`,
  3 Fin/Finset lemmas).
- №21 (2026-07-26, ACCEPTED — **K4 OUTCOME (A): `forwardUniqueRate_le` DONE**):
  **Agent-K4 delivered `Evolution/ForwardUniqueRateLe.lean`** (933 lines, 20
  public decls, 0 sorry; planner re-audit clean incl. the capstone). Currency
  bridge `innerPt_eq_inner0S` (model↔fibre pairing, orthonormal diagonal +
  POLARISATION) — without it the S-part was unprovable; IBP identities now in
  lane currency (`intInner_lap_eq_neg`, `intInner_div_eq_neg`).
  `ricciDiffSq_le` SHARPER than spec: `Ric₁−Ric₂ = tr_{g₁}S₀₄` exactly
  (pure-contraction cancellation, no h-term). Two-parameter Young
  (`habs : δ·C_A + ε ≤ 1`) handles the ∇S-feedback in the Adot slot, κ = 1.
  Capstone `rate ≤ K·E − D`, K explicit, fully named package (hSdec = R4
  shape verbatim; hAdot = K1C-b slot no-adapter; 8 Integrable slots = hdens
  debt). OWED (named, none inside K4): `hreact` micro-bound; the tensor-level
  Ric-trace slot bridge (+ missing `inner0S_domDomCongr`) — SHARED wall with
  K1C-b blocker (ii), confirmed. Ledger: 3rd copy of
  `rfns_eq_normSq0S_unit` (home: RiemannianFiberNormSq layer);
  ForwardUniqueEnergy's borel-instance block may be droppable (K4 needed none).
  For K5: `E′ ≤ K·E` is one linarith from `dissipation_nonneg`.
- №22 (2026-07-26, IN FLIGHT): closure wave — **Agent-K5**
  (`Evolution/ForwardUniqueClosure.lean`: edge-Gronwall E≡0 on Icc; integral-
  zero ⟹ pointwise metric equality via measure positivity + metric ext;
  `metrics_eq_on` capstone per-subslab then Ico; its report defines K6's
  input inventory) and **Agent-K4P** (`Tensor0SMetricCongr.lean` canonical +
  `ForwardUniqueRatePro.lean`: `inner0S_domDomCongr`, `movingReact_le`,
  `ricci_eq_trace_rm04` matching K4's `htr` verbatim — discharges the shared
  wall). K26C still unreported (long-running; check on next wake).
- №20 (2026-07-26, ACCEPTED — **K1C-b OUTCOME (B), one documented frontier**):
  **Agent-K1CB delivered `Evolution/ForwardUniqueConnBound.lean`** (555 lines,
  11 public decls, EXACTLY one real `sorry` at `:496`; planner audit: 7 decls
  axiom-clean + 2 documented sorryAx (frontier + its capstone consumer);
  probe up-to-date). Gaps (2)+(3) COLLAPSED into one sharp-constant-1
  lowering-comparison lemma (no isometry framework; `connDiffLow_eq_lower`);
  the `∇¹S₀₄` carrier NAMED (`nablaRmDiff`/`nablaRmDiffSq`/`IsRmDiffField`
  + `_self` sanity); reaction half of the ruling's bound UNCONDITIONAL;
  capstone `connDiffDot_normSq_le` in the ruling's shape, green modulo the
  frontier. **PLANNER FRAMING CORRECTED (gap 4)**: the route needs only
  ∇-commutes-past-metric-trace (∇g = 0) — Bianchi is NOT on this path; the
  REAL blockers are (i) Hamilton's ∂ₜΓ formula in INVARIANT form (repo has
  frame components only) and (ii) the tensor-level `Ric = tr_g(Rm₀₄)` slot
  bridge (component-level only today). SMALLEST UNBLOCKER (shared with K4's
  likely need — wait for K4's report before dispatching): tensor-level
  Ric-as-Rm₀₄-trace with the trace pair in slots 0,1, canonical home
  `Geometry/Curvature/` next to `metricRicciAt_eq_trace`. Ledger:
  `tensor02_expand` relocation now DUE (2nd consumer);
  `exists_onFrame`/`onFrame_inv` duplicated 3× — promote to a public pair
  under `Tensor/RSTensor/Tensor0SRiemannian/` at campaign end.
- №19 (2026-07-25, IN FLIGHT + a PLANNER FINDING): three Opus builders
  concurrent — K26C (re-lowering defect), **Agent-K4**
  (`Evolution/ForwardUniqueRateLe.lean`: Ric-difference trace bound + S-part
  IBP/Young assembly + h/A/volume parts with the K1C-b slot as a named
  hypothesis + `forwardUniqueRate_le` capstone + `forwardUniqueDissipation`),
  **Agent-K1CB** (`Evolution/ForwardUniqueConnBound.lean`: the named ∇¹S₀₄
  carrier + lowering-contraction instances + the ruling's |∂ₜA₀₃|² bound).
  FINDING (checked, №9's homework): **`curvSecondBianchi` IS PROVED**
  (`Geometry/Curvature/Bianchi.lean:820`, operator-level, torsion-free
  hypothesis, file 0-sorry); `second_bianchi`/`contracted_bianchi_of_second`
  are hypothesis-unpacking combinators BESIDE the proved producer — K1C-b
  gap (4) is contracted-trace + realization plumbing, not new mathematics;
  K2-B's deepest geometric input is likewise banked.
- №18 (2026-07-25, ACCEPTED — **K2.7 OUTCOME (A)** + **PLANNER RULING R5**):
  **Agent-K27 delivered `Evolution/ForwardUniqueIBP.lean`** (389 lines, 9
  public decls, 0 sorry; planner re-audit clean, probe up-to-date). The lane's
  field-level `∇`/`div` identified with the bundled `covGrad`/`covDivergence`
  along `ccLift0S` (unit-scalar lift, ZERO extra hypotheses — Tensor0SField ∞
  IS the Cₛ^∞ type; compact support from CompactSpace). K4 entry points:
  `l2Inner_nabla_eq_neg_div` (⟨∇T,V⟩ = −⟨T,divV⟩ in lane currency) and
  `l2Inner_nabla_self_eq_neg_lap` (free via `roughLap0SField = covDiv ∘ ∇`
  definitionally). **RULING R5**: the file's forced `[InnerProductSpace ℝ E]`
  (+Boundaryless etc.) is RATIFIED for K4/K5/K6 — the ENDPOINT's own variable
  block (`ExtendViaUniqueness.lean:53`) already carries it, so
  endpoint-altitude assembly files may inherit it; the lower-layer
  NormedSpace-cleanliness discipline stands; the Green/IBP producer de-IPS
  restatement (model-space orthonormal frames — likely MORE than an `omit`)
  joins the campaign-end list as its 5th occurrence. New debug lesson:
  Tensor0SSpace has its OWN FunLike instance — use `DFunLike.ext`, and
  ascribe CLM sums with `show … →L[ℝ] …` to fire `sum_apply`.
- №17 (2026-07-25, IN FLIGHT): **Agent-K26C** — `Evolution/ForwardUniqueReLower.lean`:
  the K2.6c slot-bookkeeping brick (reLower as g₂-trace of g₁⊗T with two
  permutations, first-order Leibniz defect via `nabla2_metric1`, instantiate
  `lapComm_eq_div_flux`). Executors now instructed to RE-RUN the targeted
  build after the final edit (fresh-olean audit lesson from №16).
  K27 (IBP) still in flight.
- №16 (2026-07-25, ACCEPTED — **K2.6b OUTCOME (B); R4 ROUTE REALIZED; NO
  ESCALATION**): **Agent-K2B6 delivered `Evolution/ForwardUniqueRmBridge.lean`**
  (656 lines, 17 public decls, 0 sorry; planner audit: initial `--no-build`
  probe showed a stale trace → authoritative rebuild 14s GREEN → axiom
  re-audit on the FRESH olean clean — trace-staleness noted as an audit
  lesson: always rebuild before auditing if the probe is not up-to-date).
  Deliverable 1 COMPLETE: `vecCurve_deriv` (frozen-metric reconstruction —
  the inverse metric is NEVER differentiated; continuity-only input via the
  vanishing-factor product rule), `metricRm04At_inner`, `rmVecComp_deriv`
  (consumes the own-lowered Uhlenbeck interface verbatim), `rmDiffVec_deriv`
  landing EXACTLY on `rmDiffLow_hasDerivAt`'s `hRm` — **the `hreal`
  mixed-lowering fallback is RETIRED on this path**; stated for arbitrary
  `s` (Ici/carrier/univ all instantiate). Deliverable 2 partial (~40%):
  `metricNabla0S_self`, **`nabla2_metric1` (∇²g₁ = −lapDiffFlux g₁ g₂ g₁ —
  bound comes free from `fluxNormSq_le`)**, `sharpFlat`/`mixLow_eq_rm04`
  (the R4 gap = last-slot precomposition by Φ = g₂♯∘g₁♭, id at equal
  metrics), and `lapComm_eq_div_flux` — the STRUCTURAL div-form regrouping
  with both defect carriers manifestly FIRST-order ⟹ **the R4 escalation
  gate does NOT fire; no consult needed**. REMAINING sub-brick K2.6c
  (slot bookkeeping, not mathematics): the re-lowering operator's Leibniz
  defect via g₂-trace of g₁⊗T with two slot permutations; all three
  ingredients located (`totalNabla0SFun_domDomCongr` NablaDomDomCongr:110,
  `nabla_metricTraceFirstTwo0S`+`traceNablaShuffle` NablaTraceGen:504/876/997,
  `nabla0SFun_product_eval` ContractionLeibniz:122); `mixLow_eq_rm04` pins
  the semantics. Hygiene: NO instances under hardened sweep.
- №15 (2026-07-25, AUTONOMOUS WINDOW OPENED): user authorized ~10 hours of
  autonomous operation; **Pro consults PRE-AUTHORIZED via the Chrome plugin**
  ("直接用chrome打开就好"). Chrome path DRY-RUN VERIFIED end-to-end short of
  submission: launch recipe = `Start-Process chrome.exe`, extension handshake
  takes ~30–40 s (an empty `list_connected_browsers` right after launch is
  normal — wait and re-probe); ChatGPT logged in (Yuan Liao Pro); the
  "Lean Pro Consult Handoff" project reachable with history intact; the
  project-scoped new-chat composer located. Consult protocol otherwise per
  CLAUDE.md (fresh chat per consultation), with two USER AMENDMENTS
  (2026-07-25): (a) expect ~20–30 MINUTES per Pro answer (not 5–10) — poll
  patiently before concluding failure; (b) Pro CANNOT read local files — the
  GitHub branch must be PUSHED up to the evidence commits before citing it
  (push of `codex/short-time-existence-align` is PRE-AUTHORIZED for consult
  evidence), or else ATTACH the needed files directly in the composer
  (添加文件 button). Prefer push+blob-links for multi-file evidence, attach
  for single-file questions. Autonomous-window queue: audit/accept K2.6b + K2.7 → dispatch
  K4 (`forwardUniqueRate_le` assembly) and the K5 closure kit (edge-Gronwall +
  integral-zero-to-equality + continuation) → K1C-b restatement once its
  remaining gaps allow → commission K2-B (second-Bianchi) as a dedicated
  long brick → hdens tower → K6 endgame wiring. Escalate to a consult on any
  R4-escalation signal or K2-B decomposition doubt.
- №14 (2026-07-25, IN FLIGHT): fifth wave, two Opus builders.
  **Agent-K2B6** — `Evolution/ForwardUniqueRmBridge.lean`: the R4 bridge —
  (1) per-flow own-metric (1,3)↔(0,4) evolution conversion (algebraic, ∇g = 0
  commutation), (2) the [g₁♭, Δ₂] commutator in divergence form (∇²g₁ = −A·g₁
  first; escalation per R4 if ∇A won't div-organize), optional (3) compose to
  retire the `hreal` fallback. **Agent-K27** — `Evolution/ForwardUniqueIBP.lean`:
  the SmoothCcTensor lift + `covDiv0SField` ↔ `covDivergence` identification +
  the lane-currency IBP corollaries (K4's entry point). Both: hardened hygiene
  (NO instances even private — report instead), standard protocol.
- №13 (2026-07-25, ACCEPTED — **K2A OUTCOME (A)** + **PLANNER RULING R4**):
  **Agent-K2A delivered `Evolution/ForwardUniqueRmDot.lean`** (691 lines, 16
  public + 9 private, 0 sorry; planner re-audit clean). Part 1: `rmDiffVec :=
  riemannOp(metricCov g₁) − riemannOp(metricCov g₂)` (canonical (1,3)
  difference, no supplied carrier), `rmDiffDot` two-term speed,
  `rmDiffLow_hasDerivAt` = K3's `hS` VERBATIM; `hPDE₂` again unnecessary.
  Part 2: `rmDiffComp_deriv` (generic in T₁ T₂) + `rmLowComp_deriv`; benign
  realization hypotheses `hL₁`/`hL₂` (supplied-`roughLapRm04` naming). Costs
  logged: `[BoundarylessManifold I M]` added (riemannOp reconcile);
  `private instance instContMDiffMetricCov` (:242, 4th InnerProductSpace-taint
  workaround — conditionally accepted, delete at campaign-end with the
  producer `omit`); `ContMDiffCovariantDerivative` is a MATHLIB root class
  (grep lesson).
  **RULING R4 (the lowering mismatch)**: the honest own-lowered Uhlenbeck
  interfaces' difference is `metricRm04At g₁ − metricRm04At g₂` ≠ S₀₄, and the
  gap's `Δ₁` sees uncontrolled `∇¹∇¹h₀₂` — carriers cannot be swapped post
  hoc. DECISION: keep the ruling's S₀₄ carrier (no ripple into K3/K2.4/K2.5)
  and bridge on the interface side — per flow, convert the own-lowered (0,4)
  interface to the (1,3) evolution ALGEBRAICALLY (own-metric raise; Δᵢ
  commutes with gᵢ♭/♯ since ∇ᵢgᵢ = 0 — no new frontier), difference at (1,3)
  = `rmDiffVec` (Part 1's object!), lower with g₁; the [g₁♭, Δ₂] commutator
  is A-algebraic (∇²g₁ = −A·g₁) with its ∇A-terms organized in DIVERGENCE
  FORM (second flux — Kotschwar's own organization; K2.3's machinery already
  proved this tractable on our stack). FALLBACK (recorded): the executor's
  mixed-lowering standing input `hreal`. ESCALATION: if the commutator
  div-organization fails on the Tensor0S stack → short Pro re-consult.
  Sub-brick K2.6b commissioned for the R4 bridge.
- №12 (2026-07-25, AUDIT HARDENING after user flag): the planner's hygiene
  grep (`^instance ` etc.) MISSED modifier-prefixed forms — a hardened sweep
  (`^(@\[..\] )?(noncomputable |private |protected |scoped |local |unsafe )*
  (axiom|instance|notation|opaque|macro|elab|syntax)\b`) found four
  `private local instance` (Borel measurable structure on E/M) in
  `ForwardUniqueEnergy.lean:249–252`, unreported by the executor. RULED
  BENIGN: identical idiom to the verified `StrongSolutionUniqueness.lean:39–42`
  (house pattern for measure-theory files); `private local` ⟹ file-local,
  non-leaking, no API contamination. Hardened grep is now the STANDARD
  acceptance check. All other lane files clean under the hardened sweep.
  COORDINATION NOTE: the user started the relocation chip
  ("movingReact0S → tensor layer") in a SEPARATE session — it may edit
  `ForwardUniqueEnergy.lean` + `Tensor0SMetricDeriv.lean`; this lane will not
  touch `ForwardUniqueEnergy.lean` until that session lands (K2A's brick does
  not edit it).
- №11 (2026-07-25, ACCEPTED — **T0S kit OUTCOME (A+)**): **Agent-T0S delivered
  `Tensor/RSTensor/FiberMetric/Tensor0SMetricIneq.lean`** (242 lines, 17 thms,
  0 sorry; planner re-audit clean — NOTE namespace is top-level
  `Tensor0SBundle`, matching the canonical layer). Full bilinearity layer +
  add/sub expansions + `abs_inner0S_le`/`normSq0S_add_le`/`normSq0S_sub_le` +
  frame-free Minkowski `sqrt_normSq0S_(add|sub)_le`. Route: `MetricFiberData.flat`
  LinearEquiv level (NEW LESSON: at the flat/Module.Dual level `rw` works —
  the FunLike diamond only bites at the CMM level); CS reused from
  `inner0S_sq_le_mul` (:467). `normSq0S_smul` correctly NOT duplicated (exists
  in `Tensor0SRiemannian/Scaling.lean:61`; LAYERING WART logged — it belongs
  down in `Tensor0SMetric.lean`). K1C-b gap (1) DISCHARGED. Dedup opportunities
  logged: HCG `sqrt_normSq0S_add_le` (basis+orthonormal hyps droppable at ~8
  call sites), HCG `normSq0S_neg` (frame-free replacement).
- №10 (2026-07-25, IN FLIGHT → T0S accepted above; K2A still running): fourth wave, two Opus builders.
  **Agent-K2A** — `Evolution/ForwardUniqueRmDot.lean`: the `∂ₜS₀₄` capstone —
  priority = `rmDiffDot` two-term speed + K3's `hS` feed (mirror K1C-a);
  then K2.6-core (Uhlenbeck-hypothesis subtraction + K2.3 spatial identity,
  supplied-`roughLapRm04` ↔ intrinsic realization as an explicit ∀-hypothesis).
  **Agent-T0S** — NEW canonical-layer file
  `Tensor/RSTensor/FiberMetric/Tensor0SMetricIneq.lean`: the fiber inequality
  kit (CS, `normSq0S_add_le`/`_sub_le`/`_smul`, abs-inner) unblocking K1C-b
  and the K4 rate estimates; Core-instantiation route, no component sums.
- №9 (2026-07-25, ACCEPTED — **K1C OUTCOME (B), the honest kind**):
  **Agent-K1C delivered `Evolution/ForwardUniqueConnDot.lean`** (628 lines,
  20 decls, 0 sorry; planner re-audit clean). K1C-a COMPLETE: the moving-
  carrier two-term speed `∂ₜA₀₃ = −2Ric₁((∇¹−∇²)·,·) + g₁(∂ₜ(∇¹−∇²)·,·)` as
  `connDiffDot` (genuine Tensor0SSpace 3); `connDiffLow_hasDerivAt_frame`
  produces K3's `hA` VERBATIM (R3 debt discharged); `connDiffVec_hasDerivAt`
  lifts K1's scalar components bilinearly, one chart frame per point, no atlas.
  BONUS FINDING: `hPDE₂` NOT needed (only g₁ lowers) — endpoint input bundle
  slimmed. `bilinOfComp`+`coeff_bilinOfComp`+`christoffelInFrame_sol` complete
  the K1→K3 wiring modulo the caller's `HasDerivWithinAt→HasDerivAt`.
  K1C-b DELIBERATELY NOT STATED (would hide four gaps behind a wrapper —
  correct per house rules): missing (1) Tensor0SSpace fiber triangle/CS API
  (smallest unblocker: `normSq0S_add_le` in `Tensor0SMetric.lean`),
  (2) lowering-isometry (blocked on the №3 `lowerAllSpace` omit),
  (3) generic (0,2)-lowering contraction bound, (4) the ∇Ric-difference →
  trace(∇¹S₀₄) Bianchi expansion — NOTE: `contracted_bianchi_of_second` is a
  hypothesis-shaped combinator, NOT a proved identity (check `second_bianchi`'s
  true status during K4 planning; affects K2-B scope). Statement blocker:
  no named `∇¹S₀₄` carrier yet. Durable lesson in the .md: Tensor0SSpace vs
  bare CMM is an INSTANCE DIAMOND — cross it with `exact` (defeq), never
  simp/rw; let `uncurryLeft` infer types.
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
