# HCG COMPACTNESS — PROJECT MAP (single entry point)

> **Wider program (2026-07-05):** this map covers the HCG compactness lane.
> The program-level plans sit one directory up:
> `../DimensionThree/HAM3_BLACKBOX_PLAN.md` (the 8 frontiers of `ham3_main`,
> incl. the Perelman no-local-collapsing box and its fill routes) and
> `../POINCARE_PLAN.md` (the Poincaré-endpoint master plan + infrastructure gap
> list).  HCG compactness is `ham3_cgh_limit`'s producer and Morgan–Tian
> `converge2`'s counterpart inside that program.

> **Migration (2026-07-07):** work moved from Claude (Fable) to Codex.  The
> full state/next-work/long-term handoff is the repo-root `CODEX_HANDOFF.md`
> (includes the durable lessons formerly held in the assistant's private
> memory).  New sessions: read `AGENTS.md` → this map → `CODEX_HANDOFF.md`.

Created 2026-07-05.  **Read this first**; it is the one place that ties the whole
Hamilton–Cheeger–Gromov compactness project together.  Keep it current: when an
endpoint, lane, or plan file changes, update the pointer here (one line), not by
writing a new overview elsewhere.

## 1. Goal and theorem tree (MSM135 Chapters 3–4)

```
Thm 3.10  Ricci-flow solution compactness            [Ch3 line]
  ⇐ Thm 3.9  metric compactness                      [Ch4 line, proved in book Ch4]
  ⇐ Lemma 3.11  whole-window C^p metric bounds       [DONE sorry-free, hShi = cited hyp]
  ⇐ hShi  Shi derivative estimates                   [CITED boundary, not a proof obligation]

Thm 3.9 (Ch4 proof) = Step A (good coverings, DONE)
                    → Step B (local metrics/transitions, ~1/3)
                    → Step C (center-of-mass averaging, ~3/4)
                    → Step D (direct limit + assembly; ENDPOINT 0% — no D6
                      assembly theorem; D1b local recursion closed but upstream
                      B1/compSep organs are still proof-frontier declarations)
                    + F-track engines (F1–F13, ~90%)
```

## 2. Endpoints and their `sorry`s (report progress ONLY against these)

| Endpoint | Where | Status |
|---|---|---|
| **Conditional Thm 3.9** `MetricCompactnessInputs.metricCompactness` | `C4/MetricCompactnessInputs.lean` | STATED 2026-07-05; `sorry` = the honest A→D assembly.  **The Ch4 target.** |
| Unconditional Thm 3.9 `metricCompactness` | `MetricCompactness.lean` | `sorry` = conditional endpoint + externally cited theorems (CGT, Bishop–Gromov, [H6]) + connectedness.  NOT dischargeable in-tree (no volume layer); out of Ch4 scope by the 2026-07-05 ruling. |
| Thm 3.10 upgrade (3.10 ⇐ 3.9) | `FlowLimitUpgrade.lean` + P4 chain | in flight (`P4_CONV_PLAN.md`) |
| Lemma 3.11 | capstone `covOrderBound_of_soln` chain | DONE sorry-free (hShi hypothesis) |

## 3. Live lanes and their entry documents

| Lane | Entry plan | State |
|---|---|---|
| Ch4 Step B/C (B1 assembly, lbl404 engine, C2') | `C4/CHAPTER4_PLAN.md` + `C4/STEPB_PLAN.md` + `C4/B1_JOIN_HANDOFF.md` + `C4/COMPCONV_HANDOFF.md` | active |
| Ch4 Step D | **`C4/STEPD_PLAN.md`** (2026-07-05) | plan ready; D3 lane is gate-free |
| Ch3 P4 final assembly (3.10 ⇐ 3.9) | `P4_CONV_PLAN.md` | active |
| Extension lane (interior-restart / Y1 3.11 inputs) | `ExtendShiInputs.md` + `Evolution/ExtendViaUniqueness` notes | active, separate from HCG critical path |
| Space-form / quotient curvature | memory note `spaceform-hardroute-build` + same-name `.md`s | parallel, unrelated to 3.9/3.10 |

Superseded/historical: `C4/STEPC_HANDOFF.md`, `C4/STEPC_B1_HANDOFF.md` (banners in
file), `PLANNER_HANDOFF.md`, `ARZELA_ASCOLI_PLAN.md` (delivered), `P3_PLAN.md`
(delivered).  Rule (2026-07-05): plan/architecture files live IN THE REPO —
do not leave approved plans only under `~/.claude/plans/`.

## 4. Honest-input audit (2026-07-05, per user request: "严格审查数学上哪些 inputs 是否成立")

Verdicts: **TRUE** = mathematically true as stated under Thm 3.9's hypotheses and
book-faithful; **FIXED** = the pre-audit statement was wrong and was corrected today.

| Input | Book cite | Verdict | Notes |
|---|---|---|---|
| `InjRadiusDecayInput` (A0) | `lbl384` (CGT) | **TRUE** | Lean form `a·min{ρ,1}^n·e^{−C·d}` matches the book verbatim; constants uniform in `k` since curvature bounds are. |
| `PackingBound` | `lbl387` | **TRUE** | per-radius count `A(r)`; no uniformity trap. |
| `VolumeComparisonInput` (A0') | Bishop–Gromov | **FIXED** | Uncapped-in-`r` multiplicity was **FALSE** (hyperbolic members: `r`-separated counts in `m·r`-balls grow like `e^{(n−1)(m−½)√C₀·r}`).  Now capped at containing scale `m * r ≤ r0`; consumers (`net_multiplicity`, `inter_count`) thread the needed Step-A ratio times `λ[0]` into the cap. |
| `RealizesEdist` | — | plumbing | provable at instantiation from `ProperMetricOn`; not external math. |
| `NormalCoordMetricBoundInput` | `lbl395` = [H6] Cor 4.12 | **TRUE** | per-center radius (positivity: `expMapC2Radius_pos`), `k`/center-uniform constants are genuine (Jacobi-ODE analysis depends only on curvature bounds; `∂g(0)=0`, `∂²g(0)~Rm`). |
| `ExpInverseDerivBoundInput` (S6) | `lbl418` | **FIXED** | Uncapped chart-overlap quantification was **over-strong** (no scale control; junk-`z` outside the exp source not excluded; `d(exp_x)` grows exponentially in negatively curved members).  Now: `r₁` cap + exp-source guard + image-in-`r₁`-ball guard — exactly the book's `r₁ ≤ min{inj/4, c/√C₀}` regime.  Consumer `exists_transitionLimit_normalTransition` min-strengthened. |
| `IsometryDerivBounds` (F8) | `lbl375` → [H6] §5 | **TRUE** (as hypothesis) | abstract per-map-sequence Prop; the polynomial recursion is the cited external content.  Bundle-v2 field shape gated on the B-loc brick. |
| `Item3RadiusInput` | `lbl391/392` ("D large") | satisfiable | pointwise-satisfiable today (`expMapC2Radius_pos`); the real content is uniformity = `lbl395`; **must be discharged at D6**, not carried to the endpoint. |
| `Item3GpScaleInput` | `lbl383/427` | satisfiable modulo `lbl395`-uniformity | same family; D6 discharge (choose `D` large against the uniform radius). |
| `SigmaScaleField` | `lbl383` family | satisfiable modulo `lbl395`-uniformity | `k`-independent `σ` needs `inf_k` radius > 0 = the same uniformity; D6 discharge. |
| `CmHessianInput` | `lbl413`-adjacent | **TRUE** at book scale | below the convexity radius `∂_z(exp⁻¹) ≈ −id`, Neumann-series invertibility; per-configuration honest input. |
| `StrictDistInput` | `lbl416/417` | **TRUE** at book scale | strict convexity of `½d²` below `min{inj/3, π/(6√K)}`. |
| endpoint `hconn` | book convention | added 2026-07-05 | connectedness is genuinely needed by the Hopf–Rinow proper realization (disconnected ⇒ emetric `⊤`); the book's manifolds are connected by convention. |

Meta-finding: 2 of the 12 audited inputs were mis-stated (one unsatisfiable, one
over-strong).  Rule going forward: any new honest-input structure gets a
one-paragraph "why is this true, at which scale, and who discharges it" note in
its docstring BEFORE consumers are built against it.

## 5. Label conventions (disambiguation — read before touching plans)

- `lblNNN` = MSM135 LaTeX labels (chapter4.tex/chapter3.tex).  **Cross-document
  references use `lblNNN` + a math name**; brick letters are plan-file-local.
- `C4/` the DIRECTORY = Chapter 4 modules.  "C1–C4" the ITEMS = Step C items
  (`lbl429/430/434/436`).  Say "Step C item 4", never bare "C4", in prose.
- "B1" = Step B item 1 (`lbl397`, `StepB1ApproxIso`).  The item-3 bricks
  formerly labeled B1–B5 live only in `ConvexBalls.md` history; P4's "Brick A/B"
  are Ch3-lane-local.  When ambiguity is possible, cite the file.
- P1–P4 = the Ch3 3.10⇐3.9 pipeline phases.  F1–F13 = Ch4 engine track.
  §2/§3/§6/§4 = the book's section numbers (non-monotone on purpose).

## 6. Honest progress (2026-07-05)

- **Conditional Thm 3.9 endpoint: stated, 0% proved.**  Its machinery: Step A done;
  Step B ~1/2 (`lbl394` done; B0 partial; **B1 assembly `stepB1_glue` PROVED
  sorry-free/axiom-clean 2026-07-05** — `exists_diffeo_of_injOn` construction +
  `BookApproxIsoPartialData` forward/reverse transport via `PreApproxIsoDataOn.congr`;
  `stepB1_approxIso` endpoint keeps ONE `sorry` = the C-track producer bundle
  (`lbl400/402/403` + lbl430-bounds), i.e. the B/C engine — **audit 2026-07-06
  (`C4/StepB1Producers.lean`): this bundle is BLOCKED BELOW the "engines ready"
  premise.**  **⭐ B1 ENDPOINT `stepB1_of_bounds` (ANY order `p`) DONE 2026-07-07
  (`C4/StepB1Producers.lean`, green/axiom-clean)**: the full `lbl397` conclusion at any
  `p` closes from honest chart-level inputs (local diffeo on `U` + `InjOn` + basepoint
  fix + forward/reverse `C⁰` `hc0` AND `C^p` covariant-derivative `hcov` bounds) via one
  `stepB1_glue` call fed by `preApproxIsoDataOn_of_bounds`.  `stepB1_zero`/
  `preApproxIsoDataOn_zero`/`bookApproxIsoData_zero` are the `p = 0` wrappers (vacuous
  `hcov`).  The `hcov` inputs are produced by `C4/PullbackField.lean`'s pullback-invariance
  machinery (`covNormWith_pd_zone` + `iterCov_metric_zero`); the endpoint consumes them.  The entire `C⁰`
  approximate-isometry lane (rounds 16–29) is now honest-input-to-endpoint:
  chart-perturbation `bilinPerturb`/`quadPerturbNeumann` → tensor-norm bridge
  `normSq0S_ortho`/`sqrtNormSq_le_of_comp`/`exists_gON(_bd)` → center-derivative
  `mfderivNormalCenter` → single-point `pullbackErrComp`/`pullbackErrNorm` → carriers
  `preApproxIsoDataOn_of_bounds`/`bookApproxIsoData_of_bounds` → endpoint
  `stepB1_of_bounds` (ANY `p`; `_zero` wrappers are the `p=0` case).  Gap to a fully
  UNCONDITIONAL `lbl397` = producing the endpoint's honest input bounds: the uniform-`hc0`
  compactness + the `hcov` covariant-derivative bounds (the latter's engine — pullback
  invariance `covNormWith_pd_zone`, `iterCov_metric_zero` — is BUILT in `C4/PullbackField.lean`;
  NOT a pinned frontier, contrary to an earlier retracted note) + the C-track input production. **(b) `lbl403` CLOSED 2026-07-07 (both halves, sorry-free/axiom-clean)**:
  manifold forward IFT `Geometry/Coordinates/LocalDiffeoIFT.lean` incl. the **`n = ∞`
  version** (`contMDiffOn_isLocalDiffeomorphOn_infty`, inverse-uniqueness upgrade of the
  order-1 diffeo) + Neumann `isInvertible_of_norm_id_sub_lt` + antilipschitz injectivity
  (`injOn_of_fderiv_near_id`) + chart-transfer `injOn_of_writtenInExtChart`; producers in
  `stepB1_glue`'s exact shape: `hlocOn_of_chartNeumann_infty` and the combined
  `hlocHinj_of_chartNeumann` (`(hloc, hinj)` pair from chart-Neumann data).  ALSO the
  `lbl404` C⁰/C¹ **diagonal engines** banked (`norm_pair_sub_self_le`,
  `fderiv_pair_sub_id_le`: diagonal identity + targets `C¹`-close ⟹ `dG ≈ id` — what the
  Neumann producers consume).  **`lbl404` ABSTRACT LAYER 100% 2026-07-07
  (`averagedCInf_id`, StepB1Producers): the "MISSING Faà-di-Bruno brick" line was STALE —
  `MapCInfConvOnCompacts.comp` is delivered, and the convergence route (comp +
  `mapCInfConv_prodMk`/`_pi`/`_const` + `congr` + the diagonal identities
  `centerOfMass_diag`/`chartCm_diag`/`diagEventuallyEqId`) needs NO quantitative
  derivative-difference bounds.**  Also `centerOfMass_delta` (δ-weights pin the center —
  the (d)-basepoint cm-core).  Remaining `lbl404`/B1 work = INSTANTIATION only: (i) POU
  weights (convergence φ_k→φ_∞ + basepoint concentration `δ_{α0}`, `StepCAveragePOU`
  lane); (ii) targets per-slot convergence (instantiate `comp_cInf_id_on` on the concrete
  transitions; C⁰ base = `stepCJoin`); (iii) `Φ_cm` `ContDiffOn ∞` + `CenterInput` family
  (C2 chain; quantitative variant awaits lbl430-bounds `j ≥ 2`); + the fixed-signature
  can't supply `stepCJoin`'s honest inputs.  B2–B6 open); Step C ~3/4
  (C1/C3/C4-shape done conditionally; C2
  regularity at `C^n` for every finite `n` DONE 2026-07-05 — `lbl430`(ii),
  `centerOfMass_contDiffAt`; C2 quantitative `|∇^j cm| ≤ C̃_j` bounds half
  (`lbl430`(i), `C4/StepCDerivBounds.lean`) — **base case + honest inputs DONE
  2026-07-05, axiom-clean**: `implicitDeriv_one_le` (abstract order-1 IFT bound
  `‖Df‖ ≤ Λ·B`, sorry-free), `CmHessianBoundInput` (`‖L⁻¹‖ ≤ Λ`, honest lbl413),
  `CmGDerivBound` (`‖∇^j G‖ ≤ B_j`, honest S6/lbl418 reduction), `cmChartFDerivLe`
  (`j=1`: `‖∇(chart∘cm)‖ ≤ Λ·B₁`, sorry-free); **2026-07-06 the Route-A minimal missing
  Mathlib bridge PROVED sorry-free/axiom-clean — `norm_iteratedFDeriv_ringInverse_le`
  (`‖∇^i (Ring.inverse) x‖ ≤ i!·‖x⁻¹‖^{i+1}`), the quantitative inverse-derivative
  Neumann bound**; **2026-07-06 ingredient (a) — the neighbourhood implicit-derivative formula —
  PROVED sorry-free/axiom-clean: `implicitFDeriv_eq` (pointwise) + `implicitFDeriv_eventuallyEq`
  (`∇f =ᶠ[𝓝 params₀] fun p => −(Ring.inverse (∂_zG(f p,p))).comp (∂_pG(f p,p))`), abstract, from
  eventual differentiability + `G(f,·)=0` + eventual z-block invertibility**; **2026-07-07 (b)
  j=2 LANDED sorry-free/axiom-clean: `graphBlockDeriv` (block-family derivative bound
  `‖∇(∂G∘graph)‖ ≤ ‖∇²G‖·(‖∇f‖+1)`), `implicitDeriv_two_le` (abstract `‖∇²f‖ ≤ Λ²a₂b₁ + Λb₂`),
  `CmHessianNbhdInput` (nbhd Hessian input bound to the center family, audit docstring), and the
  endpoint `cmChartDerivLe` j=2 case fully wired (`C²` regularity → eventual differentiability,
  `graphBlockDeriv` at `inl`/`inr` from `B 2`, `C̃₂ = Λ'²a₂B₁ + Λ'a₂`, `a₂ = B₂(ΛB₁+1)`)**;
  `cmChartDerivLe`'s ONE `sorry` is now the PURE (c) `j≥3` recursion; **2026-07-07 (c) analytic
  bricks ALSO landed green/axiom-clean** (`multilinear_prod_opNorm_le`, `norm_iteratedFDeriv_id_le`/
  `_graph_le`, `norm_iteratedFDeriv_invComp_le` (Faà-di-Bruno for `inverse∘A` on the unit set),
  `norm_iteratedFDeriv_graphComp_le` (Faà-di-Bruno through the graph)); remaining = c4/c5 pure
  threading (bilinear collection at `compL` + recursive constants + the strong induction — scoped
  in StepCDerivBounds.md); Step D ~35%
  (**D3 COMPLETE 2026-07-07 — `lbl408` all of D3a–D3e green, axiom-clean, zero warnings**:
  `Geometry/Topology/DirectLimitManifold.lean` = `ChartedSpace H Lim` (D3a) + `IsManifold I ∞ Lim`
  (D3b, `lbl409` transition crux) + σ-compact/T2/`T2Space (TangentBundle I Lim)` (D3c, via NEW
  `Geometry/Topology/FiberBundleT2.lean` general `FiberBundle.t2Space_totalSpace`) + **D3d metric
  transport `SmoothSeqSystem.limitMetric`**: per-factor metrics + isometry cocycle (`MetricCocycle`,
  D2c's shape) ⟹ `g∞` on `Lim` with `limitMetric_pullback : (incl k)^* g∞ = g k` — fiber form =
  pullback along the smooth local inverse `invFun (incl k)` (no derivative inverses), smoothness via
  the `cotangentCov_clmSection_smooth_aux` test-section engine + `tangentMapWithin`; D3e endpoint =
  `C4/StepDLimit.lean` `limitPointedCoc` (metrics+cocycle in → `PointedRiemannianManifold` out);
  no Step A/B/C imports.  **Plus 2026-07-07 later session: D4a DONE (`limitCGMaps` =
  `PointedRiemannianCGMaps` package of the `(incl k)⁻¹` comparison maps, + `rangeExhausts`,
  `factorSeq`, `inclPartialDiffeo`, limit connectedness `instConnectedSpaceLim`) and the D5
  distance cornerstones DONE (`enorm_mfd_incl` pointwise isometry, `pathELength_incl`,
  `edist_incl_le` 1-Lipschitz edist)**.
  **2026-07-07 (4th session) D1a + D1b machinery** (report as MACHINERY, not endpoint completion):
  D1a-(i) `exists_pullbackField`, D1a-(ii) `covNormWith_pd_zone` (zone-local partial-pullback
  cov-tower-norm naturality), D1a-(iii) `partialData_comp` (book lbl371 asymmetric form) +
  `PartialDiffeomorph.trans` — ALL PROVED SORRY-FREE, axiom-clean (consume F5/B1 which stay
  sorry-backed per the gate policy), in `C4/PullbackField.lean`; supporting
  `restrictOpen0S`/`tangentCoordChange_opens`/`tensor0SModelAt_opens` promoted to canonical
  `Tensor/RSTensor/Coordinates/OpensRestrict.lean` (0 sorry).  D1b `C4/StepDDirected.lean`:
  `chainComp`/`chainComp'` (two bracketings, equality-parameter right fold), `chainComp_coe_head`
  + `chainComp'_snoc`, `geomTailBudget`, `exists_strictMono_ge`, exact-zero separated base
  `reflSepData`, and the separated scalar ledger (`sepTail`, `sepBeta`, `sepFeed_le_beta`,
  `sepNextC0_le`, `sepNextCov_le`) are checked.  **2026-07-09: the `exists_directedApprox`
  local recursion body is CLOSED** in `StepDDirected.lean`: the active `hacc` carries separated
  `c0/cov` ledgers, uses peel-last `compSepFwd` and peel-first `compSepRev`, transports the
  right-fold inverse germ back to the left fold, and focused-checks with no local `sorry`
  warning.  It is **not axiom-clean yet** because it consumes `stepB1_approxIso` and the separated
  composition organs `compSepFwd`/`compSepRev`, which remain proof-frontier declarations.
  **HONEST SEPARATION (per CLAUDE.md rule):** D1b local theorem body = **100% modulo imported
  frontiers**; D1b axiom-clean completion remains blocked by those upstream frontiers.  The Step D
  ASSEMBLY endpoint (D6 discharging `metricCompactness`) is **0%** — not yet stated/proved.
  Step D **machinery estimate ≈ 85–86%** (NOT endpoint completion); remaining machinery: prove
  `compSepFwd`/`compSepRev`, D2 (lbl404-gated), D4b/c, D5a assembly, D6.
  F-track ~90% (F4 one mechanical sorry, F2-book todo).  Ch4 **machinery** overall ≈ **58%**;
  Ch4 endpoint theorems (metricCompactness / Step-D assembly) still **0%**.
- Unconditional Thm 3.9: 0%, intentionally out of scope (external citations).
- Ch3: Lemma 3.11 done (hShi hypothesis); P4 assembly in flight; 3.10 endpoint not
  yet assembled.
- **Whole HCG project — MACHINERY estimate ≈ 41–44%** (this is infrastructure coverage, NOT
  endpoint completion).  **Endpoint theorems (unconditional Thm 3.9, `metricCompactness`, and the
  Step-D assembly) remain 0% proved** — each still carries a sorry or is unstated.  D1b
  `exists_directedApprox` is locally closed but not axiom-clean because of upstream proof
  frontiers.  Do not read the machinery % as theorem completion.
  The riskiest open items (D3d metric transport RESOLVED 2026-07-07; D1a-(ii) naturality wall
  DISSOLVED 2026-07-07 — was a third walls-overcount, the restrictOpen/pullback stack pre-existed):
  the `lbl404` composition-convergence engine, the quantitative center-of-mass derivative bounds
  (`lbl430` bounds half), and the B1 producer bundle.

## 7. Real sorries in this tree (audited 2026-07-09)

`MetricCompactness.lean` (unconditional endpoint) · `C4/MetricCompactnessInputs.lean`
(conditional endpoint = the working target) · `C4/StepB1ApproxIso.lean` (B1 skeleton)
· `C4/Lemma45F4.lean` (F4 mechanical assembly) · `C4/StepCDerivBounds.lean`
(`cmChartDerivLe`, ONE sorry = the `lbl430`(i) general-`j` Faà-di-Bruno induction
step; base case `j≤1` + honest inputs sorry-free) · `C4/PullbackField.lean`
(`compSepFwd`/`compSepRev` proof organs still precise frontiers) ·
`C4/StepB1ApproxIso.lean` (B/C-track gate).  `C4/StepDDirected.lean` has no active local
proof `sorry` after the separated `hacc` replacement.  Other `sorry` grep hits in
`HCGCompactness/` may include docstring mentions; inspect before counting.  `Comparison/HopfRinow.lean` carries 4
dead sorries (3 unconsumed statements — see its header note); the C4 chain's
properness needs are served sorry-free by `HopfRinowProper.lean`.
