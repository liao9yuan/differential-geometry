# HCG COMPACTNESS — PROJECT MAP (single entry point)

> **Wider program (2026-07-05):** this map covers the HCG compactness lane.
> The program-level plans sit one directory up:
> `../DimensionThree/HAM3_BLACKBOX_PLAN.md` (the original 8-frontier audit for
> `ham3_main`; 6 remain open, incl. the Perelman no-local-collapsing box) and
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
Thm 3.10  Ricci-flow solution compactness            [unconditional endpoint 0%;
                                                       conditional wrapper checked]
  ⇐ Thm 3.9  metric compactness                      [Ch4 line, proved in book Ch4]
  ⇐ Lemma 3.11  whole-window C^p metric bounds       [DONE sorry-free, hShi = cited hyp]
  ⇐ hShi  Shi derivative estimates                   [CITED boundary, not a proof obligation]

Thm 3.9 (Ch4 proof) = Step A (good coverings, DONE)
                    → Step B (local metrics/transitions, ~1/2)
                    → Step C (center-of-mass averaging, ~3/4)
                    → Step D (direct limit + assembly; ENDPOINT 0% — D2/D3/D4
                      ambient convergence is checked; D5 metric exhaustion,
                      shrunk-stage metric transport, D6 assembly, and the B1
                      raw producer remain open)
                    + F-track engines (F1–F13, ~95%)
```

## 2. Endpoints and their `sorry`s (report progress ONLY against these)

| Endpoint | Where | Status |
|---|---|---|
| **Conditional Thm 3.9** `MetricCompactnessInputs.metricCompactness` | `C4/MetricCompactnessInputs.lean` | STATED 2026-07-05; `sorry` = the honest A→D assembly.  **The Ch4 target.** |
| Unconditional Thm 3.9 `metricCompactness` | `MetricCompactness.lean` | `sorry` = conditional endpoint + externally cited theorems (CGT, Bishop–Gromov, [H6]) + connectedness; out of Ch4 scope by the 2026-07-05 ruling. |
| Conditional Thm 3.10 `solutionComp_cond` / `compactnessSol_cond` | `C4/SolutionCompactnessInputs.lean` + `HamiltonCompactness.lean` | checked consumer from conditional Thm 3.9 plus concrete `FlowUpgradeData`; it does not prove the upstream 3.9 frontier or unconditional Thm 3.10 |
| Lemma 3.11 | capstone `covOrderBound_of_soln` chain | DONE sorry-free (hShi hypothesis) |

## 3. Live lanes and their entry documents

| Lane | Entry plan | State |
|---|---|---|
| Ch4 Step B/C (B1 assembly, lbl404 engine, C2') | `C4/CHAPTER4_PLAN.md` + `C4/STEPB_PLAN.md` + `C4/B1_JOIN_HANDOFF.md` + `C4/COMPCONV_HANDOFF.md` | active |
| Ch4 Step D | **`C4/STEPD_PLAN.md`** + `C4/StepDLimitMetrics.md` | active; D2/D3/D4 ambient convergence and shrunk-tail compact containment checked; D5 metric exhaustion, tail metric transport, and D6 open; recount stopped at 3/3 |
| Ch3 P4 producer lane (3.10 ⇐ 3.9) | `P4_CONV_PLAN.md` + `ConvFieldEndgame.md` | producer hypotheses remain active; canonical conditional wrappers are checked |
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

## 6. Honest progress (updated 2026-07-09)

- **Conditional Thm 3.9 endpoint: stated, 0% proved.**  Its machinery: Step A done;
  Step B ~1/2 (`lbl394` done; B0 partial; **B1 assembly `stepB1_glue` PROVED
  sorry-free/axiom-clean 2026-07-05** — `exists_diffeo_of_injOn` construction +
  `BookApproxIsoPartialData` forward/reverse transport via `PreApproxIsoDataOn.congr`;
  **2026-07-09 statement repair:** the false P-only `stepB1_approxIso` and its `sorry`
  were removed.  `StepB1RawInput` now exposes the C-track producer boundary, and
  `stepB1_of_raw` is the checked conditional assembly.  Producer of that package
  from the endpoint inputs: 0%; textbook B1 theorem: 0%.  **⭐ B1 ENDPOINT
  `stepB1_of_bounds` (ANY order `p`) DONE 2026-07-07
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
  NOT a pinned frontier, contrary to an earlier retracted note) + the C-track input production.
  **2026-07-09 radial-separation closure:** `mfderiv_exp_radial` + `radialEnorm_normal` close the
  former velocity-`hderiv` API gap, and `normLowerOfSepExp` now derives the coordinate norm lower
  bound directly from named-exp-ball containment and Riemannian separation.  This improves the
  producer machinery but does not change the rounded totals: the `StepB1RawInput` producer and
  textbook B1 theorem remain 0%; Step-B machinery remains about 50%.
  **Later 2026-07-09:** `seqCenter_zero` / `seqCenter_edist_ge` and
  `seqChartNorm_ge` connect the actual ordered-net centers to that coordinate
  lower bound.  The former POU representation mismatch is now resolved:
  `centerAverage.WeightDataOn`, `normWeights_data` / `bumpWeights_data`,
  `NetLimitData.unifHatCageData`, and `stepCJoinDataFixed` give a checked
  explicit-weight route through the current radius-`4 * lamInf` hat endpoint,
  while the bundled POU entrypoints remain available.  `bumpNum_sum_one`
  reduces the book-cutoff denominator bound to ordinary inner-ball coverage
  plus the concrete fact that the cutoff's non-one locus lies in the base
  inner ball.  The remaining producer work is the intrinsic quadratic
  chart-bump family and these two support/coverage facts; the literal MSM135
  radius-`5 * lamInf` support instantiation is still distinct.  The rounded
  progress totals remain unchanged.
  **(b) `lbl403` CLOSED 2026-07-07 (both halves, sorry-free/axiom-clean)**:
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
  (C2 chain; quantitative variant awaits the honest all-order lbl430 bounds); the
  `StepB1RawInput` producer must thread `stepCJoin`'s honest inputs.  B2–B6 open); Step C ~3/4
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
  checked `cmChartDerivLe2` fully wires j≤2 (`C²` regularity → eventual differentiability,
  `graphBlockDeriv` at `inl`/`inr` from `B 2`, `C̃₂ = Λ'²a₂B₁ + Λ'a₂`, `a₂ = B₂(ΛB₁+1)`)**.
  **2026-07-09 statement repair:** the former all-order `cmChartDerivLe` was removed because C²
  regularity and constraints on only `Ctil 0/1/2` cannot imply j≥3 bounds.  The honest all-order
  theorem remains unstated/0% and needs order-p regularity plus a recursive majorant.  **2026-07-07 (c) analytic
  bricks ALSO landed green/axiom-clean** (`multilinear_prod_opNorm_le`, `norm_iteratedFDeriv_id_le`/
  `_graph_le`, `norm_iteratedFDeriv_invComp_le` (Faà-di-Bruno for `inverse∘A` on the unit set),
  `norm_iteratedFDeriv_graphComp_le` (Faà-di-Bruno through the graph)); remaining = c4/c5
  (bilinear collection at `compL` + recursive constants + the strong induction — scoped
  in StepCDerivBounds.md); Step D machinery ~88%
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
  `sepNextC0_le`, `sepNextCov_le`) are checked.  **2026-07-09: the conditional consumer
  `directed_of_b1` is CLOSED** in `StepDDirected.lean`: the active `hacc` carries separated
  `c0/cov` ledgers, uses peel-last `compSepFwd` and peel-first `compSepRev`, transports the
  right-fold inverse germ back to the left fold, and focused-checks with no local `sorry`
  warning.  **2026-07-09 later: the separated composition organs `compSepFwd`/`compSepRev`
  are now proved in `PullbackField.lean`**.  **2026-07-09 F4/F5 CLOSED:**
  `claim1MulConst` / `lemma45_F3_bound` expose data-independent scaled constants,
  `RicBoundGoodFrame.metricComp_mul` absorbs the good-frame and metric-swap loss,
  and both `lemma45_corII` and `lemma45_corII_unif` are proved.  F5,
   `PullbackField`, and `StepDDirected` verify downstream.  The former false B1
   dependency is now an explicit `StepB1RawInput` argument.  **2026-07-09 D1-to-D2
   REALIZATION LANDED:** `SeqSystem.ofSucc`, `SmoothSeqSystem.ofSucc`, the range-scoped
   open-ball restriction API, and `StepDLimitMetrics.directedBallSystem` turn the eventual
   D1 maps into a tail-shifted smooth open-ball system.  The former `lbl404` gate is also
   green in `MapConvergenceComp.lean`.  D2's actual ball pullback metric, ambient-inner
   readout, restriction covariant-norm bridge, positive-order bounds, and `C0` lower/upper
   plus order-zero bounds are checked locally.  **2026-07-09 D2 PREFIX-TAIL GEOMETRY
   LANDED:** target-normalized chain splitting, nested/composite pullback equality,
   prefix image containment, and exact positive-order bound transport are focused green.
   `metricComp_iter_refs` converts bounds measured against an order-dependent prefix reference
   into uniform chart-component derivative bounds.  **D2a COMPLETE 2026-07-09:**
   `engine_input_refs` now propagates through `metricPreconv_refs` and `metricCInf_refs`;
   `chainPullback_bdd` proves the concrete fixed-stage pullback sequence's bounds, and
   `exists_chain_limit`/`exists_chain_data` produce its stagewise C-infinity limits from the
   eventual D1 package.  The live D2 frontier is the common diagonal, `lbl407`, and the cocycle.
  **HONEST SEPARATION (per CLAUDE.md rule):** conditional D1b consumer body = **100% checked**;
  producing `StepB1RawInput` and proving the textbook D1b theorem remain **0%**.  The Step D
  ASSEMBLY endpoint (D6 discharging `metricCompactness`) is **0%** — not yet stated/proved.
   Step D **machinery estimate ≈ 88%** (NOT endpoint completion); remaining machinery:
   the B/C producer bundle for D1 axiom-clean status, the D5 metric-exhaustion
   producer, shrunk-stage metric transport, and D6 reindex/assembly.
  F-track ~95% (F4 is closed; F2-book wrapper remains).
   Ch4 **machinery** overall ≈ **58–59%**;
  Ch4 endpoint theorems (metricCompactness / Step-D assembly) still **0%**.
- Unconditional Thm 3.9: 0%, intentionally out of scope (external citations).
- Ch3: Lemma 3.11 done (hShi hypothesis).  The canonical conditional assembly
  `solutionComp_cond` → `compactnessSol_cond` is checked from conditional Thm 3.9
  plus concrete `FlowUpgradeData`; its remaining producer hypotheses stay in the
  P4 lane.  Unconditional Thm 3.10 remains 0%.  **2026-07-09 noncollapse repair:**
  the canonical Perelman layer
  now defines actual time-slice metric balls, Riemannian volume, parabolic
  curvature control, and model-dimension kappa lower bounds.  Hamilton's
  `Ham3Noncollapse` now ranges over genuine `paraSolution` rescalings; the fake
  `Ham3BallPair`/numeric-volume path was removed.  The checked data/realization
  machinery includes the proved `ham3_rm_control` theorem and is about 40%, while
  `ham3_noncollapse`, no-local-collapsing, and the
  Cheeger-Gromov-Taylor `flowInj_of_vol` producer theorems remain 0%.
  **2026-07-09 CGH/3.10 repair:** `Ham3CGHLimitData` now retains the real source,
  original-index composition, `SmoothCGHConverges` maps, source-to-original
  diffeomorphisms, and limit-slice completeness.  The forgetful adapter and
  arbitrary `HamCGHTopology.lift` wrapper were removed.  `LimitRoundAt` keeps
  the exact complete slice and Ricci lower bound used by the repaired
  `limit_to_orig` statement.  `PointedRiemannianManifold.compact_of_ricci` and
  `PointedCGHMaps.exists_source_univ` / `target_univ` / `globalDiffeomorph`
  provide the real compact-limit globalization route, and `limit_to_orig` is
  now checked with no `sorry` (**theorem 100%**).  Separately, the conditional route
  `MetricCompactnessInputs.metricCompactness -> FlowUpgradeData ->
  solutionComp_cond -> compactnessSol_cond` is checked and makes zero calls to
  the unconditional Theorem 3.9; the former exact-conclusion backend has been
  removed.  This conditional assembly machinery is 100%; unconditional Theorem 3.10 and
  `ham3_cgh_limit` remain 0% pending the common-window/source compactness producer.
  The Hamilton contract now makes that producer exact: `Ham3SourceRealizes`
  carries common-time inclusion, selected basepoints, and pullback equality to
  the actual rescaled metrics; `Ham3CompactInput` retains the raw curvature
  bound, window, kappa, and noncollapse; both black boxes carry the finite
  maximal-time interval.  Transfers are bound to the actual CGH witness rather
  than quantified over arbitrary limits.  This contract refactor is checked
  infrastructure, not completion of either producer.
- **Whole HCG project — conservative MACHINERY estimate ≈ 45%** (this is infrastructure coverage,
  NOT endpoint completion).  **HCG endpoint theorems (conditional/unconditional Thm 3.9,
  the Step-D assembly, unconditional Thm 3.10, and `ham3_cgh_limit`) remain 0% proved** — each
  still carries a `sorry` or is unstated.  The
  `directed_of_b1` consumer is checked only from explicit `StepB1RawInput`; do not read that
  conditional assembly or the machinery % as theorem completion.
  The riskiest open items (D3d metric transport RESOLVED 2026-07-07; D1a-(ii) naturality wall
  DISSOLVED 2026-07-07 — was a third walls-overcount, the restrictOpen/pullback stack pre-existed):
  the arbitrary-order quantitative center-of-mass derivative theorem
  (`lbl430` bounds half), the B1 raw producer, and the D5 metric-exhaustion /
  shrunk-stage metric / D6 assembly chain.

## 7. Real sorries in this tree (audited 2026-07-09)

`MetricCompactness.lean` (unconditional endpoint) · `C4/MetricCompactnessInputs.lean`
(conditional endpoint = the working target) · `C4/PullbackField.lean`
(older ordinary `compDataFwd`/`compDataRev` wrappers remain frontiers; the D1b separated
`compSepFwd`/`compSepRev` organs are proved).  `C4/StepB1ApproxIso.lean` has no `sorry` after the
false P-only endpoint was replaced by `StepB1RawInput` plus `stepB1_of_raw`.
`C4/StepCDerivBounds.lean` also has no `sorry`: it now exposes only the checked order-two theorem
`cmChartDerivLe2`; the honest arbitrary-order theorem is not yet stated.
`C4/StepDDirected.lean` has no active local
proof `sorry` after the separated `hacc` replacement.  Other `sorry` grep hits in
`HCGCompactness/` may include docstring mentions; inspect before counting.  `Comparison/HopfRinow.lean` carries 4
dead sorries (3 unconsumed statements — see its header note); the C4 chain's
properness needs are served sorry-free by `HopfRinowProper.lean`.

The public `HCGCompactness.lean` umbrella imports the new modules and passed a
focused check after the Hamilton and adapter module refreshes.
