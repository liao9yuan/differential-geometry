# `ham3_main` black-box audit and fill plan

Written 2026-07-05 and live-updated 2026-07-09.  The original scope was seven
theorem-shaped `sorry`s behind the assembled Hamilton positive-Ricci endpoint
plus one `MaximalTime.lean` frontier.  Two of those eight boxes are now closed:
`limit_to_orig` and `spaceForm_const_metric`.  Five theorem-shaped `sorry`s
remain in `HamiltonPositiveRicci.lean`, plus the upstream `MaximalTime.lean`
frontier.
Companion program document: `../POINCARE_PLAN.md` (the two Perelman boxes are
shared infrastructure with the Poincaré program — fill them once, in the shape
that program needs).

Status legend for "difficulty": **S** = assembly against existing in-tree
machinery; **M** = new theorem layer, no new foundations; **L** = new
foundational layer required.

## Original eight frontiers (six remain open)

| # | Frontier | What it is mathematically | Difficulty | Fill route (summary) |
|---|---|---|---|---|
| 1 | `ham3_short_isSolution` | short-time existence: raw DeTurck data → `IsSolutionOn` bridge | M (active lane) | finish the ShortTime lane (see §1) |
| 2 | `ham3_flow_exists_normalized` | maximal continuation with finite-time curvature blow-up | M (active lane) | reduce to `extends_of_rmBounded` (#3) + `restart_short_time` glue (already built) |
| 3 | `extends_of_rmBounded` (`MaximalTime.lean`) | bounded `Rm` on `[0,T)` ⟹ extension past `T` | M | Shi-track: BBS all-`k` bricks are largely built; remaining = tower wiring + DeTurck/global-PDE handoff (`ExtendShiInputs.md`, `bbs-allk-route-status` memory) |
| 4 | **`ham3_noncollapse`** | **Perelman no-local-collapsing** at the blow-up scale | **L; endpoint 0%** | actual `FlowMetricBall` data and `ham3_rm_control` are checked; §2 is the remaining producer |
| 5 | `ham3_cgh_limit` | Hamilton–CGH compactness of the rescaled flows | M/L; **endpoint 0%**, whole-HCG machinery ≈45% | = the HCG compactness project (`../HCGCompactness/PROJECT_MAP.md`); keep machinery and endpoint accounting separate |
| 6 | `limit_to_orig` | compact limit globalizes the CGH maps and transfers the constant-curvature metric back | **CLOSED, theorem 100%** | Bonnet--Myers + `PointedConvergenceGlobal` + metric pullback; §3 |
| 7 | `ham3_space_box` | closed 3-manifold with a constant-positive-sectional metric is a spherical space form (Killing–Hopf + quotient) | M/L | space-form lane (active; `spaceform-hardroute-build` memory) |
| 8 | `spaceForm_const_metric` | a spherical space form admits a constant-curvature metric | **CLOSED, theorem 100%** | checked quotient-round-metric construction |

Everything else on the `ham3` chain — pinching §9/§10, point selection, blow-up
window bounds, the limit-side Einstein/constant-curvature argument, #6, and #8 — is
**checked** (see `IMPORTANT_THEOREM_INDEX.md`, "HamiltonPositiveRicci main
chain").  Thus `ham3_main` still depends on the six open boxes above; checked
consumers do not reduce an open producer endpoint above 0%.

## §1 Short-time + extension (frontiers 1–3) — active lanes, no new plan needed

Current live frontier files: `ShortTime/DeTurckRicciPde.lean` (2 sorries),
`ShortTime/WeylEigenvalueCountingBound.lean` (2), `ShortTimeFlow/
ConjugatingFlowProperties.lean` (2), `ShortTimeFlow/ForwardFlow.lean` (1),
`MaximalTime.lean` (1).  These lanes have their own plans
(`ShortTimeExistence.md`, `ExtendShiInputs.md`, `Evolution/DeTurckHandoff.md`);
this document only records that they are prerequisites of `ham3_main` and —
important for §2 — that their **linear parabolic machinery is the natural seed
of the scalar parabolic layer** the W-entropy route needs.

## §2 `ham3_noncollapse` — the Perelman box (the real subject)

### What exactly is assumed

`Ham3Noncollapse P Q hsel κ r₀`: along the blow-up sequence, the genuine
`FlowMetricBall`s in the actual `paraSolution` are `κ`-noncollapsed at scale
`r₀`.  `ham3_rm_control` is checked and supplies `IsRmControlled` on those
balls from `ham3_rm_bound` plus `Ham3Window`; no arbitrary numeric-volume or
`Ham3BallPair` wrapper remains.
So the box is exactly: *closed 3-manifold, Ricci flow on `[0,T)`, `T < ∞`,
curvature control near the singular time ⟹ κ-noncollapsed at comparable scales*
— Perelman's no-local-collapsing theorem, applied along `Q`.

### What is already in-tree (better than expected)

* **Riemannian volume + integration are NOT missing**:
  `Analysis/Integration/Measure/RiemannianMeasure.lean` +
  `riemannianVolumeMeasure` (`Invariance.lean:423`), divergence theorem
  (closed + boundary + Green), integration by parts, L² layer, `VolumeVariation`,
  `JacobiFormula` — the whole `Analysis/Integration` tree is **0-sorry**.
  (The HCG honest-input notes say "Mathlib has no Riemannian volume" — true of
  Mathlib, no longer of this project.)
* **The W-entropy layer is started**: `Entropy/Defs.lean` has `wFunctional`
  (over a supplied measure), scale/diffeomorphism invariance, first-variation
  interfaces; `Entropy/FirstVariation.lean` + `Entropy/F/` (9 files, incl.
  `Formula510Core`, `Final`) are building the F-functional variation formulas.
* Maximum principles: `MaximumPrinciple/ScalarWeak.lean`, `TensorWeak/`.

### Route decision

**Route A — W-entropy (Perelman §4).**  Chain: F/W first variation (in
progress) → W-monotonicity along the flow coupled to the **conjugate heat
equation** → log-Sobolev at small scales ⟹ volume lower bound (ε-regularity
step) → κ along `Q`.  Missing pieces, in order:
1. `A1` conjugate-heat existence: linear scalar parabolic existence/uniqueness
   on a closed manifold, coefficients from a smooth metric family.  **The only
   L-grade item on this route** — and it overlaps the DeTurck/ShortTime linear
   theory and the Weyl/spectral bricks already being built.  (~2–4 months.)
2. `A2` W-monotonicity: the Perelman integrand computation — pure tensor
   calculus + integration by parts, both native strengths of this tree; the
   Entropy lane's 5.10-family formulas are exactly its middle.  (~2–3 months.)
3. `A3` Euclidean log-Sobolev input + comparison (either prove the Gaussian
   log-Sobolev natively or take it as a clearly-cited analytic input at first;
   it is a self-contained ℝⁿ fact).  (~1 month as input, ~2–3 to prove.)
4. `A4` ε-regularity conversion: `W`-lower-bound + curvature bound on the ball
   ⟹ volume ratio lower bound (test-function argument).  (~1–2 months.)

**Route B — L-length / reduced volume (Perelman §7, Morgan–Tian Ch 6–8).**
No parabolic PDE existence needed (its monotonicity is pointwise Jacobian
comparison along L-geodesics), but requires a whole parallel geometry layer:
L-geodesics, L-exponential, L-Jacobi fields, monotonicity of reduced volume
with the measurable cut-locus bookkeeping.  (~8–12 months standalone.)
**This layer is MANDATORY for the Poincaré program anyway** (the surgery-stable
noncollapsing of Morgan–Tian Ch 16 is L-length-based; the W-route does not
survive surgery).

**Recommendation (decide before starting):** fill `ham3_noncollapse` by
**Route A** — it is the shortest path to closing `ham3_main` (its one hard item
A1 is shared with the active short-time lane, and A2 continues an existing
lane), and it does not waste work: W-entropy is independently on the Poincaré
list (M–T uses it nowhere essential, but the F/W layer already exists and A1
is needed by the standard solution and extinction phases regardless).  Build
Route B when the Poincaré program's Phase P2 starts (see `POINCARE_PLAN.md`);
do NOT build it merely for `ham3`.

Total for `ham3_noncollapse` via Route A: **≈ 6–10 months of sessions**, of
which A1 is the pole.  This is the second-longest pole of `ham3_main` (the
longest being #5 = HCG compactness, both in flight conceptually).

## §3 `limit_to_orig` (frontier 6) — CLOSED 2026-07-09

Content: the blow-up CGH limit `(N, g_∞)` of rescalings of a fixed closed `M`
is diffeomorphic to `M`, so the constant-curvature metric transfers.  The implemented route is:
constant positive curvature ⟹ (Bonnet–Myers, in-tree `Comparison/BonnetMyers`)
`N` compact ⟹ in pointed-CGH convergence with compact limit, the comparison
maps are eventually **global** diffeomorphisms `N → M_k = M` (the exhaustion
stabilizes: `K = N` is compact); pull `g_∞` back.  The reusable producers are
`PointedRiemannianManifold.compact_of_ricci` and
`PointedCGHMaps.exists_source_univ` / `target_univ` / `globalDiffeomorph` in
`HCGCompactness/PointedConvergenceGlobal.lean`.  `limit_to_orig` now consumes
the retained CGH maps, source-to-original diffeomorphisms, and slice
completeness, and is checked with no `sorry` (**theorem 100%**).  This closes
only the consumer; `ham3_cgh_limit` remains 0%.

## §4 Space forms (frontier 7 open; frontier 8 closed)

`spaceForm_const_metric` is checked (S³ curvature + quotient route).
`ham3_space_box` (Killing–Hopf direction) is the harder half: constant-curvature
simply-connected complete ⟹ isometric to the round sphere, then deck-transform
quotient bookkeeping.  Keep #7 in that lane; `ham3_main` cannot close without
it, and it is pure global geometry (no flow content), so it parallelizes with
§1–§2.

## Critical path to `ham3_main`

```
short-time lane (§1: #1)         ──┐
extension lane  (§1: #2,#3)      ──┤
W-entropy NLC   (§2: #4, poles A1)─┼──→  ham3_main
HCG compactness (#5; endpoint 0%,
  machinery ~45%)                ──┤
space-form lane (#7)             ──┘
```
Four parallel lanes; the two poles are **#5 (HCG)** and **#4/A1 (parabolic
existence)**.  Honest estimate for `ham3_main` fully sorry-free:
**12–20 months** at current velocity, dominated by those two poles.

## Status log

- 2026-07-05: audit written.  `ham3_main` assembled and checked modulo the 8
  frontiers; `ham3_noncollapse` route decision (A vs B) is OPEN for the user —
  recommendation: Route A.
- 2026-07-09: `ham3_rm_control` landed on genuine `FlowMetricBall`s;
  `ham3_noncollapse` remains 0%.  `PointedConvergenceGlobal` and
  `limit_to_orig` landed and are checked (frontier #6 closed, theorem 100%);
  `spaceForm_const_metric` is checked (frontier #8 closed).  `ham3_cgh_limit`
  remains 0%; whole-HCG machinery is conservatively about 45%, with HCG
  endpoints still 0%.
- 2026-07-09 interface audit: `ham3_noncollapse` and `ham3_cgh_limit` now retain
  the finite maximal-time interval.  `Ham3CompactInput` keeps the raw rescaled
  curvature bound, common window, kappa, and geometric noncollapse, while
  `Ham3SourceRealizes` ties the CGH source metrics and basepoints to the actual
  selected rescalings.  The refactor and public umbrella are checked; both
  producer theorems remain 0%.
