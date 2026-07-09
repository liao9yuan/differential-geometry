# `ham3_main` black-box audit and fill plan

Written 2026-07-05 (planning lane).  Scope: the seven theorem-shaped `sorry`s
behind the assembled Hamilton positive-Ricci endpoint
(`DimensionThree/HamiltonPositiveRicci.lean: ham3_main` / `thm_2_1`), plus the
one `MaximalTime.lean` frontier feeding them.  Difficulty audit + fill route for
each, with the Perelman boxes given priority per the 2026-07-05 user request.
Companion program document: `../POINCARE_PLAN.md` (the two Perelman boxes are
shared infrastructure with the Poincaré program — fill them once, in the shape
that program needs).

Status legend for "difficulty": **S** = assembly against existing in-tree
machinery; **M** = new theorem layer, no new foundations; **L** = new
foundational layer required.

## The eight frontiers

| # | Frontier | What it is mathematically | Difficulty | Fill route (summary) |
|---|---|---|---|---|
| 1 | `ham3_short_isSolution` | short-time existence: raw DeTurck data → `IsSolutionOn` bridge | M (active lane) | finish the ShortTime lane (see §1) |
| 2 | `ham3_flow_exists_normalized` | maximal continuation with finite-time curvature blow-up | M (active lane) | reduce to `extends_of_rmBounded` (#3) + `restart_short_time` glue (already built) |
| 3 | `extends_of_rmBounded` (`MaximalTime.lean`) | bounded `Rm` on `[0,T)` ⟹ extension past `T` | M | Shi-track: BBS all-`k` bricks are largely built; remaining = tower wiring + DeTurck/global-PDE handoff (`ExtendShiInputs.md`, `bbs-allk-route-status` memory) |
| 4 | **`ham3_noncollapse`** | **Perelman no-local-collapsing** at the blow-up scale | **L** | §2 below — the main subject of this plan |
| 5 | `ham3_cgh_limit` | Hamilton–CGH compactness of the rescaled flows | M/L (≈30% done) | = the HCG compactness project (`../HCGCompactness/PROJECT_MAP.md`); adapter `ham3OfCompactSol` already reduces it to `compactnessSol` + transfer producers |
| 6 | `limit_to_orig` | the compact CGH limit is diffeomorphic to the original `M`; transfer the constant-curvature metric back | M | §3 |
| 7 | `ham3_space_box` | closed 3-manifold with a constant-positive-sectional metric is a spherical space form (Killing–Hopf + quotient) | M/L | space-form lane (active; `spaceform-hardroute-build` memory) |
| 8 | `spaceForm_const_metric` | a spherical space form admits a constant-curvature metric | M | space-form lane (active, step 2/7 in flight) |

Everything else on the `ham3` chain — pinching §9/§10, point selection, blow-up
window bounds, the limit-side Einstein/constant-curvature argument — is
**checked** (see `IMPORTANT_THEOREM_INDEX.md`, "HamiltonPositiveRicci main
chain").  So `ham3_main` = these eight boxes.

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

`Ham3Noncollapse P Q κ r₀`: along the blow-up sequence, `κ`-noncollapsing
(`Perelman.KappaNoncollapsedAtBall`, `Perelman/Noncollapsing.lean` — definitions
exist, zero theorems) at scale `r₀` for the nested Perelman balls.  Hypotheses
already supplied by checked theorems: parabolic curvature bounds on the blow-up
windows (`_hrm`, from `ham3_rm_bound`) and the window discipline (`Ham3Window`).
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

## §3 `limit_to_orig` (frontier 6) — plan sketch

Content: the blow-up CGH limit `(N, g_∞)` of rescalings of a FIXED closed `M`
is diffeomorphic to `M`, so the constant-curvature metric transfers.  Route:
constant positive curvature ⟹ (Bonnet–Myers, in-tree `Comparison/BonnetMyers`)
`N` compact ⟹ in pointed-CGH convergence with compact limit, the comparison
maps are eventually **global** diffeomorphisms `N → M_k = M` (the exhaustion
stabilizes: `K = N` is compact); pull `g_∞` back.  This is a
compactness-interface theorem, to be proved against the HCG conclusion record
(a natural corollary of Step D's `MetricCompactnessConclusion` once the
directed-system layer exists — add it to `STEPD_PLAN.md` D4 as a compact-limit
corollary).  Difficulty M; ~2–4 weeks once Step D's D3/D4 exist.  Do not start
before then.

## §4 Space forms (frontiers 7–8) — already owned by the space-form lane

`spaceForm_const_metric` is in flight (S³ curvature + quotient route).
`ham3_space_box` (Killing–Hopf direction) is the harder half: constant-curvature
simply-connected complete ⟹ isometric to the round sphere, then deck-transform
quotient bookkeeping.  Keep both in that lane; nothing to re-plan here — only
note the dependency: `ham3_main` cannot close without them, and they are pure
global geometry (no flow content), so they parallelize perfectly with §1–§2.

## Critical path to `ham3_main`

```
short-time lane (§1: #1)         ──┐
extension lane  (§1: #2,#3)      ──┤
W-entropy NLC   (§2: #4, poles A1)─┼──→  ham3_main
HCG compactness (#5, ~30%)       ──┤
  └─ Step D D4 corollary → #6    ──┤
space-form lane (#7,#8)          ──┘
```
Five parallel lanes; the two poles are **#5 (HCG)** and **#4/A1 (parabolic
existence)**.  Honest estimate for `ham3_main` fully sorry-free:
**12–20 months** at current velocity, dominated by those two poles.

## Status log

- 2026-07-05: audit written.  `ham3_main` assembled and checked modulo the 8
  frontiers; `ham3_noncollapse` route decision (A vs B) is OPEN for the user —
  recommendation: Route A.
