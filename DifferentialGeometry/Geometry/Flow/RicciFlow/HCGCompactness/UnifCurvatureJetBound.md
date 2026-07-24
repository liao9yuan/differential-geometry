# UnifCurvatureJetBound — brick (2a) design note (item-6 S1 gate)

Session 3 recon (Opus 4.8, LANE C) in worktree
`C:/Users/liao9/.codex/worktrees/e87b/...`, branch `codex/analytic-producers-e87b`.
**No `.lean` written this session** (see §6 for why — two design-gating findings
need planner ratification before a build commits).  This is the design note for
the FUTURE leaf `HCGCompactness/UnifCurvatureJetBound.lean`.

## Target (planner-ratified brick 2a, order-generic)

`MetricCovDerivOrderBoundOn Set.univ (≤ b+2) g₀ gBase Λ` + `Λ`-comparability ⟹
`sup_x ‖∇^{g₀,a} Riemann(g₀)‖_{g₀} ≤ F(Λ, n)` for every `a ≤ b`, in the currency
`ccR/ccdR` consume (the appFullSec window sups of the Riemann hom-fields `H_R`,
`H_dR` — `PointwiseTensorCurvFirstOrderSection.lean:1444`, built from
`gradArmSection`/`diffArmSection`, i.e. from `Riemann(g₀)` and `∇Riemann(g₀)`).
`UnifBochnerGap.lean` (S1) plugs this into `K 0 = √(2·ccR 0 + 2·ccdR 0)` and the
commutator `Cfun` (audit §7.2 of `UNIF_ITEM6_RECON.md`).

## FINDING A (de-risking) — (2a) is an ASSEMBLY of existing jet-envelope machinery, NOT a missing layer

The curvature-difference + connDiff jet-envelope estimates already exist:

- `exists_riemannOp_LeviCivita_difference_gQuadratic_le_of_jetEnvelope`
  (`Geometry/Curvature/PerturbedRiemannOpDifferenceBound.lean:88`): for
  `g₁ = g₀ + P` with `∑_{j<3}‖∇^{g₀,j}P‖ ≤ B` and `gFibreOpBound g₀ (…P) δ`,
  `δ ≤ δ₀ < 1`, gives `‖Riemann(g₁) − Riemann(g₀)‖²_{g₀} ≤ C(δ₀,B)²·|v|²|w|²|u|²`,
  `C = √(2·CA + 2·C0²B²)`.  **This is the order-0 curvature difference** (I had
  wrongly listed it "missing" in the session-1 recon).
- `exists_norm_covGrad_connDiffSection_le_of_jetEnvelope`
  (`Geometry/Curvature/CovDerivConnDiffQuadraticBound.lean:43`): the connDiff
  order-1 covGrad bound from the same jet-envelope.
- `exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope`,
  `connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one`,
  `rfns_raisedKoszul_le_of_lt_one`, … (same file family) — the Koszul /
  Christoffel-difference building blocks.
- HCG layer: `CurvDerivBoundOn` / `CurvDerivBoundsOnWindow`
  (`AllTimesBounds.lean:3556/3572`) is a curvature-derivative bound predicate
  ALREADY paired with `MetricCovDerivOrderBoundOn` (Lemma 3.11 content, `:3760`);
  `normSqRS_connDiff_eq_componentL2Sq3` relates connDiff to metric-jet components
  in the `MetricCovDerivOrderBoundOn` context (`AllTimesBounds.lean:1975/2473`).
- The Christoffel-difference tensor `A = connDiff g₁ g₀` with the Koszul identity
  `2g₁(A(X,Y),Z) = (∇⁰g₁)(Y,Z)+(∇⁰g₁)(X,Z)−(∇⁰g₁)(Z,·)`
  (`ChristoffelDifferenceKoszul.lean:105 connDiff_koszul`).

So the mathematical content of (2a) exists; (2a) is assembling it at the g₀/gBase
pair under the class hypotheses — **modulo the two gating findings below.**

## FINDING B (gating, scope-changing) — the machinery is SMALL-PERTURBATION only (`Λ < 2`)

`gFibreOpBound g h δ` (`PosDefPerturbation.lean:70`) is the **g-operator-norm**:
`|h x v w| ≤ δ·√(g v v)·√(g w w)`.  The whole difference chain requires
`δ ≤ δ₀ < 1` (the `_of_lt_one` family).  For the (2a) role-assignment
base = gBase, `P = g₀ − gBase`, `Λ`-comparability `(1/Λ)gBase ≤ g₀ ≤ Λ·gBase`
gives `gBase`-op-norm `|g₀ − gBase|_{gBase-op} ≤ Λ − 1`, and `≥ Λ − 1` from the
upper side.  So `δ = Λ − 1`, and `δ < 1 ⟺ Λ < 2`.  Basing at g₀ instead gives the
same `Λ − 1`.  **The existing curvature-difference machinery covers only `Λ < 2`,
not the full class `Λ ≥ 1`.**

Resolution options for the full class (planner design choice):
- **(a) Telescoping chain (recommended).**  Interpolate `g_t = (1−t)gBase + t·g₀`,
  sample `t₀=0 < t₁ < … < t_N=1` with each link `|g_{t_{k+1}} − g_{t_k}|_{g_{t_k}-op}
  < 1`.  Since op-speed `≈ Λ−1`, need `N ≈ Λ` links.  Apply the order-0 asset per
  link, compose curvature differences by triangle.  Each `g_{t_k}` is a convex
  combo, so its `∇^{gBase}`-jets and its comparability are bounded by those of
  `g₀,gBase` (Λ-controlled); the composed constant is `F(Λ,n)` (poly/exp in `Λ`,
  fine for a bound).  Reuses the existing bounds as black boxes.  ~1–2 sessions.
- **(b) Large-δ re-derivation.**  General-`δ₀` analogs of the `_of_lt_one`
  lemmas.  The `1/(1−δ₀)` factors (`CovDerivConnDiffQuadraticBound:72
  s0 = finrank²·(1/(1−δ₀))²`) stay finite for `δ₀ = 1−1/Λ` (`= Λ`), so the
  algebra likely survives — but it touches many committed `_of_lt_one` lemmas
  (churn / statement-risk).  Not recommended.

## FINDING C (layering, changes S1's interface)

`MetricCovDerivOrderBoundOn` lives in `HCGCompactness/AllTimesBounds.lean`, which
is **downstream** of `Analysis/` (where S1's `UnifBochnerGap.lean` lives).  So S1
CANNOT import a bridge stated in `MetricCovDerivOrderBoundOn` terms without an
import cycle.  Correct design (mirrors the plan's `forward_ode2_of_bound` /
item-4 abstraction):

- **S1 (`Analysis/…/UnifBochnerGap.lean`)** takes the curvature-jet bound as an
  ABSTRACT hypothesis bundle `hcurv : ∀ a ≤ b, sup_x ‖∇^{g₀,a}Riemann(g₀)‖ ≤ Fc a`
  (in the ccR/ccdR-consumable currency), and produces the Λ-uniform Gårding
  constant `F(Λ,n)` as a functional of `Fc`.
- **(2a) (`HCGCompactness/UnifCurvatureJetBound.lean`, downstream)** discharges
  `hcurv` from `MetricCovDerivOrderBoundOn Λ` at the (N)-assembly level.

This **corrects `UNIF_ITEM6_RECON.md §5`**: S1's home stays `Analysis`, but it
consumes the curvature bound abstractly; (2a)'s home is `HCGCompactness` (beside
the `MetricCovDeriv*` bridges), importing the `Geometry/Curvature/` difference
assets (upstream of HCG, so importable).

## FINDING D (currency + order budget)

- Jet-envelope currency: the asset's `B` bounds `∑_{j}‖∇^{g₀,j}P‖` (the **g₀**
  connection).  `MetricCovDerivOrderBoundOn` bounds `‖∇^{gBase,j}g₀‖` (the
  **gBase** connection).  Bridge: `∇^{gBase,j}gBase = 0` for `j ≥ 1`
  (metric compat) ⟹ `∇^{gBase,j}P = ∇^{gBase,j}g₀` for `j≥1`; then convert
  `∇^{gBase}` ↔ `∇^{g₀}` via `connDiff` (a bounded, Λ-controlled conversion).
  Net: envelope `B ≤ F(Λ, metricCovDeriv jets ≤ Λ)`.  Real but bounded.
- Order: the assets are **order-0** (`riemannOp` difference) and **order-1**
  (connDiff covGrad).  (2a) needs `∇^{g₀,a}Riemann` for all `a ≤ b`.  Higher
  orders need iteration: `∇^{g₀}` of the curvature difference, converting slots
  via connDiff and re-applying — an extension of the order-0 asset the current
  file does NOT provide.  Per audit §7.4, `b` runs to `≈ a+2` (top order), so
  metric jets to `≈ A(n)+2` are consumed (order-generic statement, no hardcode).

## Sub-brick decomposition (2a)

- **2a-abs** [Analysis, landable now]: the abstract `hcurv` interface in
  `UnifBochnerGap.lean` — S1 consumes the curvature-jet bound as a hypothesis.
  This is really S1 scaffolding (Finding C); flag to planner.
- **2a-0** [HCG, Λ<2]: `sup_x‖Riemann(g₀)‖ ≤ F(Λ)` in the small-perturbation
  regime, from the order-0 asset (base=gBase, P=g₀−gBase) + fixed `Riemann(gBase)`
  sup + the Finding-D envelope bridge.  First concrete landable HCG lemma.
- **2a-tel** [HCG]: telescoping to full `Λ` (Finding B option a).
- **2a-hi** [HCG]: higher orders `∇^{g₀,a}Riemann`, `a ≤ b` (order-generic
  iteration; needs the higher-order curvature-difference extension).
- **2a-pkg** [HCG/Curvature]: package `sup‖∇^a Riemann‖` into the `H_R/H_dR`
  appFullSec window-sup currency (2b).

## Smallest first Lean brick + recommendation

Two candidates, planner to pick:
1. **2a-abs** (in `Analysis/…/UnifBochnerGap.lean`): the abstract curvature-jet
   hypothesis interface + the Λ-uniform Gårding-constant functional.  Landable in
   `Analysis` NOW (no downstream dep), unblocks all of S1 independent of the
   Λ<2 / telescoping question, and is mandated by the Finding-C layering.  **This
   is the highest-value first brick** — it lets S1 proceed while (2a) proper is
   built downstream.
2. **2a-0** (in `HCG/UnifCurvatureJetBound.lean`): the order-0 Λ<2 curvature sup.
   Concrete (2a) progress but blocked behind the telescoping design choice
   (Finding B) for the full class and the envelope bridge (Finding D).

Recommendation: ratify **Finding C** (S1 takes curvature abstractly) and dispatch
**2a-abs** first (unblocks S1), then **Finding B option (a)** for 2a-tel, then
2a-0/2a-hi/2a-pkg.  Before 2a-0, confirm the telescoping route and the
`g₀`↔`gBase` envelope-connection bridge (Finding D) are acceptable.

## Session 4 (2026-07-24, LANE C, Opus) — STEP 0 + composition core landed

### STEP 0 — asset real-green PROBE (mandatory, per false-green lesson)
`lake build` of the three consumed asset modules
(`PerturbedRiemannOpDifferenceBound`, `CovDerivConnDiffQuadraticBound`,
`ChristoffelDifferenceKoszul`): "Build completed successfully (9273 jobs)",
EXIT=0, all REPLAYED real-green (warnings pre-existing in other files).  NOT
`lake env lean` false-greens.  Safe to consume.

### Ground-truth asset signatures (verified by direct read)
- ORDER-0 DIFFERENCE (`PerturbedRiemannOpDifferenceBound.lean:88`)
  `exists_riemannOp_LeviCivita_difference_gQuadratic_le_of_jetEnvelope
   (g₀) {δ₀} (hδ₀ : δ₀<1) (B) (hB : 0≤B) : ∃ C ≥ 0, ∀ (g₁) (P : SmoothCcTensor g₀ 0 2)
   {δ} (hδ_le : δ ≤ max δ₀ 0) (hδ : gFibreOpBound g₀ (ccTensorBilinSymm g₀ P) δ)
   (htie : ∀ x v w, g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm g₀ P x v w) (x),
   (∑ j<3, ‖(iteratedCovGrad g₀ 0 2 j P).toSection x‖) ≤ B →
   ∀ v w u, g₀(R(g₁)−R(g₀), R(g₁)−R(g₀)) ≤ C²·g₀(v,v)·g₀(w,w)·g₀(u,u)`.
  KEY: the envelope uses the **asset-`g₀` connection**.  With role
  base=gBase (asset-`g₀` := gBase), it is `∇^{gBase,j}P` — direct
  `MetricCovDerivOrderBoundOn` content, so **Finding-D connection conversion is
  NOT needed** for the base=gBase assignment (corrects Finding D's worry).
- FIXED gBase CURVATURE (`UniformRiemannOperatorNormBound.lean:683`)
  `exists_uniform_riemannOp_LeviCivita_gNorm_bound (g) : ∃ Kbase ≥ 0,
   ∀ x v w u, g(R(g)vwu, R(g)vwu) ≤ Kbase·g(v,v)·g(w,w)·g(u,u)`.  (Squared-norm.)
- CONVEX COMBO (`Geometry/Metric/ConvexCombination.lean:140`)
  `SmoothRiemannianMetric.convexComb g₁ g₂ χ hχ hχ01`, `convexComb_inner :
   (g₁.convexComb g₂ χ …).inner x v w = χ x • g₁.inner x v w + (1−χ x) • g₂.inner x v w`.
  For telescoping take χ ≡ constant `t`.  NO comparability/jet lemmas yet.
- (N) comparability (inline, `ExtendViaUniqueness.lean:78`): diagonal
  `Λ⁻¹·gBase(v,v) ≤ g₀(v,v) ≤ Λ·gBase(v,v)` ∀ x v.  No named predicate.
- `MetricCovDerivOrderBoundOn K a h gRef C := ∀ x∈K, √(normSq0S gRef x (a+2)
   (metricCovDeriv h gRef a x)) ≤ C` (`AllTimesBounds.lean:661/691`)
  = `‖∇^{gRef,a}h‖_{gRef} ≤ C`.

### 2a-0 assembly SPINE (this session's math)
Role base=gBase, `g₁ = g₀`, `P = g₀−gBase`.  Chain, in gBase then g₀ currency:
1. difference asset ⟹ `gBase(R(g₀)−R(gBase),·) ≤ Cd²·gBase-quad`  (needs P/htie/fibre-op/envelope).
2. fixed asset @ gBase ⟹ `gBase(R(gBase),·) ≤ Kb·gBase-quad`.
3. g-norm triangle (`R(g₀) = (R(g₀)−R(gBase)) + R(gBase)`) + square ⟹
   `gBase(R(g₀),·) ≤ (Cd+√Kb)²·gBase-quad`.
4. comparability conversion ⟹ `g₀(R(g₀),·) ≤ Λ⁴(Cd+√Kb)²·g₀-quad`
   (one Λ on the output vector `g₀ ≤ Λ·gBase`, three on the inputs `gBase ≤ Λ·g₀`).
So **F = Λ²·(Cd + √Kb)** (norm form; squared bound uses F²).

### LANDED this session — `UnifCurvatureJetBound.lean` (composition core)
`unifCurvatureSup_singleLink_of_diff` (target-shaped, verified): takes the
difference bound (step 1's CONCLUSION) as hypothesis `hdiff` + `Λ`-comparability,
consumes the committed fixed-curvature asset (step 2), does steps 3–4, and
produces `∃ F ≥ 0, ∀ x v w u, g₀(R(g₀),·) ≤ F²·g₀(v,v)g₀(w,w)g₀(u,u)` with
`F = Λ²(Cd+√Kb)`.  Plus a private g-norm triangle helper `gAddNorm_le`.
This is the item-4-style abstraction: the genuinely-missing infrastructure
(discharging `hdiff`) is the named frontier; the composition + fixed asset +
conversion is fully proved.

### FRONTIER (remaining for full 2a-0, next sessions)
- **Discharge `hdiff`** (the crux): construct `P = g₀−gBase : SmoothCcTensor
  gBase 0 2` with `htie` (metric-difference-as-ccTensor — MISSING infra; `htie`
  is always a hypothesis in the codebase, never constructed); derive
  `gFibreOpBound gBase (ccTensorBilinSymm gBase P) (Λ−1)` from comparability
  (needs Λ<2 for δ<1); derive the envelope `∑_{j<3}‖∇^{gBase,j}P‖ ≤ B` from
  `MetricCovDerivOrderBoundOn ≤2 g₀ gBase Λ` (orders 1,2 direct; order 0 = ‖g₀−gBase‖
  from comparability).  Then apply the order-0 difference asset.
- **2a-tel** (Λ ≥ 2 full class): `g_t = convexComb g₀ gBase (const t)`; prove
  each link's convexComb comparability + jet inheritance (NEW lemmas on
  `convexComb`); compose ~2Λ(Λ+1) single-links by triangle.  Needs the
  discharge above per link.
- **2a-hi**: higher-order `∇^{g₀,a}R`, a ≤ b (order-generic; needs the
  higher-order curvature-difference extension the current asset lacks).

## Status
- 2026-07-24 (session 4, LANE C): STEP 0 asset probe PASSED (real-green);
  composition core `unifCurvatureSup_singleLink_of_diff` landed + verified +
  axiom-clean (see this file's session-4 block).  Frontier = discharge `hdiff`
  (P-construction crux) then 2a-tel/2a-hi.
- 2026-07-24 (session 3): (2a) recon COMPLETE, no Lean.  Finding A: (2a) is an
  assembly of existing jet-envelope curvature-difference machinery (de-risked).
  Finding B: that machinery is small-perturbation (`Λ<2`) only — full class needs
  telescoping.  Finding C: layering forces S1 to take the curvature bound
  abstractly (corrects recon §5).  Finding D: envelope-connection + order-budget
  bridges.  Stopped at the recon boundary pending planner ratification of the
  route (Findings B/C are scope-changing).  Recommended first brick = 2a-abs
  (abstract interface, landable in Analysis now).
