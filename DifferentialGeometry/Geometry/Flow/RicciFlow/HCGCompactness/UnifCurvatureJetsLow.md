# UnifCurvatureJetsLow — brick E3 (Λ < 2 staging), session 1

Sibling of `UnifCurvatureJetBound.lean` (order-0 Riemann sup, session 9/10).
This file is the order-`≤ 1` **connection-difference + Ricci** layer of the same
`Λ < 2` staging scope, reading three `Geometry/Curvature/` jet-envelope assets
through the discharger triple already proved in `UnifCurvatureJetBound.lean`.

## LANDED (sorry-free; focused check green, targeted module build green)

All three constants are chosen from assets applied at the fixed background
`gBase` with radius `δ₀ = Λ − 1` and envelope `B = n(Λ−1) + 2Λ` **before** any
class member `g₀` is named — i.e. closed in `(Λ, gBase)`, which is the
class-uniformity the E5/E6 endpoints need.

| theorem | bounds | source asset |
|---|---|---|
| `unifRicSup` | `g₀(Ric♯v, Ric♯v) ≤ (Λ·C)²·g₀(v,v)` for `ricEndoRaisedFib g₀` | `exists_ricEndoRaisedFib_perturbed_gQuadratic_le_of_jetEnvelope` (`Geometry/Curvature/PerturbedCurvatureOperatorBound.lean:208`) |
| `unifConnDiffSup` | `√gBase(A(v,w),A(v,w)) ≤ (C·Λ)·√gBase(v,v)·√gBase(w,w)`, `A = Γ(g₀)−Γ(gBase)` | `connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one` (`Analysis/Spectral/Tensor/CovGrad/ConnectionDifferenceFibreBound.lean:724`) + `metricDiff_orderPos_bound` for `‖∇^{gBase,1}(g₀−gBase)‖ ≤ Λ` |
| `unifCovConnDiffSup` | `√gBase(∇^{gBase}A, ∇^{gBase}A) ≤ C·√·√·√` | `exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope` (`Geometry/Curvature/CovDerivConnDiffQuadraticBound.lean:235`) |
| `unifRicBilin` | `|Ric_{g₀}(v,w)| ≤ C·√g₀(v,v)·√g₀(w,w)` — the bilinear face of `unifRicSup` | Cauchy–Schwarz + `inner_ricEndoRaisedFib` (`CovGradRoughLap/RicciTraceCarrier.lean:136`) |

Private helper: `gBase_le_scaled` (the `Λ⁻¹·gBase ≤ g₀ ⟹ gBase ≤ Λ·g₀` rearrangement).

Reuse, not reproof: every hypothesis of the three assets is discharged by the
EXISTING `metricDiff_gFibreOpBound` / `metricDiff_tie` / `metricDiff_jetEnvelope`
triple.  Nothing in `UnifCurvatureJetBound.lean` was edited.

## WHY (a)/(b)/(c) AS BRIEFED DO NOT CLOSE — three walls, all upstream

### Wall 1 — no order-`≥ 1` curvature-DIFFERENCE asset (blocks (a) at `a ≥ 1`)

`exists_riemannOp_LeviCivita_difference_gQuadratic_le_of_jetEnvelope`
(`PerturbedRiemannOpDifferenceBound.lean:88`) is that file's ONLY theorem and it
is order-`0`.  Nothing anywhere bounds `∇^{g₁}Rm(g₁) − ∇^{g₂}Rm(g₂)`, or
`∇^{gBase,a}` of a curvature difference, by a metric-jet envelope.  Two further
sub-gaps compound it:

* the only fixed-metric order-`1` curvature sup,
  `exists_uniform_nablaCurvSec_LeviCivita_gNorm_bound`
  (`CurvatureOperator/UniformDiffCurvatureNormBound.lean:1113`), bounds only the
  **frame-summed first-slot divergence** `∑_i(∇_{B_i}R)(B_i,B_a)·`, not the
  uncontracted `∇Rm`; there is no fixed-metric sup for `∇Rm` or `∇²Rm` at all;
* `∇^a Rm` cannot even be **stated** in the `iteratedCovGrad`/`SmoothCcTensor`
  currency: `metricRm04 g` is a `Tensor0SField`, and there is no
  `Tensor0SField → SmoothCcTensor g 0 4` packaging (the identification
  `curv_apply_iterCov` in `CurvTowerBridge.lean` is `private`).

This is the sub-brick the previous session's note already labels **`2a-hi`** and
records as not built (`UnifCurvatureJetBound.md:101-106, :118`).  It is a
`Geometry/Curvature/` brick (differentiated Palatini at the fibre-norm level),
not a leaf assembly.

**UPDATE 2026-07-30 — Wall 1 is PARTLY DOWN; see
`UnifCurvatureJet1Diff.lean` / `.md` and `UNIF_EXISTENCE_PLAN2.md` No. 76.**
Corrections to the two sub-gaps above:

* `∇^a Rm` **was** already stateable — as `iterCov g 4 (metricRm04 g) a`, the
  generic `Tensor0SField` currency of `MetricCovDerivLinear.lean` (which is where
  `covStep` / `diffStep` / `diffStep_jet_one_le` live).  What
  `curv_apply_iterCov` bridges is `curvCovDeriv` ↔ `iterCov`, *both*
  `Tensor0SField`-side; it says nothing about `SmoothCcTensor`.  Its public face
  is now `curvCovDeriv_normSq_eq`.  The real, still-open packaging gap is
  `iteratedCovGrad ↔ iterCov` (i.e. `covGrad ↔ covStep`) — a separate, cheaper
  brick that would unlock every `iterCov`-currency estimate for the E3 consumers
  at once.
* the missing uncontracted fixed-metric `∇^a Rm` sup is now
  `exists_curvJet_sup` (all orders, one line off `sqrtNormSq0S_bddOn`).
* the brick cannot live in `Geometry/Curvature/`: `iterCov`, `diffStep` and
  `MetricCovDerivOrderBoundOn` are all `HCGCompactness/`.

Banked from the difference itself: the exact split `curvJet1_diff_eq`, the
`(0,4)`-field Λ-class order-`0` sup `unifRm04Sup`, and the
**connection-insertion term** `unifCurvJet1Conn`.  What remains of Wall 1 is
exactly one object, `covStep gBase 4 (metricRm04 g₀ − metricRm04 gBase)`,
blocked on a *bundled* (rather than eval-level) Palatini difference identity —
all of its analytic inputs already exist.

### Wall 2 — the `Fc` family is unreachable, and NOT for Λ-class reasons (blocks (b))

`hcurv` (`UnifBochnerGap.lean:304`) quantifies over **all** `(r, p)`:
`‖∇^p(pointwiseTensorCurv g₀ r S)‖ ≤ Fc p · ∑_{a<p+2}‖∇^a S‖`.

* Order-budget check done: `hsCovsumC`/`covsumHsC` at `n ≤ 4` only ever reference
  `Fc p` for `p ≤ 2` (traced through `roughLapCommC`→`rawLapIterC`→`iterRawLapC`
  and `bochnerStepC`→`baseLowerC`).  So a `p ≤ 2` producer would suffice
  numerically — but every consumer theorem takes the UNRESTRICTED `hcurv`, so
  exploiting this needs a p-restricted refactor of the ~14-theorem E1 chain.
* Worse, even `Fc 0` is out of reach.  The existing per-metric witness
  `exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le`
  (`AllOrderGardingConstant.lean:193`) factors through Hom-fields `H_R`, `H_dR`
  produced by the ABSTRACT representation theorem `exists_value_local_appFullSec`
  — no norm control on them exists, so no constant-exposed version is derivable
  from that route.  The alternative route, the constant-exposed order-`0` leaf
  `pointwiseTensorCurv_fiberNormSq_le_first_order`
  (`Bochner/PointwiseTensorCurvFirstOrderBound.lean:1675`), IS internally
  explicit — `K_R = √(nR(16·Kpure + 2·Cc))`, `K_dR = √(4·nR·Cd)` with
  `Cc = n·(n·n·Kbase)` — but `Kpure`/`Cd` are explicit in the ∇R sup `Kw(g₀)`,
  which is Wall 1.  So `Fc 0` needs (i) constant exposure of three private
  ∃-form files AND (ii) Wall 1.

Consequence: `unifFc` was NOT written.  Writing a `def unifFc : ℕ → ℝ` today
would be a name promising content the tree cannot supply — exactly the
"polished frontier wrapper" CLAUDE.md forbids.

### Wall 3 — `Ksup` splits cleanly; `j = 0` is one lemma away, `j = 1` is Wall 1

`deTurckRicciRHS gBase g₀ = −2·Ric(g₀) + 𝓛_W g₀`, `W = deTurckVF g₀ gBase`
(`Geometry/Flow/RicciFlow/DeTurckRHS.lean:110`; no decomposition lemma exists —
the in-tree idiom is `simp only [deTurckRicciRHS, ContinuousLinearMap.add_apply,
ContinuousLinearMap.smul_apply, smul_eq_mul, lieDerivMetricClm_apply]`).

* **Ricci half, `j = 0`: DONE** — `unifRicSup` + `ricEndoRaisedFib`'s defining
  property gives `|Ric(v,w)| ≤ ΛC·√g₀(v,v)·√g₀(w,w)`.
* **Lie half, `j = 0`: ONE missing lemma.**  Route: Cartan
  `cartan_formula_for_lie_deriv_metric` (`Pullback/Cartan/Formula.lean:483`)
  gives `𝓛_W g₀(v,w) = g₀(∇^{g₀}_v W, w) + g₀(v, ∇^{g₀}_w W)`.  The bridge
  `connDiff_outerCovDeriv_eq` (`Geometry/Flow/DeTurckVFConnDiffVariation.lean:382`)
  converts `∇^{g₀}A` into `covDerivConnDiff gBase g₀` plus a quadratic `A·A`
  remainder — and its two inputs are EXACTLY `unifCovConnDiffSup` and
  `unifConnDiffSup`, landed here.  **The missing step is the trace:** no lemma
  in the tree computes `∇^{g₀}(deTurckVF g₀ gBase)` as the `g₀`-trace of
  `∇^{g₀}(connDiff g₀ gBase)`.  `deTurckVF_eq_orthoFrame_trace`
  (`DeTurckVFConnDiffVariation.lean:289`) represents `W` as a frame-sum, but the
  frame `smoothOrthoFrame g₀ x i` is orthonormal only AT `x`, so it cannot be
  differentiated pointwise — the trace must be differentiated invariantly using
  `∇^{g₀}g₀⁻¹ = 0`.  That is the smallest next lemma.
* **`j = 1`: Wall 1.**  `∇(−2Ric + 𝓛_W g₀)` needs `∇Ric(g₀)`, a contraction of
  `∇Rm(g₀)`.  Also needs a Leibniz expansion of `∇𝓛_W g₀` (order-2 connDiff
  derivative — `covDConnDiff2_gJet_le`, `ConnDiffDeriv2Bound.lean:814`, exists).

Fibre packaging, once the component bounds are in hand, is settled: compose
`rfns0_unit_eq` (`UnifJetTowerMatch.lean:223`) with
`normSq0S_le_card_of_component_bound`
(`Tensor/RSTensor/Tensor0SRiemannian/Comparison.lean:267`) on a `g₀`-orthonormal
frame — the same shape `metricDiff_order0_bound` already uses.

## Assets found and reused (do not re-derive)

* discharger triple: `metricDiff_gFibreOpBound`, `metricDiff_tie`,
  `metricDiff_jetEnvelope`, plus `metricDiff_orderPos_bound`
  (`UnifCurvatureJetBound.lean`).
* ungated class-currency siblings, NO `Λ < 2` gate, EXPLICIT constants:
  `covDerivConnDiff_gJet_le` (`ConnDiffDerivBound.lean:489`, constant
  `(3/2)Λ⁴(Λ''+ΛΛ'²)`), `lcDiff_norm_le` (`MetricLapDiff.lean:164`),
  `covDConnDiff2_gJet_le` (`ConnDiffDeriv2Bound.lean:814`).  These are the route
  to a general-Λ version of `unifConnDiffSup`/`unifCovConnDiffSup`; they need
  the REVERSED jets `MetricCovDerivOrderBoundOn K a gBase g₀ ·` as extra
  hypotheses (as `UnifJetTowerMatch.sqrtRfns_cross_le` also does).
* cross-metric transfer: `fibreNormSq_cross_le`
  (`SobolevEmbeddingUnif.lean:183`, factor `Λ^s`), `sqrtRfns_cross_le`
  (`UnifJetTowerMatch.lean:462`, orders `≤ 2`, unconditional).

## Lean lessons

* `metricDiff_orderPos_bound … 0 hjet1 x` types directly against the asset's
  `TensorRSSpace 0 3` slot — `2 + (0+1)` and `3` are defeq and the
  `tensorRS_riemannianBundle` instances coincide; no cast needed.
* `refine h.trans (le_of_eq ?_ |>.trans ?_)` does NOT split as intended in a
  `≤`-chain; use `refine h.trans ?_` then a plain `calc`.  `set N := ‖…‖` before
  building the hypotheses keeps the `calc` readable and lets `ring` close the
  reassociations.
* The three assets take their perturbation-package arguments in DIFFERENT
  orders: `connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one` takes
  `(g₁) (T) (htie) {δ} (hδ) (hδ0) (hbound) (x) (v w)`, while the two
  `_of_jetEnvelope` assets take `(g₁) (P) {δ} (hδ_le) (hδ) (htie) (x) (henv)`.
  Read the signature before applying.

## Status / next target

Landed: the order-`≤ 1` connection-difference + Ricci layer of E3 at `Λ < 2`,
4 public theorems, sorry-free, axiom-clean.

Next concrete target (smallest unblocking lemma): the invariant
trace-differentiation identity
`∇^{g₀}(deTurckVF g₀ gBase) = tr_{g₀}(∇^{g₀}(connDiff g₀ gBase))`,
in `Geometry/Flow/DeTurckVFConnDiffVariation.lean` or a sibling.  With it,
`Ksup` at `j = 0` closes from what is already in this file.  `Ksup` at `j = 1`,
`Fc`, and `∇^a Rm` for `a ≥ 1` all remain behind Wall 1 (`2a-hi`), which should
be dispatched as its own `Geometry/Curvature/` brick.
