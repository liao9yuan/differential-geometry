# UnifCurvatureJet1Diff — brick 2a-hi, stages 1–2

Status: **stage 1 DONE, stage 2 HALF DONE (connection term closed; Palatini term
is the wall), stage 3 gBase half DONE / g₀ half blocked.**  Verification passed
(focused check + targeted module build, no warnings); all four new theorems are
axiom-clean.

Entry pointers: `UNIF_EXISTENCE_PLAN2.md` No. 71 (E3 recon),
`UnifCurvatureJetsLow.md` (Wall 1), `PROJECT_MAP.md`.

## 1. Two recon corrections to the brief

**(a) The stage-1 premise was wrong.**  The brief said `∇^a Rm` "is not even
STATEABLE in the iteratedCovGrad/SmoothCcTensor currency", and that publicizing
`curv_apply_iterCov` would make `iteratedCovGrad` apply to curvature.  It does
not, and it does not need to:

* `iterCov g 4 (metricRm04 g) a` (`MetricCovDerivLinear.lean`) **already is**
  `∇^a Rm` as a rank-`4+a` `Tensor0SField`, is public, and is the currency in
  which the whole `covStep`/`diffStep`/telescoping machinery is written.
* `curv_apply_iterCov` relates the HCG static tower `curvCovDeriv` to that
  object; **both live in `Tensor0SField` currency**.  It has nothing to do with
  `SmoothCcTensor`/`iteratedCovGrad`, which go through a different
  implementation (`covGrad` ⟶ `covGradBundleEquiv` ⟶
  `tensorRSCovariantDerivative`).  Bridging *those* two towers is a separate,
  genuinely non-mechanical piece of work (still unbuilt; see §5).

So stage 1 was delivered as the honest thing: a **public, `curvEquiv`-free**
face of the private bridge.

**(b) Layer placement.**  The brief asked for a `Geometry/Curvature/` brick.
That is impossible without a broad refactor: `iterCov`, `covStep`, `diffStep`,
`diffStep_jet_one_le`, `MetricCovDerivOrderBoundOn` all live in
`HCGCompactness/`, far above `Geometry/Curvature/`.  The new file is a sibling of
`UnifCurvatureJetsLow.lean`, which is the lowest layer where the statement is
expressible.

## 2. Delivered

### Stage 1 — `CurvTowerBridge.lean`

`curvCovDeriv_normSq_eq (g) (m) (x)` :
`normSq0S g x (m+4) (curvCovDeriv g m x) = normSq0S g x (4+m) (iterCov g 4 (metricRm04 g) m x)`.

Extracted from the body of `curvNormSq_eq`, which now calls it (net −20 lines).
Mentions no private declaration; the slot-reindexing `curvEquiv` stays private.
This is what lets an estimate proved in generic `iterCov` currency be read off on
the canonical static tower and back.

### Stage 2 — `UnifCurvatureJet1Diff.lean` (new, 4 theorems)

1. `curvJet1_diff_eq (g₀ gBase)` — the exact split, pure operator algebra:
   `∇^{g₀}Rm(g₀) − ∇^{gBase}Rm(gBase) = diffStep g₀ gBase 4 (metricRm04 g₀) +
   covStep gBase 4 (metricRm04 g₀ − metricRm04 gBase)`.

2. `unifRm04Sup` — **new asset**: the first Λ-class curvature bound in the tree
   stated on the *(0,4) field* rather than on `riemannOp`.
   `√normSq0S g₀ x 4 (metricRm04 g₀ x) ≤ n²·F`, `F` = the constant of
   `unifCurvatureSup_singleLink`, closed in `(Λ, gBase)`.
   Route: `g₀`-orthonormal frame → `metricRm04StdAt_eq_inner_riemannOp`
   (`MetricCovDerivPullback.lean:551`) → Cauchy–Schwarz
   (`abs_metric_inner_le_sqrt_metric_quadratic`) → each of the `n⁴` components
   is `≤ F` → `normSq0S_le_card_of_component_bound`.

3. `unifCurvJet1Conn` — **the first term of the a=1 envelope, closed**:
   `√normSq0S g₀ x 5 (diffStep g₀ gBase 4 (metricRm04 g₀) x) ≤
   4·√(n⁵)·(3/2)·√(Λ³)·Λ·(n²F)`, uniform in `x`, constant fixed before any class
   member is named.

4. `exists_curvJet_sup (g) (a)` — fixed-metric sup of `∇^a Rm(g)`, every order.
   One-line instantiation of `sqrtNormSq0S_bddOn`
   (`MetricCovDerivContinuity.lean:87`).

## 3. Key routing lesson (the ROLE SWAP)

`diffStep_jet_one_le (g₁ g₂ …)` measures the norm in `g₂` and consumes
`MetricCovDerivOrderBoundOn K 1 g₂ g₁ Λ'` — i.e. the jets of `g₂` against `g₁`.
Taking the obvious `g₁ = g₀, g₂ = gBase` therefore demands the **reversed** jets
`∇^{g₀}gBase`, which the Λ-class does not carry (this is the extra hypothesis
flagged as side-finding (ii) in plan No. 71).

Fix: apply it with `g₁ = gBase, g₂ = g₀`.  Then the jet hypothesis is exactly the
class jet `hjet1 : MetricCovDerivOrderBoundOn univ 1 g₀ gBase Λ`, and the norm
comes out in `g₀` — which is also the norm the E3 consumers want, so **no
cross-metric `Λ^{s/2}` conversion is needed anywhere**.  The sign is absorbed by
`diffStep g₀ gBase … x = −(diffStep gBase g₀ … x)` (`ContMDiffSection.coe_sub`
+ `abel`) and `normSq0S_neg`.

This trick should be reused for every future `diffStep`-based Λ-class bound.

## 4. THE WALL — stage 2, second term

Not proved, not stated as a hypothesis anywhere (deliberately: an
envelope theorem carrying it as `hpal` would move no mathematics).

Missing statement:

```
∃ C (closed in Λ, gBase), ∀ x,
  √ normSq0S g₀ x 5 (covStep gBase 4 (metricRm04 g₀ − metricRm04 gBase) x) ≤ C
```

under `hcomp` + `MetricCovDerivOrderBoundOn univ a g₀ gBase Λ` for `a ≤ 3`.

Classification: **missing groundwork / new math**, not a local proof failure.
The order-`0` sibling (`PerturbedRiemannOpDifferenceBound.lean:88`) proves the
`(1,3)` Palatini split `Rm(g₁)−Rm(g₀) = (A₁−A₂) + (Q₁−Q₂)` via
`riemannSec_difference` and *never differentiates it*.  The order-1 term needs
that identity differentiated once by `∇^{gBase}`, giving `∇²A + (∇A)·A` — no
curvature on the right-hand side, which is why the route is not circular.

Two sub-obstructions, in order:

* **(W1) tensorial Palatini.**  `riemannSec_difference` is an *eval-level*
  identity on `smoothExtensionTangent`-extended vector fields.  Differentiating
  it in that form drags in `∇^{gBase}(extension)` correction terms at every slot.
  What is needed is the Palatini difference as a **bundled `(0,4)` or `(1,3)`
  field identity**, so that `covStep`/`diffStep` apply directly.  The
  Kotschwar lane has the closest objects (`rmDiffLowAt`,
  `ForwardUniqueSdec.lean:291 rmDiffLow_split`,
  `ForwardUniqueRmDiff.lean:339 rm2Low_eq_sub`) but no `A`-jet expression.
  Smallest next lemma: a field-level
  `metricRm04 g₀ − metricRm04 gBase = (lowering-defect term) + gBase ⋆ Palatini(A)`
  with `Palatini(A)` built from `connDiff` and `covDerivConnDiff`.

* **(W2) the analytic inputs, which already EXIST** — this half is not a wall:
  `covDConnDiff2_gJet_le` (`ConnDiffDeriv2Bound.lean:814`, `∇²A`),
  `unifCovConnDiffSup` (`∇A`), `unifConnDiffSup` (`A`),
  `covStepDiff_norm_le` / `covStepDiff_jet_le` (`UnifCovSumCross.lean:711`).
  So W1 is the whole frontier.

Difficulty assessment: **not a routine local proof.**  W1 is a design +
bookkeeping brick on the scale of the order-0 asset itself (≈350 lines there,
with a differentiation layer on top).  Do not expect it to close without a
dedicated session; it should be planned as its own lane entry.

Do NOT re-attempt by adding hypotheses to `unifCurvJet1Conn`.

## 5. Still-open packaging gap (separate from the wall)

The E3 consumers (`hcurv` in `UnifBochnerGap.lean:304`, `hsup` in
`UnifNZeroBound.lean:343`) speak `SmoothCcTensor g₀ 0 r` + `iteratedCovGrad` +
`riemannianFiberNormSq`.  Everything proved here is `Tensor0SField` + `iterCov`
+ `normSq0S`.  Those two towers are **not** bridged anywhere in the tree.
Ingredients that exist: `Tensor0SField.toTensorRSField`
(`Tensor/RSTensor/Coordinates/Field.lean:307`) for the object; compact support is
free on `CompactSpace M`.  Missing: `iteratedCovGrad g 0 s j (toRS0 A) =
toRS0 (iterCov g s A j)` (or the norm-level equivalent), i.e. `covGrad ≈ covStep`.
This is independent of the curvature wall and is worth a separate small brick —
it would unlock *every* `iterCov`-currency estimate for the E3 consumers at once.

## 6. Honest progress

* brick 2a-hi (order-1 curvature jet envelope): **~35 %** — split + connection
  term + the order-0 `(0,4)` sup + the fixed-metric sup are banked; the Palatini
  term (the majority of the mathematical content) is 0 %.
* lane E3 (`unifFc` satisfying `hcurv`, `Ksup` satisfying `hsup`): **still 0 %** —
  neither theorem is stated, and both additionally need the §5 packaging bridge.
* `ricci_flow_unif_existence` (the campaign endpoint): unchanged.
