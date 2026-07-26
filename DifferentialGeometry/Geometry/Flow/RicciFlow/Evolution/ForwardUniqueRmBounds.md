# ForwardUniqueRmBounds.lean — Route-K bricks K2.4 + K2.5

Companion note for
`DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/ForwardUniqueRmBounds.lean`.
Governing ruling: `ShortTime/FORWARD_UNIQUE_PRO_RULING.md` §4/§6 (the pointwise inequalities
of the Kotschwar system).  Dispatch: `ShortTime/FORWARD_UNIQUE_PLAN.md` №2 and №5 (the flux
substitution and its recorded `|∇²∇²T|` cost).

## Outcome: (A) — both bounds proven, 0 sorry

Focused check: PASS.  Targeted module build: PASS (`✔ Built … (14s)`, no errors and no
warnings attributable to this file).  Axiom audit: all 8 public declarations depend on exactly
`[propext, Classical.choice, Quot.sound]`.  19 declarations total (8 public, 11 private).

No file outside this brick's own `.lean`/`.md` pair was touched.

## The two estimates

Both are pointwise, two fixed smooth metrics, one fixed point, no time parameter — exactly the
scope of `ForwardUniqueRmDiff.lean`.  Write `n = finrank ℝ E`.

**K2.4 (flux).**  `fluxNormSq_le`:

```
|U|²_{g₁} ≤ s² · n^{s+1} · |A₀₃|²_{g₁} · |T|²_{g₁},        U = lapDiffFlux g₁ g₂ T = ∇¹T − ∇²T
```

The background factor is the *field itself*, not a derivative of it.  That is the whole point
of the flux substitution recorded in `ForwardUniqueRmDiff.md`: `∇¹T − ∇²T` is the algebraic
action of the connection-difference tensor on `T` (`lapDiffFlux_eval`), so `U` is zeroth order
in `T` and first order in nothing.  Kotschwar's required `|U| ≤ C(|h₀₂| + |A₀₃|)` therefore
holds in the sharper `|A₀₃|`-only form.

`rmFluxNormSq_le` is the `(0,5)` curvature instance, with the background bound supplied as an
explicit hypothesis `hB : normSq0S g₁ x 4 (Rm2 x) ≤ B`, giving
`|U₀₅|² ≤ 16·n⁵·|A₀₃|²·B`.

**K2.5 (remainder).**  `remNormSq_le`:

```
|R|²_{g₁} ≤ 2(s+1)²·n^{2s+4}·|A₀₃|²_{g₁}·B₁  +  2·n^{s+6}·Λ²·|h₀₂|²_{g₁}·B₂
```

with the `(0,4)` instance `rmRemNormSq_le` (constants `50·n¹²` and `2·n¹⁰`).  The two summands
of `lapDiffRem` are estimated separately and combined by the crude parallelogram bound
`normSqAdd_le`, so each carrier is paired with *its own* background factor rather than with a
common maximum.

## Hypothesis shapes chosen for the background factors and the metric comparison

These were the design choices; they are deliberately the weakest shapes the proofs actually
consume, and none of them is hidden inside a definition.

* `hB₁ : normSq0S g₁ x (s+1) (metricNabla0S g₂ T x) ≤ B₁` — the `|∇²T|²` background.
* `hB₂ : normSq0S g₁ x (s+2) (metricNabla0S g₂ (metricNabla0S g₂ T) x) ≤ B₂` — the
  `|∇²∇²T|²` background.  This is the extra covariant derivative that plan №5 recorded as the
  honest cost of the flux substitution; it appears here as a *named argument*, not as a
  surprise.  Note both are measured in the `g₁` fibre norm (the energy's norm), while the
  derivative is the `g₂` one — that is what the remainder literally contains.
* `hΛ0 : 0 ≤ Λ` and `hΛ : ∀ v, g₁.inner x v v ≤ Λ * g₂.inner x v v` — the one-sided metric
  comparison `g₁ ≤ Λ·g₂`, which is exactly what the inverse-metric difference needs.  This is
  the `ricciEdgeMetric` output shape (`Evolution/RicciEdgeBounds.lean`) restricted to the one
  direction used.  `hΛ0` is a separate argument rather than derived from `hΛ`: deriving
  `0 < Λ` from `hΛ` needs a nonzero tangent vector, i.e. `n ≥ 1`, and the brick should not
  silently assume the manifold is positive-dimensional.

`fluxNormSq_le` and `traceNormSq_le` need **no** comparison hypothesis at all — they are
single-metric statements.  `traceDiffNormSq_le` is where `Λ` enters, and only there.

## What each declaration provides

Public:

* `lapDiffFlux_eval` — pointwise evaluation of the flux on arbitrary vectors:
  `U(v, slots) = −∑ₐ T(slotsₐ ↦ (∇¹−∇²)(slotsₐ, v))`.  The `metricCov`-currency, field-level
  counterpart of `HCGCompactness.MetricCovDerivLinear.diffStep_eval`.
* `connDiffVec_le` — `|(∇¹−∇²)_X Y|_{g₁} ≤ |A₀₃|_{g₁}·|X|_{g₁}·|Y|_{g₁}`, sharp constant `1`.
  This is the `A₀₃`-currency companion of `Tensor0SBundle.connDiffVec_norm_le`, which delivers
  the same content in the mixed Hilbert–Schmidt currency `normSqRS(connectionDifferenceTensorAt)`.
* `fluxNormSq_le` — K2.4, generic rank.
* `traceNormSq_le` — `|tr_g V|²_g ≤ n^{s+2}·|V|²_g`.
* `traceDiffNormSq_le` — `|tr_{g₁}W − tr_{g₂}W|²_{g₁} ≤ n^{s+6}·Λ²·|h₀₂|²_{g₁}·|W|²_{g₁}`.
* `remNormSq_le` — K2.5, generic rank.
* `rmFluxNormSq_le`, `rmRemNormSq_le` — the `(0,5)`/`(0,4)` curvature instances with named
  background hypotheses.

Private infrastructure: `innerSelfNonneg`, `exists_onFrame`, `frankEq`, `onFrame_inv`,
`metricCS`, `onFrame_coord`, `absBasis_le`, `normSqAdd_le`, `invDiag_le`, `invEntry_le`,
`invDiff_le`.

## The mathematical decision in K2.5

The second summand of `lapDiffRem` is `(tr_{g₁} − tr_{g₂})(∇²∇²T)`, i.e. the contraction of
the background field with the **inverse-metric difference**.  Rather than build a cometric
difference object, the estimate is done entirely inside the `basisInvMetric` API in a
`g₁`-orthonormal frame:

* `basisInvMetric g₂ x e` is the canonical inverse-metric component function in *any* basis
  (`Tensor/RSTensor/CotangentRiemannian.lean`), and `basisInvMetric_real` says it satisfies
  `MetricInverseInBasis_gen`, so `metricTraceFirstTwo0SAt_eq_sum_basis` expresses **both**
  traces in the **same** frame — the `g₁` one with the identity witness, the `g₂` one with
  `basisInvMetric g₂`.  The difference is then a single double sum with coefficient
  `δ_{ij} − (g₂^{-1})_{ij}`.
* `invEntry_le` bounds every entry of `g₂^{-1}` in a `g₁`-orthonormal frame by `Λ`.  Route:
  `basisInvMetric g₂ x e i j = g₂(u_j, u_i)` with `u_i = ♯₂(e.coord i)`; Cauchy–Schwarz in `g₂`
  reduces to the diagonal, and the diagonal satisfies the self-improving inequality
  `Q_{ii} = g₁(e_i, u_i) ≤ √(g₁(u_i,u_i)) ≤ √(Λ·Q_{ii})`, whence `Q_{ii} ≤ Λ`.
* `invDiff_le` then uses the frame identity `g₁^{-1} − g₂^{-1} = −g₂^{-1}·h₀₂` — obtained by
  substituting `g₂(e_k,e_j) = δ_{kj} − h₀₂(e_k,e_j)` into the defining relation
  `∑_k (g₂^{-1})_{ik} g₂(e_k,e_j) = δ_{ij}` — to get
  `|δ_{ij} − (g₂^{-1})_{ij}| ≤ n·Λ·|h₀₂|_{g₁}`.

No matrix-inverse machinery, no `Matrix.PosDef`, no determinant estimate, and no new cometric
layer were needed.

## Reuse vs new

Reused as-is (no adapters, no reproofs):

* `Tensor0SBundle.nabla0SFun_sub_cov` (`NablaOnTensors/HigherOrder.lean`) +
  `totalNabla0SFun_apply_section` — the engine of `lapDiffFlux_eval`;
* `Geometry.Riemannian.exists_contMDiff_vectorField_eq`
  (`Geometry/Metric/SmoothVectorFieldExtGlobal.lean`) — the section→pointwise transfer;
* `abs_apply_le_sqrt_normSq0S`, `normSq0S_le_card_of_component_bound`,
  `normSq0S_identity_eq_sum_sq`, `identityInvMetric`/`diagonalInvMetric`
  (`Tensor0SRiemannian/Comparison.lean`) — the entire component→fibre-norm machinery;
* `basisInvMetric`, `basisInvMetric_real`, `tangentFlatEquiv_gen`
  (`Tensor/RSTensor/CotangentRiemannian.lean`);
* `metricTraceFirstTwo0SAt_eq_sum_basis`, `metricTraceFirstTwo0STensor_apply`,
  `metricTrace0S2InBasis`, `metricTraceInput` (`Geometry/Operator/RoughLaplacian.lean`);
* `metricDiffAt_apply`, `connDiffLowAt_apply`, `metricDiffSq_def`, `connDiffSq_def`
  (`Evolution/ForwardUniqueFields.lean`); `lapDiffFlux`, `lapDiffRem`, `rmDiffFlux`,
  `metricNabla0S` (`Evolution/ForwardUniqueRmDiff.lean`).

New, and why:

* `exists_onFrame` — the repository has no basis-free "there is a `g`-orthonormal frame at `x`"
  lemma; the construction (`tangentMetricData_gen … |>.toCore` + `stdOrthonormalBasis`) is
  open-coded inside `connDiffVec_norm_le` and `diffStep_norm_le`.  Packaging it once removes
  ~20 lines from each of the four theorems here that need a frame.
* `metricCS`, `innerSelfNonneg` — the library versions
  (`Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic`, `metric_inner_self_nonneg`,
  `Analysis/Elliptic/MetricBounds.lean`) are unusable here: that file's section block carries
  a model-space `[InnerProductSpace ℝ E]`, the constraint this project rules out.  Both are
  re-proved locally and privately (`metricCS` as the `(0,1)` case of the tensor Cauchy–Schwarz,
  ~10 lines) rather than compensated downstream.
* `onFrame_coord`, `absBasis_le`, `normSqAdd_le`, `frankEq` — small frame-arithmetic helpers.
* `invDiag_le` / `invEntry_le` / `invDiff_le` — the inverse-metric-difference layer described
  above.

## Items for the planner (deliberately not acted on — brick scope was one file)

1. **Canonical homes.**  `exists_onFrame` is generic Riemannian fibre linear algebra and
   belongs next to `tangentMetricData_gen` (`Tensor/RSTensor/TangentRiemannianRealized.lean`)
   or in `Tensor0SRiemannian/`; once hoisted, `connDiffVec_norm_le` and `diffStep_norm_le`
   should consume it instead of re-open-coding the frame.  `absBasis_le` and `normSqAdd_le`
   belong beside `abs_apply_le_sqrt_normSq0S` / `normSq0S_le_card_of_component_bound` in
   `Tensor0SRiemannian/Comparison.lean`.  `onFrame_coord` belongs in `CotangentRiemannian.lean`.
   `traceNormSq_le` is a single-metric fact about `metricTraceFirstTwo0STensor` and belongs in
   `Geometry/Operator/RoughLaplacian.lean` or a norm sibling.  All are `private` here only
   because the protocol forbade editing existing files.
2. **`Analysis/Elliptic/MetricBounds.lean` producer-side `omit`.**  `metric_inner_self_nonneg`
   and `abs_metric_inner_le_sqrt_metric_quadratic` do not use `[InnerProductSpace ℝ E]` in
   their proofs; an `omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in` on those two would
   make them consumable from the NormedSpace-only trees and let `metricCS`/`innerSelfNonneg`
   here be deleted.  This is the same class of item as the `lowerAllSpace` omit recorded in
   `ForwardUniqueFields.md`, and `Geometry/Comparison/Volume/RadialGronwall.lean:656` already
   carries a third private copy of the nonnegativity lemma — three consumers now.
3. **Sharper constants are available but not needed.**  Every `n^{…}` here comes from bounding
   all components uniformly and summing squares; a per-component Parseval identity would
   remove one `n` per slot.  The energy estimate only needs *a* constant, so this was not paid
   for.
4. **`connDiffVec_le` vs `connDiffVec_norm_le`.**  These are the same inequality in two
   currencies, related by the lowering isometry `normSqRS_eq_normSq0S_lowerAllSpace`
   (`Tensor/RSTensor/RSLoweringNorm.lean`).  That bridge was *not* used, because that file also
   sits behind `[InnerProductSpace ℝ E]` (item 1 of `ForwardUniqueFields.md`).  After that
   omit lands, `connDiffVec_le` could be derived from `connDiffVec_norm_le` instead of
   re-proved — but the direct proof is 25 lines, so this is cosmetic.

## Lean lessons from this pass

* **The `A₀₃` currency is cheaper than the `normSqRS` currency for this lane.**  The recon
  anchors (`connDiffVec_norm_le`, `diffStep_norm_le`) both deliver their bound in terms of
  `normSqRS (connectionDifferenceTensorAt …)`, which would then have to be converted to
  `connDiffSq` through the lowering isometry — a conversion blocked by a wrong section
  hypothesis at the producer.  Reading the estimate straight off `connDiffLowAt_apply` instead
  (`A₀₃(X,Y,Z) = g₁((∇¹−∇²)_X Y, Z)`, then set `Z` equal to the vector being measured) gives
  the bound directly in the energy's own currency with sharp constant.  When a recon anchor is
  in the "wrong" currency, check whether the target currency has a defining evaluation lemma
  that reproves it in a dozen lines.
* `Module.finrank ℝ (TangentSpace I x)` and `Module.finrank ℝ E` are `rfl`-equal but not
  syntactically equal, and `simp`/`Finset.sum_const` arithmetic will happily strand a goal
  `finrank (TangentSpace I x) = finrank E ∨ NV = 0`.  Naming the identity once
  (`frankEq`) and `rw`-ing with it is much more robust than hoping `simp` closes it.
* `Basis.coord_apply` / `Basis.repr_self` are `Module.Basis.coord_apply` /
  `Module.Basis.repr_self` in this Mathlib.
* `rw [hQ] at hQ1` when `hQ1`'s **right**-hand side also contains the rewritten term silently
  destroys the hypothesis; a `calc` chain that never rewrites is the fix.
* The `unusedFintypeInType` linter fires on private helpers whose statement needs only
  `DecidableEq`.  Two fixes both work: drop `[Fintype Idx]` outright when the proof does not
  need it (`onFrame_coord`, `invDiag_le`, `invEntry_le`), or weaken to `[Finite Idx]` and open
  `haveI : Fintype Idx := Fintype.ofFinite Idx` in the proof (`absBasis_le`).  The second is
  safe here because the conclusion contains no `Idx`-indexed sum, so the instance cannot leak.
* `set x := e with h` gives `h : x = e`, so folding a later-created hypothesis needs
  `rw [← h]`; and `set` does not retro-fold terms hidden under a `def` (here `basisInvMetric`),
  so the idiom is `simp only [basisInvMetric]; rw [← h]`.
* The whole file elaborates in ~16 s on top of `ForwardUniqueRmDiff`.  The variable block is
  the `ForwardUniqueRmDiff` one verbatim; `set_option backward.isDefEq.respectTransparency
  false` **is** needed here (unlike in `ForwardUniqueRmDiff`) because
  `totalNabla0SFun_apply_section` is used at the variable rank `s + 1`.

## What this brick does NOT do

No time dependence, no integration by parts, no energy.  It does not connect the generic field
`T` to the curvature carriers: the consumer must supply `T = riemannCurvature04At g₁ (metricCov
g₂) …` and use `rm2Low_eq_sub` (`ForwardUniqueRmDiff.lean`) to read the result in terms of
`metricRm04At g₁ − rmDiffLowAt g₁ g₂`.  It also does not produce the background bounds `B`,
`B₁`, `B₂` — those are slab-uniformity facts for the consumer (`Icc a c` compactness plus the
smooth-class `(B)` statement), and they are exactly where the `|∇²∇²T|` cost of the flux
substitution has to be paid.  This file is not yet wired into any aggregate import — the
planner does that.
