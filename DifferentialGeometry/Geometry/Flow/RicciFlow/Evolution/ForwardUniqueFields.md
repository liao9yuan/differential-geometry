# ForwardUniqueFields.lean — Route-K brick FIELDS

Companion note for
`DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/ForwardUniqueFields.lean`.
Governing ruling: `ShortTime/FORWARD_UNIQUE_PRO_RULING.md`, §"Recommended tensor
variances" and §4.

## Status

Focused check: PASS. Targeted module build: PASS (no warnings from this file).
Axiom audit: all 16 public declarations depend on exactly
`[propext, Classical.choice, Quot.sound]`. Zero `sorry`.

## What each declaration provides

All three carriers are **metric-indexed**, not solution-indexed. `SolutionFamily`
carries only `metric : ℝ → SmoothRiemannianMetric I M` (connection, `rm13`, `rm04`,
Ricci are all `def`s of it), so for two solutions `S₁ S₂ : SolutionOn D` at time `s`
the ruling's fields are

```
h₀₂ = metricDiffAt  (S₁.family.metric s) (S₂.family.metric s) x
A₀₃ = connDiffLowAt (S₁.family.metric s) (S₂.family.metric s) x
S₀₄ = rmDiffLowAt   (S₁.family.metric s) (S₂.family.metric s) x
```

and the requested "`S₁ = S₂` at time `s` ⟹ carriers vanish" is exactly the `*_self`
lemmas after rewriting `S₁.family.metric s = S₂.family.metric s`. This is the weakest
honest hypothesis form and matches the ruling's own K3 signature style
(`forwardUniqueEnergy g₁ g₂`).

Public API (16 declarations):

* `metricDiffAt g₁ g₂ x : Tensor0SSpace 2 I x` — `h₀₂ = g₁ − g₂`, the difference of the
  two canonical `(0,2)` metric tensor fields.
  `metricDiffAt_apply` (`@[simp]`), `metricDiffAt_self` (`@[simp]`).
* `connDiffLowAt g₁ g₂ x : Tensor0SSpace 3 I x` — `A₀₃`, standard slot order
  `(X,Y,Z) ↦ g₁((∇¹ − ∇²)_X Y, Z)`.
  `connDiffLowAt_apply`, `connDiffLowAt_self` (`@[simp]`).
* `rmDiffLowAt g₁ g₂ x : Tensor0SSpace 4 I x` — `S₀₄`, standard slot order
  `(X,Y,Z,W) ↦ g₁((Rm¹ − Rm²)(X,Y)Z, W)`.
  `rmDiffLowAt_apply` (generic slots; identifies the first summand with the canonical
  `metricRm04At g₁ x`), `rmDiffLowAt_std` (the `(X,Y,Z,W)` lowering identity in terms of
  the two canonical `metricRm13At`), `rmDiffLowAt_self` (`@[simp]`).
* `metricDiffSq`, `connDiffSq`, `rmDiffSq` — the pointwise `g₁`-squared norms
  `normSq0S g₁ x k (carrier)` that the energy integrand `|h|² + |A|² + |S|²` is built
  from, with `*_def` unfolding lemmas (deliberately NOT `@[simp]`: they are definitional
  aliases, not normal forms).

## Reuse vs new

Reused as-is:

* `Tensor0SBundle.metricTensorField` (+ `metricTensorField_apply`) for `h₀₂`. The fiber
  difference is taken in `Tensor0SSpace 2 I x`, which is a plain `ContinuousMultilinearMap`
  fiber — no `ContMDiffSection` smoothness obligation is incurred.
* `Tensor0SBundle.connectionDifferenceTensorAt` / `connectionDifferenceOutput`
  (+ `connectionDifferenceOutput_apply`) for the `(1,2)` connection difference.
* `DifferentialGeometry.Integral.L2.lowerAllUpperIndices`
  (+ `lowerAllUpperIndices_apply`, `separableFormAt_apply`) for the `(1,2) → (0,3)`
  all-upper-index metric lowering.
* `CovariantDerivative.riemannCurvature04At`
  (+ `riemannCurvature04At_eq_lower_riemannCurvatureAt`) for `S₀₄`. This was the key
  simplification: the `(1,3) → (0,4)` lowering with an *arbitrary* metric is already the
  canonical construction, so `S₀₄` needed **no** new lowering machinery — it is literally
  `riemannCurvature04At g₁ ∇¹ − riemannCurvature04At g₁ ∇²`, and the first summand is
  definitionally `metricRm04At g₁ x`. No new curvature representation was introduced
  (Route-K gate respected).
* `Tensor0SSpace.sub_apply`, `Tensor0SSpace.domDomCongr_apply` for the fiber algebra.

New, and why:

* `covDiff_self` (private): `CovariantDerivative.difference cov cov x = 0`. Needed for
  `connDiffLowAt_self`. Proof pattern copied from `Geometry/Flow/ConnectionDifference.lean`'s
  `connDiff_self` (smooth section through a fiber vector + `difference_apply` + `sub_self`).
* `connDiffOutAt` / `connDiffStdPerm` / `connDiffOutAt_apply` (private): the output-first
  lowering and the slot permutation putting the lowered slot last, so the public carrier
  matches the ruling's `A₀₃ = g₁(∇¹ − ∇², ·)` and the project's standard-slot convention
  (same role `tensor04StdOfOutAt` plays for `riemannCurvature04At`).

## Two dedup items for the planner (deliberately not acted on — brick scope was one file)

1. `Tensor/RSTensor/RSLoweringNorm.lean` already defines `lowerAllSpace g r s x`, which is
   exactly `Tensor0SSpace.ofModel ∘ lowerAllUpperIndices ∘ TensorRSSpace.toModel` — i.e.
   the body of `connDiffOutAt` at `(r,s) = (1,2)`. It was **not** reused because that
   file's section-variable block carries `[InnerProductSpace ℝ E]`, `[CompleteSpace E]`,
   `[NeZero (Module.finrank ℝ E)]`, `[BoundarylessManifold I M]`; instance-implicit section
   variables mentioning `E` are included in the declaration, so consuming `lowerAllSpace`
   would have forced a model-space `InnerProductSpace ℝ E` hypothesis into this carrier API
   and into every K2/K3 consumer. That constraint is known-wrong for this project. The
   surgical fix is an `omit` on `lowerAllSpace` in `RSLoweringNorm.lean` (producer side);
   after that, `connDiffOutAt` should be replaced by `lowerAllSpace g 1 2 x`.
   `lowerAllSpace` currently has no consumers outside its own file, so this is cheap.
2. `covDiff_self` is stated for an arbitrary pair of equal `CovariantDerivative`s and is
   strictly more general than the existing `DeTurck.connDiff_self` (which is about
   `LeviCivita` pairs and also lives behind `[InnerProductSpace ℝ E]`). Its canonical home
   is the connection layer (next to Mathlib's `CovariantDerivative.difference`), not this
   Ricci-flow file. It is `private` here so no parallel public API is created.

## Lean lessons from this pass

* **`rw` on `Tensor0SSpace` fiber algebra is unreliable; use the lemma as a term.**
  `rw [Tensor0SSpace.sub_apply]` and `rw [Tensor0SSpace.domDomCongr_apply]` both failed
  with "did not find an occurrence of the pattern `(?A - ?B) ?v`" even though the goal
  displayed exactly that shape — the `FunLike` coercion instance path for
  `Tensor0SSpace s I x` (a non-reducible `def` over `Bundle.continuousMultilinearMap`)
  does not match syntactically. Every such step went through instead as
  `have h : <lhs> = <rhs> := Tensor0SSpace.sub_apply (I := I) k x _ _ v` followed by
  `rw [h]`. The `have`-with-explicit-type form also silently absorbs the beta/permutation
  reduction (`(fun i => v (perm i)) 0 ≡ v 2`), which is why `connDiffLowAt_apply` needs no
  `fin_cases` bookkeeping at all.
* `ContinuousMultilinearMap.ext` **does** apply directly to a `Tensor0SSpace` goal
  (`Tensor0SSpace` unfolds at default transparency), so no basis-based `ext0S_basis` was
  needed.
* `change` chains work well for stepping through `Tensor0SSpace.ofModel` /
  `TensorRSSpace.toModel`: those are definitional identities, which is also how
  `riemannCurvature04At_apply_const` is proved upstream.
* Namespace traps: `dualToCotangent_gen` and `tangentFlatLinear_gen` live in
  `Tensor0SBundle`, not `DifferentialGeometry.Integral.Connection`; `vec3`/`vec4`/
  `riemannCurvature04At` do live under `Integral.Connection(.CovariantDerivative)`.
  `metricCov`, `metricCov_smooth`, `metricRm13At`, `metricRm04At` all have
  `DifferentialGeometry.PDE.RicciFlow` compatibility aliases, so they resolve bare.
* `rw` closes with `rfl` only at reducible transparency: identifying
  `riemannCurvatureAt (metricCov g) _ x` with `metricRm13At g x` needed an explicit
  trailing `rfl`.
* No instance-synthesis trouble at all: the K1 variable block
  (`[IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]`
  `[CompleteSpace E] [SigmaCompactSpace M] [T2Space M]`, `NormedSpace` only) synthesised
  `VectorBundle`/`ContMDiffVectorBundle` for `connectionDifferenceTensorAt` and
  `ContMDiffSection.exists_eq_at` without help. `set_option
  backward.isDefEq.respectTransparency false` was never needed.

## What this brick does NOT do

No time dependence, no derivative, no estimate. K1's `christoffelEvolutionDiffInFrameOn`
(`ForwardUniqueConnectionDiff.lean`) is the frame-component time derivative; K2 (the
divergence-form curvature-difference evolution) and K3 (the moving triple-energy
derivative) are the next bricks and are untouched here. This file is also not yet wired
into any aggregate import — the planner does that.
