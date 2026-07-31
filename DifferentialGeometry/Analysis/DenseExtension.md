# DenseExtension.lean — dense extension of a locally Lipschitz core map

Status: **DONE, green, axiom-clean** (`[propext, Classical.choice, Quot.sound]`
on all eight declarations), zero `sorry`, 226 lines.
Dispatched by `ShortTime/UNIF_EXISTENCE_PLAN2.md` planner update No. 74,
follow-up (2): "a dense-extension lemma for locally Lipschitz core maps".

## Why the lemma exists

No. 74 ruled `hHiPair` (one global Lipschitz constant for the completed `a1Hi`
coefficient) **false** by counterexample.  The honest replacement, `a1_pair_lip`
in `DeTurckRemainderLowBaseA1Pair.lean`, is Lipschitz only on the ball
`lowJetSq g 3 T, lowJetSq g 3 U ≤ A²`, with a constant that grows in `A`.  With
an `R`-dependent constant there is nothing global to extend, so
`dense_lipschitz` (one constant, `LipschitzWith` conclusion) is inapplicable and
the completed operator can only be asserted **continuous**.

## What Mathlib already had, and what it did not

Already there and used:

* `Dense.extend` / `Dense.extend_eq` / `Dense.isDenseInducing_val`
  (`Topology/DenseEmbedding.lean`) — the extension itself and its value on the
  core.  This is the same `Dense.extend` that `lowA1Hi` / `lowA1Lo` are *defined*
  as, which is why the deliverable is phrased against it.
* `IsDenseInducing.continuous_extend_of_cauchy`
  (`Topology/UniformSpace/CompleteSeparated.lean`) — the engine: it suffices
  that every ambient neighbourhood filter, pulled back to the core, has Cauchy
  image.
* `LipschitzOnWith.uniformContinuousOn`, `LipschitzOnWith.continuousOn`,
  `Cauchy.map_of_le`, `Set.rangeSplitting` / `Set.apply_rangeSplitting`,
  `DenseRange.induction_on`.

**Not** there: any form of the statement itself.  Mathlib's Lipschitz-extension
theorems (`LipschitzOnWith.extend_real`, `.extend_pi`, `.extend_lp_infty`,
`.extend_finite_dimension`) extend off an *arbitrary* subset but only into
special codomains (`ℝ`, `ι → ℝ`, `ℓ^∞`, finite-dimensional); here the codomain is
an arbitrary complete normed space — in the application a space of continuous
linear maps — and it is *density* that does the work, not a Kirszbraun-type
extension theorem.  So this is a genuine (if short) build, not an adapter.

## In-tree prior art

`dense_cont_on_balls` in
`Analysis/Parabolic/QuasiLinear/TensorMaximalRegularity/TameForcingFixedPoint.lean`
is the **same mathematics** in the subset face (`D : Set X`, `F : D → Y`,
centre `x₀`).  It was found during the prior-art sweep and its proof is the
source of `cont_extend_lip`'s proof here.  It could not be *reused* because it
sits high in the `QuasiLinear` tree (imports `PartialForcingFixedPoint`), which
a generic `Analysis/` file must not import, and because its subtype-phrased
hypothesis is not what a core-index estimate produces.

Deliberate follow-up (NOT done, to stay surgical and avoid touching a file in
another agent's lane): re-derive `dense_cont_on_balls` as a one-line consequence
of `cont_extend_lip` and delete its proof body.  Statement is identical up to
the weaker typeclasses here.  Same remark for `dense_lipschitz` /
`mixed_of_dense` in `DenseMixedBound.lean`, which are generic normed-space facts
living in the `QuasiLinear` namespace; their canonical home is this file.

## What was built

Namespace `DifferentialGeometry.Analysis`, file
`DifferentialGeometry/Analysis/DenseExtension.lean`, five Mathlib imports only
(`Normed.Group.Basic`, `Normed.Group.Continuity`, `Topology.DenseEmbedding`,
`Topology.MetricSpace.Lipschitz`, `UniformSpace.CompleteSeparated`).  No
manifold, metric, or Sobolev content; `ι` (the core index) carries **no**
structure at all.

Subset face:

* `cont_of_lipBalls` — `F : D → Y` Lipschitz on every ball about `x₀` ⟹
  `Continuous F`.  `[PseudoMetricSpace X] [PseudoMetricSpace Y]`.
* `cont_extend_lip` — same hypotheses plus `Dense D` ⟹
  `Continuous (Dense.extend hD F)`.  Codomain needs only
  `[CompleteSpace Y] [T0Space Y]` (exactly what `continuous_extend_of_cauchy`
  demands); no group structure anywhere.

Dense-range face (`j : ι → X`, `hj : DenseRange j`, `f : ι → Y` the core map;
`[SeminormedAddCommGroup X] [NormedAddCommGroup Y] [CompleteSpace Y]`).  The
uniform hypothesis shape is

    hpair : ∀ R : ℝ, ∃ K : ℝ, ∀ v w : ι,
      ‖j v‖ ≤ R → ‖j w‖ ≤ R → ‖f v - f w‖ ≤ K * ‖j v - j w‖

(`K : ℝ`, not `ℝ≥0` — sign is handled internally by `max K 0`, so a caller
never has to produce a nonnegativity proof):

* `eq_of_lipPair` — the estimate forces `j v = j w → f v = f w`, i.e. the core
  map descends to `Set.range j`.  (Used for `exists_extend_pair`; also the
  honest reason no injectivity hypothesis is needed.)
* `cont_extend_pair` — for `F : ↥(Set.range j) → Y` with
  `hval : ∀ v, F ⟨j v, ⟨v, rfl⟩⟩ = f v`, gives `Continuous (Dense.extend hj F)`.
* `extend_pair_apply` — the `_apply` face: `Dense.extend hj F (j v) = f v`
  (no completeness needed).
* `exists_extend_pair` — `∃ F : X → Y, Continuous F ∧ ∀ v, F (j v) = f v`, for
  a caller who has not already named the extension.

Norm transport (the M-witness face):

* `norm_extend_le` — `Continuous F`, `∀ v, F (j v) = f v`, `∀ v, ‖f v‖ ≤ Φ ‖j v‖`,
  `Continuous Φ` ⟹ `∀ x, ‖F x‖ ≤ Φ ‖x‖`.  Codomain only
  `[SeminormedAddCommGroup Y]`, no completeness.
  **Monotonicity of `Φ` is not needed** — the closed set `{x | ‖F x‖ ≤ Φ ‖x‖}`
  only needs both sides continuous.  The dispatch asked for "monotone
  continuous `Φ`"; the monotonicity hypothesis was dropped.
* `exists_extend_le` — the packaged `∃ F, Continuous F ∧ (∀ v, F (j v) = f v) ∧
  ∀ x, ‖F x‖ ≤ Φ ‖x‖`.

## Consuming it in the A1 lane

`lowA1Hi` / `lowA1Lo` are *literally* `Dense.extend (ccToHsLin_dense …)
(lowA1HiCore …)`, and `highCore g` is *literally*
`Set.range (ccToHsLin g 2 (3:ℝ))`, so `cont_extend_pair` /
`extend_pair_apply` apply with no glue: `hval` is exactly the shape of
`a1HiCore_value` (the same shape the existing private `highCorePair` consumes).
Two call-site facts:

1. The right-hand side conversion `‖j T - j U‖ = ‖ccTensorToHs g 2 3 (T - U)‖`
   is one `map_sub` rewrite (`simpa only [map_sub]`), the same rewrite
   `highCorePair` already performs.
2. The ball condition here is `‖j T‖ ≤ R` (`H³` norm), while `a1_pair_lip`'s is
   `lowJetSq g 3 T ≤ A²`.  Converting the two is a lane-local bridge, not
   something this file can supply.

A probe file exercising all three faces at exactly the application shape
(`φ : A →L[ℝ] X` a CLM with dense range, `↥(Set.range ⇑φ)` subtype, estimate
written with `‖φ (T - U)‖`, codomain a complete normed space) elaborates
cleanly; it lives in the scratchpad, not the repo.

## Lean notes worth keeping

* `Dense.extend` accepts a `DenseRange j` term directly (`DenseRange` is a
  plain `def` for `Dense (range j)` and unifies), which is what makes the
  `DenseRange` face and the `Set`-face interoperate.
* `Continuous.norm` / `continuous_norm` are **not** in
  `Mathlib.Analysis.Normed.Group.Basic`; they need
  `Mathlib.Analysis.Normed.Group.Continuity`.  This was the only compile error
  in the whole build.
* `NormedSpace` and `→L[ℝ]` are also not reachable from the imports of this
  file; that is intentional (the file is norm-only), and a consumer probe must
  add `Mathlib.Analysis.Normed.Module.Basic`.
* Descending along `x.2.choose` by hand is avoidable: `Set.rangeSplitting j`
  plus `Set.apply_rangeSplitting` is the clean idiom, and the same idiom the
  tree already uses by hand in `highRep` / `highRep_spec`.

## Verification

Focused check and targeted module build both passed.  `#print axioms` on all
eight declarations returned `[propext, Classical.choice, Quot.sound]` (the block
was temporary and has been removed).  The module is a leaf: it is not yet in the
root `DifferentialGeometry.lean` umbrella, matching the lane's current practice
for new files (`LowRegOperatorTime`, `DeTurckRemainderLowBaseA1Pair` are not
there either); it will be built once a consumer imports it.
