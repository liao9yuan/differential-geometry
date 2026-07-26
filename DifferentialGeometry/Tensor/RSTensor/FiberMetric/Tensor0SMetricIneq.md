# `Tensor0SMetricIneq.lean` — fiber inequality kit for `inner0S` / `normSq0S`

Status: **DONE, verified green, axiom-clean** (2026-07-25).
Consumer: forward-uniqueness lane, `FORWARD_UNIQUE_PLAN.md` §Dispatch №9 — the
`|∂ₜA₀₃|²` estimate (K1C-b) and the upcoming Gronwall-rate brick.

## What the file provides

Namespace `Tensor0SBundle`, section hypotheses copied verbatim from
`Tensor0SMetric.lean` (`[NormedAddCommGroup E] [NormedSpace ℝ E]
[FiniteDimensional ℝ E]`, `{I : ModelWithCorners ℝ E H}`, `[IsManifold I ∞ M]`).
No extra typeclass, no basis, no frame, no orthonormality, no point/rank
restriction.

Bilinearity layer (was entirely missing):
`inner0S_comm`, `inner0S_add_left`, `inner0S_add_right`, `inner0S_sub_left`,
`inner0S_sub_right`, `inner0S_smul_left`, `inner0S_smul_right`.

Quadratic expansions: `normSq0S_add`, `normSq0S_sub`
(`|A ± B|² = |A|² ± 2⟨A,B⟩ + |B|²`), `normSq0S_neg`.

Inequalities: `abs_inner0S_le` (`|⟨A,B⟩| ≤ √|A|²·√|B|²`), `two_inner0S_le`,
`neg_two_inner0S_le`, `normSq0S_add_le` and `normSq0S_sub_le` (the doubling
form `|A ± B|² ≤ 2|A|² + 2|B|²` that the estimates consume),
`sqrt_normSq0S_add_le` / `sqrt_normSq0S_sub_le` (coordinate-free Minkowski).

17 declarations, 0 `sorry`, ~240 lines.

## Route that worked

The mission suggested instantiating the local `PreInnerProductSpace.Core`.
That turned out to be unnecessary: **`MetricFiberData.flat` is already a
`LinearEquiv`**, so bilinearity of `inner0S` is just `map_add` / `map_sub` /
`map_smul` on `flat` followed by `LinearMap.add_apply` / `sub_apply` /
`smul_apply` on the resulting `Module.Dual` element. Three-line proofs, no
`Core` instantiation, no `letI`, no diamond exposure.

Concretely the working idiom is
`unfold inner0S MetricFiberData.inner` then `rw [map_add, LinearMap.add_apply]`
(same shape for `sub`/`smul`). This is the pattern already used by
`HCGCompactness.normSq0S_smul` in `AllTimesBounds.lean:3926`.

Cauchy–Schwarz was **not** re-derived: `Tensor0SMetric.lean:467`
`inner0S_sq_le_mul` already gives `⟨A,B⟩² ≤ |A|²·|B|²` (it is the place the
local `PreInnerProductSpace.Core` lives). `abs_inner0S_le` is
`Real.sqrt_le_sqrt` of it plus `Real.sqrt_sq_eq_abs` and `Real.sqrt_mul` —
two lines. Nonnegativity `normSq0S_nonneg` (`Tensor0SMetric.lean:497`) reused
as-is.

Everything downstream (doubling bounds, Minkowski) is `linarith` from the
expansions plus nonnegativity of `normSq0S` at `A ± B`. No component
enumeration anywhere.

## Deliberate omission: `normSq0S_smul`

Mission item 4 (`normSq0S (c • A) = c² · normSq0S A`) was **not** added:
`Tensor0SBundle.normSq0S_smul` already exists at
`Tensor/RSTensor/Tensor0SRiemannian/Scaling.lean:61`, in the *same namespace*,
with the *same* typeclass hypotheses. Redeclaring it here would be a duplicate
fully-qualified name and would break any file importing both modules. Callers
that only want the fiber algebra can instead use `inner0S_smul_left` +
`inner0S_smul_right` (`normSq0S (c•A) = c * (c * normSq0S A)` in one `simp`),
which is what this file exports.

Note the layering: `Scaling.lean` sits *above* `FiberMetric/` (it imports
`Geometry.Metric.Scaling` and `Tensor0SRiemannian.Coordinate`), so
`normSq0S_smul` is not reachable from this file's import set. If a consumer at
the `FiberMetric` layer needs it, the right fix is to **move** `normSq0S_smul`
down into `Tensor0SMetric.lean` (its proof needs nothing beyond
`flat.map_smul`), not to duplicate it. Left for the planner — the brick
protocol forbade editing other files.

## Dedup items for the planner

1. `HCGCompactness.sqrt_normSq0S_add_le`
   (`ProductMFoldNorm.lean:233`) proves the same Minkowski inequality but
   through `normSq0S_identity_eq_sum_sq` + `compL2_add_le`, so it demands a
   `Module.Basis Idx ℝ (TangentSpace I x)` **and** a
   `MetricInverseInBasis_gen … identityInvMetric` hypothesis (i.e. a
   `gRef`-orthonormal frame). `Tensor0SBundle.sqrt_normSq0S_add_le` here is
   coordinate-free and strictly more general; its call sites
   (`ProductMFoldNorm.lean:352`, `UnifCovSumCross.lean:1203-1204`,
   `C4/PullbackField.lean` ×4, `C4/ApproxIsometryCompHigher.lean` ×2) can drop
   the basis/`hinv` arguments.
2. `HCGCompactness.normSq0S_neg` (`MetricPreconvWindowGInf.lean:300`) is proved
   by producing an orthonormal basis via `exists_gOrthonormalBasis`;
   `Tensor0SBundle.normSq0S_neg` here is four lines and frame-free. Same
   replacement opportunity.
   (Both are in namespace `DifferentialGeometry.HCGCompactness`, so there is no
   name clash today — this is cleanup, not a build problem.)
3. `DifferentialGeometry.lean` (the umbrella) does **not** import this module.
   It is not exhaustive for `FiberMetric/` anyway (`Tensor0SBochnerProduct`,
   `Tensor0SBochnerSplit`, `Tensor0SInnerLeibniz`, `Tensor0SMetricContinuity`,
   `Tensor0SMetricDeriv`, `ConnectionDifferenceNorm` are also absent and only
   reached transitively), so this is cosmetic until a consumer imports it.

## Lean lessons (durable)

* **The `Tensor0SSpace` FunLike-coercion diamond recorded in
  `ForwardUniqueFields.md` / `ForwardUniqueConnDot.md` never appears here**, and
  the reason is worth remembering: those failures came from `rw` on lemmas whose
  statement is about *applying a fiber tensor to a vector*
  (`(A - B) v`). Everything in this file stays one level up — it manipulates
  `MetricFiberData.flat`, a `LinearEquiv` between fiber and dual — so the
  rewrites are `map_add` / `LinearMap.add_apply` on ordinary `LinearMap`s and
  `rw` behaves normally. **Rule of thumb: keep fiber-metric algebra at the
  `flat`/`Module.Dual` level and it stays `rw`-friendly; drop to
  `Tensor0SSpace`-application level and you need the term-form `have … := lemma …`
  idiom.**
* `inner0S_comm` is closed by `exact (tensor0SMetricData … ).inner_comm A B`
  with no `change`: `inner0S` is a plain `def` delegating to
  `MetricFiberData.inner`, so defeq crosses it. (`Tensor0SMetric.lean:485` uses
  a `change` only because the surrounding goal had already been rewritten.)
* `Real.sq_sqrt` (`√a ^ 2 = a`) vs `Real.sqrt_sq` (`√(a^2) = a`) — both under
  `0 ≤ a`; the Minkowski proof needs both, in that order.
* Duplicate-name check before writing: `Tensor0SBundle.normSq0S_smul` is a live
  trap (see above). Grep `theorem <name>` across `--include=*.lean` *and* check
  the enclosing `namespace` before choosing a name — several `normSq0S_*`
  helpers exist under `DifferentialGeometry.HCGCompactness` and are harmless,
  but `Tensor0SRiemannian/Scaling.lean` shares this namespace.

## Verification

Focused check green; targeted module build green (the only warnings are
pre-existing `unusedFintypeInType` notices from `Tensor/Multilinear/Comp.lean`
and `Tensor/Alternating/Comp.lean`, untouched by this brick). `#print axioms`
on all 17 declarations: `[propext, Classical.choice, Quot.sound]` only — no
`sorryAx`.
