import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear

/-! # The bilinear covariant Leibniz rule for the iterated covariant gradient

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`, the
linear file `IteratedCovGradLinear` records that the iterated section-level covariant gradient
`∇^j = iteratedCovGrad g r s j` is additive in its section, and the scalar file
`CovariantLeibniz` records the single-step covariant Leibniz rule for a *smooth-scalar-weighted*
section.  Neither provides a Leibniz/product rule for `∇^j` of a tensor *contraction/product* — the
keystone needed to expand the covariant jet of a bilinear combination of two tensor sections.

This file supplies that rule for a smooth *parallel* fibrewise continuous-bilinear bundle map,
the kind realized by metric contractions of a tensor product (parallel because `∇g = 0`).  Such a
map is packaged here as `ParallelTensorProduct`: a section-level bilinear product `prod`, valid at
every shifted gradient order, that is fibrewise-operator-bounded (`norm_prod_le`) and satisfies the
exact single-step covariant Leibniz identity `∇(prod S T) = prod (∇S) T + prod S (∇T)`
(`covGrad_prod`).  From these two genuine `∇`-compatibility hypotheses the binomial covariant jet
expansion follows, and its pointwise-fibre-norm corollary — the deliverable the covariant
Faà-di-Bruno chain consumes — is proved by induction on the gradient order.

## Main definitions

* `ParallelTensorProduct g r₁ s₁ r₂ s₂ r₀ s₀` — a parallel fibrewise continuous-bilinear bundle map
  from `(r₁, s₁ + a)`-tensors and `(r₂, s₂ + b)`-tensors to `(r₀, s₀ + a + b)`-tensors.  Its
  hypotheses are the genuine constraints of a `∇`-compatible bounded bilinear map: a uniform
  fibrewise operator bound, and the exact single-step covariant Leibniz identity.

## Main results

* `ParallelTensorProduct.prod_zero_left`, `prod_zero_right` — a parallel product kills the zero
  section in either argument (non-degeneracy: the operator bound is genuine).
* `ParallelTensorProduct.norm_covGrad_prod_le` — the single-step covariant Leibniz law read off in
  pointwise-norm form, `‖∇(prod S T)‖ ≤ ‖prod (∇S) T‖ + ‖prod S (∇T)‖`.
* `ParallelTensorProduct.norm_iteratedCovGrad_prod_le_jetGrid` — the **bilinear covariant Leibniz
  norm bound**: for every gradient order `j`, the pointwise fibre norm of `∇^j (prod S T)` is at most
  `opNorm · 2^j` times the double sum, over gradient orders `p, q ≤ j`, of the product
  `‖∇^p S‖ · ‖∇^q T‖` of the iterated covariant gradients of the two factors.  The factor `2^j`
  absorbs the binomial coefficients of the exact covariant Leibniz expansion.
* `ParallelTensorProduct.exists_norm_iteratedCovGrad_prod_le` — the existence form (a nonnegative
  order-dependent constant `C : ℕ → ℝ`, uniform over `S`, `T`, `x` at each gradient order `j`), the
  deliverable the covariant Faà-di-Bruno chain cites.

## Strategy

The recursion is on the gradient order `j`, peeling the *innermost* covariant gradient.  The base
case `j = 0` is `iteratedCovGrad_zero` together with the fibrewise operator bound `norm_prod_le`
(specialised to the `(p, q) = (0, 0)` summand).  The successor step rewrites `∇^{j+1}(prod S T)`
through the pointwise front-commutation `norm_toSection_iteratedCovGrad_covGrad_comm` (a fibrewise
recast of the heterogeneous commutation `iteratedCovGrad_covGrad_comm_heq`, both proven locally as
short `subst`/induction lemmas) as `∇^j(∇(prod S T))`, expands `∇(prod S T)` by the exact Leibniz
identity `covGrad_prod`, distributes `∇^j` over the resulting sum (`iteratedCovGrad_add`), recurses
on the two shifted-order pieces, and dominates both shifted `(j + 1)`-grids by the common
`range (j + 2)` grid (`shift_left_grid_le`, `shift_right_grid_le`) — every contributing pair has both
coordinates `≤ j + 1`.  The two dominating copies combine into the `2^{j + 1}` factor. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **Heterogeneous rank-congruence for `covGrad`.** If two ranks agree (`h : a = b`), then the
once-differentiated tensors `covGrad g r a Y` and `covGrad g r b Z` are heterogeneously equal
whenever `Y` and `Z` are. Proved by `subst` on the rank variable. -/
private theorem covGrad_heq_congr (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ} (h : a = b)
    {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) :
    HEq (covGrad g r a Y) (covGrad g r b Z) := by
  subst h
  rw [eq_of_heq hYZ]

/-- **Heterogeneous commuting of one covariant gradient through the iterated gradient.** Applying
`m` covariant gradients to `covGrad g r s X` is heterogeneously equal to the `(m + 1)`-fold iterated
gradient of `X`; the two live in the ranks `(s + 1) + m` and `s + (m + 1)`, which agree as naturals.
Proved by induction on `m` through `covGrad_heq_congr`. -/
private theorem iteratedCovGrad_covGrad_comm_heq (g : SmoothRiemannianMetric I M) (r s m : ℕ)
    (X : SmoothCcTensor g r s) :
    HEq (iteratedCovGrad g r (s + 1) m (covGrad g r s X))
      (iteratedCovGrad g r s (m + 1) X) := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_zero, iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact HEq.rfl
  | succ k ih =>
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s + 1) (j := k) (covGrad g r s X)]
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s) (j := k + 1) X]
      exact covGrad_heq_congr g r (by omega : (s + 1) + k = s + (k + 1)) ih

/-- **The pointwise fibre norm is invariant under a `SmoothCcTensor` rank-cast.** Heterogeneously
equal smooth compactly-supported tensors over agreeing ranks have equal section-value fibre norms
at every point. Proved by `subst` on the rank variable. -/
private theorem norm_toSection_heq_congr (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) (x : M) :
    ‖Y.toSection x‖ = ‖Z.toSection x‖ := by
  subst h
  rw [eq_of_heq hYZ]

/-- **Commuting one covariant gradient through the iterated gradient (pointwise-norm form).**
Applying `m` covariant gradients to `covGrad g r s X` has the same section-value fibre norm at `x`
as the `(m + 1)`-fold iterated gradient of `X`: the rank reassociation `(s + 1) + m = s + (m + 1)`
is invisible to the fibre norm. Proved from `iteratedCovGrad_covGrad_comm_heq` through
`norm_toSection_heq_congr`. -/
private theorem norm_toSection_iteratedCovGrad_covGrad_comm (g : SmoothRiemannianMetric I M)
    (r s m : ℕ) (X : SmoothCcTensor g r s) (x : M) :
    ‖(iteratedCovGrad g r (s + 1) m (covGrad g r s X)).toSection x‖ =
      ‖(iteratedCovGrad g r s (m + 1) X).toSection x‖ :=
  norm_toSection_heq_congr g r (by omega : (s + 1) + m = s + (m + 1))
    (iteratedCovGrad_covGrad_comm_heq (g := g) (r := r) (s := s) (m := m) X) x

/-- The rank-cast of a smooth compactly-supported tensor along a `Nat` equality of covariant ranks,
transported through `SmoothCcTensor.congr_simp`.  Used only to align the left Leibniz summand
`prod (∇S) T` (covariant rank `(s₀ + a + 1) + b`) with the differentiated product
`∇(prod S T)` (covariant rank `(s₀ + a + b) + 1`). -/
private def castRankCc (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ} (h : a = b)
    (Y : SmoothCcTensor g r a) : SmoothCcTensor g r b :=
  h ▸ Y

/-- **The iterated-gradient fibre norm is invariant under the rank-cast.** The `j`-fold iterated
covariant gradient of the rank-cast `castRankCc g r h Y` has the same section-value fibre norm at
`x` as that of `Y`. Proved by `subst` on the rank equality, which collapses the cast to the
identity. -/
private theorem norm_toSection_iteratedCovGrad_castRankCc (g : SmoothRiemannianMetric I M) (r : ℕ)
    {a b : ℕ} (h : a = b) (Y : SmoothCcTensor g r a) (j : ℕ) (x : M) :
    ‖(iteratedCovGrad g r b j (castRankCc g r h Y)).toSection x‖ =
      ‖(iteratedCovGrad g r a j Y).toSection x‖ := by
  subst h
  rfl

/-- **A parallel fibrewise continuous-bilinear bundle map** between tensor bundles, packaged at the
section level uniformly over the gradient order.

The map sends a smooth compactly-supported `(r₁, s₁ + a)`-tensor section and a smooth
compactly-supported `(r₂, s₂ + b)`-tensor section to a smooth compactly-supported
`(r₀, s₀ + a + b)`-tensor section, for every pair of extra-slot counts `a, b`.  The fields encode
exactly the two genuine constraints of a `∇`-compatible bounded bilinear map:

* `norm_prod_le` — a single uniform fibrewise operator bound `‖prod S T‖ ≤ opNorm · ‖S‖ · ‖T‖`
  (the continuity/boundedness of the bilinear map; in particular it forces `prod 0 T = 0` and
  `prod S 0 = 0`, so a degenerate nonzero witness is rejected);
* `covGrad_prod` — the exact single-step covariant Leibniz identity
  `∇(prod S T) = prod (∇S) T + prod S (∇T)` (the cross terms vanish precisely because the map is
  parallel, `∇ Φ = 0`).  The left summand `prod (∇S) T` carries covariant rank `(s₀ + a + 1) + b`,
  reindexed to the differentiated rank `(s₀ + a + b) + 1` by the rank-cast `castRankCc`.

This is the abstraction realized by a metric contraction of a tensor product (`∇g = 0`); it is kept
generic and decoupled from any specific nonlinearity so as to be a reusable covariant-calculus
byproduct. -/
structure ParallelTensorProduct (g : SmoothRiemannianMetric I M) (r₁ s₁ r₂ s₂ r₀ s₀ : ℕ) where
  /-- The section-level bilinear product, at every shifted gradient order `(a, b)`. -/
  prod : ∀ {a b : ℕ}, SmoothCcTensor g r₁ (s₁ + a) → SmoothCcTensor g r₂ (s₂ + b) →
    SmoothCcTensor g r₀ (s₀ + a + b)
  /-- The fibrewise operator norm of the bilinear map. -/
  opNorm : ℝ
  /-- The operator norm is nonnegative. -/
  opNorm_nonneg : 0 ≤ opNorm
  /-- The uniform fibrewise operator bound: the boundedness of the continuous bilinear map. -/
  norm_prod_le : ∀ {a b : ℕ} (S : SmoothCcTensor g r₁ (s₁ + a)) (T : SmoothCcTensor g r₂ (s₂ + b))
    (x : M), ‖(prod S T).toSection x‖ ≤ opNorm * ‖S.toSection x‖ * ‖T.toSection x‖
  /-- The exact single-step covariant Leibniz identity: parallelism of the map makes the derivative
  of the product split into the two one-sided derivatives with no cross term.  The left summand
  carries covariant rank `(s₀ + a + 1) + b`, rank-cast to the differentiated rank `(s₀ + a + b) + 1`
  via `castRankCc`. -/
  covGrad_prod : ∀ {a b : ℕ} (S : SmoothCcTensor g r₁ (s₁ + a)) (T : SmoothCcTensor g r₂ (s₂ + b)),
    covGrad g r₀ (s₀ + a + b) (prod S T) =
      castRankCc g r₀ (by omega : s₀ + (a + 1) + b = s₀ + a + b + 1)
          (prod (a := a + 1) (b := b) (covGrad g r₁ (s₁ + a) S) T) +
        prod (a := a) (b := b + 1) S (covGrad g r₂ (s₂ + b) T)

namespace ParallelTensorProduct

variable {g : SmoothRiemannianMetric I M} {r₁ s₁ r₂ s₂ r₀ s₀ : ℕ}

/-- A parallel product kills the zero section in its left argument: `prod 0 T = 0`.

This is the non-degeneracy witness for the operator bound `norm_prod_le`: at the zero left section
the bound forces every fibre norm of `prod 0 T` to vanish, hence the section is zero. -/
theorem prod_zero_left (Φ : ParallelTensorProduct g r₁ s₁ r₂ s₂ r₀ s₀) {a b : ℕ}
    (T : SmoothCcTensor g r₂ (s₂ + b)) :
    Φ.prod (0 : SmoothCcTensor g r₁ (s₁ + a)) T = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have hle := Φ.norm_prod_le (0 : SmoothCcTensor g r₁ (s₁ + a)) T x
  have hzero : ((0 : SmoothCcTensor g r₁ (s₁ + a)).toSection x) = 0 := by
    rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl
  rw [hzero, norm_zero, mul_zero, zero_mul] at hle
  have hval : (Φ.prod (0 : SmoothCcTensor g r₁ (s₁ + a)) T).toSection x = 0 :=
    norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  rw [show ((0 : SmoothCcTensor g r₀ (s₀ + a + b)).toSection x) = 0 from by
    rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl]
  exact hval

/-- A parallel product kills the zero section in its right argument: `prod S 0 = 0`. -/
theorem prod_zero_right (Φ : ParallelTensorProduct g r₁ s₁ r₂ s₂ r₀ s₀) {a b : ℕ}
    (S : SmoothCcTensor g r₁ (s₁ + a)) :
    Φ.prod S (0 : SmoothCcTensor g r₂ (s₂ + b)) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have hle := Φ.norm_prod_le S (0 : SmoothCcTensor g r₂ (s₂ + b)) x
  have hzero : ((0 : SmoothCcTensor g r₂ (s₂ + b)).toSection x) = 0 := by
    rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl
  rw [hzero, norm_zero, mul_zero] at hle
  have hval : (Φ.prod S (0 : SmoothCcTensor g r₂ (s₂ + b))).toSection x = 0 :=
    norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  rw [show ((0 : SmoothCcTensor g r₀ (s₀ + a + b)).toSection x) = 0 from by
    rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl]
  exact hval

/-- **The single-step covariant Leibniz law, in pointwise-norm form.** The pointwise fibre norm of
`∇(prod S T)` is at most the sum of the fibre norms of the two one-sided derivatives `prod (∇S) T`
and `prod S (∇T)`.  Read off from the exact identity `covGrad_prod` by the triangle inequality and
the rank-cast invariance of the fibre norm. -/
theorem norm_covGrad_prod_le (Φ : ParallelTensorProduct g r₁ s₁ r₂ s₂ r₀ s₀) {a b : ℕ}
    (S : SmoothCcTensor g r₁ (s₁ + a)) (T : SmoothCcTensor g r₂ (s₂ + b)) (x : M) :
    ‖(covGrad g r₀ (s₀ + a + b) (Φ.prod S T)).toSection x‖ ≤
      ‖(Φ.prod (a := a + 1) (b := b) (covGrad g r₁ (s₁ + a) S) T).toSection x‖ +
        ‖(Φ.prod (a := a) (b := b + 1) S (covGrad g r₂ (s₂ + b) T)).toSection x‖ := by
  rw [Φ.covGrad_prod S T]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  have hcast : ‖(castRankCc g r₀ (by omega : s₀ + (a + 1) + b = s₀ + a + b + 1)
        (Φ.prod (a := a + 1) (b := b) (covGrad g r₁ (s₁ + a) S) T)).toSection x‖ =
      ‖(Φ.prod (a := a + 1) (b := b) (covGrad g r₁ (s₁ + a) S) T).toSection x‖ := by
    have := norm_toSection_iteratedCovGrad_castRankCc g r₀
      (by omega : s₀ + (a + 1) + b = s₀ + a + b + 1)
      (Φ.prod (a := a + 1) (b := b) (covGrad g r₁ (s₁ + a) S) T) 0 x
    rwa [iteratedCovGrad_zero, iteratedCovGrad_zero] at this
  refine le_trans (norm_add_le _ _) ?_
  rw [hcast]
  exact le_refl _

set_option linter.unusedVariables false in
/-- Every product `‖∇^p S‖ · ‖∇^q T‖` of iterated-gradient fibre norms is nonnegative.  Carries the
map `Φ` only as the dot-notation receiver; the bound is independent of it. -/
private lemma jet_summand_nonneg (Φ : ParallelTensorProduct g r₁ s₁ r₂ s₂ r₀ s₀) {a b : ℕ}
    (S : SmoothCcTensor g r₁ (s₁ + a)) (T : SmoothCcTensor g r₂ (s₂ + b)) (x : M) (p q : ℕ) :
    0 ≤ ‖(iteratedCovGrad g r₁ (s₁ + a) p S).toSection x‖ *
      ‖(iteratedCovGrad g r₂ (s₂ + b) q T).toSection x‖ :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- **Left shift of the covariant-jet grid.** Differentiating the left factor once and grading over
the `(j + 1) × (j + 1)` grid is dominated by the `(j + 2) × (j + 2)` grid of the undifferentiated
factors: the front-commutation `∇^p(∇S) ↦ ∇^{p + 1}S` reindexes the `p`-axis into `{1, …, j + 1}`,
a subgrid of `range (j + 2)`. -/
private lemma shift_left_grid_le (Φ : ParallelTensorProduct g r₁ s₁ r₂ s₂ r₀ s₀) {a b : ℕ}
    (S : SmoothCcTensor g r₁ (s₁ + a)) (T : SmoothCcTensor g r₂ (s₂ + b)) (x : M) (j : ℕ) :
    (∑ p ∈ Finset.range (j + 1), ∑ q ∈ Finset.range (j + 1),
        ‖(iteratedCovGrad g r₁ (s₁ + a + 1) p (covGrad g r₁ (s₁ + a) S)).toSection x‖ *
          ‖(iteratedCovGrad g r₂ (s₂ + b) q T).toSection x‖) ≤
      ∑ p ∈ Finset.range (j + 2), ∑ q ∈ Finset.range (j + 2),
        ‖(iteratedCovGrad g r₁ (s₁ + a) p S).toSection x‖ *
          ‖(iteratedCovGrad g r₂ (s₂ + b) q T).toSection x‖ := by
  -- Reindex the differentiated left factor `∇^p(∇S)` to `∇^{p+1}S` via front-commutation,
  -- and widen the inner `q`-range from `range (j+1)` to `range (j+2)` (nonnegative summands).
  have hstep1 : (∑ p ∈ Finset.range (j + 1), ∑ q ∈ Finset.range (j + 1),
        ‖(iteratedCovGrad g r₁ (s₁ + a + 1) p (covGrad g r₁ (s₁ + a) S)).toSection x‖ *
          ‖(iteratedCovGrad g r₂ (s₂ + b) q T).toSection x‖) ≤
      ∑ p ∈ Finset.range (j + 1), ∑ q ∈ Finset.range (j + 2),
        ‖(iteratedCovGrad g r₁ (s₁ + a) (p + 1) S).toSection x‖ *
          ‖(iteratedCovGrad g r₂ (s₂ + b) q T).toSection x‖ := by
    refine Finset.sum_le_sum fun p _ => ?_
    rw [show (∑ q ∈ Finset.range (j + 1),
          ‖(iteratedCovGrad g r₁ (s₁ + a + 1) p (covGrad g r₁ (s₁ + a) S)).toSection x‖ *
            ‖(iteratedCovGrad g r₂ (s₂ + b) q T).toSection x‖) =
        ∑ q ∈ Finset.range (j + 1),
          ‖(iteratedCovGrad g r₁ (s₁ + a) (p + 1) S).toSection x‖ *
            ‖(iteratedCovGrad g r₂ (s₂ + b) q T).toSection x‖ from by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [norm_toSection_iteratedCovGrad_covGrad_comm g r₁ (s₁ + a) p S x]]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 (by omega : j + 1 ≤ j + 2))
      fun q _ _ => Φ.jet_summand_nonneg S T x (p + 1) q
  -- Shift the outer `p`-axis: the target grid equals the shifted source plus the `p = 0` row.
  refine hstep1.trans ?_
  rw [Finset.sum_range_succ' (n := j + 1)
    (f := fun p => ∑ q ∈ Finset.range (j + 2),
      ‖(iteratedCovGrad g r₁ (s₁ + a) p S).toSection x‖ *
        ‖(iteratedCovGrad g r₂ (s₂ + b) q T).toSection x‖)]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun q _ => Φ.jet_summand_nonneg S T x 0 q)

/-- **Right shift of the covariant-jet grid.** Differentiating the right factor once and grading over
the `(j + 1) × (j + 1)` grid is dominated by the `(j + 2) × (j + 2)` grid of the undifferentiated
factors. -/
private lemma shift_right_grid_le (Φ : ParallelTensorProduct g r₁ s₁ r₂ s₂ r₀ s₀) {a b : ℕ}
    (S : SmoothCcTensor g r₁ (s₁ + a)) (T : SmoothCcTensor g r₂ (s₂ + b)) (x : M) (j : ℕ) :
    (∑ p ∈ Finset.range (j + 1), ∑ q ∈ Finset.range (j + 1),
        ‖(iteratedCovGrad g r₁ (s₁ + a) p S).toSection x‖ *
          ‖(iteratedCovGrad g r₂ (s₂ + b + 1) q (covGrad g r₂ (s₂ + b) T)).toSection x‖) ≤
      ∑ p ∈ Finset.range (j + 2), ∑ q ∈ Finset.range (j + 2),
        ‖(iteratedCovGrad g r₁ (s₁ + a) p S).toSection x‖ *
          ‖(iteratedCovGrad g r₂ (s₂ + b) q T).toSection x‖ := by
  -- Reindex the differentiated right factor `∇^q(∇T)` to `∇^{q+1}T` and shift the inner `q`-axis:
  -- for each `p`, the target inner grid equals the shifted source plus the `q = 0` term.
  have hstep1 : (∑ p ∈ Finset.range (j + 1), ∑ q ∈ Finset.range (j + 1),
        ‖(iteratedCovGrad g r₁ (s₁ + a) p S).toSection x‖ *
          ‖(iteratedCovGrad g r₂ (s₂ + b + 1) q (covGrad g r₂ (s₂ + b) T)).toSection x‖) ≤
      ∑ p ∈ Finset.range (j + 1), ∑ q ∈ Finset.range (j + 2),
        ‖(iteratedCovGrad g r₁ (s₁ + a) p S).toSection x‖ *
          ‖(iteratedCovGrad g r₂ (s₂ + b) q T).toSection x‖ := by
    refine Finset.sum_le_sum fun p _ => ?_
    rw [show (∑ q ∈ Finset.range (j + 1),
          ‖(iteratedCovGrad g r₁ (s₁ + a) p S).toSection x‖ *
            ‖(iteratedCovGrad g r₂ (s₂ + b + 1) q (covGrad g r₂ (s₂ + b) T)).toSection x‖) =
        ∑ q ∈ Finset.range (j + 1),
          ‖(iteratedCovGrad g r₁ (s₁ + a) p S).toSection x‖ *
            ‖(iteratedCovGrad g r₂ (s₂ + b) (q + 1) T).toSection x‖ from by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [norm_toSection_iteratedCovGrad_covGrad_comm g r₂ (s₂ + b) q T x]]
    rw [Finset.sum_range_succ' (n := j + 1)
      (f := fun q => ‖(iteratedCovGrad g r₁ (s₁ + a) p S).toSection x‖ *
        ‖(iteratedCovGrad g r₂ (s₂ + b) q T).toSection x‖)]
    exact le_add_of_nonneg_right (Φ.jet_summand_nonneg S T x p 0)
  -- Widen the outer `p`-range from `range (j+1)` to `range (j+2)` (nonnegative summands).
  refine hstep1.trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.2 (by omega : j + 1 ≤ j + 2))
    fun p _ _ => Finset.sum_nonneg fun q _ => Φ.jet_summand_nonneg S T x p q

/-- **The bilinear covariant Leibniz norm bound.** For every gradient order `j`, the pointwise fibre
norm of `∇^j (prod S T)` is at most `opNorm · 2^j` times the double sum, over gradient orders
`p, q ∈ {0, …, j}`, of the products `‖∇^p S‖ · ‖∇^q T‖` of the iterated covariant gradients of the
two factors.  The factor `2^j` absorbs the binomial coefficients of the exact Leibniz expansion.

Proved by induction on `j`, generalising the two factors and their gradient-order shifts.  The base
case `j = 0` is the `(p, q) = (0, 0)` summand of the operator bound; the successor step
front-commutes the innermost gradient (`norm_toSection_iteratedCovGrad_covGrad_comm`), expands the
single covariant gradient by the exact Leibniz identity `covGrad_prod`, distributes `∇^j` over the
resulting sum (`iteratedCovGrad_add`), recurses on the two shifted-order pieces, and dominates both
shifted grids by the common `range (j + 2)` grid (`shift_left_grid_le`, `shift_right_grid_le`),
the two copies combining into the `2^{j + 1}` factor. -/
theorem norm_iteratedCovGrad_prod_le_jetGrid (Φ : ParallelTensorProduct g r₁ s₁ r₂ s₂ r₀ s₀)
    (j : ℕ) :
    ∀ {a b : ℕ} (S : SmoothCcTensor g r₁ (s₁ + a)) (T : SmoothCcTensor g r₂ (s₂ + b)) (x : M),
      ‖(iteratedCovGrad g r₀ (s₀ + a + b) j (Φ.prod S T)).toSection x‖ ≤
        Φ.opNorm * (2 : ℝ) ^ j * ∑ p ∈ Finset.range (j + 1), ∑ q ∈ Finset.range (j + 1),
          ‖(iteratedCovGrad g r₁ (s₁ + a) p S).toSection x‖ *
            ‖(iteratedCovGrad g r₂ (s₂ + b) q T).toSection x‖ := by
  induction j with
  | zero =>
      intro a b S T x
      rw [iteratedCovGrad_zero]
      have hsum : (∑ p ∈ Finset.range 1, ∑ q ∈ Finset.range 1,
          ‖(iteratedCovGrad g r₁ (s₁ + a) p S).toSection x‖ *
            ‖(iteratedCovGrad g r₂ (s₂ + b) q T).toSection x‖) =
          ‖S.toSection x‖ * ‖T.toSection x‖ := by
        rw [Finset.sum_range_one, Finset.sum_range_one]
        congr 1 <;> rw [iteratedCovGrad_zero]
      rw [hsum, pow_zero, mul_one, ← mul_assoc]
      exact Φ.norm_prod_le S T x
  | succ j ih =>
      intro a b S T x
      -- Front-commute the innermost gradient: ‖∇^{j+1}(prod S T)‖ = ‖∇^j(∇(prod S T))‖.
      rw [show ‖(iteratedCovGrad g r₀ (s₀ + a + b) (j + 1) (Φ.prod S T)).toSection x‖ =
          ‖(iteratedCovGrad g r₀ (s₀ + a + b + 1) j
              (covGrad g r₀ (s₀ + a + b) (Φ.prod S T))).toSection x‖ from
        (norm_toSection_iteratedCovGrad_covGrad_comm g r₀ (s₀ + a + b) j (Φ.prod S T) x).symm]
      -- Expand ∇(prod S T) by the exact Leibniz identity and distribute ∇^j over the sum.
      rw [Φ.covGrad_prod S T, iteratedCovGrad_add]
      rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
      refine norm_add_le _ _ |>.trans ?_
      -- Recast the rank-cast left piece through the fibre-norm cast invariance.
      rw [norm_toSection_iteratedCovGrad_castRankCc g r₀
        (by omega : s₀ + (a + 1) + b = s₀ + a + b + 1) (Φ.prod (covGrad g r₁ (s₁ + a) S) T) j x]
      -- Apply the induction hypothesis to each shifted piece, then dominate by the common grid.
      have hL := ih (a := a + 1) (b := b) (covGrad g r₁ (s₁ + a) S) T x
      have hR := ih (a := a) (b := b + 1) S (covGrad g r₂ (s₂ + b) T) x
      have hgridL := Φ.shift_left_grid_le S T x j
      have hgridR := Φ.shift_right_grid_le S T x j
      have hopNN : 0 ≤ Φ.opNorm := Φ.opNorm_nonneg
      have hpowNN : (0 : ℝ) ≤ (2 : ℝ) ^ j := by positivity
      calc
        ‖(iteratedCovGrad g r₀ (s₀ + (a + 1) + b) j
              (Φ.prod (covGrad g r₁ (s₁ + a) S) T)).toSection x‖ +
            ‖(iteratedCovGrad g r₀ (s₀ + a + (b + 1)) j
                (Φ.prod S (covGrad g r₂ (s₂ + b) T))).toSection x‖
            ≤ (Φ.opNorm * (2 : ℝ) ^ j * ∑ p ∈ Finset.range (j + 1), ∑ q ∈ Finset.range (j + 1),
                  ‖(iteratedCovGrad g r₁ (s₁ + a + 1) p (covGrad g r₁ (s₁ + a) S)).toSection x‖ *
                    ‖(iteratedCovGrad g r₂ (s₂ + b) q T).toSection x‖) +
                (Φ.opNorm * (2 : ℝ) ^ j * ∑ p ∈ Finset.range (j + 1), ∑ q ∈ Finset.range (j + 1),
                  ‖(iteratedCovGrad g r₁ (s₁ + a) p S).toSection x‖ *
                    ‖(iteratedCovGrad g r₂ (s₂ + b + 1) q (covGrad g r₂ (s₂ + b) T)).toSection x‖) :=
          add_le_add hL hR
        _ ≤ (Φ.opNorm * (2 : ℝ) ^ j * ∑ p ∈ Finset.range (j + 2), ∑ q ∈ Finset.range (j + 2),
                ‖(iteratedCovGrad g r₁ (s₁ + a) p S).toSection x‖ *
                  ‖(iteratedCovGrad g r₂ (s₂ + b) q T).toSection x‖) +
              (Φ.opNorm * (2 : ℝ) ^ j * ∑ p ∈ Finset.range (j + 2), ∑ q ∈ Finset.range (j + 2),
                ‖(iteratedCovGrad g r₁ (s₁ + a) p S).toSection x‖ *
                  ‖(iteratedCovGrad g r₂ (s₂ + b) q T).toSection x‖) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left hgridL (mul_nonneg hopNN hpowNN)
          · exact mul_le_mul_of_nonneg_left hgridR (mul_nonneg hopNN hpowNN)
        _ = Φ.opNorm * (2 : ℝ) ^ (j + 1) * ∑ p ∈ Finset.range (j + 1 + 1),
              ∑ q ∈ Finset.range (j + 1 + 1),
                ‖(iteratedCovGrad g r₁ (s₁ + a) p S).toSection x‖ *
                  ‖(iteratedCovGrad g r₂ (s₂ + b) q T).toSection x‖ := by
          show _ = Φ.opNorm * (2 : ℝ) ^ (j + 1) * ∑ p ∈ Finset.range (j + 2),
              ∑ q ∈ Finset.range (j + 2),
                ‖(iteratedCovGrad g r₁ (s₁ + a) p S).toSection x‖ *
                  ‖(iteratedCovGrad g r₂ (s₂ + b) q T).toSection x‖
          rw [pow_succ]
          ring

/-- **The bilinear covariant Leibniz norm bound, existence form.** There is a nonnegative constant
`C j` (the operator norm of the parallel bilinear map scaled by `2^j`) such that, for every gradient
order `j` and every point `x`, the pointwise fibre norm of `∇^j (prod S T)` is at most `C j` times
the double sum, over gradient orders `p, q ≤ j`, of the products `‖∇^p S‖ · ‖∇^q T‖`.  This is the
deliverable the covariant Faà-di-Bruno chain consumes; the constant absorbs the binomial
coefficients of the exact covariant Leibniz expansion. -/
theorem exists_norm_iteratedCovGrad_prod_le (Φ : ParallelTensorProduct g r₁ s₁ r₂ s₂ r₀ s₀)
    (S : SmoothCcTensor g r₁ s₁) (T : SmoothCcTensor g r₂ s₂) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀ (x : M) (j : ℕ),
      ‖(iteratedCovGrad g r₀ s₀ j (Φ.prod (a := 0) (b := 0) S T)).toSection x‖ ≤
        C j * ∑ p ∈ Finset.range (j + 1), ∑ q ∈ Finset.range (j + 1),
          ‖(iteratedCovGrad g r₁ s₁ p S).toSection x‖ *
            ‖(iteratedCovGrad g r₂ s₂ q T).toSection x‖ := by
  refine ⟨fun j => Φ.opNorm * (2 : ℝ) ^ j, fun j => mul_nonneg Φ.opNorm_nonneg (by positivity),
    fun x j => ?_⟩
  exact Φ.norm_iteratedCovGrad_prod_le_jetGrid j (a := 0) (b := 0) S T x

end ParallelTensorProduct

end RicciFlow
end PDE
end DifferentialGeometry

end
