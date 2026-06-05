import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FiberNormSubadditivity

/-! # The covariant-Leibniz curvature-coefficient grid for the metric contraction, constructed

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file *constructs* the iterated covariant-gradient
curvature-coefficient grid for the metric curvature contraction
`R(X, Y) Z := curvatureContraction g s Z hX hY` (a smooth compactly-supported `(0, s)`-tensor
section), in the intrinsic `riemannianFiberNormSq` (`rfns`) form the order-`m` curvature-jet
induction consumes.

## The exact covariant Leibniz of the curvature contraction is a coefficient grid

The curvature contraction `R(X, Y)·` is a *fixed* operator built from the metric and the smooth
frame fields `X, Y`, *linear in the single section* `W`, applicable at *every* covariant rank `r`
(`diffCurvOp 0 r W := curvatureContraction g r W hX hY`). It is **not parallel** (`∇R ≠ 0` on a
non-flat manifold), so the exact single-step covariant Leibniz reads
`∇(R W) = (∇R) W + R(∇W)` with the *non-vanishing* differentiated-curvature cross term `(∇R) W`.
We make this exact by *defining* the order-`p` differentiated-curvature contraction recursively as
the Leibniz remainder,
```
diffCurvOp (p + 1) r W := ∇(diffCurvOp p r W) − diffCurvOp p (r + 1) (∇W),
```
so the single-step Leibniz `∇(diffCurvOp p r W) = diffCurvOp (p + 1) r W + diffCurvOp p (r + 1) (∇W)`
holds *by definition* (`sub_add_cancel`). Iterating it (the binomial covariant jet expansion) gives
the curvature contraction's own double grid: a sum over the differentiation order `p` of the
curvature factor `∇^p R` (the operator `diffCurvOp p`) and the gradient order `q` of the contracted
section `W`,
```
rfns(∇^j(R W))(x) ≤ A j · ∑_{p ≤ j} kappa p · ∑_{q ≤ j} rfns(∇^q W)(x).
```
The curvature factor enters only as the *base-point-uniform, section-proportional* coefficient
`kappa p` — the proportional fibre-operator norm of the smooth fixed operator `diffCurvOp p` on the
compact `M` — while only the gradient order `q` of the *section* survives as a fibre-norm grid; the
constant `A j := 2 ^ j` absorbs the binomial coefficients of the exact covariant Leibniz expansion.

## What is posited vs. derived

The single genuinely-irreducible analytic primitive is the **per-order section-proportional fibre
bound for the differentiated-curvature contraction operators**, `exists_proportional_diffCurvOp`:
`rfns(diffCurvOp p r W)(x) ≤ kappa p · rfns(W)(x)`. Each `diffCurvOp p` is a smooth fixed
fibrewise-linear operator (a recursive Leibniz remainder of the smooth curvature contraction), so it
is uniformly bounded, proportionally to its section, on the compact `M` — the order-`0` case
`kappa 0` is the curvature operator's own uniform proportional bound
`exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional`. It is posited here as the
precise true primitive; consumers transitively depend on `sorryAx` through it. The degenerate witness
is rejected: at `p = 0`, `j = 0` the grid reads `rfns(R W)(x) ≤ A 0 · kappa 0 · rfns(W)(x)`, false
with `kappa 0 = 0` on a non-flat manifold whenever `R W ≠ 0`.

Everything else — the recursive operator construction, the binomial covariant-Leibniz induction
(through `riemannianFiberNormSq_add_le` and the iterated-gradient additivity `iteratedCovGrad_add`),
and the grid bookkeeping — is *derived* here, and the headline grid
`exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_kappaGrid_le` is the order-`p = 0`
specialisation. -/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

section RankCast

set_option linter.unusedSectionVars false in
/-- **Heterogeneous rank-congruence for `covGrad`.** If two ranks agree (`h : a = b`), then the
once-differentiated tensors `covGrad g r a Y` and `covGrad g r b Z` are heterogeneously equal
whenever `Y` and `Z` are. Proved by `subst` on the rank variable. -/
private theorem covGrad_heq_congr_lg (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) :
    HEq (covGrad g r a Y) (covGrad g r b Z) := by
  subst h
  rw [eq_of_heq hYZ]

/-- **Heterogeneous commuting of one covariant gradient through the iterated gradient.** Applying
`m` covariant gradients to `covGrad g r s X` is heterogeneously equal to the `(m + 1)`-fold iterated
gradient of `X`; the two live in the ranks `(s + 1) + m` and `s + (m + 1)`, which agree as naturals.
Proved by induction on `m` through `covGrad_heq_congr_lg`. -/
private theorem iteratedCovGrad_covGrad_comm_heq_lg (g : SmoothRiemannianMetric I M) (r s m : ℕ)
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
      exact covGrad_heq_congr_lg g r (by omega : (s + 1) + k = s + (k + 1)) ih

set_option linter.unusedSectionVars false in
/-- **The intrinsic fibre norm is invariant under a `SmoothCcTensor` rank-cast.** Heterogeneously
equal smooth compactly-supported tensors over agreeing ranks have equal section-value
`riemannianFiberNormSq` at every point. Proved by `subst` on the rank variable. -/
private theorem rfns_toSection_heq_congr_lg (g : SmoothRiemannianMetric I M)
    (r : ℕ) {a b : ℕ} (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b}
    (hYZ : HEq Y Z) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r a x (Y.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r b x (Z.toSection x) := by
  subst h
  rw [eq_of_heq hYZ]

/-- **Front-commuting one covariant gradient through the iterated gradient (rfns form).** The
intrinsic squared fibre norm of `∇^m(∇W)` at `x` equals that of `∇^{m+1}W`: the rank reassociation
`(s + 1) + m = s + (m + 1)` is invisible to the fibre norm. From
`iteratedCovGrad_covGrad_comm_heq_lg` through `rfns_toSection_heq_congr_lg`. -/
private theorem rfns_iteratedCovGrad_covGrad_comm_lg (g : SmoothRiemannianMetric I M)
    (r s m : ℕ) (W : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r ((s + 1) + m) x
        ((iteratedCovGrad g r (s + 1) m (covGrad g r s W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + (m + 1)) x
        ((iteratedCovGrad g r s (m + 1) W).toSection x) :=
  rfns_toSection_heq_congr_lg g r (by omega : (s + 1) + m = s + (m + 1))
    (iteratedCovGrad_covGrad_comm_heq_lg g r s m W) x

/-- The rank-cast of a smooth compactly-supported tensor along a `Nat` equality of covariant ranks,
used to align the differentiated rank of the curvature-Leibniz remainder. -/
private def castRankCc_lg (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ} (h : a = b)
    (W : SmoothCcTensor g r a) : SmoothCcTensor g r b :=
  h ▸ W

set_option linter.unusedSectionVars false in
/-- **The iterated-gradient fibre norm is invariant under the rank-cast `castRankCc_lg`.** The
`j`-fold iterated covariant gradient of `castRankCc_lg g r h W` has the same section-value fibre norm
at `x` as that of `W`. Proved by `subst` on the rank equality, collapsing the cast to the
identity. -/
private theorem rfns_iteratedCovGrad_castRankCc_lg (g : SmoothRiemannianMetric I M) (r : ℕ)
    {a b : ℕ} (h : a = b) (W : SmoothCcTensor g r a) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (b + j) x
        ((iteratedCovGrad g r b j (castRankCc_lg g r h W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (a + j) x
        ((iteratedCovGrad g r a j W).toSection x) := by
  subst h
  rfl

end RankCast

variable (g : SmoothRiemannianMetric I M)
  {X Y : Π b : M, TangentSpace I b}
  (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
  (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))

/-- **The order-`p` differentiated-curvature contraction operator.** Acting on a smooth
compactly-supported `(0, r)`-tensor section `W`, `diffCurvOp p r W` is the `p`-times
covariantly-differentiated curvature contraction `(∇^p R)(X, Y) W`, a smooth compactly-supported
`(0, r + p)`-tensor section, defined recursively as the exact covariant-Leibniz remainder:

* `diffCurvOp 0 r W := curvatureContraction g r W hX hY` (the curvature contraction `R(X, Y) W`);
* `diffCurvOp (p + 1) r W := ∇(diffCurvOp p r W) − (rank-cast) diffCurvOp p (r + 1) (∇W)` (the
  differentiated curvature: the part of `∇(∇^p R · W)` not captured by `∇^p R · (∇W)`); the right
  summand carries covariant rank `(r + 1) + p`, rank-cast to the differentiated rank `(r + p) + 1`
  via `castRankCc_lg`.

By construction the single-step covariant Leibniz `∇(diffCurvOp p r W) = diffCurvOp (p + 1) r W +
(rank-cast) diffCurvOp p (r + 1) (∇W)` holds *by definition* (`sub_add_cancel`). -/
def diffCurvOp : ∀ (p r : ℕ) (_ : SmoothCcTensor g 0 r), SmoothCcTensor g 0 (r + p)
  | 0, r => fun W => curvatureContraction (I := I) (M := M) g r W hX hY
  | (p + 1), r => fun W =>
      covGrad (I := I) (M := M) g 0 (r + p) (diffCurvOp p r W) -
        castRankCc_lg g 0 (by omega : (r + 1) + p = r + (p + 1))
          (diffCurvOp p (r + 1) (covGrad (I := I) (M := M) g 0 r W))

set_option linter.unusedSectionVars false in
/-- `diffCurvOp 0 r W` is the curvature contraction `R(X, Y) W`. Definitional. -/
theorem diffCurvOp_zero (r : ℕ) (W : SmoothCcTensor g 0 r) :
    diffCurvOp (I := I) (M := M) g hX hY 0 r W =
      curvatureContraction (I := I) (M := M) g r W hX hY := rfl

set_option linter.unusedSectionVars false in
/-- **The exact single-step covariant Leibniz of the differentiated-curvature contraction.** By the
recursive definition of `diffCurvOp`, `∇(diffCurvOp p r W)` splits exactly into the higher-order
remainder `diffCurvOp (p + 1) r W` and the rank-cast lower-order term applied to `∇W`. Proved by
`sub_add_cancel` on the recursive definition. -/
theorem covGrad_diffCurvOp_eq (p r : ℕ) (W : SmoothCcTensor g 0 r) :
    covGrad (I := I) (M := M) g 0 (r + p) (diffCurvOp (I := I) (M := M) g hX hY p r W) =
      diffCurvOp (I := I) (M := M) g hX hY (p + 1) r W +
        castRankCc_lg g 0 (by omega : (r + 1) + p = r + (p + 1))
          (diffCurvOp (I := I) (M := M) g hX hY p (r + 1)
            (covGrad (I := I) (M := M) g 0 r W)) := by
  change _ = (covGrad (I := I) (M := M) g 0 (r + p) (diffCurvOp (I := I) (M := M) g hX hY p r W) -
      castRankCc_lg g 0 (by omega : (r + 1) + p = r + (p + 1))
        (diffCurvOp (I := I) (M := M) g hX hY p (r + 1)
          (covGrad (I := I) (M := M) g 0 r W))) + _
  rw [sub_add_cancel]

/-- **Posited continuous per-order section-proportional fibre envelope for the differentiated-curvature
contraction.** For a closed smooth Riemannian manifold `(M, g)` and smooth global tangent fields
`X, Y`, and at every differentiation order `p`, there is a *continuous* nonnegative envelope
`Cp : M → ℝ` such that, for every covariant rank `r`, every smooth compactly-supported `(0, r)`-tensor
section `W`, and every point `x`, the order-`p` differentiated-curvature contraction
`(∇^p R)(X, Y) W = diffCurvOp p r W` has intrinsic squared fibre norm at most `Cp x` times that of
`W`:

```
rfns(diffCurvOp p r W)(x) ≤ Cp x · rfns(W)(x).
```

**Why this is TRUE.** Each `diffCurvOp p` is a smooth *fixed* fibrewise-`ℝ`-linear operator on tensor
sections (a recursive covariant-Leibniz remainder of the smooth Riemann curvature contraction
`R(X, Y)·`), assembled from the smooth metric `g`, the smooth Levi-Civita curvature and its smooth
covariant derivatives, and the smooth frame fields `X, Y`. Its fibre-operator norm — the least `c`
with `rfns(diffCurvOp p r W)(x) ≤ c · rfns(W)(x)` for all `W` at `x` — is *continuous* in `x` because
the constituent chart Christoffel / Riemann coordinate data and their iterated partials are `C^∞` and
uniformly bounded on the compact chart partition-of-unity supports
(`exists_chartRiemannData_uniform_bound_compact`), controlled through the forward chart-frame Gram
Rayleigh route on the positive-definite chart Gram matrix. The order-`0` case `Cp = `
`Ccurv x · g(X x, X x) · g(Y x, Y x)` is exactly the existing continuous curvature-operator envelope
`exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional` (continuous, with
`g(X x, X x)`, `g(Y x, Y x)` continuous by smoothness). This is the same continuity-of-the-iterated-
curvature-operator-norm analytic primitive that the existing order-`0` curvature envelope
`exists_continuous_riemannOp_tensorCovS_frameEnergy_bound` is itself discharged by, here lifted to
every differentiation order `p`; it is the genuinely-irreducible analytic content posited as the
precise primitive (the chart-locality-free route — no `HasLocallyConstantChartAt`, no
chart-trivialisation operator-norm scalar).

**Non-vacuity.** A degenerate witness `Cp ≡ 0` is rejected on any non-flat manifold: at `p = 0`, at a
point `x` and a section `W` with `R(X, Y) W ≠ 0`, one has `rfns(diffCurvOp 0 r W)(x) > 0` while
`0 · rfns(W)(x) = 0`, contradicting the bound. So the envelope must carry the genuine curvature
magnitude; it genuinely *uses* `W` (the operator is applied to `W`), so it is not a vacuous
predicate. -/
theorem exists_continuous_proportional_diffCurvOp (p : ℕ) :
    ∃ Cp : M → ℝ, Continuous Cp ∧ (∀ x, 0 ≤ Cp x) ∧
      ∀ (r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x
            ((diffCurvOp (I := I) (M := M) g hX hY p r W).toSection x) ≤
          Cp x * riemannianFiberNormSq (I := I) (M := M) g 0 r x (W.toSection x) := by
  sorry

set_option linter.unusedSectionVars false in
/-- **Per-order section-proportional fibre bound for the differentiated-curvature contraction,
uniform over the compact manifold.** Derived from the posited continuous envelope
`exists_continuous_proportional_diffCurvOp` by supremising over the compact `M`: the uniform
coefficient `kappa p` is the supremum of the continuous envelope `Cp` (a continuous real function on
a compact space has bounded range, `IsCompact.bddAbove_image`), so for every differentiation order
`p`, covariant rank `r`, section `W` and point `x`,

```
rfns(diffCurvOp p r W)(x) ≤ kappa p · rfns(W)(x).
```

This is the base-point-uniform coefficient family the binomial covariant-Leibniz grid consumes; it
depends on `sorryAx` only through the continuous-envelope primitive. -/
theorem exists_proportional_diffCurvOp :
    ∃ kappa : ℕ → ℝ, (∀ p, 0 ≤ kappa p) ∧
      ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x
            ((diffCurvOp (I := I) (M := M) g hX hY p r W).toSection x) ≤
          kappa p * riemannianFiberNormSq (I := I) (M := M) g 0 r x (W.toSection x) := by
  classical
  choose Cp hCp_cont hCp_nn hCp_bound using
    fun p => exists_continuous_proportional_diffCurvOp (I := I) (M := M) g hX hY p
  refine ⟨fun p => sSup (Set.range (Cp p)), fun p => ?_, fun p r W x => ?_⟩
  · -- The supremum of a nonnegative continuous function on the compact `M` is nonnegative.
    have hbdd : BddAbove (Set.range (Cp p)) := (isCompact_range (hCp_cont p)).bddAbove
    rcases isEmpty_or_nonempty M with hM | hM
    · simp [Set.range_eq_empty (f := Cp p)]
    · obtain ⟨x₀⟩ := hM
      exact le_trans (hCp_nn p x₀) (le_csSup hbdd ⟨x₀, rfl⟩)
  · have hbdd : BddAbove (Set.range (Cp p)) := (isCompact_range (hCp_cont p)).bddAbove
    have hCp_le : Cp p x ≤ sSup (Set.range (Cp p)) := le_csSup hbdd ⟨x, rfl⟩
    refine (hCp_bound p r W x).trans ?_
    exact mul_le_mul_of_nonneg_right hCp_le
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 r x _)

/-- Extending the range of a nonnegative-tailed real sum by one only increases it:
`∑_{i<n} f i ≤ ∑_{i<n+1} f i` when `0 ≤ f n`. -/
private lemma sum_range_le_succ_of_nonneg (n : ℕ) (f : ℕ → ℝ) (hf : 0 ≤ f n) :
    ∑ i ∈ Finset.range n, f i ≤ ∑ i ∈ Finset.range (n + 1), f i := by
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right hf

/-- A one-step index shift of a real sum is dominated by the range-extended undiffed sum:
`∑_{i<n} f (i + 1) ≤ ∑_{i<n+1} f i` when every `f` value on `range (n + 1)` is nonnegative. -/
private lemma sum_range_shift_le (n : ℕ) (f : ℕ → ℝ)
    (hf : ∀ i ∈ Finset.range (n + 1), 0 ≤ f i) :
    ∑ i ∈ Finset.range n, f (i + 1) ≤ ∑ i ∈ Finset.range (n + 1), f i := by
  rw [Finset.sum_range_succ' f n]
  exact le_add_of_nonneg_right (hf 0 (Finset.mem_range.2 (Nat.succ_pos n)))

section GridInduction

variable {kappa : ℕ → ℝ} (hkappa_nn : ∀ p, 0 ≤ kappa p)
  (hkappa : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
    riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x
        ((diffCurvOp (I := I) (M := M) g hX hY p r W).toSection x) ≤
      kappa p * riemannianFiberNormSq (I := I) (M := M) g 0 r x (W.toSection x))

include hkappa_nn hkappa in
set_option linter.unusedSectionVars false in
/-- **The binomial covariant-Leibniz grid for the differentiated-curvature contraction.** Given the
section-proportional fibre bounds `hkappa` for the operators `diffCurvOp p`, the `j`-fold iterated
covariant gradient of the order-`p` differentiated-curvature contraction `diffCurvOp p r W` is
fibre-bounded, uniformly in the base point, by the `4^j`-scaled curvature-order sum
`∑_{p' ≤ j} kappa (p + p')` of the gradient-order grid `∑_{q ≤ j} rfns(∇^q W)`:

```
rfns(∇^j(diffCurvOp p r W))(x) ≤ 4^j · ∑_{p' ≤ j} kappa (p + p') · ∑_{q ≤ j} rfns(∇^q W)(x).
```

Proved by induction on `j`, generalising over the differentiation order `p`, the rank `r` and the
section `W`. The base case is `hkappa` (`∇^0 = id`, single-term sums). The successor step
front-commutes the innermost gradient (`rfns_iteratedCovGrad_covGrad_comm_lg`), expands the single
covariant gradient by the exact Leibniz identity `covGrad_diffCurvOp_eq` and distributes `∇^j`
(`iteratedCovGrad_add`), bounds the resulting sum by `riemannianFiberNormSq_add_le`, recurses on the
two pieces (the higher-order remainder `diffCurvOp (p + 1)`, and the lower-order operator on `∇W`
front-commuted by `rfns_iteratedCovGrad_covGrad_comm_lg` and rank-cast by
`rfns_iteratedCovGrad_castRankCc_lg`), and dominates both by the common `range (j + 2)` grids, the two
copies combining into the `4^{j + 1}` factor. -/
theorem rfns_iteratedCovGrad_diffCurvOp_grid (j : ℕ) :
    ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 ((r + p) + j) x
          ((iteratedCovGrad g 0 (r + p) j
            (diffCurvOp (I := I) (M := M) g hX hY p r W)).toSection x) ≤
        (4 : ℝ) ^ j * ∑ p' ∈ Finset.range (j + 1), kappa (p + p') *
          ∑ q ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  induction j with
  | zero =>
      intro p r W x
      have hrhs : (4 : ℝ) ^ 0 * ∑ p' ∈ Finset.range (0 + 1), kappa (p + p') *
            ∑ q ∈ Finset.range (0 + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
                ((iteratedCovGrad g 0 r q W).toSection x) =
          kappa p * riemannianFiberNormSq (I := I) (M := M) g 0 (r + 0) x
            ((iteratedCovGrad g 0 r 0 W).toSection x) := by
        rw [pow_zero, one_mul, Finset.sum_range_one, Finset.sum_range_one, add_zero]
      rw [iteratedCovGrad_zero, hrhs, iteratedCovGrad_zero]
      exact hkappa p r W x
  | succ j ih =>
      intro p r W x
      -- Abbreviations for the target curvature-order sum `K` and gradient-order grid `S` at j+1.
      set K : ℝ := ∑ p' ∈ Finset.range (j + 1 + 1), kappa (p + p') with hK_def
      set S : ℝ := ∑ q ∈ Finset.range (j + 1 + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
          ((iteratedCovGrad g 0 r q W).toSection x) with hS_def
      have hK_nn : 0 ≤ K := Finset.sum_nonneg fun p' _ => hkappa_nn (p + p')
      have hS_nn : 0 ≤ S := Finset.sum_nonneg fun q _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x _
      have hpow_nn : (0 : ℝ) ≤ (4 : ℝ) ^ j := by positivity
      -- Front-commute the innermost gradient and expand the single covariant gradient by Leibniz.
      rw [show riemannianFiberNormSq (I := I) (M := M) g 0 ((r + p) + (j + 1)) x
            ((iteratedCovGrad g 0 (r + p) (j + 1)
              (diffCurvOp (I := I) (M := M) g hX hY p r W)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (((r + p) + 1) + j) x
            ((iteratedCovGrad g 0 ((r + p) + 1) j
              (covGrad (I := I) (M := M) g 0 (r + p)
                (diffCurvOp (I := I) (M := M) g hX hY p r W))).toSection x) from
        (rfns_iteratedCovGrad_covGrad_comm_lg g 0 (r + p) j
          (diffCurvOp (I := I) (M := M) g hX hY p r W) x).symm]
      rw [covGrad_diffCurvOp_eq g hX hY p r W, iteratedCovGrad_add]
      refine (riemannianFiberNormSq_add_le (I := I) (M := M) g 0 (((r + p) + 1) + j) x
          ((iteratedCovGrad g 0 ((r + p) + 1) j
            (diffCurvOp (I := I) (M := M) g hX hY (p + 1) r W)).toSection x)
          ((iteratedCovGrad g 0 ((r + p) + 1) j
            (castRankCc_lg g 0 (by omega : (r + 1) + p = r + (p + 1))
              (diffCurvOp (I := I) (M := M) g hX hY p (r + 1)
                (covGrad (I := I) (M := M) g 0 r W)))).toSection x)).trans ?_
      -- Abbreviate the curvature-order sums (`kA`, `kB`) and gradient grids (`sA`, `sB`) of the two
      -- pieces, each dominated by the target `K` resp. `S`.
      set kA : ℝ := ∑ p' ∈ Finset.range (j + 1), kappa ((p + 1) + p') with hkA_def
      set kB : ℝ := ∑ p' ∈ Finset.range (j + 1), kappa (p + p') with hkB_def
      set sA : ℝ := ∑ q ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
          ((iteratedCovGrad g 0 r q W).toSection x) with hsA_def
      set sB : ℝ := ∑ q ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + (q + 1)) x
          ((iteratedCovGrad g 0 r (q + 1) W).toSection x) with hsB_def
      -- The induction hypothesis on the two pieces, factored to `4^j · (k · s)`.
      have hA : riemannianFiberNormSq (I := I) (M := M) g 0 ((r + (p + 1)) + j) x
            ((iteratedCovGrad g 0 (r + (p + 1)) j
              (diffCurvOp (I := I) (M := M) g hX hY (p + 1) r W)).toSection x) ≤
          (4 : ℝ) ^ j * (kA * sA) := by
        refine (ih (p + 1) r W x).trans_eq ?_
        rw [hkA_def, hsA_def, Finset.sum_mul]
      have hB0 := ih p (r + 1) (covGrad (I := I) (M := M) g 0 r W) x
      -- Shift the second piece's `q`-grid `∇^q(∇W) = ∇^{q+1}W`.
      have hBshift : ∑ p' ∈ Finset.range (j + 1), kappa (p + p') *
            ∑ q ∈ Finset.range (j + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((r + 1) + q) x
                ((iteratedCovGrad g 0 (r + 1) q (covGrad (I := I) (M := M) g 0 r W)).toSection x) =
          kB * sB := by
        rw [hkB_def, hsB_def, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p' _ => ?_
        congr 1
        exact Finset.sum_congr rfl fun q _ => rfns_iteratedCovGrad_covGrad_comm_lg g 0 r q W x
      have hB : riemannianFiberNormSq (I := I) (M := M) g 0 (((r + 1) + p) + j) x
            ((iteratedCovGrad g 0 ((r + 1) + p) j
              (diffCurvOp (I := I) (M := M) g hX hY p (r + 1)
                (covGrad (I := I) (M := M) g 0 r W))).toSection x) ≤
          (4 : ℝ) ^ j * (kB * sB) := by
        refine hB0.trans_eq ?_
        rw [← hBshift]
      -- The four sums are dominated by `K` resp. `S`, all nonnegative.
      have hkA_le : kA ≤ K := by
        rw [hkA_def, hK_def]
        refine (sum_range_shift_le (j + 1) (fun i => kappa (p + i))
          (fun i _ => hkappa_nn (p + i))).trans' ?_
        exact le_of_eq (Finset.sum_congr rfl fun p' _ => by congr 1; omega)
      have hkB_le : kB ≤ K := by
        rw [hkB_def, hK_def]
        exact sum_range_le_succ_of_nonneg (j + 1) (fun p' => kappa (p + p')) (hkappa_nn (p + (j + 1)))
      have hsA_le : sA ≤ S := by
        rw [hsA_def, hS_def]
        exact sum_range_le_succ_of_nonneg (j + 1) _
          (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + (j + 1)) x _)
      have hsB_le : sB ≤ S := by
        rw [hsB_def, hS_def]
        exact sum_range_shift_le (j + 1)
          (fun q => riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
            ((iteratedCovGrad g 0 r q W).toSection x))
          (fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x _)
      have hkA_nn : 0 ≤ kA := Finset.sum_nonneg fun p' _ => hkappa_nn ((p + 1) + p')
      have hkB_nn : 0 ≤ kB := Finset.sum_nonneg fun p' _ => hkappa_nn (p + p')
      have hsA_nn : 0 ≤ sA :=
        Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x _
      have hsB_nn : 0 ≤ sB :=
        Finset.sum_nonneg fun q _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + (q + 1)) x _
      -- Combine: 2·4^j·(kA·sA) + 2·4^j·(kB·sB) ≤ 4^{j+1}·(K·S).
      have hprodA : kA * sA ≤ K * S := mul_le_mul hkA_le hsA_le hsA_nn hK_nn
      have hprodB : kB * sB ≤ K * S := mul_le_mul hkB_le hsB_le hsB_nn hK_nn
      have hgoal : (2 : ℝ) * ((4 : ℝ) ^ j * (kA * sA)) +
            (2 : ℝ) * ((4 : ℝ) ^ j * (kB * sB)) ≤
          (4 : ℝ) ^ (j + 1) * (K * S) := by
        have h4 : (4 : ℝ) ^ (j + 1) = 4 * (4 : ℝ) ^ j := by rw [pow_succ]; ring
        rw [h4]
        nlinarith [hprodA, hprodB, hpow_nn,
          mul_le_mul_of_nonneg_left hprodA hpow_nn,
          mul_le_mul_of_nonneg_left hprodB hpow_nn]
      have htarget : (4 : ℝ) ^ (j + 1) * (K * S) =
          (4 : ℝ) ^ (j + 1) * ∑ p' ∈ Finset.range (j + 1 + 1), kappa (p + p') *
            ∑ q ∈ Finset.range (j + 1 + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
                ((iteratedCovGrad g 0 r q W).toSection x) := by
        rw [hK_def, hS_def, Finset.sum_mul]
      rw [htarget] at hgoal
      refine le_trans ?_ hgoal
      -- The second addend carries the rank-cast; convert it to `hB`'s uncast fibre norm.
      have hb_eq : riemannianFiberNormSq (I := I) (M := M) g 0 (((r + p) + 1) + j) x
            ((iteratedCovGrad g 0 ((r + p) + 1) j
              (castRankCc_lg g 0 (by omega : (r + 1) + p = r + (p + 1))
                (diffCurvOp (I := I) (M := M) g hX hY p (r + 1)
                  (covGrad (I := I) (M := M) g 0 r W)))).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (((r + 1) + p) + j) x
            ((iteratedCovGrad g 0 ((r + 1) + p) j
              (diffCurvOp (I := I) (M := M) g hX hY p (r + 1)
                (covGrad (I := I) (M := M) g 0 r W))).toSection x) :=
        rfns_iteratedCovGrad_castRankCc_lg g 0 (by omega : (r + 1) + p = r + (p + 1))
          (diffCurvOp (I := I) (M := M) g hX hY p (r + 1)
            (covGrad (I := I) (M := M) g 0 r W)) j x
      rw [hb_eq]
      exact add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num))
        (mul_le_mul_of_nonneg_left hB (by norm_num))

end GridInduction

set_option linter.unusedSectionVars false in
/-- **The covariant-Leibniz curvature-coefficient grid for the metric contraction.** Assembling the
posited per-order proportional bound `exists_proportional_diffCurvOp` (the curvature factor `∇^p R`
as the base-point-uniform coefficient `kappa p`) with the constructed binomial covariant-Leibniz grid
`rfns_iteratedCovGrad_diffCurvOp_grid` (specialised to differentiation order `p = 0`, where
`diffCurvOp 0 s Z = curvatureContraction g s Z hX hY = R(X, Y) Z`), the `j`-fold iterated covariant
gradient of the curvature contraction satisfies the coefficient grid

```
rfns(∇^j(R(X, Y) Z))(x) ≤ 4^j · ∑_{p < j + 1} kappa p · ∑_{q < j + 1} rfns(∇^q Z)(x),
```

with `A j := 4^j` absorbing the binomial coefficients and `kappa` the per-order curvature-coefficient
family. This is the precise conclusion the order-`m` curvature-jet induction consumes; consumers
transitively depend on `sorryAx` only through `exists_proportional_diffCurvOp`. -/
theorem exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_kappaGrid_le_of_construction
    (s : ℕ) :
    ∃ (A : ℕ → ℝ) (kappa : ℕ → ℝ), (∀ j, 0 ≤ A j) ∧ (∀ p, 0 ≤ kappa p) ∧
      ∀ (Z : SmoothCcTensor g 0 s) (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
            ((iteratedCovGrad g 0 s j (curvatureContraction (I := I) (M := M) g s Z hX hY)).toSection
              x) ≤
          A j * ∑ p ∈ Finset.range (j + 1), kappa p *
            ∑ q ∈ Finset.range (j + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + q) x
                ((iteratedCovGrad g 0 s q Z).toSection x) := by
  obtain ⟨kappa, hkappa_nn, hkappa⟩ := exists_proportional_diffCurvOp (I := I) (M := M) g hX hY
  refine ⟨fun j => (4 : ℝ) ^ j, kappa, fun j => by positivity, hkappa_nn, fun Z j x => ?_⟩
  have hgrid := rfns_iteratedCovGrad_diffCurvOp_grid (I := I) (M := M) g hX hY
    hkappa_nn hkappa j 0 s Z x
  -- `diffCurvOp 0 s Z = curvatureContraction g s Z hX hY`, and `s + 0 = s`, `0 + p' = p'`.
  rw [diffCurvOp_zero g hX hY s Z] at hgrid
  refine hgrid.trans_eq ?_
  refine congrArg (fun t => (4 : ℝ) ^ j * t) ?_
  exact Finset.sum_congr rfl fun p' _ => by rw [Nat.zero_add]

end Connection
end Integral
end DifferentialGeometry

end
