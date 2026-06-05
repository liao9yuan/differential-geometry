import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovariantBilinearLeibniz
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup

/-! # The iterated-gradient grid bound for the metric curvature contraction

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file records the **iterated covariant-gradient grid bound** for the
metric curvature contraction `R(X, Y) Z := riemannOp (tensorCov g 0 s) (X, Y) Z`
(`curvatureContraction g s Z hX hY`, a smooth compactly-supported `(0, s)`-tensor section), in the
intrinsic `riemannianFiberNormSq` form the order-`m` curvature-jet induction consumes.

## The parallel-tensor-product abstraction and the structural obstruction

The bilinear covariant-Leibniz file `CovariantBilinearLeibniz` packages a *parallel* fibrewise
continuous-bilinear bundle map as `ParallelTensorProduct g r₁ s₁ r₂ s₂ r₀ s₀`, and from its two
genuine `∇`-compatibility hypotheses — the uniform fibrewise operator bound `norm_prod_le` and the
*exact* single-step covariant Leibniz identity `covGrad_prod`
(`∇(prod S T) = prod (∇S) T + prod S (∇T)`) — derives the iterated-gradient double-grid bound
`exists_norm_iteratedCovGrad_prod_le`:
`‖∇^j(prod S T)‖ ≤ C j · ∑_{p, q ≤ j} ‖∇^p S‖ · ‖∇^q T‖`.

That abstraction is realized exactly by a contraction whose bilinear map is *parallel* (`∇Φ = 0`),
the prototypical case being a metric contraction `contract_g(S ⊗ T)` of two tensor *sections* `S, T`,
parallel because `∇g = 0`, with `covGrad_prod` then the genuine theorem *covariant differentiation
commutes with the metric contraction*.

The metric curvature contraction `R(X, Y) Z` does **not** fit `ParallelTensorProduct` as a two-section
product directly: `R(X, Y)·` is *linear in the single section* `Z` (`curvatureContraction`,
`curvatureContraction_toSection_apply`), the curvature `R` being a *fixed* operator built from the
metric and the frame fields `X, Y`, not a second differentiable `SmoothCcTensor` argument; and the
curvature is **not parallel** (`∇R ≠ 0` on a non-flat manifold), so the single-step rule reads
`∇(R(X, Y) Z) = (∇R)(X, Y) Z + R(X, Y)(∇Z)` with the *non-vanishing* differentiated-curvature cross
term `(∇R)(X, Y) Z` — which is not of the form `prod (∇S) T` for any second section `S`. Realizing
`R(X, Y) Z` as a genuine `ParallelTensorProduct` therefore requires the strictly-upstream
construction of (a) the curvature packaged as a differentiable tensor *section* `Rm`, (b) a parallel
metric-contraction bilinear product of two sections, and (c) its exact covariant Leibniz equality
`covGrad_prod` — the covariant-derivative–metric-contraction commutation, presently absent from the
library and a large independent differential-geometry construction.

## What is proved vs. posited

By the iterated covariant Leibniz of that (posited) parallel realization, together with the
base-point-uniform curvature / differentiated-curvature fibre-norm sups
`exists_uniform_riemannianFiberNormSq_riemannOp_bound` (`‖R‖_∞`),
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound` (`‖∇R‖_∞`) — which absorb every
iterated-curvature coefficient `‖∇^p R‖` into a single order-dependent constant on the compact
manifold — the genuine conclusion is the **single-sum** iterated-gradient grid bound: the `S`-factor
double sum of `exists_norm_iteratedCovGrad_prod_le` collapses, because the curvature factor is a
uniformly bounded coefficient, to a single sum over the gradient orders of the *contracted section*
`Z`. Bridged to the intrinsic fibre norm through `norm_eq_sqrt_tensorInnerPointwise` /
`riemannianFiberNormSq_eq_tensorInnerPointwise` (`riemannianFiberNormSq = ‖·‖²` for the installed
Riemannian-bundle inner product), this reads

```
rfns(∇^j(R(X, Y) Z))(x) ≤ C j · ∑_{q ≤ j} rfns(∇^q Z)(x),
```

with `C : ℕ → ℝ` nonnegative and *uniform in the base point* `x` (the curvature sups are uniform).
This rfns grid bound — the deliverable the order-`m` curvature-jet induction consumes to feed
`IsGradedCurvJet` — is **posited** here as the precise true conclusion of the (blocked) parallel
realization, `exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le`; consumers
transitively depend on `sorryAx` through it. The genuine, immediately-derivable consumer API is
**proved** on top of it: the nonnegativity of the grid constant, and the gradient-order-`0`
specialisation `riemannianFiberNormSq_curvatureContraction_le` (the `∇^0 = id` head term, the single
order-`0` fibre comparison the per-step's seed reads off).

The degenerate witness is rejected: at gradient order `j = 0` the bound reads
`rfns(R(X, Y) Z)(x) ≤ C 0 · rfns(Z)(x)`, false with `C 0 = 0` on a non-flat manifold whenever the
curvature contraction `R(X, Y) Z` is nonzero (it carries the genuine Riemann curvature of `Z`); the
grid constant must be strictly positive, so the bound is not vacuous.

## Rank genericity

`ParallelTensorProduct` and its grid bound `exists_norm_iteratedCovGrad_prod_le` are rank-generic;
the curvature contraction `curvatureContraction g s` and its uniform sups are stated at general
covariant rank `s` (contravariant rank `0`, the case the moving-frame curvature engine uses). The
grid bound below is correspondingly stated at general `s`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

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

/-- **Posited iterated-gradient grid bound for the metric curvature contraction, in intrinsic
fibre-norm form.** For a closed smooth Riemannian manifold `(M, g)`, smooth global tangent fields
`X, Y`, and at every covariant rank `s`, there is a nonnegative order-dependent constant
`C : ℕ → ℝ`, *uniform in the base point*, such that for every smooth compactly-supported
`(0, s)`-tensor section `Z`, every gradient order `j`, and every point `x`, the `j`-fold iterated
covariant gradient of the curvature contraction `R(X, Y) Z := curvatureContraction g s Z hX hY` has
intrinsic squared fibre norm at most `C j` times the sum, over gradient orders `q ≤ j`, of the
intrinsic squared fibre norms of the iterated covariant gradients of `Z`:

```
rfns(∇^j(R(X, Y) Z))(x) ≤ C j · ∑_{q < j + 1} rfns(∇^q Z)(x).
```

This is the genuine conclusion of realizing the curvature contraction as a parallel tensor product
(`ParallelTensorProduct`, blocked on the absent covariant-derivative–metric-contraction commutation
`covGrad_prod`) and applying its iterated covariant-Leibniz grid bound
`exists_norm_iteratedCovGrad_prod_le`: the `S`-factor double sum collapses to the single `Z`-sum
because every iterated-curvature coefficient `‖∇^p R‖` is absorbed, uniformly over the compact
manifold, into `C j` via the curvature / differentiated-curvature sups
`exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`; the ambient-to-intrinsic step is the
fibre-norm bridge `riemannianFiberNormSq = ‖·‖²`. It is posited as a precise true child; consumers
transitively depend on `sorryAx` through it.

The degenerate witness is rejected: at `j = 0` the bound reads `rfns(R(X, Y) Z)(x) ≤ C 0 · rfns(Z)(x)`,
false with `C 0 = 0` on a non-flat manifold when `R(X, Y) Z ≠ 0` (the contraction carries the genuine
Riemann curvature of `Z`), so the constant is genuinely positive. -/
theorem exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (Z : SmoothCcTensor g 0 s) (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
            ((iteratedCovGrad g 0 s j (curvatureContraction (I := I) (M := M) g s Z hX hY)).toSection
              x) ≤
          C j * ∑ q ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + q) x
              ((iteratedCovGrad g 0 s q Z).toSection x) := by
  sorry

/-- **The grid constant of the curvature-contraction fibre bound is nonnegative at every order.**
A direct read-off of the nonnegativity field of
`exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le`, packaged as a standalone
fact for downstream constant bookkeeping. -/
theorem curvatureContraction_grid_const_nonneg
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) (j : ℕ) :
    0 ≤ (exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le
        (I := I) (M := M) g s hX hY).choose j :=
  (exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le
    (I := I) (M := M) g s hX hY).choose_spec.1 j

/-- **Gradient-order-`0` fibre comparison for the metric curvature contraction.** Specialising the
grid bound `exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le` to gradient
order `j = 0` (where `∇^0 = id` and the order sum `∑_{q < 1}` collapses to its single `q = 0` term):
the intrinsic squared fibre norm of the curvature contraction `R(X, Y) Z` at `x` is bounded by the
nonnegative constant `C 0` times the intrinsic squared fibre norm of `Z` at `x`,

```
rfns(R(X, Y) Z)(x) ≤ C 0 · rfns(Z)(x).
```

This is the genuine order-`0` head term the curvature-jet seed reads off the grid bound; it is proved
from the grid bound by collapsing `iteratedCovGrad … 0 = id` (`iteratedCovGrad_zero`) and the
single-term range sum (`Finset.sum_range_one`). It is *false* with `C 0 = 0` on a non-flat manifold
when `R(X, Y) Z ≠ 0`, so the bound is not vacuous. -/
theorem riemannianFiberNormSq_curvatureContraction_le
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (Z : SmoothCcTensor g 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        ((curvatureContraction (I := I) (M := M) g s Z hX hY).toSection x) ≤
      (exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le
          (I := I) (M := M) g s hX hY).choose 0 *
        riemannianFiberNormSq (I := I) (M := M) g 0 s x (Z.toSection x) := by
  have hgrid :=
    (exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le
      (I := I) (M := M) g s hX hY).choose_spec.2 Z 0 x
  rw [iteratedCovGrad_zero] at hgrid
  rw [Finset.sum_range_one, iteratedCovGrad_zero] at hgrid
  exact hgrid

end Connection
end Integral
end DifferentialGeometry

end
