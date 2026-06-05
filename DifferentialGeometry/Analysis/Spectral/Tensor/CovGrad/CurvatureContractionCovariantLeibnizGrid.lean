import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureContractionLeibnizGridConstruction

/-! # The intrinsic covariant-Leibniz curvature-coefficient grid for the metric contraction

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file isolates the genuine differential-geometry content behind the
iterated covariant-gradient bound for the metric curvature contraction
`R(X, Y) Z := curvatureContraction g s Z hX hY` (a smooth compactly-supported `(0, s)`-tensor
section), in the intrinsic `riemannianFiberNormSq` form the order-`m` curvature-jet induction
consumes.

## The covariant Leibniz of a fixed-operator contraction is a curvature-coefficient grid

The bilinear covariant-Leibniz engine `CovariantBilinearLeibniz` derives, from a *parallel*
fibrewise continuous-bilinear bundle map `ParallelTensorProduct`, the iterated-gradient double-grid
`exists_norm_iteratedCovGrad_prod_le`,
`‖∇^j(prod S T)‖ ≤ C j · ∑_{p, q ≤ j} ‖∇^p S‖ · ‖∇^q T‖`.

The metric curvature contraction `R(X, Y) Z` is *not* a two-section product: `R(X, Y)·` is a *fixed*
operator built from the metric and the frame fields `X, Y`, *linear in the single section* `Z`
(`curvatureContraction_toSection_apply`), and is **not parallel** (`∇R ≠ 0` on a non-flat manifold),
so the exact single-step covariant Leibniz reads `∇(R Z) = (∇R) Z + R(∇Z)` with the *non-vanishing*
differentiated-curvature cross term `(∇R) Z`. Iterating that exact Leibniz (the binomial covariant
jet expansion) gives the curvature contraction's own double grid: a sum over the differentiation
order `p` of the curvature factor `∇^p R` and the gradient order `q` of the contracted section
`∇^q Z`,

```
rfns(∇^j(R Z))(x) ≤ A j · ∑_{p ≤ j} ‖∇^p R‖_∞ · ∑_{q ≤ j} rfns(∇^q Z)(x).
```

Here the curvature factor enters only as the *base-point-uniform* coefficient `‖∇^p R‖_∞` (the
order-`p` differentiated curvature is a smooth section of a tensor bundle on the compact `M`, hence
has a uniform fibre-norm sup — the orders `p = 0, 1` are exactly the existing curvature /
differentiated-curvature sups `exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`), while only the gradient order `q` of
the *section* `Z` survives as a fibre-norm grid. The constant `A j` absorbs the binomial coefficients
`2^j` of the exact covariant Leibniz expansion.

## What is posited vs. derived

This curvature-coefficient grid `exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_kappaGrid_le`
is **posited** here (its full proof realizes `R(X, Y) Z` as a genuine `ParallelTensorProduct`, which
requires the strictly-upstream construction of the curvature packaged as a differentiable tensor
*section* `Rm`, the parallel metric-contraction bilinear product, and the covariant-derivative–metric-contraction
commutation `covGrad_prod` — a large independent differential-geometry construction presently absent
from the library). It is the precise true conclusion of that blocked realization; consumers
transitively depend on `sorryAx` through it. Its sibling
`exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le`
(`CurvatureContractionParallelProduct`) is then *derived* from it by collapsing the curvature-order
`p`-sum: `∑_{p ≤ j} ‖∇^p R‖_∞` is a finite nonnegative constant `C' j`, which factors out of the
section grid, leaving the single-sum bound `C j · ∑_{q ≤ j} rfns(∇^q Z)(x)` with
`C j := A j · ∑_{p ≤ j} ‖∇^p R‖_∞`.

The degenerate witness is rejected: at gradient order `j = 0` the bound reads
`rfns(R(X, Y) Z)(x) ≤ A 0 · ‖R‖_∞ · rfns(Z)(x)`, false with `‖R‖_∞ = 0` (equivalently `kappa 0 = 0`)
on a non-flat manifold whenever the curvature contraction `R(X, Y) Z` is nonzero (it carries the
genuine Riemann curvature of `Z`); the curvature coefficient `kappa 0` must be strictly positive, so
the grid is not vacuous. -/

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

/-- **Posited covariant-Leibniz curvature-coefficient grid for the metric curvature contraction.**
For a closed smooth Riemannian manifold `(M, g)`, smooth global tangent fields `X, Y`, and at every
covariant rank `s`, there is a nonnegative *base-point-uniform, per-rank* curvature-coefficient family
`kappa : ℕ → ℕ → ℝ` (`kappa p r ≈ r · ‖∇^p R‖_∞`, the uniform fibre-norm sup of the order-`p`
differentiated curvature as a derivation on rank-`r` tensors) such that for every smooth
compactly-supported `(0, s)`-tensor section `Z`, every gradient order `j`, and every point `x`, the
`j`-fold iterated covariant gradient of the curvature contraction `R(X, Y) Z` has intrinsic squared
fibre norm at most `4^j` times the order × rank window sum `gridWindowSum kappa 0 s j` times the
gradient-order grid of the iterated covariant gradients of `Z`:

```
rfns(∇^j(R(X, Y) Z))(x) ≤ 4^j · gridWindowSum kappa 0 s j · ∑_{q < j + 1} rfns(∇^q Z)(x),
```

where `gridWindowSum kappa 0 s j = ∑_{p < j + 1} ∑_{r < j + 1} kappa p (s + r)` ranges the curvature
order over `[0, j]` and the rank over `[s, s + j]` the covariant-Leibniz recursion climbs.

This is the genuine conclusion of realizing the curvature contraction as a parallel tensor product
(`ParallelTensorProduct`, blocked on the absent covariant-derivative–metric-contraction commutation
`covGrad_prod`) and applying its iterated covariant-Leibniz double grid
`exists_norm_iteratedCovGrad_prod_le`: the curvature factor `∇^p R` enters only as the
base-point-uniform, per-rank coefficient `kappa p r` (its `p = 0, 1` values are the existing curvature /
differentiated-curvature sups `exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`), while only the gradient order `q` of
the section `Z` survives as a fibre-norm grid; `4^j` absorbs the binomial coefficients. The rank index
is genuine: the rank-`r` curvature derivation acts on all `r` slots, so a single rank-uniform `kappa p`
cannot bound the operator at all ranks the grid reaches. It is posited as a precise true child;
consumers transitively depend on `sorryAx` through it.

The degenerate witness is rejected: at `j = 0` the bound reads
`rfns(R(X, Y) Z)(x) ≤ kappa 0 s · rfns(Z)(x)`, false with `kappa 0 s = 0` on a non-flat manifold
when `R(X, Y) Z ≠ 0` (the contraction carries the genuine Riemann curvature of `Z`), so the curvature
coefficient `kappa 0 s` is genuinely positive. -/
theorem exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_kappaGrid_le
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ∃ kappa : ℕ → ℕ → ℝ, (∀ p r, 0 ≤ kappa p r) ∧
      ∀ (Z : SmoothCcTensor g 0 s) (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
            ((iteratedCovGrad g 0 s j (curvatureContraction (I := I) (M := M) g s Z hX hY)).toSection
              x) ≤
          (4 : ℝ) ^ j * gridWindowSum kappa 0 s j *
            ∑ q ∈ Finset.range (j + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + q) x
                ((iteratedCovGrad g 0 s q Z).toSection x) :=
  exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_kappaGrid_le_of_construction
    (I := I) (M := M) g hX hY s

end Connection
end Integral
end DifferentialGeometry

end
