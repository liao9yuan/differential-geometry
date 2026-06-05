import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformProportionalCurvatureSup

/-! # All-order proportional fibre bound for a recursively-differentiated curvature operator

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file isolates the single genuinely-irreducible analytic primitive shared
by the two recursively-differentiated *curvature*-operator families in the library — the frame-free
pure-Riemann trace tower `pureRGenuineDiffOp`
(`Geometry/Curvature/CovGradRoughLap/FrozenFramePureRCurvatureTower`) and the metric
curvature-contraction tower `diffCurvOp` (`CurvatureContractionLeibnizGridConstruction`) — namely the
**all-order, per-rank, section-proportional fibre bound** for a recursive covariant-Leibniz-remainder
operator family whose order-`0` base is a smooth fibrewise curvature operator.

## The shared recursive shape and the one deep input

Both families are recursive covariant-Leibniz remainders of a smooth *fibrewise* curvature operator
`L₀` (the order-`0` base): writing `op p r` for the `p`-times covariantly differentiated operator at
covariant rank `r`,
```
op 0 r W   = L₀_r · W       (fibrewise in the value `W (x)`),
op (p+1) r W = ∇(op p r W) − (rank-cast) op p (r+1) (∇W),
```
so the **exact single-step covariant Leibniz** `∇(op p r W) = op (p+1) r W + (rank-cast) op p (r+1)(∇W)`
holds *by definition* (`hcovGrad_op`). The order-`0` base `L₀` is a smooth fibrewise operator built
from the metric `g` and the smooth Riemann curvature `R` alone, recorded here by the order-`0`
fibrewise-factorisation hypothesis `hbase` (`op 0 r W (x) = L₀_r x (W (x))`), which fixes the family to
the genuine curvature setting and is itself *proved* on disk for both concrete towers (at order `0` the
operator reads only the value of its section).

The genuine analytic content is the *higher-order* layer. Because `L₀` is a smooth fibrewise curvature
operator, its iterated covariant derivative `∇^{p+1} L₀` is again a smooth fibrewise operator (the
covariant-derivative–curvature-operator product Leibniz `∇(L₀·W) = (∇L₀)·W + L₀·(∇W)` makes the
recursion telescope to `op (p+1) r W = (∇^{p+1} L₀)·W`, the input section's derivatives cancelling
exactly through the rank-cast term), and the iterated curvature coefficient `∇^{p+1} L₀` is uniformly
fibre-operator-bounded on the compact `M` by `‖∇^{≤ p+1} R‖_∞`. Hence `op (p+1) r` is itself a
section-proportional fibrewise operator. This telescoping is the covariant-derivative–metric-contraction
commutation, a large independent differential-geometry construction
(`CovariantBilinearLeibniz.ParallelTensorProduct.covGrad_prod` is its abstract shell; the concrete
instance for the bundled curvature operator is presently absent from the library); it is the one
posited node here.

## What is posited vs. derived

* `exists_proportional_recCurvDiffOp_highOrder` (the single posited node) — the all-order analytic
  envelope, stated for a recursive Leibniz-remainder family whose order-`0` base is a fibrewise
  curvature operator (the `hbase` factorisation carrier). Consumers transitively depend on `sorryAx`
  through it.
* `exists_proportional_recCurvDiffOp` — the *combined* per-order family (order `0` from the supplied
  order-`0` bound, order `p ≥ 1` from the posited node), the exact shape the two concrete towers'
  envelope nodes consume; *derived* here.

Both concrete towers instantiate `exists_proportional_recCurvDiffOp` with their own order-`0`
proportional bound and order-`0` factorisation (proved on disk) and the shared `hcovGrad_op` identity,
discharging their previously posited high-order envelope to this single shared node.
-/

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

/-- **The order-`0` fibrewise-curvature-operator factorisation hypothesis.** For a recursive operator
family `op`, this records the two structural facts that fix the order-`0` base `op 0 r` to a *fibrewise*
operator — one reading only the *value* of its section (no derivative), the structural fingerprint of a
bundled curvature operator:

* `linear` — the order-`0` base is `ℝ`-linear in the section: `op 0 r (c₁ • W₁ + c₂ • W₂) =
  c₁ • op 0 r W₁ + c₂ • op 0 r W₂`;
* `local'` — the order-`0` base is *value-local*: its fibre value at `x` depends only on the section
  value `W (x)` (if two sections agree at `x`, the operator's values at `x` agree).

Together these force `op 0 r` to factor, fibrewise, through a continuous-`ℝ`-linear operator on the
fibre applied to `W (x)` — the carrier of the genuine curvature setting. Both facts are *proved* on disk
for the two concrete towers (at order `0` each reads only its section's value, linearly). This is the
honest, instance-plumbing-free fingerprint of the fibrewise curvature operator; it is what fixes the
family away from a pathological free `covGrad_op`-family (whose high-order layer can be unbounded). -/
structure IsOrderZeroCurvFactor (g : SmoothRiemannianMetric I M)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p)) : Prop where
  /-- The order-`0` base is `ℝ`-linear in the section (stated at the fibre-value level). -/
  linear : ∀ (r : ℕ) (c₁ c₂ : ℝ) (W₁ W₂ : SmoothCcTensor g 0 r) (x : M),
    (op 0 r (c₁ • W₁ + c₂ • W₂)).toSection x =
      c₁ • (op 0 r W₁).toSection x + c₂ • (op 0 r W₂).toSection x
  /-- The order-`0` base is value-local: its fibre value at `x` depends only on `W (x)`. -/
  local' : ∀ (r : ℕ) (W₁ W₂ : SmoothCcTensor g 0 r) (x : M),
    W₁.toSection x = W₂.toSection x → (op 0 r W₁).toSection x = (op 0 r W₂).toSection x

/-- **The all-order iterated-gradient grid envelope for the differentiated bundled curvature
operator** (the single posited analytic primitive of this file — the genuine conclusion of the
*library-absent* operator-field covariant Leibniz construction). For a closed smooth Riemannian
manifold `(M, g)` and a recursive covariant-Leibniz-remainder operator family `op` whose

* single-step covariant Leibniz is the exact remainder identity (`hcovGrad_op`), and whose
* order-`0` base is a fibrewise curvature operator (`hbase : IsOrderZeroCurvFactor g op`),

there is a nonnegative order × rank × gradient-order envelope `C : ℕ → ℕ → ℕ → ℝ` such that for every
differentiation order `p`, covariant rank `r`, section `W`, gradient order `j` and point `x`, the
`j`-fold iterated covariant gradient of the order-`(p + 1)` differentiated operator has intrinsic
squared fibre norm at most `C p r j` times the sum, over gradient orders `q ≤ j`, of the intrinsic
squared fibre norms of the iterated covariant gradients of `W`:
```
rfns(∇^j (op (p + 1) r W))(x) ≤ C p r j · ∑_{q < j + 1} rfns(∇^q W)(x).
```

**Why this is TRUE — the operator-field telescoping.** The `hbase` linearity + value-locality
identify the order-`0` base with a smooth *fibrewise* curvature operator field `L₀`
(`op 0 r W (x) = L₀ x (W (x))`), built from the metric `g` and the smooth Riemann curvature `R`
alone. By the exact single-step covariant Leibniz `hcovGrad_op`, the recursion telescopes: the input
section's derivative `∇W` produced by `∇(op p r W)` is cancelled exactly by the rank-cast lower-order
term `op p (r + 1)(∇W)`, so `op (p + 1) r W (x) = (∇^{p + 1} L₀) · W (x)` is the iterated covariant
derivative of `L₀` applied *fibrewise* to `W (x)` — no derivative of `W` survives at order `0`. The
`j`-fold iterated gradient `∇^j (op (p + 1) r W)` is then, by the *operator-field* covariant Leibniz
`∇(L₀ · W) = (∇L₀) · W + L₀ · (∇W)` (the parallel-product realization `ParallelTensorProduct.covGrad_prod`
for the bundled curvature operator field, `CovariantBilinearLeibniz`), the binomial covariant-Leibniz
grid `∑_{i + l = j} ∇^{p + 1 + i} L₀ · ∇^l W`
(`ParallelTensorProduct.norm_iteratedCovGrad_prod_le_jetGrid`); every iterated-curvature-coefficient
fibre norm `‖∇^{≤ p + 1 + j} L₀‖` is absorbed, uniformly over the compact `M` by `‖∇^{≤ p + 1 + j} R‖_∞`
(`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound` at each order, finite by per-order
compactness), into the constant `C p r j`, leaving the displayed single `W`-grid. The
covariant-derivative–curvature-operator-field commutation that powers the telescoping is the genuine,
*large independent differential-geometry* content presently absent from the library
(`ParallelTensorProduct.covGrad_prod` for the bundled curvature operator field); it is posited here as
the precise shared analytic primitive of the two concrete curvature towers. Consumers transitively
depend on `sorryAx` through this single node.

**Non-vacuity.** A degenerate witness `C ≡ 0` is rejected on any non-flat manifold: at `p = j = 0`,
`op 1 r W (x) = (∇L₀) · W (x)` is the differentiated bundled curvature operator, genuinely nonzero
when `∇R ≠ 0` and the fibrewise operator `L₀` (from `hbase`) carries a non-zero contraction, so
`rfns(op 1 r W)(x) > 0` while `0 · rfns(W)(x) = 0`. The envelope must carry the genuine
differentiated-curvature magnitude; it genuinely *uses* `W` (the operator is applied to `W`), so it is
not vacuous. The `hbase` hypothesis fixes the family to a genuine fibrewise curvature operator (the
node is *false* for an arbitrary `covGrad_op`-family: a pathological family satisfying only the Leibniz
remainder identity can be unbounded at high order). -/
theorem exists_proportional_recCurvDiffOp_iteratedGrid
    (g : SmoothRiemannianMetric I M)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p))
    (hcovGrad_op : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
      covGrad g 0 (r + p) (op p r W) =
        op (p + 1) r W +
          castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1)) (op p (r + 1) (covGrad g 0 r W)))
    (hbase : IsOrderZeroCurvFactor (I := I) (M := M) g op) :
    ∃ C : ℕ → ℕ → ℕ → ℝ, (∀ p r j, 0 ≤ C p r j) ∧
      ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + (p + 1) + j) x
            ((iteratedCovGrad g 0 (r + (p + 1)) j (op (p + 1) r W)).toSection x) ≤
          C p r j * ∑ q ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  sorry

/-- **The all-order section-proportional fibre envelope for a recursively-differentiated bundled
curvature operator** (the single posited analytic node of this file). For a closed smooth Riemannian
manifold `(M, g)` and a recursive covariant-Leibniz-remainder operator family `op` whose

* single-step covariant Leibniz is the exact remainder identity (`hcovGrad_op`,
  `∇(op p r W) = op (p+1) r W + (rank-cast) op p (r+1)(∇W)`), and whose
* order-`0` base is a fibrewise curvature operator (`hbase : IsOrderZeroCurvFactor g op`),

there is a nonnegative all-order, per-rank envelope `kappaHigh : ℕ → ℕ → ℝ` such that for every order
`p`, rank `r`, section `W` and point `x`,
```
rfns(op (p+1) r W)(x) ≤ kappaHigh p r · rfns(W)(x).
```

**Why this is TRUE.** By the exact single-step covariant Leibniz `hcovGrad_op`, the recursion
telescopes: the `hbase` linearity + value-locality identify the order-`0` base with a fibrewise
curvature operator `L₀` (`op 0 r W (x) = L₀ x (W (x))`), and the input section's derivative `∇W`
produced by `∇(op p r W)` is cancelled by the rank-cast lower-order term `op p (r+1)(∇W)`, so
`op (p+1) r W (x) = (∇^{p+1} L₀)·W (x)` is the iterated
covariant derivative of the smooth fibrewise curvature operator `L₀` applied *fibrewise* to `W (x)` — no
derivative of `W` survives. Because `L₀` is built from `g` and the smooth Riemann curvature `R`, the
iterated coefficient `∇^{p+1} L₀` is a smooth fibrewise operator field whose fibre-operator norm is
uniformly bounded on the compact `M` by `‖∇^{≤ p+1} R‖_∞`
(`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound` at each order, finite by per-`p`
compactness), giving the displayed section-proportional fibre bound with `kappaHigh p r` the squared
iterated-curvature-operator sup. The telescoping uses the covariant-derivative–curvature-operator
product Leibniz `∇(L₀·W) = (∇L₀)·W + L₀·(∇W)` (the covariant-derivative–metric-contraction commutation,
`ParallelTensorProduct.covGrad_prod` for the bundled curvature operator, presently absent from the
library and a large independent differential-geometry construction); it is posited here as the precise
shared analytic primitive of the two concrete curvature towers. Consumers transitively depend on
`sorryAx` through this single node.

**Non-vacuity.** A degenerate witness `kappaHigh ≡ 0` is rejected on any non-flat manifold: at `p = 0`,
`op 1 r W = ∇(L₀·W) − cast(L₀·(∇W)) = (∇L₀)·W` is the differentiated bundled curvature operator,
genuinely nonzero when `∇R ≠ 0` and the fibrewise operator `L₀` (from `hbase`) carries a non-zero
contraction, so `rfns(op 1 r W)(x) > 0` while `0 · rfns(W)(x) = 0`. The envelope must carry the genuine
differentiated-curvature magnitude; it genuinely *uses* `W` (the operator is applied to `W`), so it is
not vacuous. The `hbase` hypothesis (linearity + value-locality) fixes the family to a genuine fibrewise
curvature operator (the node is *false* for an arbitrary `covGrad_op`-family: a pathological family
satisfying only the Leibniz remainder identity can be unbounded at high order), making this a genuine,
non-vacuous statement about the iterated curvature operator rather than a free family. -/
theorem exists_proportional_recCurvDiffOp_highOrder
    (g : SmoothRiemannianMetric I M)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p))
    (hcovGrad_op : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
      covGrad g 0 (r + p) (op p r W) =
        op (p + 1) r W +
          castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1)) (op p (r + 1) (covGrad g 0 r W)))
    (hbase : IsOrderZeroCurvFactor (I := I) (M := M) g op) :
    ∃ kappaHigh : ℕ → ℕ → ℝ, (∀ p r, 0 ≤ kappaHigh p r) ∧
      ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + (p + 1)) x
            ((op (p + 1) r W).toSection x) ≤
          kappaHigh p r * riemannianFiberNormSq (I := I) (M := M) g 0 r x (W.toSection x) := by
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_proportional_recCurvDiffOp_iteratedGrid (I := I) (M := M) g op hcovGrad_op hbase
  refine ⟨fun p r => C p r 0, fun p r => hC_nn p r 0, fun p r W x => ?_⟩
  have hgrid := hC p r W 0 x
  rw [iteratedCovGrad_zero] at hgrid
  rw [Finset.sum_range_one, iteratedCovGrad_zero] at hgrid
  exact hgrid

/-- **The combined all-order section-proportional fibre envelope for a recursively-differentiated
bundled curvature operator.** Combining the supplied order-`0` proportional bound `hbase0` with the
posited high-order node `exists_proportional_recCurvDiffOp_highOrder`, there is a single nonnegative
per-order, per-rank envelope `kappa : ℕ → ℕ → ℝ` with
```
rfns(op p r W)(x) ≤ kappa p r · rfns(W)(x)
```
at every order `p`, rank `r`, section `W` and point `x`. The order-`0` layer is `hbase0` (the
fully-proven curvature-operator order-`0` bound); the order-`p ≥ 1` layer is the single posited node.
Derived here; consumers transitively depend on `sorryAx` only through the high-order node. -/
theorem exists_proportional_recCurvDiffOp
    (g : SmoothRiemannianMetric I M)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p))
    (hcovGrad_op : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
      covGrad g 0 (r + p) (op p r W) =
        op (p + 1) r W +
          castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1)) (op p (r + 1) (covGrad g 0 r W)))
    (kappa0 : ℕ → ℝ) (hkappa0_nn : ∀ r, 0 ≤ kappa0 r)
    (hbase0 : ∀ (r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 (r + 0) x ((op 0 r W).toSection x) ≤
        kappa0 r * riemannianFiberNormSq (I := I) (M := M) g 0 r x (W.toSection x))
    (hbase : IsOrderZeroCurvFactor (I := I) (M := M) g op) :
    ∃ kappa : ℕ → ℕ → ℝ, (∀ p r, 0 ≤ kappa p r) ∧
      ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x ((op p r W).toSection x) ≤
          kappa p r * riemannianFiberNormSq (I := I) (M := M) g 0 r x (W.toSection x) := by
  classical
  obtain ⟨kappaHigh, hkappaHigh_nn, hkappaHigh⟩ :=
    exists_proportional_recCurvDiffOp_highOrder (I := I) (M := M) g op hcovGrad_op hbase
  refine ⟨fun p r => match p with | 0 => kappa0 r | (p' + 1) => kappaHigh p' r,
    fun p r => ?_, fun p r W x => ?_⟩
  · cases p with
    | zero => exact hkappa0_nn r
    | succ p' => exact hkappaHigh_nn p' r
  · cases p with
    | zero =>
        rw [show (fun p r => match p with
            | 0 => kappa0 r | (p' + 1) => kappaHigh p' r) 0 r = kappa0 r from rfl]
        exact hbase0 r W x
    | succ p' =>
        rw [show (fun p r => match p with
            | 0 => kappa0 r | (p'' + 1) => kappaHigh p'' r) (p' + 1) r = kappaHigh p' r from rfl]
        exact hkappaHigh p' r W x

end Connection
end Integral
end DifferentialGeometry

end
