import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Geometry.Connection.TensorNabla.LiftedSectionCovariantRealizeBridge

/-! # The intrinsic `rfns` jet grid for a parallel two-section bilinear product

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, the file `MetricContractionLeibnizGrid` packages a *non-parallel*,
*single-section* differentiated bilinear contraction (one varying tensor section against a *fixed*
operator) as `DiffBilinOp` and proves its binomial covariant-Leibniz `rfns` grid, and
`ParallelRankReducingContractionGrid` packages a *parallel*, *rank-reducing*, *single-section*
contraction (a metric trace) as `ParallelRankReducingContraction`.  Neither handles a
**quadratic** product of **two independently varying** tensor sections.

This file supplies that engine, in the intrinsic squared-fibre-norm (`riemannianFiberNormSq`, `rfns`)
currency the covariant-Faà-di-Bruno cross arm of a *quadratic-in-difference* nonlinearity consumes: a
**parallel fibrewise bilinear product** `prod` of two sections, with the exact two-section covariant
Leibniz `∇(prod S T) = prod (∇S) T + prod S (∇T)` (cross-term-free because the bilinear map is parallel,
`∇g = 0`) and a fibrewise `g`-fibre-norm operator bound, gives the `rfns` two-product jet grid
```
rfns(∇^j (prod S T))(x) ≤ C j · (∑_{p ≤ j} rfns(∇^p S)(x)) · (∑_{q ≤ j} rfns(∇^q T)(x)).
```
The single high covariant derivative may land on **either** factor (the binomial covariant Leibniz of a
two-section product), so the right side carries the full `≤ j`-jet of *both* factors — exactly the
structure of a `connDiff ∧ connDiff` quadratic cross term, where the high derivative may land on either
connection-difference factor.

## Why a self-contained `rfns` engine (not `ParallelTensorProduct`)

`CovariantBilinearLeibniz`'s `ParallelTensorProduct` proves the same binomial grid but in the **model**
fibre norm (it does not install the `tensorRS_riemannianBundle` instance, so its `‖·‖` is the
chart-trivialisation model norm, generally `≠ √rfns`); its bound is therefore in the wrong currency for
an intrinsic `rfns` consumer.  This engine works directly in the intrinsic `rfns`, exactly like the
single-section `DiffBilinOp` grid: the binomial covariant Leibniz recursion runs through the
`2`-sub-additivity of the squared fibre norm `riemannianFiberNormSq_add_le` (the per-step factor `2`
accumulating to a `4^j` absorbed into the order-dependent constant), the exact two-section Leibniz
`covGrad_prod`, and the front-commutation `riemannianFiberNormSq_toSection_heq`.

## Main definitions

* `RfnsBilinearProduct g s₁ s₂ s₀` — a parallel fibrewise continuous-bilinear product of a
  `(0, s₁ + a)`-tensor section and a `(0, s₂ + b)`-tensor section into a `(0, s₀ + a + b)`-tensor
  section, with the exact two-section covariant Leibniz (`covGrad_prod`, cross-term-free) and the
  `g`-fibre-norm operator bound in `rfns` form (`mu`, `rfns_prod_le`).

## Main results

* `RfnsBilinearProduct.exists_rfns_iteratedCovGrad_prod_twoFactor_le` — the **`rfns` two-product
  *rectangular* jet grid** `≤ C j · (∑_{i ≤ j} rfns(∇^i S)) · (∑_{l ≤ j} rfns(∇^l T))`, with a
  nonnegative order-dependent constant uniform over the two factors and the base point.
* `RfnsBilinearProduct.exists_rfns_iteratedCovGrad_prod_diagGrid_le` — the **`rfns` two-product
  *diagonal* (convolution) jet grid** `≤ C j · ∑_{i ≤ j} rfns(∇^i S) · (∑_{l ≤ j − i} rfns(∇^l T))`,
  the strictly-smaller refinement summing only over the diagonal `i + l ≤ j` (the exact pointwise shape
  the cross-correction-difference / quadratic-Cross covariant-Faà-di-Bruno arms produce, and the input
  the integrated Gagliardo–Nirenberg two-arm engine converts to two `L²` arms — the rectangular
  independent-square grid is *not* integrable to two arms, its top corner being quartic in top jets).

A reusable covariant-calculus byproduct (R1 — its own first-class home in the covariant-gradient API),
decoupled from any specific nonlinearity. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **A parallel fibrewise continuous-bilinear product of two tensor sections** (the `rfns`-currency
two-section analogue of `DiffBilinOp` / `ParallelRankReducingContraction`).

The map sends a smooth compactly-supported `(0, s₁ + a)`-tensor section and a `(0, s₂ + b)`-tensor
section to a `(0, s₀ + a + b)`-tensor section, for every pair of extra-slot counts `a, b`.  Its two
genuine `∇`-compatibility fields:

* `covGrad_prod` — the **exact two-section covariant Leibniz** `∇(prod S T) = (rank-cast) prod (∇S) T +
  prod S (∇T)`.  The cross term vanishes precisely because the bilinear map is parallel (`∇g = 0`); the
  left summand carries covariant rank `(s₀ + (a+1)) + b`, rank-cast to `(s₀ + a + b) + 1` by
  `castRankCc_db`.
* `mu`, `mu_nonneg`, `rfns_prod_le` — the **`g`-fibre-norm operator bound** in `rfns` form
  `rfns(prod S T)(x) ≤ mu · rfns(S)(x) · rfns(T)(x)`.  This is the genuine continuity/boundedness of the
  bilinear map; in particular it forces `prod 0 T = 0` and `prod S 0 = 0`, so a degenerate nonzero
  witness is rejected.

A reusable abstraction realized by a metric contraction of a tensor product, decoupled from any
nonlinearity.  A degenerate `mu ≡ 0` witness is rejected whenever `prod S T ≠ 0` on a fibre with
positive `S`, `T` fibre norms (then `rfns(prod S T)(x) > 0` while the right side is `0`). -/
structure RfnsBilinearProduct (g : SmoothRiemannianMetric I M) (s₁ s₂ s₀ : ℕ) where
  /-- The section-level bilinear product, at every shifted gradient order `(a, b)`. -/
  prod : ∀ {a b : ℕ}, SmoothCcTensor g 0 (s₁ + a) → SmoothCcTensor g 0 (s₂ + b) →
    SmoothCcTensor g 0 (s₀ + a + b)
  /-- The exact two-section covariant Leibniz (parallel: no cross term).  The left summand is rank-cast
  from `(s₀ + (a+1)) + b` to `(s₀ + a + b) + 1`. -/
  covGrad_prod : ∀ {a b : ℕ} (S : SmoothCcTensor g 0 (s₁ + a)) (T : SmoothCcTensor g 0 (s₂ + b)),
    covGrad g 0 (s₀ + a + b) (prod S T) =
      castRankCc_db g 0 (by omega : s₀ + (a + 1) + b = s₀ + a + b + 1)
          (prod (a := a + 1) (b := b) (covGrad g 0 (s₁ + a) S) T) +
        prod (a := a) (b := b + 1) S (covGrad g 0 (s₂ + b) T)
  /-- The `g`-fibre-norm operator-bound constant of the bilinear map. -/
  mu : ℝ
  /-- The operator-bound constant is nonnegative. -/
  mu_nonneg : 0 ≤ mu
  /-- The `g`-fibre-norm operator bound, in `rfns` form. -/
  rfns_prod_le : ∀ {a b : ℕ} (S : SmoothCcTensor g 0 (s₁ + a)) (T : SmoothCcTensor g 0 (s₂ + b))
    (x : M),
    riemannianFiberNormSq (I := I) (M := M) g 0 (s₀ + a + b) x ((prod S T).toSection x) ≤
      mu * riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + a) x (S.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + b) x (T.toSection x)

namespace RfnsBilinearProduct

variable {g : SmoothRiemannianMetric I M} {s₁ s₂ s₀ : ℕ}

/-- **`rfns` rank-cast invariance.**  The `rfns` of the `j`-fold iterated covariant gradient of a
rank-cast section equals that of the section. -/
private lemma rfns_iteratedCovGrad_castRankCc {a b : ℕ} (h : a = b)
    (Y : SmoothCcTensor g 0 a) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (b + j) x
        ((iteratedCovGrad g 0 b j (castRankCc_db g 0 h Y)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 (a + j) x
        ((iteratedCovGrad g 0 a j Y).toSection x) :=
  rfns_iteratedCovGrad_castRankCc_db g 0 h Y j x

/-- **`rfns` front-commutation.**  `rfns(∇^m (∇S))(x) = rfns(∇^{m+1} S)(x)`. -/
private lemma rfns_iteratedCovGrad_covGrad_comm (s m : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + m) x
        ((iteratedCovGrad g 0 (s + 1) m (covGrad g 0 s S)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + (m + 1)) x
        ((iteratedCovGrad g 0 s (m + 1) S).toSection x) :=
  DifferentialGeometry.PDE.DeTurck.riemannianFiberNormSq_toSection_heq (I := I) (M := M) g
    (by omega : (s + 1) + m = s + (m + 1))
    (DifferentialGeometry.PDE.DeTurck.iteratedCovGrad_covGrad_comm_heq_local (I := I) (M := M) g
      s m S) x

omit [CompleteSpace E] [BoundarylessManifold I M] in
/-- Every product `rfns(∇^p S) · rfns(∇^q T)` of iterated-gradient fibre norms is nonnegative. -/
private lemma jet_rfns_summand_nonneg {a b : ℕ} (S : SmoothCcTensor g 0 (s₁ + a))
    (T : SmoothCcTensor g 0 (s₂ + b)) (x : M) (p q : ℕ) :
    0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + p) x
        ((iteratedCovGrad g 0 (s₁ + a) p S).toSection x) *
      riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + q) x
        ((iteratedCovGrad g 0 (s₂ + b) q T).toSection x) :=
  mul_nonneg (riemannianFiberNormSq_nonneg _ _ _ _ _) (riemannianFiberNormSq_nonneg _ _ _ _ _)

/-- **Left shift of the `rfns` covariant-jet grid.**  Differentiating the left factor once and grading
over the `(j+1) × (j+1)` grid is dominated by the `(j+2) × (j+2)` grid of the undifferentiated factors:
front-commutation `∇^p(∇S) ↦ ∇^{p+1}S` reindexes the `p`-axis into `{1, …, j+1} ⊆ range (j+2)`. -/
private lemma shift_left_grid_rfns_le {a b : ℕ} (S : SmoothCcTensor g 0 (s₁ + a))
    (T : SmoothCcTensor g 0 (s₂ + b)) (x : M) (j : ℕ) :
    (∑ p ∈ Finset.range (j + 1), ∑ q ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a + 1) + p) x
            ((iteratedCovGrad g 0 (s₁ + a + 1) p (covGrad g 0 (s₁ + a) S)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + q) x
            ((iteratedCovGrad g 0 (s₂ + b) q T).toSection x)) ≤
      ∑ p ∈ Finset.range (j + 2), ∑ q ∈ Finset.range (j + 2),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + p) x
            ((iteratedCovGrad g 0 (s₁ + a) p S).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + q) x
            ((iteratedCovGrad g 0 (s₂ + b) q T).toSection x) := by
  have hstep1 : (∑ p ∈ Finset.range (j + 1), ∑ q ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a + 1) + p) x
            ((iteratedCovGrad g 0 (s₁ + a + 1) p (covGrad g 0 (s₁ + a) S)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + q) x
            ((iteratedCovGrad g 0 (s₂ + b) q T).toSection x)) ≤
      ∑ p ∈ Finset.range (j + 1), ∑ q ∈ Finset.range (j + 2),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + (p + 1)) x
            ((iteratedCovGrad g 0 (s₁ + a) (p + 1) S).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + q) x
            ((iteratedCovGrad g 0 (s₂ + b) q T).toSection x) := by
    refine Finset.sum_le_sum fun p _ => ?_
    rw [show (∑ q ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a + 1) + p) x
              ((iteratedCovGrad g 0 (s₁ + a + 1) p (covGrad g 0 (s₁ + a) S)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + q) x
              ((iteratedCovGrad g 0 (s₂ + b) q T).toSection x)) =
        ∑ q ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + (p + 1)) x
              ((iteratedCovGrad g 0 (s₁ + a) (p + 1) S).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + q) x
              ((iteratedCovGrad g 0 (s₂ + b) q T).toSection x) from by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [rfns_iteratedCovGrad_covGrad_comm (g := g) (s₁ + a) p S x]]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 (by omega : j + 1 ≤ j + 2))
      fun q _ _ => jet_rfns_summand_nonneg S T x (p + 1) q
  refine hstep1.trans ?_
  rw [Finset.sum_range_succ' (n := j + 1)
    (f := fun p => ∑ q ∈ Finset.range (j + 2),
      riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + p) x
          ((iteratedCovGrad g 0 (s₁ + a) p S).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + q) x
          ((iteratedCovGrad g 0 (s₂ + b) q T).toSection x))]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun q _ => jet_rfns_summand_nonneg S T x 0 q)

/-- **Right shift of the `rfns` covariant-jet grid.** -/
private lemma shift_right_grid_rfns_le {a b : ℕ} (S : SmoothCcTensor g 0 (s₁ + a))
    (T : SmoothCcTensor g 0 (s₂ + b)) (x : M) (j : ℕ) :
    (∑ p ∈ Finset.range (j + 1), ∑ q ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + p) x
            ((iteratedCovGrad g 0 (s₁ + a) p S).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b + 1) + q) x
            ((iteratedCovGrad g 0 (s₂ + b + 1) q (covGrad g 0 (s₂ + b) T)).toSection x)) ≤
      ∑ p ∈ Finset.range (j + 2), ∑ q ∈ Finset.range (j + 2),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + p) x
            ((iteratedCovGrad g 0 (s₁ + a) p S).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + q) x
            ((iteratedCovGrad g 0 (s₂ + b) q T).toSection x) := by
  have hstep1 : (∑ p ∈ Finset.range (j + 1), ∑ q ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + p) x
            ((iteratedCovGrad g 0 (s₁ + a) p S).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b + 1) + q) x
            ((iteratedCovGrad g 0 (s₂ + b + 1) q (covGrad g 0 (s₂ + b) T)).toSection x)) ≤
      ∑ p ∈ Finset.range (j + 1), ∑ q ∈ Finset.range (j + 2),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + p) x
            ((iteratedCovGrad g 0 (s₁ + a) p S).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + q) x
            ((iteratedCovGrad g 0 (s₂ + b) q T).toSection x) := by
    refine Finset.sum_le_sum fun p _ => ?_
    rw [show (∑ q ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + p) x
              ((iteratedCovGrad g 0 (s₁ + a) p S).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b + 1) + q) x
              ((iteratedCovGrad g 0 (s₂ + b + 1) q (covGrad g 0 (s₂ + b) T)).toSection x)) =
        ∑ q ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + p) x
              ((iteratedCovGrad g 0 (s₁ + a) p S).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + (q + 1)) x
              ((iteratedCovGrad g 0 (s₂ + b) (q + 1) T).toSection x) from by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [rfns_iteratedCovGrad_covGrad_comm (g := g) (s₂ + b) q T x]]
    rw [Finset.sum_range_succ' (n := j + 1)
      (f := fun q => riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + p) x
          ((iteratedCovGrad g 0 (s₁ + a) p S).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + q) x
          ((iteratedCovGrad g 0 (s₂ + b) q T).toSection x))]
    exact le_add_of_nonneg_right (jet_rfns_summand_nonneg S T x p 0)
  refine hstep1.trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.2 (by omega : j + 1 ≤ j + 2))
    fun p _ _ => Finset.sum_nonneg fun q _ => jet_rfns_summand_nonneg S T x p q

/-- **The bilinear covariant-Leibniz `rfns` grid.**  For every gradient order `j`, the `rfns` of
`∇^j (prod S T)` is at most `mu · 4^j` times the double sum, over gradient orders `p, q ≤ j`, of the
products `rfns(∇^p S) · rfns(∇^q T)`.  The factor `4^j` absorbs the binomial coefficients and the
per-step `2`-sub-additivity factor of the exact covariant Leibniz expansion.

Proved by induction on `j`: the base case is the operator bound `rfns_prod_le`; the successor step
front-commutes the innermost gradient (`rfns_iteratedCovGrad_covGrad_comm`), expands by the exact
Leibniz `covGrad_prod`, distributes `∇^j` over the sum (`iteratedCovGrad_add`) and applies the
`2`-sub-additivity `riemannianFiberNormSq_add_le`, recurses on the two shifted-order pieces, and
dominates both shifted grids by the common `range (j + 2)` grid (`shift_left_grid_rfns_le`,
`shift_right_grid_rfns_le`); the per-step `2` and the IH `4^j` combine into `4^{j+1}`. -/
theorem rfns_iteratedCovGrad_prod_le_jetGrid (Φ : RfnsBilinearProduct g s₁ s₂ s₀) (j : ℕ) :
    ∀ {a b : ℕ} (S : SmoothCcTensor g 0 (s₁ + a)) (T : SmoothCcTensor g 0 (s₂ + b)) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 ((s₀ + a + b) + j) x
          ((iteratedCovGrad g 0 (s₀ + a + b) j (Φ.prod S T)).toSection x) ≤
        Φ.mu * (4 : ℝ) ^ j * ∑ p ∈ Finset.range (j + 1), ∑ q ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + p) x
              ((iteratedCovGrad g 0 (s₁ + a) p S).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + q) x
              ((iteratedCovGrad g 0 (s₂ + b) q T).toSection x) := by
  induction j with
  | zero =>
      intro a b S T x
      rw [iteratedCovGrad_zero]
      have hsum : (∑ p ∈ Finset.range 1, ∑ q ∈ Finset.range 1,
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + p) x
              ((iteratedCovGrad g 0 (s₁ + a) p S).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + q) x
              ((iteratedCovGrad g 0 (s₂ + b) q T).toSection x)) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + a) x (S.toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + b) x (T.toSection x) := by
        rw [Finset.sum_range_one, Finset.sum_range_one]
        simp only [Nat.add_zero, iteratedCovGrad_zero]
      rw [hsum, pow_zero, mul_one, ← mul_assoc]
      exact Φ.rfns_prod_le S T x
  | succ j ih =>
      intro a b S T x
      -- Front-commute the innermost gradient.
      rw [show riemannianFiberNormSq (I := I) (M := M) g 0 ((s₀ + a + b) + (j + 1)) x
            ((iteratedCovGrad g 0 (s₀ + a + b) (j + 1) (Φ.prod S T)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s₀ + a + b + 1) + j) x
              ((iteratedCovGrad g 0 (s₀ + a + b + 1) j
                  (covGrad g 0 (s₀ + a + b) (Φ.prod S T))).toSection x) from
        (rfns_iteratedCovGrad_covGrad_comm (g := g) (s₀ + a + b) j (Φ.prod S T) x).symm]
      -- Expand ∇(prod S T) by the exact Leibniz, distribute ∇^j, apply 2-sub-additivity.
      rw [Φ.covGrad_prod S T, iteratedCovGrad_add]
      rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
      refine (riemannianFiberNormSq_add_le (I := I) (M := M) g 0 ((s₀ + a + b + 1) + j) x _ _).trans
        ?_
      -- Recast the rank-cast left piece.
      rw [rfns_iteratedCovGrad_castRankCc (g := g)
        (by omega : s₀ + (a + 1) + b = s₀ + a + b + 1)
        (Φ.prod (a := a + 1) (b := b) (covGrad g 0 (s₁ + a) S) T) j x]
      -- IH on each shifted piece, then dominate by the common grid.
      have hL := ih (a := a + 1) (b := b) (covGrad g 0 (s₁ + a) S) T x
      have hR := ih (a := a) (b := b + 1) S (covGrad g 0 (s₂ + b) T) x
      have hgridL := shift_left_grid_rfns_le (g := g) (s₁ := s₁) (s₂ := s₂) S T x j
      have hgridR := shift_right_grid_rfns_le (g := g) (s₁ := s₁) (s₂ := s₂) S T x j
      have hmuNN : 0 ≤ Φ.mu := Φ.mu_nonneg
      have hpowNN : (0 : ℝ) ≤ (4 : ℝ) ^ j := by positivity
      set G : ℝ := ∑ p ∈ Finset.range (j + 2), ∑ q ∈ Finset.range (j + 2),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + p) x
            ((iteratedCovGrad g 0 (s₁ + a) p S).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + q) x
            ((iteratedCovGrad g 0 (s₂ + b) q T).toSection x) with hG_def
      have hcoeffNN : 0 ≤ Φ.mu * (4 : ℝ) ^ j := mul_nonneg hmuNN hpowNN
      calc
        2 * riemannianFiberNormSq (I := I) (M := M) g 0 ((s₀ + (a + 1) + b) + j) x
              ((iteratedCovGrad g 0 (s₀ + (a + 1) + b) j
                  (Φ.prod (covGrad g 0 (s₁ + a) S) T)).toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g 0 ((s₀ + a + (b + 1)) + j) x
                ((iteratedCovGrad g 0 (s₀ + a + (b + 1)) j
                    (Φ.prod S (covGrad g 0 (s₂ + b) T))).toSection x)
            ≤ 2 * (Φ.mu * (4 : ℝ) ^ j * G) + 2 * (Φ.mu * (4 : ℝ) ^ j * G) := by
          refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by norm_num))
            (mul_le_mul_of_nonneg_left ?_ (by norm_num))
          · exact hL.trans (by rw [hG_def]; exact mul_le_mul_of_nonneg_left hgridL hcoeffNN)
          · exact hR.trans (by rw [hG_def]; exact mul_le_mul_of_nonneg_left hgridR hcoeffNN)
        _ = Φ.mu * (4 : ℝ) ^ (j + 1) * ∑ p ∈ Finset.range (j + 1 + 1),
              ∑ q ∈ Finset.range (j + 1 + 1),
                riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + p) x
                    ((iteratedCovGrad g 0 (s₁ + a) p S).toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + q) x
                    ((iteratedCovGrad g 0 (s₂ + b) q T).toSection x) := by
          rw [hG_def, pow_succ]; ring

/-- **The `rfns` two-product covariant-jet grid for a parallel bilinear product.**

For a parallel fibrewise bilinear product `Φ : RfnsBilinearProduct g s₁ s₂ s₀`, every gradient order
`j`, and the two undifferentiated factor sections `S`, `T`, there is a nonnegative order-dependent
constant `C : ℕ → ℝ`, **uniform** over `S`, `T`, and the base point `x`, with
```
rfns(∇^j (prod S T))(x) ≤ C j · (∑_{p ≤ j} rfns(∇^p S)(x)) · (∑_{q ≤ j} rfns(∇^q T)(x)).
```

The single high covariant derivative may land on **either** factor, so the right side carries the full
`≤ j`-jet of *both* factors — the structure the intrinsic Moser-tame two-product consumes for a
quadratic-in-difference cross term.

**Proof.**  The double-sum grid `rfns_iteratedCovGrad_prod_le_jetGrid` gives
`rfns(∇^j(prod S T)) ≤ mu·4^j·∑_p ∑_q rfns(∇^p S)·rfns(∇^q T)`, and the double sum factors as
`∑_p ∑_q rfns(∇^p S)·rfns(∇^q T) = (∑_p rfns(∇^p S))·(∑_q rfns(∇^q T))` (`Finset.sum_mul_sum`), giving
the claim with `C j := mu·4^j`.

**Non-vacuity.**  Carries both `≤ j`-jet sums; a degenerate `C ≡ 0` is rejected whenever `prod S T ≠ 0`
on a fibre with positive factor jet sums. -/
theorem exists_rfns_iteratedCovGrad_prod_twoFactor_le (Φ : RfnsBilinearProduct g s₁ s₂ s₀)
    (S : SmoothCcTensor g 0 s₁) (T : SmoothCcTensor g 0 s₂) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀ (x : M) (j : ℕ),
      riemannianFiberNormSq (I := I) (M := M) g 0 (s₀ + j) x
          ((iteratedCovGrad g 0 s₀ j (Φ.prod (a := 0) (b := 0) S T)).toSection x) ≤
        C j *
          (∑ p ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + p) x
              ((iteratedCovGrad g 0 s₁ p S).toSection x)) *
          (∑ q ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + q) x
              ((iteratedCovGrad g 0 s₂ q T).toSection x)) := by
  classical
  refine ⟨fun j => Φ.mu * (4 : ℝ) ^ j, fun j => mul_nonneg Φ.mu_nonneg (by positivity), fun x j => ?_⟩
  -- The double-sum grid at `(a, b) = (0, 0)` (the `+ 0` shifts normalised away).
  have hgrid := Φ.rfns_iteratedCovGrad_prod_le_jetGrid j (a := 0) (b := 0) S T x
  simp only [Nat.add_zero] at hgrid
  -- Factor the double sum into the product of two one-factor sums.
  have hfactor : (∑ p ∈ Finset.range (j + 1), ∑ q ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + p) x
            ((iteratedCovGrad g 0 s₁ p S).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + q) x
            ((iteratedCovGrad g 0 s₂ q T).toSection x)) =
      (∑ p ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + p) x
            ((iteratedCovGrad g 0 s₁ p S).toSection x)) *
        (∑ q ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + q) x
            ((iteratedCovGrad g 0 s₂ q T).toSection x)) := by
    rw [Finset.sum_mul_sum]
  rw [hfactor] at hgrid
  rw [mul_assoc]
  exact hgrid

/-- **Left shift of the `rfns` covariant-jet *diagonal* grid.**  Differentiating the left factor once
and grading over the diagonal window `{i + l ≤ j}` is dominated by the diagonal window `{i + l ≤ j+1}`
of the undifferentiated factors: front-commutation `∇^i(∇S) ↦ ∇^{i+1}S` reindexes the left-factor axis
`i ↦ i + 1`, carrying the `i`-row (inner window `range (j+1-i)`) onto the `(i+1)`-row of the larger
diagonal (inner window `range (j+2-(i+1)) = range (j+1-i)`, the *same* inner window), so the shifted
diagonal sits inside the `{i + l ≤ j+1}` diagonal as the rows `i' ∈ {1, …, j+1}` (the `i' = 0` row
omitted, all summands nonnegative). -/
private lemma shift_left_diagGrid_rfns_le {a b : ℕ} (S : SmoothCcTensor g 0 (s₁ + a))
    (T : SmoothCcTensor g 0 (s₂ + b)) (x : M) (j : ℕ) :
    (∑ i ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a + 1) + i) x
            ((iteratedCovGrad g 0 (s₁ + a + 1) i (covGrad g 0 (s₁ + a) S)).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + l) x
              ((iteratedCovGrad g 0 (s₂ + b) l T).toSection x)) ≤
      ∑ i ∈ Finset.range (j + 2),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + i) x
            ((iteratedCovGrad g 0 (s₁ + a) i S).toSection x) *
          ∑ l ∈ Finset.range (j + 2 - i),
            riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + l) x
              ((iteratedCovGrad g 0 (s₂ + b) l T).toSection x) := by
  -- Front-commute the left factor `∇^i(∇S) ↦ ∇^{i+1}S` row-by-row (the inner `l`-window is untouched).
  have hstep1 : (∑ i ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a + 1) + i) x
            ((iteratedCovGrad g 0 (s₁ + a + 1) i (covGrad g 0 (s₁ + a) S)).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + l) x
              ((iteratedCovGrad g 0 (s₂ + b) l T).toSection x)) =
      ∑ i ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + (i + 1)) x
            ((iteratedCovGrad g 0 (s₁ + a) (i + 1) S).toSection x) *
          ∑ l ∈ Finset.range (j + 2 - (i + 1)),
            riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + l) x
              ((iteratedCovGrad g 0 (s₂ + b) l T).toSection x) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rfns_iteratedCovGrad_covGrad_comm (g := g) (s₁ + a) i S x]
    congr 1
    rw [show j + 2 - (i + 1) = j + 1 - i from by omega]
  rw [hstep1]
  -- Reindex the outer axis `i ↦ i + 1`: the shifted sum is the `{1, …, j+1}` rows of the target.
  rw [Finset.sum_range_succ' (n := j + 1)
    (f := fun i => riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + i) x
        ((iteratedCovGrad g 0 (s₁ + a) i S).toSection x) *
      ∑ l ∈ Finset.range (j + 2 - i),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + l) x
          ((iteratedCovGrad g 0 (s₂ + b) l T).toSection x))]
  exact le_add_of_nonneg_right
    (mul_nonneg (riemannianFiberNormSq_nonneg _ _ _ _ _)
      (Finset.sum_nonneg fun l _ => riemannianFiberNormSq_nonneg _ _ _ _ _))

/-- **Right shift of the `rfns` covariant-jet *diagonal* grid.**  Differentiating the right factor once
and grading over the diagonal window `{i + l ≤ j}` is dominated by the diagonal window `{i + l ≤ j+1}`
of the undifferentiated factors: front-commutation `∇^l(∇T) ↦ ∇^{l+1}T` reindexes the inner
right-factor axis `l ↦ l + 1` within each `i`-row, carrying the inner window `range (j+1-i)` onto
`{1, …, j+1-i} ⊆ range (j+2-i)` (the inner window of the larger diagonal's `i`-row, the `l = 0` term
omitted), and the outer `i`-axis `range (j+1) ⊆ range (j+2)` widens (all summands nonnegative). -/
private lemma shift_right_diagGrid_rfns_le {a b : ℕ} (S : SmoothCcTensor g 0 (s₁ + a))
    (T : SmoothCcTensor g 0 (s₂ + b)) (x : M) (j : ℕ) :
    (∑ i ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + i) x
            ((iteratedCovGrad g 0 (s₁ + a) i S).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b + 1) + l) x
              ((iteratedCovGrad g 0 (s₂ + b + 1) l (covGrad g 0 (s₂ + b) T)).toSection x)) ≤
      ∑ i ∈ Finset.range (j + 2),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + i) x
            ((iteratedCovGrad g 0 (s₁ + a) i S).toSection x) *
          ∑ l ∈ Finset.range (j + 2 - i),
            riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + l) x
              ((iteratedCovGrad g 0 (s₂ + b) l T).toSection x) := by
  -- For each row `i`, front-commute the right factor `∇^l(∇T) ↦ ∇^{l+1}T` and reindex `l ↦ l + 1`.
  have hstep1 : (∑ i ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + i) x
            ((iteratedCovGrad g 0 (s₁ + a) i S).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b + 1) + l) x
              ((iteratedCovGrad g 0 (s₂ + b + 1) l (covGrad g 0 (s₂ + b) T)).toSection x)) ≤
      ∑ i ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + i) x
            ((iteratedCovGrad g 0 (s₁ + a) i S).toSection x) *
          ∑ l ∈ Finset.range (j + 2 - i),
            riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + l) x
              ((iteratedCovGrad g 0 (s₂ + b) l T).toSection x) := by
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_range] at hi
    refine mul_le_mul_of_nonneg_left ?_ (riemannianFiberNormSq_nonneg _ _ _ _ _)
    rw [show (∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b + 1) + l) x
            ((iteratedCovGrad g 0 (s₂ + b + 1) l (covGrad g 0 (s₂ + b) T)).toSection x)) =
        ∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + (l + 1)) x
            ((iteratedCovGrad g 0 (s₂ + b) (l + 1) T).toSection x) from by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [rfns_iteratedCovGrad_covGrad_comm (g := g) (s₂ + b) l T x]]
    -- The target inner window `range (j+2-i)` is `range ((j+1-i)+1)` (since `i ≤ j`); peel `l = 0`.
    rw [show j + 2 - i = (j + 1 - i) + 1 from by omega]
    rw [Finset.sum_range_succ' (n := j + 1 - i)
      (f := fun l => riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + l) x
        ((iteratedCovGrad g 0 (s₂ + b) l T).toSection x))]
    exact le_add_of_nonneg_right (riemannianFiberNormSq_nonneg _ _ _ _ _)
  refine hstep1.trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.2 (by omega : j + 1 ≤ j + 2))
    fun i _ _ => mul_nonneg (riemannianFiberNormSq_nonneg _ _ _ _ _)
      (Finset.sum_nonneg fun l _ => riemannianFiberNormSq_nonneg _ _ _ _ _)

/-- **The bilinear covariant-Leibniz `rfns` *diagonal* grid.**  For every gradient order `j`, the
`rfns` of `∇^j (prod S T)` is at most `mu · 4^j` times the **diagonal** (convolution) double sum, over
gradient-order pairs `i + l ≤ j`, of the products `rfns(∇^i S) · rfns(∇^l T)`:
```
rfns(∇^j (prod S T))(x) ≤ mu·4^j · ∑_{i ≤ j} rfns(∇^i S)(x) · (∑_{l ≤ j − i} rfns(∇^l T)(x)).
```
This is the **strictly-smaller** (diagonal) refinement of the rectangular grid
`rfns_iteratedCovGrad_prod_le_jetGrid` (`∑_{i ≤ j} ∑_{l ≤ j}`): the exact covariant Leibniz of a
two-section product distributes the `j` derivatives among the two factors (`i` on one, `≤ j − i` on the
other), so each Leibniz leaf lands on the diagonal `i + l ≤ j`, never in the off-diagonal corner
`i = l = j`.  The diagonal is the shape the integrated Gagliardo–Nirenberg two-arm engine
(`exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le`) consumes — the rectangular
independent-square grid is *not* integrable to two `L²` arms (its top corner is quartic in top jets).

Proved by induction on `j` exactly as the rectangular grid: the base case is the operator bound
`rfns_prod_le`; the successor step front-commutes the innermost gradient
(`rfns_iteratedCovGrad_covGrad_comm`), expands by the exact Leibniz `covGrad_prod`, distributes `∇^j`
(`iteratedCovGrad_add`) and applies the `2`-sub-additivity `riemannianFiberNormSq_add_le`, recurses on
the two shifted-order pieces, and dominates both shifted **diagonals** by the common `{i + l ≤ j+1}`
diagonal (`shift_left_diagGrid_rfns_le`, `shift_right_diagGrid_rfns_le` — the diagonal window is
preserved under both the left axis-shift `i ↦ i+1` and the right inner-shift `l ↦ l+1`); the per-step
`2` and the IH `4^j` combine into `4^{j+1}`. -/
theorem rfns_iteratedCovGrad_prod_le_diagGrid (Φ : RfnsBilinearProduct g s₁ s₂ s₀) (j : ℕ) :
    ∀ {a b : ℕ} (S : SmoothCcTensor g 0 (s₁ + a)) (T : SmoothCcTensor g 0 (s₂ + b)) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 ((s₀ + a + b) + j) x
          ((iteratedCovGrad g 0 (s₀ + a + b) j (Φ.prod S T)).toSection x) ≤
        Φ.mu * (4 : ℝ) ^ j * ∑ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + i) x
              ((iteratedCovGrad g 0 (s₁ + a) i S).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + l) x
                ((iteratedCovGrad g 0 (s₂ + b) l T).toSection x) := by
  induction j with
  | zero =>
      intro a b S T x
      rw [iteratedCovGrad_zero]
      have hsum : (∑ i ∈ Finset.range 1,
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + i) x
              ((iteratedCovGrad g 0 (s₁ + a) i S).toSection x) *
            ∑ l ∈ Finset.range (1 - i),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + l) x
                ((iteratedCovGrad g 0 (s₂ + b) l T).toSection x)) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + a) x (S.toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + b) x (T.toSection x) := by
        rw [Finset.sum_range_one, Nat.sub_zero, Finset.sum_range_one]
        simp only [Nat.add_zero, iteratedCovGrad_zero]
      rw [hsum, pow_zero, mul_one, ← mul_assoc]
      exact Φ.rfns_prod_le S T x
  | succ j ih =>
      intro a b S T x
      -- Front-commute the innermost gradient.
      rw [show riemannianFiberNormSq (I := I) (M := M) g 0 ((s₀ + a + b) + (j + 1)) x
            ((iteratedCovGrad g 0 (s₀ + a + b) (j + 1) (Φ.prod S T)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s₀ + a + b + 1) + j) x
              ((iteratedCovGrad g 0 (s₀ + a + b + 1) j
                  (covGrad g 0 (s₀ + a + b) (Φ.prod S T))).toSection x) from
        (rfns_iteratedCovGrad_covGrad_comm (g := g) (s₀ + a + b) j (Φ.prod S T) x).symm]
      -- Expand ∇(prod S T) by the exact Leibniz, distribute ∇^j, apply 2-sub-additivity.
      rw [Φ.covGrad_prod S T, iteratedCovGrad_add]
      rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
      refine (riemannianFiberNormSq_add_le (I := I) (M := M) g 0 ((s₀ + a + b + 1) + j) x _ _).trans
        ?_
      -- Recast the rank-cast left piece.
      rw [rfns_iteratedCovGrad_castRankCc (g := g)
        (by omega : s₀ + (a + 1) + b = s₀ + a + b + 1)
        (Φ.prod (a := a + 1) (b := b) (covGrad g 0 (s₁ + a) S) T) j x]
      -- IH on each shifted piece, then dominate by the common diagonal.
      have hL := ih (a := a + 1) (b := b) (covGrad g 0 (s₁ + a) S) T x
      have hR := ih (a := a) (b := b + 1) S (covGrad g 0 (s₂ + b) T) x
      have hgridL := shift_left_diagGrid_rfns_le (g := g) (s₁ := s₁) (s₂ := s₂) S T x j
      have hgridR := shift_right_diagGrid_rfns_le (g := g) (s₁ := s₁) (s₂ := s₂) S T x j
      have hmuNN : 0 ≤ Φ.mu := Φ.mu_nonneg
      have hpowNN : (0 : ℝ) ≤ (4 : ℝ) ^ j := by positivity
      set G : ℝ := ∑ i ∈ Finset.range (j + 2),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + i) x
            ((iteratedCovGrad g 0 (s₁ + a) i S).toSection x) *
          ∑ l ∈ Finset.range (j + 2 - i),
            riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + l) x
              ((iteratedCovGrad g 0 (s₂ + b) l T).toSection x) with hG_def
      have hcoeffNN : 0 ≤ Φ.mu * (4 : ℝ) ^ j := mul_nonneg hmuNN hpowNN
      calc
        2 * riemannianFiberNormSq (I := I) (M := M) g 0 ((s₀ + (a + 1) + b) + j) x
              ((iteratedCovGrad g 0 (s₀ + (a + 1) + b) j
                  (Φ.prod (covGrad g 0 (s₁ + a) S) T)).toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g 0 ((s₀ + a + (b + 1)) + j) x
                ((iteratedCovGrad g 0 (s₀ + a + (b + 1)) j
                    (Φ.prod S (covGrad g 0 (s₂ + b) T))).toSection x)
            ≤ 2 * (Φ.mu * (4 : ℝ) ^ j * G) + 2 * (Φ.mu * (4 : ℝ) ^ j * G) := by
          refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by norm_num))
            (mul_le_mul_of_nonneg_left ?_ (by norm_num))
          · exact hL.trans (by rw [hG_def]; exact mul_le_mul_of_nonneg_left hgridL hcoeffNN)
          · exact hR.trans (by rw [hG_def]; exact mul_le_mul_of_nonneg_left hgridR hcoeffNN)
        _ = Φ.mu * (4 : ℝ) ^ (j + 1) * ∑ i ∈ Finset.range (j + 1 + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((s₁ + a) + i) x
                  ((iteratedCovGrad g 0 (s₁ + a) i S).toSection x) *
                ∑ l ∈ Finset.range (j + 1 + 1 - i),
                  riemannianFiberNormSq (I := I) (M := M) g 0 ((s₂ + b) + l) x
                    ((iteratedCovGrad g 0 (s₂ + b) l T).toSection x) := by
          rw [hG_def, pow_succ]; ring

/-- **The `rfns` two-product covariant-jet *diagonal* grid for a parallel bilinear product.**

For a parallel fibrewise bilinear product `Φ : RfnsBilinearProduct g s₁ s₂ s₀`, every gradient order
`j`, and the two undifferentiated factor sections `S`, `T`, there is a nonnegative order-dependent
constant `C : ℕ → ℝ`, **uniform** over `S`, `T`, and the base point `x`, with the **diagonal**
(convolution) product grid
```
rfns(∇^j (prod S T))(x) ≤ C j · ∑_{i ≤ j} rfns(∇^i S)(x) · (∑_{l ≤ j − i} rfns(∇^l T)(x)).
```

This is the consumer-facing existence form of `rfns_iteratedCovGrad_prod_le_diagGrid`, with
`C j := mu · 4^j`.  It is the exact pointwise shape the cross-correction-difference and quadratic-Cross
covariant-Faà-di-Bruno arms of the segment-metric Ricci difference produce (one difference factor
against one fixed factor, the high derivative distributed on the diagonal), and the input the integrated
Gagliardo–Nirenberg two-arm engine `exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le`
converts to two `L²` arms.

**Non-vacuity.**  Carries the full diagonal `≤ j`-jet of both factors; a degenerate `C ≡ 0` is rejected
whenever `prod S T ≠ 0` on a fibre with positive factor jet sums (the `i = l = 0` diagonal corner is
present). -/
theorem exists_rfns_iteratedCovGrad_prod_diagGrid_le (Φ : RfnsBilinearProduct g s₁ s₂ s₀)
    (S : SmoothCcTensor g 0 s₁) (T : SmoothCcTensor g 0 s₂) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀ (x : M) (j : ℕ),
      riemannianFiberNormSq (I := I) (M := M) g 0 (s₀ + j) x
          ((iteratedCovGrad g 0 s₀ j (Φ.prod (a := 0) (b := 0) S T)).toSection x) ≤
        C j * ∑ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + i) x
              ((iteratedCovGrad g 0 s₁ i S).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + l) x
                ((iteratedCovGrad g 0 s₂ l T).toSection x) := by
  refine ⟨fun j => Φ.mu * (4 : ℝ) ^ j, fun j => mul_nonneg Φ.mu_nonneg (by positivity), fun x j => ?_⟩
  -- The diagonal grid at `(a, b) = (0, 0)` (the `+ 0` shifts normalised away).
  have hgrid := Φ.rfns_iteratedCovGrad_prod_le_diagGrid j (a := 0) (b := 0) S T x
  simp only [Nat.add_zero] at hgrid
  exact hgrid

end RfnsBilinearProduct

end Connection
end Integral
end DifferentialGeometry

end
