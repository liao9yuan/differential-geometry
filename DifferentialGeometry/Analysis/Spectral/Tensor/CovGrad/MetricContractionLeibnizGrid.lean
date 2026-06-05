import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FiberNormSubadditivity

/-! # The abstract `rfns` covariant-Leibniz grid for a differentiated bilinear contraction

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, the curvature file `CurvatureContractionLeibnizGridConstruction` builds, for
the *specific* Riemann curvature contraction `R(X, Y)·`, the intrinsic `riemannianFiberNormSq`
(`rfns`) binomial covariant-Leibniz grid
```
rfns(∇^j(R(X, Y) Z))(x) ≤ 4^j · ∑_{p ≤ j} kappa p · ∑_{q ≤ j} rfns(∇^q Z)(x),
```
through the recursive differentiated-curvature operators `diffCurvOp p` (the exact covariant-Leibniz
remainders) and their per-order section-proportional fibre envelope `kappa p`.

This file **liberates that construction to its abstract form** (R7 — extend, do not duplicate): a
generic *fibrewise-linear, non-parallel, recursively-differentiated* bilinear contraction operator,
packaged as `DiffBilinOp`, with the *same* recursive Leibniz-remainder structure but no curvature
specifics.  The genuine constraints — the exact single-step covariant Leibniz of the family
(`covGrad_op`, the non-parallel rule `∇(D_p W) = D_{p+1} W + D_p(∇W)`) and the per-order
section-proportional fibre envelope (`rfns_op_le`) — are the structure *fields*, the genuine
mathematical inputs a working geometer supplies (exactly as `ParallelTensorProduct`'s fields are).
From them the `rfns` binomial grid is **proved outright** by the same binomial covariant-Leibniz
induction the curvature file uses, with **no posit of its own**.

This is the engine the covariant Faà-di-Bruno expansion of the second-order Ricci–DeTurck right-hand
side needs for its metric-built fields (`ricciTensor(g_t)`, the inverse-metric Neumann factor, the
`deTurckVF` Christoffel difference): each is a fibrewise-linear contraction of the metric jet against
the perturbation, non-parallel, with a bounded per-order envelope on the supercritical `H^{a+2}`
family — exactly a `DiffBilinOp`.

## Main definitions

* `DiffBilinOp g r₀ s₀` — a differentiated fibrewise-linear bilinear contraction operator family: a
  section-level operator `op p` at every differentiation order `p` and base width, satisfying the
  exact recursive covariant Leibniz (`covGrad_op`) and a per-order base-point-uniform proportional
  fibre envelope (`kappa`, `rfns_op_le`).

## Main results

* `DiffBilinOp.rfns_iteratedCovGrad_grid` — the binomial covariant-Leibniz `rfns` double grid
  `rfns(∇^j(op 0 W))(x) ≤ 4^j · ∑_{p ≤ j} kappa(p) · ∑_{q ≤ j} rfns(∇^q W)(x)`, proved by induction.
* `DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le` — its single-sum collapse
  `rfns(∇^j(op 0 W))(x) ≤ C j · ∑_{q ≤ j} rfns(∇^q W)(x)`, the shape the order-`m` jet induction and
  the intrinsic Moser-tame product consume. -/

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
/-- **Heterogeneous rank-congruence for `covGrad`.** If `h : a = b`, then `covGrad g r a Y` and
`covGrad g r b Z` are heterogeneously equal whenever `Y, Z` are. -/
private theorem covGrad_heq_congr_db (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) :
    HEq (covGrad g r a Y) (covGrad g r b Z) := by
  subst h; rw [eq_of_heq hYZ]

/-- **Heterogeneous commuting of one covariant gradient through the iterated gradient.** -/
private theorem iteratedCovGrad_covGrad_comm_heq_db (g : SmoothRiemannianMetric I M) (r s m : ℕ)
    (X : SmoothCcTensor g r s) :
    HEq (iteratedCovGrad g r (s + 1) m (covGrad g r s X))
      (iteratedCovGrad g r s (m + 1) X) := by
  induction m with
  | zero => rw [iteratedCovGrad_zero, iteratedCovGrad_succ, iteratedCovGrad_zero]; exact HEq.rfl
  | succ k ih =>
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s + 1) (j := k) (covGrad g r s X)]
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s) (j := k + 1) X]
      exact covGrad_heq_congr_db g r (by omega : (s + 1) + k = s + (k + 1)) ih

set_option linter.unusedSectionVars false in
/-- **`rfns` is invariant under a `SmoothCcTensor` rank-cast.** -/
private theorem rfns_toSection_heq_congr_db (g : SmoothRiemannianMetric I M)
    (r : ℕ) {a b : ℕ} (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b}
    (hYZ : HEq Y Z) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r a x (Y.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r b x (Z.toSection x) := by
  subst h; rw [eq_of_heq hYZ]

/-- **Front-commuting one covariant gradient through the iterated gradient (rfns form).** The
intrinsic squared fibre norm of `∇^m(∇W)` at `x` equals that of `∇^{m+1}W`. -/
private theorem rfns_iteratedCovGrad_covGrad_comm_db (g : SmoothRiemannianMetric I M)
    (r s m : ℕ) (W : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r ((s + 1) + m) x
        ((iteratedCovGrad g r (s + 1) m (covGrad g r s W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + (m + 1)) x
        ((iteratedCovGrad g r s (m + 1) W).toSection x) :=
  rfns_toSection_heq_congr_db g r (by omega : (s + 1) + m = s + (m + 1))
    (iteratedCovGrad_covGrad_comm_heq_db g r s m W) x

/-- The rank-cast of a smooth compactly-supported tensor along a `Nat` equality of covariant ranks. -/
def castRankCc_db (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ} (h : a = b)
    (W : SmoothCcTensor g r a) : SmoothCcTensor g r b :=
  h ▸ W

set_option linter.unusedSectionVars false in
/-- **The iterated-gradient `rfns` is invariant under the rank-cast `castRankCc_db`.** -/
theorem rfns_iteratedCovGrad_castRankCc_db (g : SmoothRiemannianMetric I M) (r : ℕ)
    {a b : ℕ} (h : a = b) (W : SmoothCcTensor g r a) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (b + j) x
        ((iteratedCovGrad g r b j (castRankCc_db g r h W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (a + j) x
        ((iteratedCovGrad g r a j W).toSection x) := by
  subst h; rfl

/-- Two `range`-sum bookkeeping helpers (shift / truncate), used in the grid induction. -/
private lemma sum_range_shift_le_db (n : ℕ) (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ Finset.range n, f (i + 1) ≤ ∑ i ∈ Finset.range (n + 1), f i := by
  rw [Finset.sum_range_succ' f n]
  exact le_add_of_nonneg_right (hf 0)

private lemma sum_range_le_succ_of_nonneg_db (n : ℕ) (f : ℕ → ℝ) (hlast : 0 ≤ f n) :
    ∑ i ∈ Finset.range n, f i ≤ ∑ i ∈ Finset.range (n + 1), f i := by
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right hlast

end RankCast

/-- **A differentiated fibrewise-linear bilinear contraction operator family.**

The genuine abstraction realized by a non-parallel metric contraction of the metric jet against a
varying tensor section (the structure of every nonlinear term `g⁻¹ · ∂g · ∂g`, `g⁻¹ · ∂²g`,
`R(X, Y)·` in the covariant Faà-di-Bruno expansion).  The family `op p` is the `p`-times covariantly
differentiated operator (a smooth compactly-supported `(0, r + p)`-tensor at each rank `r`,
fibrewise-`ℝ`-linear in the contracted section), with two genuine `∇`-compatibility / boundedness
fields:

* `covGrad_op` — the **exact recursive single-step covariant Leibniz** `∇(op p r W) = op (p+1) r W +
  (rank-cast) op p (r+1) (∇W)` (the operator is *not* parallel, so the differentiated-operator cross
  term `op (p+1)` survives; the right summand carries covariant rank `(r+1)+p`, rank-cast to the
  differentiated rank `(r+p)+1`).  This is the defining identity of the recursive Leibniz-remainder
  construction of the differentiated operators.
* `kappa`, `kappa_nonneg`, `rfns_op_le` — the **per-order base-point-uniform proportional fibre
  envelope** `rfns(op p r W)(x) ≤ kappa p · rfns(W)(x)`, the boundedness of the smooth fixed operator
  on the compact manifold, uniform over the contracted section.

These are genuine mathematical inputs (the consumer constructs `op` and discharges the two fields);
the structure is kept generic and decoupled from any specific nonlinearity as a reusable
covariant-calculus byproduct.  A degenerate `kappa ≡ 0` witness is rejected whenever `op 0 r W ≠ 0`
(then `rfns(op 0 r W)(x) > 0 = 0 · rfns(W)(x)`), so the envelope genuinely uses the section. -/
structure DiffBilinOp (g : SmoothRiemannianMetric I M) where
  /-- The `p`-times differentiated operator at base rank `r`, fibrewise-linear in the section. -/
  op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p)
  /-- The exact recursive single-step covariant Leibniz of the family (non-parallel). -/
  covGrad_op : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
    covGrad g 0 (r + p) (op p r W) =
      op (p + 1) r W +
        castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1)) (op p (r + 1) (covGrad g 0 r W))
  /-- The per-order proportional fibre-envelope constant. -/
  kappa : ℕ → ℝ
  /-- The envelope constant is nonnegative. -/
  kappa_nonneg : ∀ p, 0 ≤ kappa p
  /-- The per-order base-point-uniform proportional fibre bound (boundedness of the operator). -/
  rfns_op_le : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
    riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x ((op p r W).toSection x) ≤
      kappa p * riemannianFiberNormSq (I := I) (M := M) g 0 r x (W.toSection x)

namespace DiffBilinOp

variable {g : SmoothRiemannianMetric I M}

/-- **The binomial covariant-Leibniz `rfns` double grid for a differentiated bilinear contraction.**

For every gradient order `j`, every differentiation order `p`, every base rank `r`, every section
`W`, and every point `x`, the intrinsic squared fibre norm of `∇^j(op p r W)` is bounded by the
binomial grid
```
rfns(∇^j(op p r W))(x) ≤ 4^j · ∑_{p' ≤ j} kappa(p + p') · ∑_{q ≤ j} rfns(∇^q W)(x),
```
the differentiated operator entering only as the base-point-uniform coefficient `kappa(p + p')` and
only the gradient order `q` of the contracted section surviving as a fibre-norm grid; the `4^j`
absorbs the binomial coefficients of the exact covariant Leibniz expansion.

Proved by induction on `j`: the base case is the per-order envelope `rfns_op_le` (at `q = 0`); the
successor step front-commutes the innermost gradient (`rfns_iteratedCovGrad_covGrad_comm_db`), expands
the single covariant gradient by the exact recursive Leibniz `covGrad_op`, distributes `∇^j` over the
sum (`iteratedCovGrad_add`, `riemannianFiberNormSq_add_le`), recurses on the two shifted pieces, and
dominates the four resulting sums by the common `range (j + 2)` grid, the two copies combining into
the `4^{j+1}` factor.  No posit (the curvature file's `rfns_iteratedCovGrad_diffCurvOp_grid` is the
`R(X, Y)·` instance of this proof). -/
theorem rfns_iteratedCovGrad_grid (Φ : DiffBilinOp g) (j : ℕ) :
    ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 ((r + p) + j) x
          ((iteratedCovGrad g 0 (r + p) j (Φ.op p r W)).toSection x) ≤
        (4 : ℝ) ^ j * ∑ p' ∈ Finset.range (j + 1), Φ.kappa (p + p') *
          ∑ q ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  induction j with
  | zero =>
      intro p r W x
      have hrhs : (4 : ℝ) ^ 0 * ∑ p' ∈ Finset.range (0 + 1), Φ.kappa (p + p') *
            ∑ q ∈ Finset.range (0 + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
                ((iteratedCovGrad g 0 r q W).toSection x) =
          Φ.kappa p * riemannianFiberNormSq (I := I) (M := M) g 0 (r + 0) x
            ((iteratedCovGrad g 0 r 0 W).toSection x) := by
        rw [pow_zero, one_mul, Finset.sum_range_one, Finset.sum_range_one, add_zero]
      rw [iteratedCovGrad_zero, hrhs, iteratedCovGrad_zero]
      exact Φ.rfns_op_le p r W x
  | succ j ih =>
      intro p r W x
      set K : ℝ := ∑ p' ∈ Finset.range (j + 1 + 1), Φ.kappa (p + p') with hK_def
      set S : ℝ := ∑ q ∈ Finset.range (j + 1 + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
          ((iteratedCovGrad g 0 r q W).toSection x) with hS_def
      have hK_nn : 0 ≤ K := Finset.sum_nonneg fun p' _ => Φ.kappa_nonneg (p + p')
      have hS_nn : 0 ≤ S := Finset.sum_nonneg fun q _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x _
      have hpow_nn : (0 : ℝ) ≤ (4 : ℝ) ^ j := by positivity
      rw [show riemannianFiberNormSq (I := I) (M := M) g 0 ((r + p) + (j + 1)) x
            ((iteratedCovGrad g 0 (r + p) (j + 1) (Φ.op p r W)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (((r + p) + 1) + j) x
            ((iteratedCovGrad g 0 ((r + p) + 1) j
              (covGrad g 0 (r + p) (Φ.op p r W))).toSection x) from
        (rfns_iteratedCovGrad_covGrad_comm_db g 0 (r + p) j (Φ.op p r W) x).symm]
      rw [Φ.covGrad_op p r W, iteratedCovGrad_add]
      refine (riemannianFiberNormSq_add_le (I := I) (M := M) g 0 (((r + p) + 1) + j) x
          ((iteratedCovGrad g 0 ((r + p) + 1) j (Φ.op (p + 1) r W)).toSection x)
          ((iteratedCovGrad g 0 ((r + p) + 1) j
            (castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1))
              (Φ.op p (r + 1) (covGrad g 0 r W)))).toSection x)).trans ?_
      set kA : ℝ := ∑ p' ∈ Finset.range (j + 1), Φ.kappa ((p + 1) + p') with hkA_def
      set kB : ℝ := ∑ p' ∈ Finset.range (j + 1), Φ.kappa (p + p') with hkB_def
      set sA : ℝ := ∑ q ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
          ((iteratedCovGrad g 0 r q W).toSection x) with hsA_def
      set sB : ℝ := ∑ q ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + (q + 1)) x
          ((iteratedCovGrad g 0 r (q + 1) W).toSection x) with hsB_def
      have hA : riemannianFiberNormSq (I := I) (M := M) g 0 ((r + (p + 1)) + j) x
            ((iteratedCovGrad g 0 (r + (p + 1)) j (Φ.op (p + 1) r W)).toSection x) ≤
          (4 : ℝ) ^ j * (kA * sA) := by
        refine (ih (p + 1) r W x).trans_eq ?_
        rw [hkA_def, hsA_def, Finset.sum_mul]
      have hB0 := ih p (r + 1) (covGrad g 0 r W) x
      have hBshift : ∑ p' ∈ Finset.range (j + 1), Φ.kappa (p + p') *
            ∑ q ∈ Finset.range (j + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((r + 1) + q) x
                ((iteratedCovGrad g 0 (r + 1) q (covGrad g 0 r W)).toSection x) =
          kB * sB := by
        rw [hkB_def, hsB_def, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p' _ => ?_
        congr 1
        exact Finset.sum_congr rfl fun q _ => rfns_iteratedCovGrad_covGrad_comm_db g 0 r q W x
      have hB : riemannianFiberNormSq (I := I) (M := M) g 0 (((r + 1) + p) + j) x
            ((iteratedCovGrad g 0 ((r + 1) + p) j
              (Φ.op p (r + 1) (covGrad g 0 r W))).toSection x) ≤
          (4 : ℝ) ^ j * (kB * sB) := by
        refine hB0.trans_eq ?_
        rw [← hBshift]
      have hkA_le : kA ≤ K := by
        rw [hkA_def, hK_def]
        refine (sum_range_shift_le_db (j + 1) (fun i => Φ.kappa (p + i))
          (fun i => Φ.kappa_nonneg (p + i))).trans' ?_
        exact le_of_eq (Finset.sum_congr rfl fun p' _ => by congr 1; omega)
      have hkB_le : kB ≤ K := by
        rw [hkB_def, hK_def]
        exact sum_range_le_succ_of_nonneg_db (j + 1) (fun p' => Φ.kappa (p + p'))
          (Φ.kappa_nonneg (p + (j + 1)))
      have hsA_le : sA ≤ S := by
        rw [hsA_def, hS_def]
        exact sum_range_le_succ_of_nonneg_db (j + 1) _
          (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + (j + 1)) x _)
      have hsB_le : sB ≤ S := by
        rw [hsB_def, hS_def]
        exact sum_range_shift_le_db (j + 1)
          (fun q => riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
            ((iteratedCovGrad g 0 r q W).toSection x))
          (fun q => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x _)
      have hkA_nn : 0 ≤ kA := Finset.sum_nonneg fun p' _ => Φ.kappa_nonneg ((p + 1) + p')
      have hkB_nn : 0 ≤ kB := Finset.sum_nonneg fun p' _ => Φ.kappa_nonneg (p + p')
      have hsA_nn : 0 ≤ sA :=
        Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x _
      have hsB_nn : 0 ≤ sB :=
        Finset.sum_nonneg fun q _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + (q + 1)) x _
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
          (4 : ℝ) ^ (j + 1) * ∑ p' ∈ Finset.range (j + 1 + 1), Φ.kappa (p + p') *
            ∑ q ∈ Finset.range (j + 1 + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
                ((iteratedCovGrad g 0 r q W).toSection x) := by
        rw [hK_def, hS_def, Finset.sum_mul]
      rw [htarget] at hgoal
      refine le_trans ?_ hgoal
      have hb_eq : riemannianFiberNormSq (I := I) (M := M) g 0 (((r + p) + 1) + j) x
            ((iteratedCovGrad g 0 ((r + p) + 1) j
              (castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1))
                (Φ.op p (r + 1) (covGrad g 0 r W)))).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (((r + 1) + p) + j) x
            ((iteratedCovGrad g 0 ((r + 1) + p) j
              (Φ.op p (r + 1) (covGrad g 0 r W))).toSection x) :=
        rfns_iteratedCovGrad_castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1))
          (Φ.op p (r + 1) (covGrad g 0 r W)) j x
      rw [hb_eq]
      exact add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num))
        (mul_le_mul_of_nonneg_left hB (by norm_num))

/-- **The single-sum collapse of the differentiated-operator `rfns` grid.**

Assembling the binomial grid `rfns_iteratedCovGrad_grid` at differentiation order `p = 0` (where
`op 0 r W` is the undifferentiated contraction): there is a single nonnegative order-dependent
constant `C : ℕ → ℝ` such that for every gradient order `j`, base rank `r`, section `W`, and point
`x`,
```
rfns(∇^j(op 0 r W))(x) ≤ C j · ∑_{q ≤ j} rfns(∇^q W)(x).
```
The double `p'`-sum collapses to a single constant because the differentiated-operator coefficients
`kappa p'` are base-point-uniform; `C j := 4^j · ∑_{p' ≤ j} kappa p'`.  This is the exact shape the
order-`m` jet induction and the intrinsic Moser-tame product
`exists_moserTameProduct_iteratedCovGrad_l2Norm_le` consume.  Proved from the grid by
`∑_{p'} kappa p' · ∑_q rfns = (∑_{p'} kappa p') · ∑_q rfns`. -/
theorem exists_rfns_iteratedCovGrad_singleSum_le (Φ : DiffBilinOp g) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (r : ℕ) (W : SmoothCcTensor g 0 r) (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + j) x
            ((iteratedCovGrad g 0 r j (Φ.op 0 r W)).toSection x) ≤
          C j * ∑ q ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  refine ⟨fun j => (4 : ℝ) ^ j * ∑ p' ∈ Finset.range (j + 1), Φ.kappa p',
    fun j => mul_nonneg (by positivity) (Finset.sum_nonneg fun p' _ => Φ.kappa_nonneg p'),
    fun r W j x => ?_⟩
  have hgrid := Φ.rfns_iteratedCovGrad_grid j 0 r W x
  -- The `p = 0` instance: `kappa (0 + p') = kappa p'`, and `op 0 r W` lives at rank `(r + 0) + j`.
  simp only [Nat.zero_add, Nat.add_zero] at hgrid
  refine hgrid.trans_eq ?_
  rw [← Finset.sum_mul, mul_assoc]

end DiffBilinOp

end Connection
end Integral
end DifferentialGeometry

end
