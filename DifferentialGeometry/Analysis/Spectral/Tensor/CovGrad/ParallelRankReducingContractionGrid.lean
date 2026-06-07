import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseTensorCurvL2Bound

/-! # The intrinsic `rfns` jet grid for a parallel rank-reducing single-section contraction

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, the file `MetricContractionLeibnizGrid` packages a *non-parallel*,
*rank-preserving* differentiated bilinear contraction as `DiffBilinOp` (`op p r : (0, r) → (0, r + p)`,
output rank ≥ input rank) and proves its binomial covariant-Leibniz `rfns` grid.  Two structural
features of that engine make it unable to realise the **curvature trace**:

* it is **rank-preserving** (the output covariant rank is the input rank plus the differentiation
  order), so it cannot lower the slot count, whereas a metric trace `g^{ij}·` of a `(0, s + 1)`-tensor
  produces a `(0, s)`-tensor (slot count down by one — actually down by two for a double trace);
* its single-step Leibniz carries a *non-parallel* differentiated-operator cross term `op (p + 1)`,
  forcing the weaker order-`≤ p` *jet* envelope.

This file supplies the complementary engine: a **parallel** (cross-term-free), **rank-reducing**
*single-section* contraction, `ParallelRankReducingContraction`.  Its contracting tensor is parallel
(`∇g = 0` for the metric, `∇(g⁻¹) = 0` for the inverse metric), so the exact single-step covariant
Leibniz is the clean `∇(op a R) = (rank-cast) op (a + 1) (∇R)` with **no** differentiated-operator
cross term, and its fibre envelope is the strong **single-value** form `rfns(op a R)(x) ≤ kappa ·
rfns(R)(x)` (the contraction is value-local: it reads only `R(x)`, never a jet of `R`).  From these two
genuine `∇`-compatibility fields the `rfns` jet grid is **proved outright** (no posit, no binomial — a
parallel single-section contraction commutes with `∇` exactly, so `∇^j(op 0 R)` is, up to a rank-cast,
`op j (∇^j R)`):
```
rfns(∇^j (op 0 R))(x) ≤ kappa · rfns(∇^j R)(x).
```

This is the rank-reducing trace grid the curvature-trace step of the Ricci difference arm needs (the
model-basis trace contracting the connection-level realized covariant gradient `R = covGrad g 0 2 w`
against the parallel metric, lowering the rank back to `(0, 2)`).  A reusable covariant-calculus
byproduct (R1 — its own first-class home in the covariant gradient API), decoupled from any specific
contraction: every parallel metric contraction `g^{ij}·`, `g_{ij}·`, double trace, etc. of a single
tensor section is an instance.

## Main definitions

* `ParallelRankReducingContraction g sIn sOut` — a parallel rank-reducing single-section contraction
  family: a section-level operator `op a` at every gradient-shift `a` lowering covariant rank
  `sIn + a → sOut + a`, satisfying the exact parallel single-step covariant Leibniz (`covGrad_op`,
  cross-term-free) and a base-point-uniform single-value proportional fibre envelope
  (`kappa`, `rfns_op_le`).

## Main results

* `ParallelRankReducingContraction.rfns_iteratedCovGrad_le` — the clean one-term `rfns` jet grid
  `rfns(∇^j (op 0 R))(x) ≤ kappa · rfns(∇^j R)(x)`, proved by induction on `j` front-commuting the
  innermost gradient through the parallel operator. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

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
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **A parallel rank-reducing single-section contraction family.**

The genuine abstraction realised by a *parallel* metric contraction of a *single* varying tensor
section (the structure of the curvature trace `g^{ij} R_{ij··}`, the Ricci trace, any `g`- or
`g⁻¹`-contraction): the operator `op a` lowers the covariant rank `sIn + a → sOut + a` (necessarily
`sOut ≤ sIn`), is fibrewise-`ℝ`-linear in the section, and has two genuine `∇`-compatibility fields:

* `covGrad_op` — the **exact parallel single-step covariant Leibniz** `∇(op a R) = (rank-cast)
  op (a + 1) (∇R)`.  Because the contracting tensor is parallel (`∇g = 0`), the differentiated-operator
  cross term *vanishes*: the only surviving term differentiates the section, with the new slot carried
  at the front, rank-cast from `(sOut + (a + 1))` to `((sOut + a) + 1)`.
* `kappa`, `kappa_nonneg`, `rfns_op_le` — the **single-value** base-point-uniform proportional fibre
  envelope `rfns(op a R)(x) ≤ kappa · rfns(R)(x)`.  A parallel contraction is value-local (it reads
  only the fibre value `R(x)`, never a jet), so — unlike the non-parallel `DiffBilinOp` whose recursion
  reads `∇^p R` — the strong single-value form holds.

These are genuine mathematical inputs (the consumer constructs `op` from the contracting tensor and
discharges the two fields).  A degenerate `kappa ≡ 0` witness is rejected whenever `op a R ≠ 0` (then
`rfns(op a R)(x) > 0` while `0 · rfns(R)(x) = 0`), so the envelope genuinely uses the section. -/
structure ParallelRankReducingContraction (g : SmoothRiemannianMetric I M) (sIn sOut : ℕ) where
  /-- The contraction at gradient-shift `a`, fibrewise-linear, lowering rank `sIn + a → sOut + a`. -/
  op : ∀ a : ℕ, SmoothCcTensor g 0 (sIn + a) → SmoothCcTensor g 0 (sOut + a)
  /-- The exact parallel single-step covariant Leibniz (no differentiated-operator cross term). -/
  covGrad_op : ∀ (a : ℕ) (R : SmoothCcTensor g 0 (sIn + a)),
    covGrad g 0 (sOut + a) (op a R) =
      castRankCc_db g 0 (by omega : sOut + (a + 1) = (sOut + a) + 1)
        (op (a + 1) (covGrad g 0 (sIn + a) R))
  /-- The base-point-uniform single-value proportional fibre-envelope constant. -/
  kappa : ℝ
  /-- The envelope constant is nonnegative. -/
  kappa_nonneg : 0 ≤ kappa
  /-- The single-value base-point-uniform proportional fibre bound (value-locality of a parallel
  contraction). -/
  rfns_op_le : ∀ (a : ℕ) (R : SmoothCcTensor g 0 (sIn + a)) (x : M),
    riemannianFiberNormSq (I := I) (M := M) g 0 (sOut + a) x ((op a R).toSection x) ≤
      kappa * riemannianFiberNormSq (I := I) (M := M) g 0 (sIn + a) x (R.toSection x)

/-- **`rfns` is invariant under a section `HEq` at `Nat`-equal covariant ranks** (the rank equality
collapses the `HEq` to an `Eq` by `subst`).  Local re-statement (no extra import). -/
private theorem rfns_toSection_heq_local (g : SmoothRiemannianMetric I M) {a b : ℕ} (h : a = b)
    {S : SmoothCcTensor g 0 a} {S' : SmoothCcTensor g 0 b} (hSS' : HEq S S') (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 a x (S.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 b x (S'.toSection x) := by
  subst h; rw [eq_of_heq hSS']

namespace ParallelRankReducingContraction

variable {g : SmoothRiemannianMetric I M} {sIn sOut : ℕ}

/-- **Front-commuting one covariant gradient of the section through the parallel contraction (`rfns`
form).**  By the exact parallel Leibniz `covGrad_op` and the rank-cast invariance of `rfns`, for every
shift `a`, gradient order `j`, section `R`, and point `x`:
`rfns(∇^j (∇(op a R)))(x) = rfns(∇^j (op (a+1) (∇R)))(x)`. -/
private theorem rfns_iteratedCovGrad_covGrad_op (Φ : ParallelRankReducingContraction g sIn sOut)
    (a j : ℕ) (R : SmoothCcTensor g 0 (sIn + a)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 ((sOut + a) + 1 + j) x
        ((iteratedCovGrad g 0 ((sOut + a) + 1) j
            (covGrad g 0 (sOut + a) (Φ.op a R))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 ((sOut + (a + 1)) + j) x
        ((iteratedCovGrad g 0 (sOut + (a + 1)) j
            (Φ.op (a + 1) (covGrad g 0 (sIn + a) R))).toSection x) := by
  rw [Φ.covGrad_op a R]
  exact rfns_iteratedCovGrad_castRankCc_db g 0
    (by omega : sOut + (a + 1) = (sOut + a) + 1)
    (Φ.op (a + 1) (covGrad g 0 (sIn + a) R)) j x

/-- **The clean one-term `rfns` jet grid for a parallel rank-reducing contraction.**

For every gradient order `j`, every shift `a`, every section `R`, and every point `x`, the intrinsic
squared fibre norm of `∇^j (op a R)` is bounded by `kappa` times that of `∇^j R`:
```
rfns(∇^j (op a R))(x) ≤ kappa · rfns(∇^j R)(x).
```

A parallel single-section contraction commutes with `∇` exactly (`covGrad_op`, no differentiated-
operator cross term), so `∇^j(op a R)` is, up to a rank-cast, `op (a + j) (∇^j R)`, and the value-local
envelope `rfns_op_le` then bounds it by `kappa · rfns(∇^j R)(x)`.  Proved by induction on `j`,
front-commuting the innermost gradient (`rfns_iteratedCovGrad_covGrad_op`) and recursing at shift
`a + 1` on `∇R`; the base case `j = 0` is the single-value envelope `rfns_op_le`.  No posit, no binomial
expansion. -/
theorem rfns_iteratedCovGrad_le (Φ : ParallelRankReducingContraction g sIn sOut) (j : ℕ) :
    ∀ (a : ℕ) (R : SmoothCcTensor g 0 (sIn + a)) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 ((sOut + a) + j) x
          ((iteratedCovGrad g 0 (sOut + a) j (Φ.op a R)).toSection x) ≤
        Φ.kappa * riemannianFiberNormSq (I := I) (M := M) g 0 ((sIn + a) + j) x
          ((iteratedCovGrad g 0 (sIn + a) j R).toSection x) := by
  induction j with
  | zero =>
      intro a R x
      rw [iteratedCovGrad_zero, iteratedCovGrad_zero]
      exact Φ.rfns_op_le a R x
  | succ j ih =>
      intro a R x
      -- Front-commute the innermost gradient on both sides: `∇^{j+1}(op a R) = ∇^j(∇(op a R))`.
      have hLHS : riemannianFiberNormSq (I := I) (M := M) g 0 ((sOut + a) + (j + 1)) x
            ((iteratedCovGrad g 0 (sOut + a) (j + 1) (Φ.op a R)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 ((sOut + a) + 1 + j) x
            ((iteratedCovGrad g 0 ((sOut + a) + 1) j
                (covGrad g 0 (sOut + a) (Φ.op a R))).toSection x) :=
        (rfns_toSection_heq_local g
          (by omega : (sOut + a) + 1 + j = (sOut + a) + (j + 1))
          (iteratedCovGrad_covGrad_comm_heq g 0 (sOut + a) j (Φ.op a R)) x).symm
      have hRHS : riemannianFiberNormSq (I := I) (M := M) g 0 ((sIn + a) + (j + 1)) x
            ((iteratedCovGrad g 0 (sIn + a) (j + 1) R).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 ((sIn + a) + 1 + j) x
            ((iteratedCovGrad g 0 ((sIn + a) + 1) j
                (covGrad g 0 (sIn + a) R)).toSection x) :=
        (rfns_toSection_heq_local g
          (by omega : (sIn + a) + 1 + j = (sIn + a) + (j + 1))
          (iteratedCovGrad_covGrad_comm_heq g 0 (sIn + a) j R) x).symm
      rw [hLHS, hRHS]
      -- Rewrite `∇(op a R)` through the parallel Leibniz; the LHS becomes `rfns(∇^j (op (a+1) (∇R)))`.
      rw [Φ.rfns_iteratedCovGrad_covGrad_op a j R]
      -- The induction hypothesis at shift `a + 1` on `∇R : (0, sIn + (a + 1))` (`(sIn+a)+1` defeq
      -- `sIn+(a+1)`), front-commuting the RHS gradient back the same way.
      have hRHS2 : riemannianFiberNormSq (I := I) (M := M) g 0 ((sIn + a) + 1 + j) x
            ((iteratedCovGrad g 0 ((sIn + a) + 1) j (covGrad g 0 (sIn + a) R)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 ((sIn + (a + 1)) + j) x
            ((iteratedCovGrad g 0 (sIn + (a + 1)) j
                (covGrad g 0 (sIn + a) R)).toSection x) := rfl
      rw [hRHS2]
      exact ih (a + 1) (covGrad g 0 (sIn + a) R) x

end ParallelRankReducingContraction

end Connection
end Integral
end DifferentialGeometry
