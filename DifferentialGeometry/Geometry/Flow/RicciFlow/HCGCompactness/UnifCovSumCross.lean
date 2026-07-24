import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import Mathlib.Analysis.Matrix.PosDef

/-!
# Covariant-sum cross-metric equivalence (item-6 statement S0) — fiber-level layer

This leaf builds toward item-6 statement **S0** (`covsum_cross_unif`, see
`ShortTime/UNIF_ITEM6_RECON.md` §S0): for `Λ`-comparable metrics `g₀`, `gBase` with
`MetricCovDerivOrderBoundOn` jets `≤ Λ`, the two-sided equivalence of covariant-derivative
sums
`∑_{j≤n} ‖∇^{g₀,j}T‖_{L²(g₀)} ≍_{C(Λ,n)} ∑_{j≤n} ‖∇^{gBase,j}T‖_{L²(gBase)}`.

Per the recon §3 route table, S0 decomposes into three levels: **fiber** (Λ-comparability ⟹
per-slot `√Λ` fibre-norm comparison — routine), **volume** (`dV_{g₀} ≍_{Λ^{n/2}} dV_{gBase}` —
a Loewner→determinant estimate the project deliberately avoided, see
`Measure/CompactVolumeEquiv.lean:9`), and **derivative** (the iterated change-of-connection
`∇^{g₀} = ∇^{gBase} + Γ-difference`, the main frontier).  The `volume` and `derivative`
bricks, plus the RS↔0S fibre-norm currency bridge (the sibling `MetricCovDerivBridge` lane's
`normBridge`), are multi-session; see `UnifCovSumCross.md`.

**This file** delivers the sorry-free **fiber-level layer** in the `normSq0S` currency, keyed
on the project comparability predicate `MetricUniformEquivalentOn` (`= Λ`-comparability with
`C = Λ`).  It packages the general-order pointwise fibre comparison and the covariant-*sum*
shell that the eventual L² assembly composes with the connection-change and volume bricks.

## Main results

* `covsumCross_fibSq` — two-sided per-order fibre squared-norm comparison:
  `Λ^{-s}·|A|²_{gBase} ≤ |A|²_{g₀} ≤ Λ^s·|A|²_{gBase}` for a `(0,s)` fibre tensor `A`.
* `covsumCross_fibNorm` — the `√`/norm upper form `|A|_{g₀} ≤ Λ^{s/2}·|A|_{gBase}`.
* `covsumCross_fibSum` — the covariant-sum shell: over a derivative-indexed family of
  `(0, s+j)` tensors, `∑_{j≤n} |A j|_{g₀} ≤ Λ^{(s+n)/2}·∑_{j≤n} |A j|_{gBase}` with a single
  explicit constant `Λ^{(s+n)/2}`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.HCGCompactness

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

/-! ### Matrix determinant building blocks for the volume (Loewner→det) brick

These generic real-matrix lemmas are the pure linear-algebra core of the volume comparison
`dV_{g₀} ≍_{Λ^{n/2}} dV_{gBase}` (recon §3 volume level): the chart densities are
`√det(chartGram)`, so the comparison reduces to `det(chartGram g₀) ≤ Λ^n·det(chartGram gBase)`
(Loewner→determinant monotonicity).  Mathlib has no matrix square root, Weyl monotonicity, or
`det`-order lemma, so this is built from the spectral theorem; the reusable core is
`det_le_one_of_rayleigh` (`A ≤ I ⟹ det A ≤ 1`).  Candidate canonical home:
`Geometry/Comparison/Volume/JacobianBounds.lean` `MatrixBounds` (beside the existing
`eigenvalues_ge_of_rayleigh`/`sqrt_pow_le_sqrt_det`); kept private here pending planner hoist. -/
section MatrixDet

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Unit-vector Rayleigh **upper** bound ⟹ every eigenvalue is `≤ a` (the upper companion of
`Geometry/Comparison/Volume/JacobianBounds.lean`'s `eigenvalues_ge_of_rayleigh`). -/
private lemma eigenvalues_le_of_rayleigh
    {A : Matrix ι ι ℝ} {a : ℝ} (hA : A.IsHermitian)
    (hray : ∀ v : EuclideanSpace ℝ ι, ‖v‖ = 1 →
      RCLike.re (dotProduct (star ⇑v) (Matrix.mulVec A ⇑v)) ≤ a) :
    ∀ i, hA.eigenvalues i ≤ a := by
  intro i
  rw [hA.eigenvalues_eq i]
  exact hray (hA.eigenvectorBasis i) (hA.eigenvectorBasis.norm_eq_one i)

/-- A positive-semidefinite real matrix whose Rayleigh quotient is `≤ 1` on the unit sphere
(i.e. `A ≤ I` in the Loewner order) has `det A ≤ 1`: its eigenvalues lie in `[0,1]` and the
determinant is their product.  This is the `B = I` core of Loewner→determinant monotonicity. -/
private lemma det_le_one_of_rayleigh
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hray : ∀ v : EuclideanSpace ℝ ι, ‖v‖ = 1 →
      RCLike.re (dotProduct (star ⇑v) (Matrix.mulVec A ⇑v)) ≤ 1) :
    A.det ≤ 1 := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  refine Finset.prod_le_one (fun i _ => ?_) (fun i _ => ?_)
  · exact_mod_cast hA.eigenvalues_nonneg i
  · exact_mod_cast eigenvalues_le_of_rayleigh hA.isHermitian hray i

end MatrixDet

-- The fibre-level comparison is purely pointwise: it needs only the fibre inner-product /
-- finite-dimensionality on `E` and a charted smooth manifold structure.  The manifold
-- topology instances (`CompactSpace`/`T2Space`/`SigmaCompactSpace`/boundarylessness) and
-- `NeZero (finrank E)` are deliberately dropped (weakest hypotheses); they re-enter only at
-- the L² / volume assembly, not here.
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **Fiber-level squared-norm cross-metric comparison** (S0 fibre atom, both directions).
For `Λ`-comparable `g₀`, `gBase` (as the project predicate `MetricUniformEquivalentOn`) and a
covariant `(0,s)` fibre tensor `A` at `x`, the two `g`-fibre squared norms differ by `Λ^{±s}`
(one `Λ` per tensor slot).  Forwards `normSq0S_le_of_metric_equiv` against the comparability
supplied pointwise by the class hypothesis. -/
theorem covsumCross_fibSq
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (x : M) (s : ℕ) (A : Tensor0SSpace s I x) :
    Λ ^ (-(s : ℤ)) * normSq0S (I := I) gBase x s A ≤ normSq0S (I := I) g₀ x s A ∧
      normSq0S (I := I) g₀ x s A ≤ Λ ^ (s : ℤ) * normSq0S (I := I) gBase x s A :=
  normSq0S_le_of_metric_equiv (I := I) gBase g₀ x s hEq.1
    (fun v => hEq.2 x (Set.mem_univ x) v) A

/-- **Fiber-level norm cross-metric comparison** (`√` form of `covsumCross_fibSq`, upper
direction).  `|A|_{g₀} ≤ Λ^{s/2}·|A|_{gBase}` for a covariant `(0,s)` fibre tensor.  This is
the fibre factor consumed term-by-term by the L² covariant-sum comparison. -/
theorem covsumCross_fibNorm
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (x : M) (s : ℕ) (A : Tensor0SSpace s I x) :
    Real.sqrt (normSq0S (I := I) g₀ x s A) ≤
      Real.sqrt (Λ ^ s) * Real.sqrt (normSq0S (I := I) gBase x s A) :=
  sqrt_normSq0S_le_of_metric_equiv (I := I) gBase g₀ x s hEq.1
    (fun v => hEq.2 x (Set.mem_univ x) v) A

/-- **Covariant-sum fibre shell** (the S0-shaped fibre reduction).  Over a derivative-indexed
family `A j : Tensor0SSpace (s + j) I x` (the fibres of the `(0,s)`-base covariant tower up to
order `n`), the `g₀`-fibre-norm sum is bounded by the `gBase`-fibre-norm sum times the single
explicit constant `Λ^{(s+n)/2}` (`= √(Λ^{s+n})`), obtained from the per-order factor
`Λ^{(s+j)/2}` by monotonicity `Λ ≥ 1`, `s+j ≤ s+n`.  The L² statement S0 is this shell
composed with the pointwise connection-change bound and the volume comparison (both frontier;
see `UnifCovSumCross.md`). -/
theorem covsumCross_fibSum
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (x : M) (s n : ℕ) (A : (j : ℕ) → Tensor0SSpace (s + j) I x) :
    ∑ j ∈ Finset.range (n + 1), Real.sqrt (normSq0S (I := I) g₀ x (s + j) (A j)) ≤
      Real.sqrt (Λ ^ (s + n)) *
        ∑ j ∈ Finset.range (n + 1),
          Real.sqrt (normSq0S (I := I) gBase x (s + j) (A j)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun j hj => ?_)
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hmono : Real.sqrt (Λ ^ (s + j)) ≤ Real.sqrt (Λ ^ (s + n)) :=
    Real.sqrt_le_sqrt (pow_le_pow_right₀ hEq.1 (by omega))
  calc Real.sqrt (normSq0S (I := I) g₀ x (s + j) (A j))
      ≤ Real.sqrt (Λ ^ (s + j)) *
          Real.sqrt (normSq0S (I := I) gBase x (s + j) (A j)) :=
        covsumCross_fibNorm gBase g₀ hEq x (s + j) (A j)
    _ ≤ Real.sqrt (Λ ^ (s + n)) *
          Real.sqrt (normSq0S (I := I) gBase x (s + j) (A j)) :=
        mul_le_mul_of_nonneg_right hmono (Real.sqrt_nonneg _)

end RicciFlow
end PDE
end DifferentialGeometry
