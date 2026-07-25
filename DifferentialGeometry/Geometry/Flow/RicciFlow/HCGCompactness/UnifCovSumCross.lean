import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

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
open scoped Manifold Topology ContDiff BigOperators Matrix MatrixOrder
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Measure

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

/-- Plain-vector form of `det_le_one_of_rayleigh`: if the (real) quadratic form of a
positive-semidefinite matrix `A` is dominated by the Euclidean one (`x ⬝ᵥ A *ᵥ x ≤ x ⬝ᵥ x`,
i.e. `A ≤ I`), then `det A ≤ 1`.  Isolates the `EuclideanSpace`/`star`/`RCLike.re`
bookkeeping so the general Loewner→determinant lemma stays in `ι → ℝ` currency. -/
private lemma det_le_one_of_dotProduct
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hray : ∀ x : ι → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ x) :
    A.det ≤ 1 := by
  refine det_le_one_of_rayleigh hA (fun v hv => ?_)
  have hnorm : (⇑v : ι → ℝ) ⬝ᵥ ⇑v = 1 := by
    have h1 := EuclideanSpace.inner_eq_star_dotProduct (𝕜 := ℝ) v v
    rw [star_trivial] at h1
    have h2 : (⇑v : ι → ℝ) ⬝ᵥ ⇑v = ‖v‖ ^ 2 := by
      rw [← h1]; exact real_inner_self_eq_norm_sq v
    rw [h2, hv, one_pow]
  simp only [star_trivial, RCLike.re_to_real]
  exact (hray ⇑v).trans hnorm.le

/-- **General Loewner→determinant monotonicity.**  A positive-semidefinite matrix `A` dominated
(in the quadratic-form / Loewner sense) by a positive-definite matrix `B` has no larger
determinant.  Proof: the congruence `C := B^{-1/2} A B^{-1/2}` satisfies `C ≤ I` (so
`det C ≤ 1`) and `A = B^{1/2} C B^{1/2}`, whence `det A = det B · det C ≤ det B`.  Mathlib has
no matrix Loewner→det lemma; this is built from the CFC matrix square root
(`Analysis/Matrix/Order.lean`).  Reusable core of the volume brick (hoist candidate:
`Geometry/Comparison/Volume/JacobianBounds.lean` `MatrixBounds`). -/
private lemma det_le_of_posSemidef_le
    {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosDef)
    (hAB : ∀ x : ι → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x)) :
    A.det ≤ B.det := by
  classical
  -- self-adjointness of the quadratic pairing for a symmetric real matrix
  have quad_symm : ∀ (S : Matrix ι ι ℝ), Sᵀ = S → ∀ x z : ι → ℝ,
      x ⬝ᵥ (S *ᵥ z) = (S *ᵥ x) ⬝ᵥ z := by
    intro S hS x z
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS]
  -- the positive square root `M = √B` and its basic algebra
  set M := CFC.sqrt B with hM_def
  have hM_nonneg : (0 : Matrix ι ι ℝ) ≤ M := by rw [hM_def]; exact CFC.sqrt_nonneg B
  have hM_psd : M.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hM_nonneg
  have hM_herm : Mᴴ = M := hM_psd.isHermitian
  have hMsymm : Mᵀ = M := by
    ext i j
    simpa [Matrix.transpose_apply, star_trivial] using hM_psd.isHermitian.apply i j
  have hMM : M * M = B := by
    rw [hM_def]; exact CFC.sqrt_mul_sqrt_self B (Matrix.nonneg_iff_posSemidef.mpr hB.posSemidef)
  -- determinant bookkeeping for `M`
  have hdetB_pos : 0 < B.det := hB.det_pos
  have hdetMM : M.det * M.det = B.det := by rw [← Matrix.det_mul, hMM]
  have hdetM_ne : M.det ≠ 0 := fun h0 => hdetB_pos.ne' (by rw [← hdetMM, h0, zero_mul])
  have hdetM_unit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdetM_ne
  have hMinv_r : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdetM_unit
  have hMinv_l : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdetM_unit
  have hMinvsymm : (M⁻¹)ᵀ = M⁻¹ := by rw [Matrix.transpose_nonsing_inv, hMsymm]
  -- the congruence `C = M⁻¹ A M⁻¹` is PSD with Rayleigh quotient `≤ 1`
  have hC_psd : (M⁻¹ * A * M⁻¹).PosSemidef := by
    have h := hA.conjTranspose_mul_mul_same M⁻¹
    rwa [Matrix.conjTranspose_nonsing_inv, hM_herm] at h
  have hC_ray : ∀ x : ι → ℝ, x ⬝ᵥ ((M⁻¹ * A * M⁻¹) *ᵥ x) ≤ x ⬝ᵥ x := by
    intro x
    have hMw : M *ᵥ (M⁻¹ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, hMinv_r, Matrix.one_mulVec]
    have e1 : x ⬝ᵥ ((M⁻¹ * A * M⁻¹) *ᵥ x) = (M⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ (M⁻¹ *ᵥ x)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact quad_symm M⁻¹ hMinvsymm x (A *ᵥ (M⁻¹ *ᵥ x))
    have e3 : (M⁻¹ *ᵥ x) ⬝ᵥ (B *ᵥ (M⁻¹ *ᵥ x)) = x ⬝ᵥ x := by
      rw [← hMM, ← Matrix.mulVec_mulVec,
        quad_symm M hMsymm (M⁻¹ *ᵥ x) (M *ᵥ (M⁻¹ *ᵥ x)), hMw]
    calc x ⬝ᵥ ((M⁻¹ * A * M⁻¹) *ᵥ x)
        = (M⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ (M⁻¹ *ᵥ x)) := e1
      _ ≤ (M⁻¹ *ᵥ x) ⬝ᵥ (B *ᵥ (M⁻¹ *ᵥ x)) := hAB (M⁻¹ *ᵥ x)
      _ = x ⬝ᵥ x := e3
  have hdetC : (M⁻¹ * A * M⁻¹).det ≤ 1 := det_le_one_of_dotProduct hC_psd hC_ray
  -- reassemble `A = M C M` and conclude `det A = det B · det C ≤ det B`
  have hACM : M * (M⁻¹ * A * M⁻¹) * M = A := by
    rw [show M * (M⁻¹ * A * M⁻¹) * M = (M * M⁻¹) * A * (M⁻¹ * M) by simp only [mul_assoc]]
    rw [hMinv_r, hMinv_l, one_mul, mul_one]
  have hdetA : A.det = B.det * (M⁻¹ * A * M⁻¹).det := by
    have hcongr := congrArg Matrix.det hACM
    rw [Matrix.det_mul, Matrix.det_mul] at hcongr
    rw [← hcongr, ← hdetMM]; ring
  rw [hdetA]
  exact mul_le_of_le_one_right hdetB_pos.le hdetC

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

/-! ### Volume level — chart-Gram / chart-density cross-metric comparison

The volume brick `dV_{g₀} ≍_{Λ^{n/2}} dV_{gBase}`.  `chartDensity g x₀ x = √det(chartGramMatrix
g x₀ x)`, so the comparison reduces to the Loewner→determinant estimate `det(chartGram g₀) ≤
Λ^n·det(chartGram gBase)` (`det_le_of_posSemidef_le`) fed by the chart-Gram quadratic-form
comparison below.  The measure-level lift (via `chart_lintegral_le` and the POU sum) is the
remaining piece; see `UnifCovSumCross.md`. -/

/-- **Chart-Gram quadratic-form comparison** (volume-brick step 2).  `Λ`-comparability of
`g₀`, `gBase` transfers to a pointwise Loewner bound on their chart-Gram matrices: the
`g₀`-Gram quadratic form is bounded by `Λ` times the `gBase`-Gram quadratic form, at every
point and coefficient vector.  Proved by writing each quadratic form as the fibre inner
product of the same linear combination of chart-basis vectors and applying comparability. -/
theorem chartGram_quad_le_of_equiv
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (x₀ x : M) (v : Fin (Module.finrank ℝ E) → ℝ) :
    v ⬝ᵥ (chartGramMatrix (I := I) g₀ x₀ x) *ᵥ v ≤
      Λ * (v ⬝ᵥ (chartGramMatrix (I := I) gBase x₀ x) *ᵥ v) := by
  have hg₀ : v ⬝ᵥ (chartGramMatrix (I := I) g₀ x₀ x) *ᵥ v =
      g₀.inner x (∑ i, v i • chartBasisVecFiber (I := I) x₀ i x)
        (∑ j, v j • chartBasisVecFiber (I := I) x₀ j x) := by
    rw [← chartGramMatrix_dotProduct_mulVec (I := I) g₀ x₀ x v, star_trivial]
  have hgB : v ⬝ᵥ (chartGramMatrix (I := I) gBase x₀ x) *ᵥ v =
      gBase.inner x (∑ i, v i • chartBasisVecFiber (I := I) x₀ i x)
        (∑ j, v j • chartBasisVecFiber (I := I) x₀ j x) := by
    rw [← chartGramMatrix_dotProduct_mulVec (I := I) gBase x₀ x v, star_trivial]
  rw [hg₀, hgB]
  exact (hEq.2 x (Set.mem_univ x)
    (∑ i, v i • chartBasisVecFiber (I := I) x₀ i x)).2

/-- **Chart-density cross-metric bound** (volume-brick step 3).  On the tangent trivialization
base set — where both chart-Gram matrices are positive-definite — the `g₀` chart density is
bounded by `√(Λ^n)` times the `gBase` chart density (`n = finrank ℝ E`), the pointwise
`Λ^{n/2}` volume-density comparison.  Combines the chart-Gram quadratic comparison with the
Loewner→determinant estimate and `√`-monotonicity. -/
theorem chartDensity_cross_le
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    chartDensity (I := I) g₀ x₀ x ≤
      Real.sqrt (Λ ^ Module.finrank ℝ E) * chartDensity (I := I) gBase x₀ x := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hEq.1
  have hA : (chartGramMatrix (I := I) g₀ x₀ x).PosSemidef :=
    (chartGramMatrix_posDef (I := I) g₀ x₀ hx).posSemidef
  have hB : (Λ • chartGramMatrix (I := I) gBase x₀ x).PosDef :=
    (chartGramMatrix_posDef (I := I) gBase x₀ hx).smul hΛpos
  have hAB : ∀ v : Fin (Module.finrank ℝ E) → ℝ,
      v ⬝ᵥ (chartGramMatrix (I := I) g₀ x₀ x) *ᵥ v ≤
        v ⬝ᵥ (Λ • chartGramMatrix (I := I) gBase x₀ x) *ᵥ v := by
    intro v
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact chartGram_quad_le_of_equiv (I := I) gBase g₀ hEq x₀ x v
  have hdet : (chartGramMatrix (I := I) g₀ x₀ x).det ≤
      Λ ^ Module.finrank ℝ E * (chartGramMatrix (I := I) gBase x₀ x).det := by
    have h := det_le_of_posSemidef_le hA hB hAB
    rwa [Matrix.det_smul, Fintype.card_fin] at h
  change Real.sqrt ((chartGramMatrix (I := I) g₀ x₀ x).det) ≤
    Real.sqrt (Λ ^ Module.finrank ℝ E) *
      Real.sqrt ((chartGramMatrix (I := I) gBase x₀ x).det)
  rw [← Real.sqrt_mul (pow_nonneg hΛpos.le _)]
  exact Real.sqrt_le_sqrt hdet

end RicciFlow
end PDE
end DifferentialGeometry
