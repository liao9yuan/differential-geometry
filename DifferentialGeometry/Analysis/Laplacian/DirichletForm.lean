import DifferentialGeometry.Analysis.Laplacian.H1Intrinsic
import DifferentialGeometry.Integral.Integration.GlobalPairing.Defs

/-!
# Dirichlet form and shifted form on the intrinsic `H¹` space

For an `H¹` element `u : H1Intrinsic g`, the Dirichlet form is
$$Q(u, v) = \int_M g(\nabla u, \nabla v)\, d\mu_g.$$
The shifted form is
$$B(u, v) = Q(u, v) + \int_M u\, v\, d\mu_g.$$

This file defines both forms and proves the basic algebraic properties:
symmetry and non-negativity (for `Q`).

The shifted form recovers the natural intrinsic `H¹` quadratic form for
the Riemannian metric `g`. The ambient `H1Intrinsic g` carries the
inherited L²-product Hilbert structure (whose inner product on the
gradient slot uses the Euclidean inner product on the model fiber `E`,
not the Riemannian metric `g`); the shifted form is provided here as a
distinct bilinear form that captures the intrinsic Riemannian H¹ pairing.

## Main definitions

* `dirichletForm g u v` : the Dirichlet form `Q(u, v)`.
* `shiftedForm g u v` : the shifted form `B(u, v) = Q(u, v) +
  ⟨toLp u, toLp v⟩_{L²(ℝ)}`.

## Main results

* Symmetry of both forms.
* Non-negativity on the diagonal of both forms.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Function
open scoped Manifold Topology ContDiff ENNReal NNReal Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.IntrinsicH1Lp

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace H1Intrinsic

variable [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]

/-! ## The Dirichlet form -/

/-- The Dirichlet form `Q(u, v) := ∫_M g(∇u, ∇v) dμ_g`. -/
def dirichletForm (g : SmoothRiemannianMetric I M)
    (u v : H1Intrinsic (I := I) (M := M) g) : ℝ :=
  ∫ x : M,
    g.inner x ((gradL2 (I := I) (M := M) g u : M → E) x)
      ((gradL2 (I := I) (M := M) g v : M → E) x)
    ∂(riemannianVolumeMeasure I M g)

/-- Symmetry of the Dirichlet form. -/
theorem dirichletForm_symm (g : SmoothRiemannianMetric I M)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    dirichletForm (I := I) (M := M) g u v =
      dirichletForm (I := I) (M := M) g v u := by
  unfold dirichletForm
  refine integral_congr_ae ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  exact g.symm x _ _

/-- The Dirichlet form on the diagonal is non-negative. -/
theorem dirichletForm_self_nonneg (g : SmoothRiemannianMetric I M)
    (u : H1Intrinsic (I := I) (M := M) g) :
    0 ≤ dirichletForm (I := I) (M := M) g u u := by
  unfold dirichletForm
  apply integral_nonneg
  intro x
  change (0 : ℝ) ≤
    g.inner x ((gradL2 (I := I) (M := M) g u : M → E) x)
      ((gradL2 (I := I) (M := M) g u : M → E) x)
  rcases eq_or_ne ((gradL2 (I := I) (M := M) g u : M → E) x) 0 with h0 | h0
  · -- gradient at x is zero, so the integrand at x is g(0, 0) = 0.
    have h_zero : g.inner x ((gradL2 (I := I) (M := M) g u : M → E) x)
        ((gradL2 (I := I) (M := M) g u : M → E) x) = 0 := by
      rw [h0]
      change g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0
      rw [map_zero]
    linarith [h_zero]
  · exact (g.pos x _ h0).le

/-- The Dirichlet form vanishes on the zero element (left slot). -/
theorem dirichletForm_zero_left (g : SmoothRiemannianMetric I M)
    (u : H1Intrinsic (I := I) (M := M) g) :
    dirichletForm (I := I) (M := M) g 0 u = 0 := by
  unfold dirichletForm
  -- gradL2 0 = 0 (linear map), so g.inner x 0 _ = 0 a.e.
  have h0 : (gradL2 (I := I) (M := M) g (0 : H1Intrinsic (I := I) (M := M) g) :
      Lp E 2 (riemannianVolumeMeasure I M g)) = 0 := by
    rw [(gradL2 (I := I) (M := M) g).map_zero]
  -- (gradL2 g 0 : M → E) =ᵐ 0 via Lp.coeFn_zero.
  have h_ae : (fun x : M =>
        g.inner x ((gradL2 g (0 : H1Intrinsic g) : M → E) x)
          ((gradL2 g u : M → E) x)) =ᵐ[riemannianVolumeMeasure I M g]
      (fun _ : M => (0 : ℝ)) := by
    have hzero_fn : (fun x : M => ((gradL2 g (0 : H1Intrinsic g) :
          Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x)
        =ᵐ[riemannianVolumeMeasure I M g] (fun _ : M => (0 : E)) := by
      rw [h0]
      filter_upwards [Lp.coeFn_zero (E := E) (μ := riemannianVolumeMeasure I M g)
        (p := (2 : ℝ≥0∞))] with x hx
      exact hx
    filter_upwards [hzero_fn] with x hx
    rw [hx]
    -- g.inner x 0 v = 0 by linearity.
    rw [show (0 : E) = (0 : TangentSpace I x) from rfl,
      map_zero, ContinuousLinearMap.zero_apply]
  rw [integral_congr_ae h_ae]
  simp

/-- The Dirichlet form vanishes on the zero element (right slot). -/
theorem dirichletForm_zero_right (g : SmoothRiemannianMetric I M)
    (u : H1Intrinsic (I := I) (M := M) g) :
    dirichletForm (I := I) (M := M) g u 0 = 0 := by
  rw [dirichletForm_symm (I := I) (M := M) g u 0]
  exact dirichletForm_zero_left (I := I) (M := M) g u

/-! ## The shifted form -/

/-- The shifted form `B(u, v) := Q(u, v) + ⟨toLp u, toLp v⟩_{L²}`. The L²
inner product term `⟨toLp u, toLp v⟩_{L²}` is realized as a Bochner
integral of `u · v`. -/
def shiftedForm (g : SmoothRiemannianMetric I M)
    (u v : H1Intrinsic (I := I) (M := M) g) : ℝ :=
  dirichletForm (I := I) (M := M) g u v +
    ∫ x : M, ((toLp (I := I) (M := M) g u : M → ℝ) x) *
      ((toLp (I := I) (M := M) g v : M → ℝ) x)
    ∂(riemannianVolumeMeasure I M g)

/-- Symmetry of the shifted form. -/
theorem shiftedForm_symm (g : SmoothRiemannianMetric I M)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    shiftedForm (I := I) (M := M) g u v =
      shiftedForm (I := I) (M := M) g v u := by
  unfold shiftedForm
  rw [dirichletForm_symm (I := I) (M := M) g u v]
  congr 1
  refine integral_congr_ae ?_
  refine Filter.Eventually.of_forall (fun x => mul_comm _ _)

/-- The shifted form is non-negative on the diagonal. -/
theorem shiftedForm_self_nonneg (g : SmoothRiemannianMetric I M)
    (u : H1Intrinsic (I := I) (M := M) g) :
    0 ≤ shiftedForm (I := I) (M := M) g u u := by
  unfold shiftedForm
  refine add_nonneg (dirichletForm_self_nonneg (I := I) (M := M) g u) ?_
  apply integral_nonneg
  intro x
  exact mul_self_nonneg _

/-- The shifted form vanishes on the zero element (left slot). -/
theorem shiftedForm_zero_left (g : SmoothRiemannianMetric I M)
    (u : H1Intrinsic (I := I) (M := M) g) :
    shiftedForm (I := I) (M := M) g 0 u = 0 := by
  unfold shiftedForm
  rw [dirichletForm_zero_left (I := I) (M := M) g u]
  rw [zero_add]
  -- toLp 0 = 0 → (toLp 0 : M → ℝ) =ᵐ 0 → integral of 0 * v = 0.
  have hzero : (toLp (I := I) (M := M) g (0 : H1Intrinsic (I := I) (M := M) g) :
      Lp ℝ 2 (riemannianVolumeMeasure I M g)) = 0 := by
    rw [(toLp (I := I) (M := M) g).map_zero]
  have h_ae : (fun x : M => ((toLp g (0 : H1Intrinsic g) : M → ℝ) x) *
      ((toLp g u : M → ℝ) x)) =ᵐ[riemannianVolumeMeasure I M g]
      (fun _ : M => (0 : ℝ)) := by
    have hzero_fn : (fun x : M => ((toLp g (0 : H1Intrinsic g) :
          Lp ℝ 2 (riemannianVolumeMeasure I M g)) : M → ℝ) x)
        =ᵐ[riemannianVolumeMeasure I M g] (fun _ : M => (0 : ℝ)) := by
      rw [hzero]
      filter_upwards [Lp.coeFn_zero (E := ℝ) (μ := riemannianVolumeMeasure I M g)
        (p := (2 : ℝ≥0∞))] with x hx
      exact hx
    filter_upwards [hzero_fn] with x hx
    rw [hx, zero_mul]
  rw [integral_congr_ae h_ae]
  simp

/-- The shifted form vanishes on the zero element (right slot). -/
theorem shiftedForm_zero_right (g : SmoothRiemannianMetric I M)
    (u : H1Intrinsic (I := I) (M := M) g) :
    shiftedForm (I := I) (M := M) g u 0 = 0 := by
  rw [shiftedForm_symm (I := I) (M := M) g u 0]
  exact shiftedForm_zero_left (I := I) (M := M) g u

end H1Intrinsic

end Laplacian
end Analysis
end DifferentialGeometry

end
