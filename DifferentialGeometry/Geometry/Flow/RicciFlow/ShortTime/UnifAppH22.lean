import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H1H2AppCcRS
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifGridRS

/-!
# Class-first mixed H2 application estimate

This module turns the class-uniform order-two mixed product grid into the
dimension-three `H2 × H2 → H2` application estimate used by the low-regularity
Ricci--DeTurck coefficient packets.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

private lemma triGrid_le
    (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    {i : ℕ} (hi : i < 3) :
    (∑ n ∈ Finset.range (i + 1), a n *
        ∑ l ∈ Finset.range (i + 1 - n), b l) ≤
      ∑ n ∈ Finset.range 3, a n *
        ∑ l ∈ Finset.range (3 - n), b l := by
  have hi3 : i + 1 ≤ 3 := by omega
  calc
    (∑ n ∈ Finset.range (i + 1), a n *
        ∑ l ∈ Finset.range (i + 1 - n), b l) ≤
        ∑ n ∈ Finset.range (i + 1), a n *
          ∑ l ∈ Finset.range (3 - n), b l := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_left _ (ha n)
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega)) (fun l _ _ => hb l)
    _ ≤ ∑ n ∈ Finset.range 3, a n *
        ∑ l ∈ Finset.range (3 - n), b l := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono hi3) (fun n _ _ =>
          mul_nonneg (ha n) (Finset.sum_nonneg (fun l _ => hb l)))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **Dimension-three class-first mixed `H2` application estimate.**

For arbitrary mixed valences, the full order-two jet of an operator-field
application is controlled by the product of the two input order-two jet
radii.  The constant is selected before the class metric varies, and the
public interface uses only metric jets of orders one and two. -/
theorem appRS_h22_unif
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
        ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r) (A B : ℝ),
          0 ≤ A → 0 ≤ B →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) ≤ A ^ 2 →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2) ≤ B ^ 2 →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g p c j
              (appCcRS (I := I) (M := M) g p r c Φ W)‖ ^ 2) ≤
            (C * A * B) ^ 2 := by
  classical
  obtain ⟨Cg, hCg, hgrid⟩ :=
    DifferentialGeometry.PDE.RicciFlow.grid_rs_unif
      (I := I) (M := M) hDim gBase hΛ r p c r
  let D : ℝ := ∑ i ∈ Finset.range 3, appCcGdiag (E := E) i
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact Finset.sum_nonneg (fun i _ => appCcGdiag_nonneg (E := E) i)
  let K : ℝ := D * Cg
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg hD hCg
  let C : ℝ := Real.sqrt K
  refine ⟨C, Real.sqrt_nonneg _, ?_⟩
  intro g hEq hjet1 hjet2 Φ W A B hA hB hΦ hW
  let grid : M → ℝ := fun x =>
    ∑ n ∈ Finset.range 3,
      riemannianFiberNormSq (I := I) (M := M) g r (c + n) x
          ((iteratedCovGrad (I := I) g r c n Φ).toSection x) *
        ∑ l ∈ Finset.range (3 - n),
          riemannianFiberNormSq (I := I) (M := M) g p (r + l) x
            ((iteratedCovGrad (I := I) g p r l W).toSection x)
  obtain ⟨hgridInt, hgridBd⟩ :=
    hgrid g hEq hjet1 hjet2 Φ W A B hA hB hΦ hW
  have hgridInt' : Integrable grid
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    simpa only [grid] using hgridInt
  have hterm : ∀ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g p c i
          (appCcRS (I := I) (M := M) g p r c Φ W)‖ ^ 2 ≤
        appCcGdiag (E := E) i *
          ∫ x, grid x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro i hi
    have hpoint : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g p (c + i) x
            ((iteratedCovGrad (I := I) g p c i
              (appCcRS (I := I) (M := M) g p r c Φ W)).toSection x) ≤
          appCcGdiag (E := E) i * grid x := by
      intro x
      refine (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
        (I := I) (M := M) g i p r c Φ W x).trans ?_
      apply mul_le_mul_of_nonneg_left _ (appCcGdiag_nonneg (E := E) i)
      simpa only [grid] using
        (triGrid_le
          (fun n => riemannianFiberNormSq (I := I) (M := M) g r (c + n) x
            ((iteratedCovGrad (I := I) g r c n Φ).toSection x))
          (fun l => riemannianFiberNormSq (I := I) (M := M) g p (r + l) x
            ((iteratedCovGrad (I := I) g p r l W).toSection x))
          (fun n => riemannianFiberNormSq_nonneg
            (I := I) (M := M) g r (c + n) x _)
          (fun l => riemannianFiberNormSq_nonneg
            (I := I) (M := M) g p (r + l) x _)
          (Finset.mem_range.mp hi))
    have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g p (c + i)
      (iteratedCovGrad (I := I) g p c i
        (appCcRS (I := I) (M := M) g p r c Φ W))
      (fun x => appCcGdiag (E := E) i * grid x)
      (hgridInt'.const_mul (appCcGdiag (E := E) i)) hpoint
    calc
      _ ≤ ∫ x, appCcGdiag (E := E) i * grid x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := hkey
      _ = appCcGdiag (E := E) i *
          ∫ x, grid x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        rw [MeasureTheory.integral_const_mul]
  calc
    (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g p c i
          (appCcRS (I := I) (M := M) g p r c Φ W)‖ ^ 2) ≤
        ∑ i ∈ Finset.range 3, appCcGdiag (E := E) i *
          ∫ x, grid x ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      Finset.sum_le_sum hterm
    _ = D * ∫ x, grid x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      dsimp only [D]
      rw [Finset.sum_mul]
    _ ≤ D * (Cg * A ^ 2 * B ^ 2) :=
      mul_le_mul_of_nonneg_left (by simpa only [grid] using hgridBd) hD
    _ = K * A ^ 2 * B ^ 2 := by
      dsimp only [K]
      ring
    _ = (C * A * B) ^ 2 := by
      rw [mul_pow, mul_pow, show C ^ 2 = K by
        simp only [C, Real.sq_sqrt hK]]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
