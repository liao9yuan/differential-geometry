import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingSharpC0JetSum
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge

/-!
# Three-dimensional H2 pointwise control

This file packages the sharp covariant-jet Sobolev embedding in the intrinsic
spectral norm used by the low-regularity Ricci--DeTurck theory.
-/

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- In dimension three, the pointwise squared fibre norm of a smooth
covariant tensor is controlled by its intrinsic spectral `H2` norm. -/
theorem hs2_fiber_sq
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : SmoothCcTensor g 0 s) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (T.toSection x) ≤
        C ^ 2 * ‖ccTensorToHs (I := I) (M := M) g s (2 : ℝ) T‖ ^ 2 := by
  classical
  obtain ⟨Cpt, hCpt, hpt⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g 0 s
  obtain ⟨Chs, hChs, hhs⟩ := hsJet_le (I := I) (M := M) g s 2
  refine ⟨Cpt * Chs, mul_nonneg hCpt hChs, ?_⟩
  intro T x
  have hrange : Finset.range (Module.finrank ℝ E / 2 + 2) = Finset.range 3 := by
    rw [hDim]
  have hpt' := hpt T x
  rw [hrange] at hpt'
  have hsq :
      ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 s j T‖ ^ 2 ≤
        (∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 s j T‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg _)
  have hsum :
      ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 s j T‖ ≤
        Chs * ‖ccTensorToHs (I := I) (M := M) g s (2 : ℝ) T‖ := by
    simpa using hhs T
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 s x (T.toSection x)
        ≤ Cpt ^ 2 * ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 s j T‖ ^ 2 := hpt'
    _ ≤ Cpt ^ 2 *
          (∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 s j T‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg Cpt)
    _ ≤ Cpt ^ 2 *
          (Chs * ‖ccTensorToHs (I := I) (M := M) g s (2 : ℝ) T‖) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀
          (Finset.sum_nonneg (fun j _ => norm_nonneg _)) hsum 2)
        (sq_nonneg Cpt)
    _ = (Cpt * Chs) ^ 2 *
          ‖ccTensorToHs (I := I) (M := M) g s (2 : ℝ) T‖ ^ 2 := by
      ring

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- In dimension three, the intrinsic spectral `H2` norm supplies the
fibrewise operator bound needed to realize a small metric perturbation. -/
theorem hs2_op_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : SmoothCcTensor g 0 2,
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g T)
        (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖) := by
  classical
  obtain ⟨C0, hC0, hpt⟩ := hs2_fiber_sq (I := I) (M := M) hDim g 2
  refine ⟨C0 + 1, by linarith, ?_⟩
  intro T
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  have hN : 0 ≤ N := norm_nonneg _
  have hC : 0 ≤ C0 + 1 := by linarith
  have hpt' : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤
        ((C0 + 1) * N) ^ 2 := by
    intro x
    calc
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x)
          ≤ C0 ^ 2 * N ^ 2 := hpt T x
      _ ≤ (C0 + 1) ^ 2 * N ^ 2 :=
        mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg N)
      _ = ((C0 + 1) * N) ^ 2 := by ring
  intro x v w
  letI instTens : Bundle.RiemannianBundle
      (fun b : M => Tensor0SBundle.TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 2
  letI instNormed : ∀ b : M,
      NormedAddCommGroup (Tensor0SBundle.TensorRSSpace 0 2 I b) :=
    fun b =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) b
  have hnorm : ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ≤
      (C0 + 1) * N := by
    rw [norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g 0 2 x (T.toSection x),
      ← riemannianFiberNormSq_eq_tensorInnerPointwise
        (I := I) (M := M) g 0 2 x (T.toSection x)]
    calc
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x))
          ≤ Real.sqrt (((C0 + 1) * N) ^ 2) := Real.sqrt_le_sqrt (hpt' x)
      _ = (C0 + 1) * N := Real.sqrt_sq (mul_nonneg hC hN)
  have hcs := ccTensorBilin_abs_le_fibreNorm_mul_sqrt
    (I := I) (M := M) g T x
  have hsv : 0 ≤ Real.sqrt (g.inner x v v) := Real.sqrt_nonneg _
  have hsw : 0 ≤ Real.sqrt (g.inner x w w) := Real.sqrt_nonneg _
  have hvw : |ccTensorBilin (I := I) g T x v w| ≤
      ((C0 + 1) * N) * Real.sqrt (g.inner x v v) *
        Real.sqrt (g.inner x w w) := by
    exact (hcs v w).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnorm hsv) hsw)
  have hwv : |ccTensorBilin (I := I) g T x w v| ≤
      ((C0 + 1) * N) * Real.sqrt (g.inner x w w) *
        Real.sqrt (g.inner x v v) := by
    exact (hcs w v).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnorm hsw) hsv)
  rw [ccTensorBilinSymm_apply]
  calc
    |(1 / 2 : ℝ) *
        (ccTensorBilin (I := I) g T x v w + ccTensorBilin (I := I) g T x w v)|
        ≤ (1 / 2 : ℝ) *
          (|ccTensorBilin (I := I) g T x v w| +
            |ccTensorBilin (I := I) g T x w v|) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) *
          (((C0 + 1) * N) * Real.sqrt (g.inner x v v) *
              Real.sqrt (g.inner x w w) +
            ((C0 + 1) * N) * Real.sqrt (g.inner x w w) *
              Real.sqrt (g.inner x v v)) :=
      mul_le_mul_of_nonneg_left (add_le_add hvw hwv) (by norm_num)
    _ = (C0 + 1) * N * Real.sqrt (g.inner x v v) *
          Real.sqrt (g.inner x w w) := by ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
