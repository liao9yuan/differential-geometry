import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Geometry.Curvature.RealizedFamCurvatureJetBound
import DifferentialGeometry.Geometry.Curvature.PerturbedRiemannOpDifferenceBound
import DifferentialGeometry.Geometry.Curvature.CovDerivConnDiffQuadraticBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.InverseMetricPerturbationFibreBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Sobolev.Embedding.ConvexPerturbationPointwiseC2
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FiberNormSubadditivity

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private noncomputable def fiveSlotCometricCoeff (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) : ℝ :=
  g₀.inner x
    (inverseMetricSharpFib (I := I) g₁ x
      (g0FlatCLM (I := I) g₀ x (smoothOrthoFrame (I := I) g₀ x a x)))
    (smoothOrthoFrame (I := I) g₀ x b x)

private noncomputable def fiveSlotEvalCLM (x : M) (u : Fin 3 → E) :
    Tensor0SSpace 3 I x →L[ℝ] ℝ :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 => E) ℝ u).comp
    (Tensor0SSpace.toModelL 3 x)

private lemma fiveSlotEvalCLM_apply (x : M) (u : Fin 3 → E) (D : Tensor0SSpace 3 I x) :
    fiveSlotEvalCLM (I := I) x u D = Tensor0SSpace.toModel D u := rfl

private noncomputable def fiveSlotKernelBilin (g₀ : SmoothRiemannianMetric I M) (x : M)
    (c d : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  ((g₀.inner x).flip (smoothOrthoFrame (I := I) g₀ x c x)).smulRight
    ((g₀.inner x).flip (smoothOrthoFrame (I := I) g₀ x d x))

private lemma fiveSlotKernelBilin_apply (g₀ : SmoothRiemannianMetric I M) (x : M)
    (c d : Fin (Module.finrank ℝ E)) (v0 v1 : TangentSpace I x) :
    fiveSlotKernelBilin (I := I) g₀ x c d v0 v1 =
      g₀.inner x v0 (smoothOrthoFrame (I := I) g₀ x c x) *
        g₀.inner x v1 (smoothOrthoFrame (I := I) g₀ x d x) := by
  rw [fiveSlotKernelBilin, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]

private noncomputable def fiveSlotTriple (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b c d : Fin (Module.finrank ℝ E)) (call : Fin 4) (contrib : Fin 5) : Fin 3 → E :=
  let va := smoothOrthoFrame (I := I) g₀ x a x
  let vb := smoothOrthoFrame (I := I) g₀ x b x
  let vc := smoothOrthoFrame (I := I) g₀ x c x
  let vd := smoothOrthoFrame (I := I) g₀ x d x
  let args : Fin 4 →
      TangentSpace I x × TangentSpace I x × TangentSpace I x × TangentSpace I x :=
    ![(va, vc, vb, vd), (va, vd, vb, vc), (va, vb, vc, vd), (vc, vd, va, vb)]
  let α := (args call).1
  let β := (args call).2.1
  let γ := (args call).2.2.1
  let δ := (args call).2.2.2
  let cd : TangentSpace I x → TangentSpace I x → TangentSpace I x :=
    fun p q => PDE.DeTurck.connDiff (I := I) g₁ g₀ x p q
  (![ ![(α : E), (cd β γ : E), (δ : E)],
      ![(α : E), (γ : E), (cd β δ : E)],
      ![(cd α β : E), (γ : E), (δ : E)],
      ![(β : E), (cd α γ : E), (δ : E)],
      ![(β : E), (γ : E), (cd α δ : E)] ] : Fin 5 → Fin 3 → E) contrib

private def fiveSlotSign (call : Fin 4) : ℝ := if (call : ℕ) < 2 then 1 else -1

private noncomputable def fiveSlotAtom (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b c d : Fin (Module.finrank ℝ E)) (call : Fin 4) (contrib : Fin 5) :
    Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (((-(1 : ℝ) / 2) * fiveSlotCometricCoeff (I := I) g₀ g₁ x a b * fiveSlotSign call) •
      fiveSlotEvalCLM (I := I) x
        (fiveSlotTriple (I := I) g₀ g₁ x a b c d call contrib)).smulRight
    (Tensor0SSpace.ofModel (I := I) (x := x)
      (bilinFormToModel E (fiveSlotKernelBilin (I := I) g₀ x c d)))

set_option linter.unusedVariables false in
def arm1FiveSlotFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x :=
  ∑ i : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E) × Fin 4 × Fin 5,
    fiveSlotAtom (I := I) g₀ g₁ x i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2

private lemma fiveSlotAtom_component (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b c d : Fin (Module.finrank ℝ E)) (call : Fin 4) (contrib : Fin 5)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin 3 → Fin n) (J : Fin 2 → Fin n) :
    Tensor0SSpace.toModel
        (fiveSlotAtom (I := I) g₀ g₁ x a b c d call contrib
          (coframeS (I := I) (M := M) g₀ x 3 e K))
        (fun j => e (J j)) =
      ((-(1 : ℝ) / 2) * fiveSlotCometricCoeff (I := I) g₀ g₁ x a b * fiveSlotSign call) *
          Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 3 e K)
            (fiveSlotTriple (I := I) g₀ g₁ x a b c d call contrib) *
        fiveSlotKernelBilin (I := I) g₀ x c d (e (J 0)) (e (J 1)) := by
  simp only [fiveSlotAtom, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    fiveSlotEvalCLM_apply, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul, Tensor0SSpace.toModel_ofModel, bilinFormToModel_apply]
  rfl

set_option linter.unusedVariables false in
theorem arm1FiveSlotFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) x
        (arm1FiveSlotFib (I := I) g₀ g₁ x)) :=
  sorry

def arm1FiveSlotCoeff (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 3 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 3 2 I x from arm1FiveSlotFib (I := I) g₀ g₁ x)
      contMDiff_toFun := arm1FiveSlotFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] theorem arm1FiveSlotCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (arm1FiveSlotCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 3 2 I x from arm1FiveSlotFib (I := I) g₀ g₁ x) := rfl

def arm1FiveSlotField (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 3 2 :=
  arm1FiveSlotCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)

private lemma fiberNormSqComponent_arm1FiveSlotFib
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) {n : ℕ}
    (e : Fin n → TangentSpace I x) (K : Fin 3 → Fin n) (J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 3 2
        (show Tensor0SBundle.TensorRSSpace 3 2 I x from arm1FiveSlotFib (I := I) g₀ g₁ x)
        n e K J =
      ∑ i : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
            Fin (Module.finrank ℝ E) × Fin 4 × Fin 5,
        ((-(1 : ℝ) / 2) * fiveSlotCometricCoeff (I := I) g₀ g₁ x i.1 i.2.1 *
              fiveSlotSign i.2.2.2.2.1) *
            Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 3 e K)
              (fiveSlotTriple (I := I) g₀ g₁ x i.1 i.2.1 i.2.2.1 i.2.2.2.1
                i.2.2.2.2.1 i.2.2.2.2.2) *
          fiveSlotKernelBilin (I := I) g₀ x i.2.2.1 i.2.2.2.1 (e (J 0)) (e (J 1)) := by
  classical
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 3 2
      (show Tensor0SBundle.TensorRSSpace 3 2 I x from arm1FiveSlotFib (I := I) g₀ g₁ x) n e K J =
      Tensor0SSpace.toModel
        ((arm1FiveSlotFib (I := I) g₀ g₁ x) (coframeS (I := I) (M := M) g₀ x 3 e K))
        (fun j => e (J j)) := rfl
  rw [hcomp, arm1FiveSlotFib, ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Tensor0SSpace.toModelL_apply]
  exact fiveSlotAtom_component (I := I) g₀ g₁ x i.1 i.2.1 i.2.2.1 i.2.2.2.1
    i.2.2.2.2.1 i.2.2.2.2.2 e K J

set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem rfns_arm1FiveSlotFib_le_of_lt_one
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (P : SmoothCcTensor g₀ 0 2)
      (h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
      {δ : ℝ} (hδ : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
      (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
      (x : M),
      letI : Bundle.RiemannianBundle (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
          (show Tensor0SBundle.TensorRSSpace 3 2 I x from arm1FiveSlotFib (I := I) g₀ g₁ x) ≤
        C * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 := by
  classical
  have h1δ : (0 : ℝ) < 1 - δ₀ := by linarith
  have hinv_pos : (0 : ℝ) < 1 / (1 - δ₀) := div_pos one_pos h1δ
  obtain ⟨C₀, hC₀0, hpw⟩ :=
    connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one (I := I) (M := M) g₀ hδ₀0 hδ₀
  set Mc : ℝ := ((Module.finrank ℝ E : ℝ) ^ 4 * 20) * ((1 / 2) * (1 / (1 - δ₀)) * C₀) with hMc
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 5 * Mc ^ 2,
    mul_nonneg (by positivity) (sq_nonneg _), ?_⟩
  intro g₁ P h δ hδ hδ0 hbound x
  letI instTens : Bundle.RiemannianBundle (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum_rfns⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ hδ₀
  have h1δ' : (0 : ℝ) < 1 - δ := by linarith
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG_def
  have hG_nn : 0 ≤ G := norm_nonneg _
  have hframe1 : ∀ z : Fin (Module.finrank ℝ E),
      g₀.inner x (smoothOrthoFrame (I := I) g₀ x z x)
        (smoothOrthoFrame (I := I) g₀ x z x) = 1 := by
    intro z; rw [smoothOrthoFrame_orthonormal_at_center]; simp
  have he1 : ∀ i : Fin n, g₀.inner x (e i) (e i) = 1 := by
    intro i; rw [horth i i]; simp
  have hsign : ∀ call : Fin 4, |fiveSlotSign call| = 1 := by
    intro call; unfold fiveSlotSign; split_ifs <;> norm_num
  have hcometric : ∀ a b : Fin (Module.finrank ℝ E),
      |fiveSlotCometricCoeff (I := I) g₀ g₁ x a b| ≤ 1 / (1 - δ₀) := by
    intro a b
    rw [fiveSlotCometricCoeff]
    have hcs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x
      (inverseMetricSharpFib (I := I) g₁ x
        (g0FlatCLM (I := I) g₀ x (smoothOrthoFrame (I := I) g₀ x a x)))
      (smoothOrthoFrame (I := I) g₀ x b x)
    rw [hframe1 b, Real.sqrt_one, mul_one] at hcs
    have hsharp := sqrt_inner_inverseMetricSharpFib_g0FlatCLM_le (I := I) (M := M) g₀ g₁
      (fun y => ccTensorBilinSymm (I := I) g₀ P y) h hδ_lt hδ0 hbound x
      (smoothOrthoFrame (I := I) g₀ x a x)
    rw [hframe1 a, Real.sqrt_one, mul_one] at hsharp
    refine le_trans hcs (le_trans hsharp ?_)
    exact one_div_le_one_div_of_le h1δ (by linarith)
  have hsqrt_cd : ∀ z w : Fin (Module.finrank ℝ E),
      Real.sqrt (g₀.inner x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (smoothOrthoFrame (I := I) g₀ x z x)
          (smoothOrthoFrame (I := I) g₀ x w x))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (smoothOrthoFrame (I := I) g₀ x z x)
          (smoothOrthoFrame (I := I) g₀ x w x))) ≤ C₀ * G := by
    intro z w
    have ht := hpw g₁ P h hδ hδ0 hbound x (smoothOrthoFrame (I := I) g₀ x z x)
      (smoothOrthoFrame (I := I) g₀ x w x)
    rw [hframe1 z, hframe1 w, Real.sqrt_one, mul_one, mul_one, ← hG_def] at ht
    exact ht
  have key3 : ∀ (K : Fin 3 → Fin n) (u : Fin 3 → E),
      |Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 3 e K) u| ≤
        Real.sqrt (g₀.inner x (u 0) (u 0)) * Real.sqrt (g₀.inner x (u 1) (u 1)) *
          Real.sqrt (g₀.inner x (u 2) (u 2)) := by
    intro K u
    rw [show Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 3 e K) u =
        coframeS (I := I) (M := M) g₀ x 3 e K u from rfl, coframeS_apply,
      Fin.prod_univ_three, abs_mul, abs_mul]
    have b0 := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (e (K 0)) (u 0)
    have b1 := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (e (K 1)) (u 1)
    have b2 := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (e (K 2)) (u 2)
    rw [he1 (K 0), Real.sqrt_one, one_mul] at b0
    rw [he1 (K 1), Real.sqrt_one, one_mul] at b1
    rw [he1 (K 2), Real.sqrt_one, one_mul] at b2
    exact mul_le_mul (mul_le_mul b0 b1 (abs_nonneg _) (Real.sqrt_nonneg _)) b2 (abs_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have htriple : ∀ (K : Fin 3 → Fin n) (a b c d : Fin (Module.finrank ℝ E))
      (call : Fin 4) (contrib : Fin 5),
      |Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 3 e K)
          (fiveSlotTriple (I := I) g₀ g₁ x a b c d call contrib)| ≤ C₀ * G := by
    intro K a b c d call contrib
    refine le_trans (key3 K (fiveSlotTriple (I := I) g₀ g₁ x a b c d call contrib)) ?_
    fin_cases call <;> fin_cases contrib <;>
      simp only [fiveSlotTriple, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta,
        Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero, hframe1, Real.sqrt_one,
        one_mul, mul_one] <;>
      exact hsqrt_cd _ _
  have heach_abs : ∀ (K : Fin 3 → Fin n) (J : Fin 2 → Fin n),
      |fiberNormSqComponent (I := I) (M := M) g₀ x 3 2
          (show Tensor0SBundle.TensorRSSpace 3 2 I x from arm1FiveSlotFib (I := I) g₀ g₁ x)
          n e K J| ≤ Mc * G := by
    intro K J
    rw [fiberNormSqComponent_arm1FiveSlotFib (I := I) g₀ g₁ x e K J]
    have hkernel : ∀ c d : Fin (Module.finrank ℝ E),
        |fiveSlotKernelBilin (I := I) g₀ x c d (e (J 0)) (e (J 1))| ≤ 1 := by
      intro c d
      rw [fiveSlotKernelBilin_apply, abs_mul]
      have h0 := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (e (J 0))
        (smoothOrthoFrame (I := I) g₀ x c x)
      have h1 := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (e (J 1))
        (smoothOrthoFrame (I := I) g₀ x d x)
      rw [he1 (J 0), hframe1 c, Real.sqrt_one, mul_one] at h0
      rw [he1 (J 1), hframe1 d, Real.sqrt_one, mul_one] at h1
      calc |g₀.inner x (e (J 0)) (smoothOrthoFrame (I := I) g₀ x c x)| *
              |g₀.inner x (e (J 1)) (smoothOrthoFrame (I := I) g₀ x d x)|
          ≤ 1 * 1 := mul_le_mul h0 h1 (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hsummand_bd : ∀ i : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × Fin 4 × Fin 5,
        |((-(1 : ℝ) / 2) * fiveSlotCometricCoeff (I := I) g₀ g₁ x i.1 i.2.1 *
              fiveSlotSign i.2.2.2.2.1) *
            Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 3 e K)
              (fiveSlotTriple (I := I) g₀ g₁ x i.1 i.2.1 i.2.2.1 i.2.2.2.1
                i.2.2.2.2.1 i.2.2.2.2.2) *
            fiveSlotKernelBilin (I := I) g₀ x i.2.2.1 i.2.2.2.1 (e (J 0)) (e (J 1))| ≤
          (1 / 2) * (1 / (1 - δ₀)) * C₀ * G := by
      intro i
      obtain ⟨a, b, c, d, call, contrib⟩ := i
      rw [abs_mul, abs_mul]
      have hX : |(-(1 : ℝ) / 2) * fiveSlotCometricCoeff (I := I) g₀ g₁ x a b *
          fiveSlotSign call| ≤ (1 / 2) * (1 / (1 - δ₀)) := by
        rw [abs_mul, abs_mul, hsign call, mul_one,
          show |(-(1 : ℝ) / 2)| = 1 / 2 from by norm_num]
        exact mul_le_mul_of_nonneg_left (hcometric a b) (by norm_num)
      have hX_nn : (0 : ℝ) ≤ (1 / 2) * (1 / (1 - δ₀)) :=
        mul_nonneg (by norm_num) (le_of_lt hinv_pos)
      calc |(-(1 : ℝ) / 2) * fiveSlotCometricCoeff (I := I) g₀ g₁ x a b *
                fiveSlotSign call| *
              |Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 3 e K)
                (fiveSlotTriple (I := I) g₀ g₁ x a b c d call contrib)| *
              |fiveSlotKernelBilin (I := I) g₀ x c d (e (J 0)) (e (J 1))|
          ≤ (1 / 2) * (1 / (1 - δ₀)) * (C₀ * G) * 1 :=
            mul_le_mul
              (mul_le_mul hX (htriple K a b c d call contrib) (abs_nonneg _) hX_nn)
              (hkernel c d) (abs_nonneg _)
              (mul_nonneg hX_nn (mul_nonneg hC₀0 hG_nn))
        _ = (1 / 2) * (1 / (1 - δ₀)) * C₀ * G := by ring
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun i _ => hsummand_bd i)) ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hMc]
    have hcardT : (Fintype.card (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × Fin 4 × Fin 5) : ℝ) =
        (Module.finrank ℝ E : ℝ) ^ 4 * 20 := by
      simp only [Fintype.card_prod, Fintype.card_fin]; push_cast; ring
    rw [hcardT]; exact le_of_eq (by ring)
  have heach : ∀ (K : Fin 3 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 3 2
          (show Tensor0SBundle.TensorRSSpace 3 2 I x from arm1FiveSlotFib (I := I) g₀ g₁ x)
          n e K J) ^ 2 ≤ (Mc * G) ^ 2 := by
    intro K J
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (heach_abs K J) 2
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 3 2 x
    (show Tensor0SBundle.TensorRSSpace 3 2 I x from arm1FiveSlotFib (I := I) g₀ g₁ x)
    e bse hnE hbse horth]
  calc ∑ K : Fin 3 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 3 2
          (show Tensor0SBundle.TensorRSSpace 3 2 I x from arm1FiveSlotFib (I := I) g₀ g₁ x)
          n e K J) ^ 2
      ≤ ∑ K : Fin 3 → Fin n, ∑ J : Fin 2 → Fin n, (Mc * G) ^ 2 :=
        Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => heach K J))
    _ = (Fintype.card (Fin 3 → Fin n) : ℝ) * (Fintype.card (Fin 2 → Fin n) : ℝ) *
          (Mc * G) ^ 2 := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]; ring
    _ = (Module.finrank ℝ E : ℝ) ^ 5 * Mc ^ 2 * G ^ 2 := by
        have hcard : (Fintype.card (Fin 3 → Fin n) : ℝ) * (Fintype.card (Fin 2 → Fin n) : ℝ) =
            (n : ℝ) ^ 5 := by
          simp only [Fintype.card_fun, Fintype.card_fin]
          push_cast; ring
        rw [hcard, ← hnE]; ring

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_arm1FiveSlotField_realizedFam_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((arm1FiveSlotField (I := I) g₀ T T' hδ hδ' s).toSection x) ≤ Λ := by
  classical
  obtain ⟨C, hC0, hbnd⟩ :=
    rfns_arm1FiveSlotFib_le_of_lt_one (I := I) (M := M) g₀
      (le_max_right δ₀ 0) (max_lt hδ₀ (by norm_num))
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    exists_Csob_convexPerturbation_pointwise_C2_le (I := I) (M := M) g₀ a ha_super
  refine ⟨C * (Csob * R) ^ 2, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  letI instTens : Bundle.RiemannianBundle (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  set m : ℝ := max δ₀ 0 with hm_def
  have hm0 : 0 ≤ m := le_max_right _ _
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w :=
    fun y v w => realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hs_mem y v w
  have hδs_raw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s
  obtain ⟨hs0, hs1⟩ := hs
  have habs_eq : |1 - s| * δ' + |s| * δ = (1 - s) * δ' + s * δ := by
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s), abs_of_nonneg hs0]
  have hsmall_le : (1 - s) * δ' + s * δ ≤ m := by
    have h1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le (by linarith)
    have h2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
    have hδ₀_le : δ₀ ≤ m := le_max_left _ _
    nlinarith [h1, h2, hδ₀_le]
  have hδs : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s)) m := by
    intro y v w
    refine le_trans (hδs_raw y v w) ?_
    have hprod : 0 ≤ Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hle' : |1 - s| * δ' + |s| * δ ≤ m := by rw [habs_eq]; exact hsmall_le
    nlinarith [hle', hprod]
  have hmain := hbnd (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) htie (le_of_eq hm_def.symm) hm0 hδs x
  rw [show (arm1FiveSlotField (I := I) g₀ T T' hδ hδ' s).toSection x =
      (show Tensor0SBundle.TensorRSSpace 3 2 I x from
        arm1FiveSlotFib (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) x) from rfl]
  refine le_trans hmain ?_
  have hG_le : ‖((iteratedCovGrad (I := I) g₀ 0 2 1
        (convexPerturbation (I := I) g₀ T T' s)).toSection x :
        Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ≤ Csob * R := by
    have hCsob_sum := hCsob T T' hR hTball hT'ball s ⟨hs0, hs1⟩ x
    have hterms : ∀ k ∈ Finset.range 3, 0 ≤
        (letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + k) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
        ‖(iteratedCovGrad (I := I) g₀ 0 2 k
            (convexPerturbation (I := I) g₀ T T' s)).toSection x‖) := by
      intro k _
      letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + k) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
      exact norm_nonneg _
    exact le_trans (Finset.single_le_sum hterms
      (show (1 : ℕ) ∈ Finset.range 3 from Finset.mem_range.mpr (by norm_num))) hCsob_sum
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hG_le 2) hC0

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
