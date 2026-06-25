import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
private lemma coframeS_one_eq_g0FlatCLM (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin 1 → Fin n) :
    coframeS (I := I) (M := M) g₀ x 1 e K = g0FlatCLM (I := I) g₀ x (e (K 0)) := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply, cotangentToDual_apply,
    cotangentToDual_apply]
  rw [show coframeS (I := I) (M := M) g₀ x 1 e K (fun _ : Fin 1 => w) =
      ∏ k : Fin 1, g₀.inner x (e (K k)) w from coframeS_apply (I := I) (M := M) g₀ x 1 e K _]
  rw [Fin.prod_univ_one]
  rw [g0FlatCLM_apply, dualToCotangent_apply]
  rfl

set_option linter.unusedSectionVars false in
private lemma fiberNormSqComponent_sharpFlatEndoCc
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) {n : ℕ}
    (e : Fin n → TangentSpace I x)
    (K : Fin 1 → Fin n) (J : Fin 1 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
        ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) n e K J =
      g₀.inner x
        (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 0)))) (e (J 0)) := by
  rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
        ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) n e K J =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (sharpFlatEndoCc (I := I) g₀ g₁).toSection x)
        (coframeS (I := I) (M := M) g₀ x 1 e K))
        (fun k => e (J k)) from rfl]
  rw [coframeS_one_eq_g0FlatCLM (I := I) (M := M) g₀ x e K]
  rw [sharpFlatEndoCc_toSection]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        TensorRSSpace.ofCLM
          ((g0FlatCLM (I := I) g₀ x).comp (inverseMetricSharpFib (I := I) g₁ x)))
        (g0FlatCLM (I := I) g₀ x (e (K 0))) =
      g0FlatCLM (I := I) g₀ x
        (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 0)))) from rfl]
  rw [show (g0FlatCLM (I := I) g₀ x
        (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 0)))))
        (fun k => e (J k)) =
      cotangentToDual (I := I) (x := x)
        (g0FlatCLM (I := I) g₀ x
          (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 0)))))
        (e (J 0)) from by
    rw [cotangentToDual_apply]
    rfl]
  rw [cotangentToDual_g0FlatCLM (I := I) g₀ x
    (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 0)))) (e (J 0))]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem rfns_sharpFlatEndoCc_le_of_lt_one
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1)
    (g₁ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    (h : ∀ y v w, g₁.inner y v w =
      g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {δ : ℝ} (hδ : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
    (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) ≤
      ((Module.finrank ℝ E : ℝ)) ^ 2 * (1 / (1 - δ₀)) ^ 2 := by
  classical
  have hceil0 : 0 < 1 - δ₀ := by linarith
  have hcoeff : 0 < 1 - δ := by linarith
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  have hg₁ : ∀ (b : M) (u₁ u₂ : TangentSpace I b),
      g₁.inner b u₁ u₂ = g₀.inner b u₁ u₂ + ccTensorBilinSymm (I := I) g₀ T b u₁ u₂ :=
    fun b u₁ u₂ => h b u₁ u₂
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 1 x
    ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) e bse hnE hbse horth]
  have hinv_le : 1 / (1 - δ) ≤ 1 / (1 - δ₀) := by
    rw [div_le_div_iff₀ hcoeff hceil0]; linarith
  have hinv₀_nn : 0 ≤ 1 / (1 - δ₀) := by positivity
  have heach : ∀ (K J : Fin 1 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
        ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) n e K J) ^ 2 ≤
        (1 / (1 - δ₀)) ^ 2 := by
    intro K J
    rw [fiberNormSqComponent_sharpFlatEndoCc (I := I) (M := M) g₀ g₁ x e K J]
    set u : TangentSpace I x :=
      inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 0))) with hu_def
    have hcs := metric_inner_cauchy_schwarz_sq (I := I) (M := M) g₀ x u (e (J 0))
    have hJJ : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by rw [horth (J 0) (J 0)]; simp
    rw [hJJ, mul_one] at hcs
    have hsfib := sqrt_inner_inverseMetricSharpFib_g0FlatCLM_le
      (I := I) (M := M) g₀ g₁ (ccTensorBilinSymm (I := I) g₀ T) hg₁
      (by linarith : δ < 1) hδ0 hbound x (e (K 0))
    have hKK : g₀.inner x (e (K 0)) (e (K 0)) = 1 := by rw [horth (K 0) (K 0)]; simp
    rw [hKK, Real.sqrt_one, mul_one] at hsfib
    rw [← hu_def] at hsfib
    have huu_nn : 0 ≤ g₀.inner x u u := metric_inner_self_nonneg (I := I) (M := M) g₀ x u
    have hsqrt_eq : Real.sqrt (g₀.inner x u u) ^ 2 = g₀.inner x u u :=
      Real.sq_sqrt huu_nn
    have hsqrt_nn : 0 ≤ Real.sqrt (g₀.inner x u u) := Real.sqrt_nonneg _
    have huu_le : g₀.inner x u u ≤ (1 / (1 - δ₀)) ^ 2 := by
      rw [← hsqrt_eq]
      have hsfib' : Real.sqrt (g₀.inner x u u) ≤ 1 / (1 - δ₀) := le_trans hsfib hinv_le
      have := mul_self_le_mul_self hsqrt_nn hsfib'
      nlinarith [this, hsfib', hinv₀_nn]
    calc (g₀.inner x u (e (J 0))) ^ 2
        ≤ g₀.inner x u u := hcs
      _ ≤ (1 / (1 - δ₀)) ^ 2 := huu_le
  calc ∑ K : Fin 1 → Fin n, ∑ J : Fin 1 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
          ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) n e K J) ^ 2
      ≤ ∑ K : Fin 1 → Fin n, ∑ J : Fin 1 → Fin n, (1 / (1 - δ₀)) ^ 2 :=
        Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => heach K J))
    _ = (Fintype.card (Fin 1 → Fin n) : ℝ) * (Fintype.card (Fin 1 → Fin n) : ℝ) *
        (1 / (1 - δ₀)) ^ 2 := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
        ring
    _ = ((Module.finrank ℝ E : ℝ)) ^ 2 * (1 / (1 - δ₀)) ^ 2 := by
        simp only [Fintype.card_fun, Fintype.card_fin, pow_one]
        rw [← hnE]
        ring

set_option linter.unusedSectionVars false in
private lemma g0_inner_sharpFlatRaiseEndo_eq_g1
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    g₀.inner x (sharpFlatRaiseEndo (I := I) g₀ g₁ x v) w = g₁.inner x v w := by
  rw [sharpFlatRaiseEndo_apply]
  rw [inverseMetricSharpFib_inner (I := I) g₀ x (g0FlatCLM (I := I) g₁ x v) w]
  rw [cotangentToDualLinear_apply]
  rw [cotangentToDual_g0FlatCLM (I := I) g₁ x v w]

set_option linter.unusedSectionVars false in
private lemma g1_self_upper_bound
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (h : ∀ y v w, g₁.inner y v w =
      g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {δ : ℝ} (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) (v : TangentSpace I x) :
    g₁.inner x v v ≤ (1 + δ) * g₀.inner x v v := by
  have hgate := hbound x v v
  have hnn : 0 ≤ g₀.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hsq : Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) = g₀.inner x v v := by
    rw [← Real.sqrt_mul hnn, Real.sqrt_mul_self hnn]
  have habs : |ccTensorBilinSymm (I := I) g₀ T x v v| ≤ δ * g₀.inner x v v := by
    calc |ccTensorBilinSymm (I := I) g₀ T x v v|
        ≤ δ * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) := hgate
      _ = δ * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) := by ring
      _ = δ * g₀.inner x v v := by rw [hsq]
  have hle : ccTensorBilinSymm (I := I) g₀ T x v v ≤ δ * g₀.inner x v v :=
    le_trans (le_abs_self _) habs
  rw [h x v v]
  nlinarith [hle]

set_option linter.unusedSectionVars false in
theorem sqrt_inner_sharpFlatRaiseEndo_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (h : ∀ y v w, g₁.inner y v w =
      g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {δ : ℝ} (hδ_nn : 0 ≤ δ)
    (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) (v : TangentSpace I x) :
    Real.sqrt (g₀.inner x (sharpFlatRaiseEndo (I := I) g₀ g₁ x v)
        (sharpFlatRaiseEndo (I := I) g₀ g₁ x v))
      ≤ (1 + δ) * Real.sqrt (g₀.inner x v v) := by
  set p : TangentSpace I x := sharpFlatRaiseEndo (I := I) g₀ g₁ x v with hp_def
  set Np : ℝ := Real.sqrt (g₀.inner x p p) with hNp_def
  set Nv : ℝ := Real.sqrt (g₀.inner x v v) with hNv_def
  have hNp_nn : 0 ≤ Np := Real.sqrt_nonneg _
  have hNv_nn : 0 ≤ Nv := Real.sqrt_nonneg _
  have hpp_nn : 0 ≤ g₀.inner x p p := metric_inner_self_nonneg (I := I) (M := M) g₀ x p
  have hvv_nn : 0 ≤ g₀.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hNp_sq : Np * Np = g₀.inner x p p := by
    rw [hNp_def, ← Real.sqrt_mul hpp_nn, Real.sqrt_mul_self hpp_nn]
  have h1delta_nn : 0 ≤ 1 + δ := by linarith
  -- g₀ p p = g₁ v p
  have hpp_eq : g₀.inner x p p = g₁.inner x v p := by
    rw [hp_def]
    rw [g0_inner_sharpFlatRaiseEndo_eq_g1 (I := I) g₀ g₁ x v p]
  -- g₁-Cauchy-Schwarz: g₁ v p ≤ √(g₁ v v) √(g₁ p p)
  have hg1cs : g₁.inner x v p ≤
      Real.sqrt (g₁.inner x v v) * Real.sqrt (g₁.inner x p p) := by
    have habs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₁ x v p
    exact le_trans (le_abs_self _) habs
  -- upper bounds g₁ a a ≤ (1+δ) g₀ a a
  have hg1vv := g1_self_upper_bound (I := I) g₀ g₁ T h hbound x v
  have hg1pp := g1_self_upper_bound (I := I) g₀ g₁ T h hbound x p
  have hg1vv_nn : 0 ≤ g₁.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₁ x v
  have hg1pp_nn : 0 ≤ g₁.inner x p p := metric_inner_self_nonneg (I := I) (M := M) g₁ x p
  have hsqrt_g1vv : Real.sqrt (g₁.inner x v v) ≤ Real.sqrt ((1 + δ) * g₀.inner x v v) :=
    Real.sqrt_le_sqrt hg1vv
  have hsqrt_g1pp : Real.sqrt (g₁.inner x p p) ≤ Real.sqrt ((1 + δ) * g₀.inner x p p) :=
    Real.sqrt_le_sqrt hg1pp
  have hsplit_vv : Real.sqrt ((1 + δ) * g₀.inner x v v) =
      Real.sqrt (1 + δ) * Nv := by
    rw [Real.sqrt_mul h1delta_nn, hNv_def]
  have hsplit_pp : Real.sqrt ((1 + δ) * g₀.inner x p p) =
      Real.sqrt (1 + δ) * Np := by
    rw [Real.sqrt_mul h1delta_nn, hNp_def]
  -- assemble: g₀ p p ≤ (√(1+δ) Nv)(√(1+δ) Np) = (1+δ) Nv Np
  have hroot_sq : Real.sqrt (1 + δ) * Real.sqrt (1 + δ) = 1 + δ := by
    rw [← Real.sqrt_mul h1delta_nn, Real.sqrt_mul_self h1delta_nn]
  have hroot_nn : 0 ≤ Real.sqrt (1 + δ) := Real.sqrt_nonneg _
  have hchain : g₀.inner x p p ≤ (1 + δ) * Nv * Np := by
    calc g₀.inner x p p = g₁.inner x v p := hpp_eq
      _ ≤ Real.sqrt (g₁.inner x v v) * Real.sqrt (g₁.inner x p p) := hg1cs
      _ ≤ (Real.sqrt (1 + δ) * Nv) * (Real.sqrt (1 + δ) * Np) := by
          rw [← hsplit_vv, ← hsplit_pp]
          exact mul_le_mul hsqrt_g1vv hsqrt_g1pp (Real.sqrt_nonneg _)
            (le_trans (Real.sqrt_nonneg _) hsqrt_g1vv)
      _ = (1 + δ) * Nv * Np := by
          rw [show (Real.sqrt (1 + δ) * Nv) * (Real.sqrt (1 + δ) * Np)
              = (Real.sqrt (1 + δ) * Real.sqrt (1 + δ)) * (Nv * Np) from by ring]
          rw [hroot_sq]; ring
  -- Np² ≤ (1+δ) Nv Np ⟹ Np ≤ (1+δ) Nv
  rw [← hNp_sq] at hchain
  rcases eq_or_lt_of_le hNp_nn with hNp0 | hNppos
  · rw [← hNp0]
    exact mul_nonneg h1delta_nn hNv_nn
  · have h2 : Np * Np ≤ ((1 + δ) * Nv) * Np := by nlinarith [hchain]
    exact le_of_mul_le_mul_right h2 hNppos

set_option linter.unusedSectionVars false in
private lemma fiberNormSqComponent_raisedKoszul
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) {n : ℕ}
    (e : Fin n → TangentSpace I x)
    (K : Fin 1 → Fin n) (J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 1 2
        ((raisedKoszul (I := I) g₀ g₁).toSection x) n e K J =
      g₀.inner x (e (K 0))
        (sharpFlatRaiseEndo (I := I) g₀ g₁ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (e (J 0)) (e (J 1)))) := by
  rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 1 2
        ((raisedKoszul (I := I) g₀ g₁).toSection x) n e K J =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          (raisedKoszul (I := I) g₀ g₁).toSection x)
        (coframeS (I := I) (M := M) g₀ x 1 e K))
        (fun k => e (J k)) from rfl]
  rw [coframeS_one_eq_g0FlatCLM (I := I) (M := M) g₀ x e K]
  rw [raisedKoszul_toSection]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        raisedKoszulFib (I := I) g₀ g₁ x) (g0FlatCLM (I := I) g₀ x (e (K 0)))
      = raisedKoszulPairing (I := I) g₀ g₁ x (g0FlatCLM (I := I) g₀ x (e (K 0))) from rfl]
  rw [show (raisedKoszulPairing (I := I) g₀ g₁ x (g0FlatCLM (I := I) g₀ x (e (K 0))))
        (fun k => e (J k))
      = (g0FlatCLM (I := I) g₀ x (e (K 0)))
          (fun _ : Fin 1 => raisedKoszulVec (I := I) g₀ g₁ x (e (J 0)) (e (J 1))) from rfl]
  rw [raisedKoszulVec_apply]
  rw [sharpFlatRaiseEndo_apply]
  rw [show (g0FlatCLM (I := I) g₀ x (e (K 0)))
        (fun _ : Fin 1 => inverseMetricSharpFib (I := I) g₀ x
          (g0FlatCLM (I := I) g₁ x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (e (J 0)) (e (J 1))))) =
      cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x (e (K 0)))
        (inverseMetricSharpFib (I := I) g₀ x
          (g0FlatCLM (I := I) g₁ x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (e (J 0)) (e (J 1)))))
      from (cotangentToDual_apply (I := I) (x := x) _ _).symm]
  rw [cotangentToDual_g0FlatCLM (I := I) g₀ x (e (K 0))]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem rfns_raisedKoszul_le_of_lt_one
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      (h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      {δ : ℝ} (hδ : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
      (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((raisedKoszul (I := I) g₀ g₁).toSection x) ≤
        C ^ 2 * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  obtain ⟨C₀, hC₀0, hpw⟩ :=
    connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one (I := I) (M := M) g₀ hδ₀0 hδ₀
  refine ⟨Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) * ((1 + δ₀) * C₀), by positivity, ?_⟩
  intro g₁ T h δ hδ hδ0 hbound x
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG_def
  have hG_nn : 0 ≤ G := norm_nonneg _
  have hδ_lt1 : δ < 1 := by linarith
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 2 x
    ((raisedKoszul (I := I) g₀ g₁).toSection x) e bse hnE hbse horth]
  have heach : ∀ (K : Fin 1 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 1 2
        ((raisedKoszul (I := I) g₀ g₁).toSection x) n e K J) ^ 2 ≤
        ((1 + δ₀) * C₀) ^ 2 * G ^ 2 := by
    intro K J
    rw [fiberNormSqComponent_raisedKoszul (I := I) (M := M) g₀ g₁ x e K J]
    set d : TangentSpace I x :=
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (e (J 0)) (e (J 1)) with hd_def
    set u : TangentSpace I x := sharpFlatRaiseEndo (I := I) g₀ g₁ x d with hu_def
    have hcs := metric_inner_cauchy_schwarz_sq (I := I) (M := M) g₀ x (e (K 0)) u
    have hKK : g₀.inner x (e (K 0)) (e (K 0)) = 1 := by rw [horth (K 0) (K 0)]; simp
    rw [hKK, one_mul] at hcs
    -- √(g₀ u u) ≤ (1+δ) √(g₀ d d)
    have hrev := sqrt_inner_sharpFlatRaiseEndo_le (I := I) g₀ g₁ T h hδ0 hbound x d
    rw [← hu_def] at hrev
    -- √(g₀ d d) ≤ C₀ G (using J0,J1 unit)
    have hconn := hpw g₁ T h hδ hδ0 hbound x (e (J 0)) (e (J 1))
    have hJ0 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by rw [horth (J 0) (J 0)]; simp
    have hJ1 : g₀.inner x (e (J 1)) (e (J 1)) = 1 := by rw [horth (J 1) (J 1)]; simp
    rw [hJ0, hJ1, Real.sqrt_one, mul_one, mul_one, ← hG_def, ← hd_def] at hconn
    have hd_sqrt_nn : 0 ≤ Real.sqrt (g₀.inner x d d) := Real.sqrt_nonneg _
    have h1delta_nn : 0 ≤ 1 + δ := by linarith
    have hconn' : (1 + δ) * Real.sqrt (g₀.inner x d d) ≤ (1 + δ₀) * (C₀ * G) := by
      have hstep1 : (1 + δ) * Real.sqrt (g₀.inner x d d) ≤ (1 + δ) * (C₀ * G) :=
        mul_le_mul_of_nonneg_left hconn h1delta_nn
      have hstep2 : (1 + δ) * (C₀ * G) ≤ (1 + δ₀) * (C₀ * G) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hC₀0 hG_nn)
      exact le_trans hstep1 hstep2
    have hu_sqrt_le : Real.sqrt (g₀.inner x u u) ≤ (1 + δ₀) * (C₀ * G) :=
      le_trans hrev hconn'
    have huu_nn : 0 ≤ g₀.inner x u u := metric_inner_self_nonneg (I := I) (M := M) g₀ x u
    have hsqrt_eq : Real.sqrt (g₀.inner x u u) ^ 2 = g₀.inner x u u := Real.sq_sqrt huu_nn
    have hsqrt_nn : 0 ≤ Real.sqrt (g₀.inner x u u) := Real.sqrt_nonneg _
    have hrhs_nn : 0 ≤ (1 + δ₀) * (C₀ * G) := by positivity
    have huu_le : g₀.inner x u u ≤ ((1 + δ₀) * C₀ * G) ^ 2 := by
      rw [← hsqrt_eq]
      have := mul_self_le_mul_self hsqrt_nn hu_sqrt_le
      nlinarith [this, hu_sqrt_le, hrhs_nn]
    calc (g₀.inner x (e (K 0)) u) ^ 2
        ≤ g₀.inner x u u := hcs
      _ ≤ ((1 + δ₀) * C₀ * G) ^ 2 := huu_le
      _ = ((1 + δ₀) * C₀) ^ 2 * G ^ 2 := by ring
  calc ∑ K : Fin 1 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 1 2
          ((raisedKoszul (I := I) g₀ g₁).toSection x) n e K J) ^ 2
      ≤ ∑ K : Fin 1 → Fin n, ∑ J : Fin 2 → Fin n, ((1 + δ₀) * C₀) ^ 2 * G ^ 2 :=
        Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => heach K J))
    _ = (Fintype.card (Fin 1 → Fin n) : ℝ) * (Fintype.card (Fin 2 → Fin n) : ℝ) *
        (((1 + δ₀) * C₀) ^ 2 * G ^ 2) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
        ring
    _ = (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) * ((1 + δ₀) * C₀)) ^ 2 * G ^ 2 := by
        have hcard : (Fintype.card (Fin 1 → Fin n) : ℝ) * (Fintype.card (Fin 2 → Fin n) : ℝ)
            = (n : ℝ) ^ 3 := by
          rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
            Fintype.card_fin]
          push_cast
          ring
        rw [hcard, ← hnE]
        have hsq : Real.sqrt ((n : ℝ) ^ 3) ^ 2 = (n : ℝ) ^ 3 :=
          Real.sq_sqrt (by positivity)
        rw [show (Real.sqrt ((n : ℝ) ^ 3) * ((1 + δ₀) * C₀)) ^ 2 * G ^ 2
            = Real.sqrt ((n : ℝ) ^ 3) ^ 2 * (((1 + δ₀) * C₀) ^ 2 * G ^ 2) from by ring]
        rw [hsq]

set_option linter.unusedSectionVars false in
private lemma fiberNormSqComponent_covGrad_raisedKoszul
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) {n : ℕ}
    (e : Fin n → TangentSpace I x)
    (K : Fin 1 → Fin n) (J : Fin 3 → Fin n)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hXx : X x = e (J 0)) (hYx : Y x = e (J 1)) (hZx : Z x = e (J 2)) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 1 3
        ((covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁)).toSection x) n e K J =
      g₀.inner x (e (K 0))
        (covDerivRaisedKoszulVec (I := I) g₀ g₁ X Y Z x) := by
  classical
  obtain ⟨om, hom⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 1 ℝ E) (V := fun y : M => Tensor0SSpace 1 I y)
    (n := (⊤ : ℕ∞)) x (coframeS (I := I) (M := M) g₀ x 1 e K)
  have homx : om x = coframeS (I := I) (M := M) g₀ x 1 e K := hom
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 1 3
        ((covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁)).toSection x) n e K J =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁)).toSection x)
          (om x))
        (Fin.cons (X x) (Fin.cons (Y x) ![Z x])) := by
    rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 1 3
          ((covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁)).toSection x) n e K J =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
            (covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁)).toSection x)
          (coframeS (I := I) (M := M) g₀ x 1 e K))
          (fun k => e (J k)) from rfl]
    rw [← homx]
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁)).toSection x)
          (om x))
          (fun k => e (J k)) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
            (covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁)).toSection x)
            (om x))
          (fun k => (show E from e (J k))) from rfl]
    congr 1
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · rw [Fin.cons_zero]; exact hXx.symm
    · refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_succ, Fin.cons_zero]; exact hYx.symm
      · refine Fin.cases ?_ (fun j' => ?_) j
        · rw [Fin.cons_succ, Fin.cons_succ]
          rw [show (![Z x] : Fin 1 → TangentSpace I x) 0 = Z x from rfl]
          exact hZx.symm
        · exact j'.elim0
  rw [hcomp]
  rw [raisedKoszul_covGrad_eq_covDerivRaisedKoszulVec (I := I) g₀ g₁ om X Y Z x]
  rw [homx, coframeS_one_eq_g0FlatCLM (I := I) (M := M) g₀ x e K]
  rw [show (g0FlatCLM (I := I) g₀ x (e (K 0)))
        (fun _ : Fin 1 => covDerivRaisedKoszulVec (I := I) g₀ g₁ X Y Z x) =
      cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x (e (K 0)))
        (covDerivRaisedKoszulVec (I := I) g₀ g₁ X Y Z x) from
    (cotangentToDual_apply (I := I) (x := x) _ _).symm]
  rw [cotangentToDual_g0FlatCLM (I := I) g₀ x (e (K 0))]

set_option linter.unusedSectionVars false in
private lemma sqrt_g0_inner_add_le_arm
    (g₀ : SmoothRiemannianMetric I M) (x : M) (a b : TangentSpace I x) :
    Real.sqrt (g₀.inner x (a + b) (a + b)) ≤
      Real.sqrt (g₀.inner x a a) + Real.sqrt (g₀.inner x b b) := by
  set na := Real.sqrt (g₀.inner x a a) with hna
  set nb := Real.sqrt (g₀.inner x b b) with hnb
  have haa_nn : 0 ≤ g₀.inner x a a := metric_inner_self_nonneg (I := I) (M := M) g₀ x a
  have hbb_nn : 0 ≤ g₀.inner x b b := metric_inner_self_nonneg (I := I) (M := M) g₀ x b
  have hna_nn : 0 ≤ na := Real.sqrt_nonneg _
  have hnb_nn : 0 ≤ nb := Real.sqrt_nonneg _
  have hna_sq : na ^ 2 = g₀.inner x a a := by rw [hna, Real.sq_sqrt haa_nn]
  have hnb_sq : nb ^ 2 = g₀.inner x b b := by rw [hnb, Real.sq_sqrt hbb_nn]
  have hcross : g₀.inner x a b ≤ na * nb := by
    have habs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x a b
    rw [← hna, ← hnb] at habs
    exact le_trans (le_abs_self _) habs
  have hexpand : g₀.inner x (a + b) (a + b) =
      g₀.inner x a a + 2 * g₀.inner x a b + g₀.inner x b b := by
    have h1 : g₀.inner x (a + b) (a + b)
        = g₀.inner x a (a + b) + g₀.inner x b (a + b) := by
      rw [map_add (g₀.inner x), ContinuousLinearMap.add_apply]
    have h2 : g₀.inner x a (a + b) = g₀.inner x a a + g₀.inner x a b :=
      map_add (g₀.inner x a) a b
    have h3 : g₀.inner x b (a + b) = g₀.inner x b a + g₀.inner x b b :=
      map_add (g₀.inner x b) a b
    have h4 : g₀.inner x b a = g₀.inner x a b := g₀.symm x b a
    rw [h1, h2, h3, h4]; ring
  have hle_sq : g₀.inner x (a + b) (a + b) ≤ (na + nb) ^ 2 := by
    rw [hexpand]
    have hsq : (na + nb) ^ 2 = na ^ 2 + 2 * (na * nb) + nb ^ 2 := by ring
    rw [hsq, hna_sq, hnb_sq]
    nlinarith [hcross]
  have hsum_pos_nn : 0 ≤ na + nb := add_nonneg hna_nn hnb_nn
  calc Real.sqrt (g₀.inner x (a + b) (a + b))
      ≤ Real.sqrt ((na + nb) ^ 2) := Real.sqrt_le_sqrt hle_sq
    _ = na + nb := by rw [Real.sqrt_sq hsum_pos_nn]

def sharpFlatRaiseEndoField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => sharpFlatRaiseEndo (I := I) g₀ g₁ x
  contMDiff_toFun := sharpFlatRaiseEndo_contMDiff (I := I) g₀ g₁

@[simp] lemma sharpFlatRaiseEndoField_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁ x) =
      sharpFlatRaiseEndo (I := I) g₀ g₁ x := rfl

set_option linter.unusedSectionVars false in
private lemma covDerivRaisedKoszulVec_eq_endoCov_add_sharpFlat
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    covDerivRaisedKoszulVec (I := I) g₀ g₁ X Y Z x =
      ((endoCovariantDerivative (I := I) (M := M) g₀)
          (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁) x (X x))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x))
      + sharpFlatRaiseEndo (I := I) g₀ g₁ x
          (covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x) := by
  classical
  set S : Π b : M, TangentSpace I b →L[ℝ] TangentSpace I b :=
    fun b => sharpFlatRaiseEndo (I := I) g₀ g₁ b with hS_def
  have hDsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (Y b) (Z b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ Y.contMDiff Z.contMDiff
  set Dsec : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (Y b) (Z b), hDsm⟩ with hDsec_def
  have hDsecx : Dsec x = PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x) := rfl
  have hLeib := endoCovariantDerivative_apply (I := I) (M := M) g₀
    (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁) Dsec x (X x)
  have hΛapp : (fun y : M => (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁ y) (Dsec y)) =
      (fun y : M => raisedKoszulVec (I := I) g₀ g₁ y (Y y) (Z y)) := by
    funext y
    rw [sharpFlatRaiseEndoField_apply, hDsec_def]
    change sharpFlatRaiseEndo (I := I) g₀ g₁ y
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ y (Y y) (Z y)) = _
    rw [raisedKoszulVec]
  rw [hΛapp] at hLeib
  rw [sharpFlatRaiseEndoField_apply, hDsecx] at hLeib
  rw [covDerivRaisedKoszulVec]
  have hgrad_eq : (LeviCivita (I := I) g₀).toFun
        (fun b => raisedKoszulVec (I := I) g₀ g₁ b (Y b) (Z b)) x (X x) =
      ((endoCovariantDerivative (I := I) (M := M) g₀)
          (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁) x (X x))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x))
      + sharpFlatRaiseEndo (I := I) g₀ g₁ x
          ((LeviCivita (I := I) g₀).toFun (fun b => Dsec b) x (X x)) := by
    have h : ((endoCovariantDerivative (I := I) (M := M) g₀)
          (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁) x (X x))
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x)) =
        (LeviCivita (I := I) g₀).toFun
            (fun b => raisedKoszulVec (I := I) g₀ g₁ b (Y b) (Z b)) x (X x) -
          sharpFlatRaiseEndo (I := I) g₀ g₁ x
            ((LeviCivita (I := I) g₀).toFun (fun b => Dsec b) x (X x)) := hLeib
    rw [h]; abel
  rw [hgrad_eq]
  set ET : TangentSpace I x :=
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁) x (X x))
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x)) with hET_def
  set gradY : TangentSpace I x :=
    (LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x) with hgradY_def
  set gradZ : TangentSpace I x :=
    (LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x) with hgradZ_def
  set gradD : TangentSpace I x :=
    (LeviCivita (I := I) g₀).toFun (fun b => Dsec b) x (X x) with hgradD_def
  have hrkY : raisedKoszulVec (I := I) g₀ g₁ x gradY (Z x) =
      sharpFlatRaiseEndo (I := I) g₀ g₁ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x gradY (Z x)) := by
    rw [raisedKoszulVec]
  have hrkZ : raisedKoszulVec (I := I) g₀ g₁ x (Y x) gradZ =
      sharpFlatRaiseEndo (I := I) g₀ g₁ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) gradZ) := by
    rw [raisedKoszulVec]
  rw [hrkY, hrkZ]
  have hcollapse :
      ET + sharpFlatRaiseEndo (I := I) g₀ g₁ x gradD
        - sharpFlatRaiseEndo (I := I) g₀ g₁ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x gradY (Z x))
        - sharpFlatRaiseEndo (I := I) g₀ g₁ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) gradZ) =
      ET + sharpFlatRaiseEndo (I := I) g₀ g₁ x
          (gradD - PDE.DeTurck.connDiff (I := I) g₁ g₀ x gradY (Z x)
            - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) gradZ) := by
    rw [map_sub, map_sub]; abel
  rw [hcollapse]
  congr 1
  rw [covDerivConnDiff, covDerivDiff]
  have hdiffSec_x : diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
        (fun b => Z b) (fun b => Y b) = fun b => Dsec b := by
    funext b
    rw [diffSec]
    rfl
  rw [hdiffSec_x, ← hgradD_def]
  have hcovApplyZ : covApply (LeviCivita (I := I) g₀) (fun b => X b) (fun b => Z b) x = gradZ := by
    rw [covApply_apply, hgradZ_def]
  have hcovApplyY : covApply (LeviCivita (I := I) g₀) (fun b => X b) (fun b => Y b) x = gradY := by
    rw [covApply_apply, hgradY_def]
  rw [hcovApplyZ, hcovApplyY]
  rw [show CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) x
        (Y x) gradZ = PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) gradZ from rfl]
  rw [show CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) x
        gradY (Z x) = PDE.DeTurck.connDiff (I := I) g₁ g₀ x gradY (Z x) from rfl]
  abel

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
private lemma sqrt_inner_endoCov_sharpFlatRaiseEndo_apply_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      (h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      {δ : ℝ} (hδ : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
      (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M) (v w : TangentSpace I x),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      Real.sqrt (g₀.inner x
          (((endoCovariantDerivative (I := I) (M := M) g₀)
            (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁) x v) w)
          (((endoCovariantDerivative (I := I) (M := M) g₀)
            (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁) x v) w)) ≤
        C * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ *
          Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
  sorry

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
private lemma sqrt_inner_covDerivConnDiff_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      (h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      {δ : ℝ} (hδ : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
      (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M)
      (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 4 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
      Real.sqrt (g₀.inner x
          (covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x)
          (covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x)) ≤
        C *
          Real.sqrt (‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
                Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 +
              ‖((iteratedCovGrad (I := I) g₀ 0 2 2 T).toSection x :
                Tensor0SBundle.TensorRSSpace 0 4 I x)‖ ^ 2) *
          Real.sqrt (g₀.inner x (X x) (X x)) * Real.sqrt (g₀.inner x (Y x) (Y x)) *
          Real.sqrt (g₀.inner x (Z x) (Z x)) := by
  sorry

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
private lemma sqrt_inner_covDerivRaisedKoszulVec_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ Carm : ℝ, 0 ≤ Carm ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      (h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      {δ : ℝ} (hδ : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
      (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M)
      (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
      (hX : g₀.inner x (X x) (X x) = 1) (hY : g₀.inner x (Y x) (Y x) = 1)
      (hZ : g₀.inner x (Z x) (Z x) = 1)
      {R : ℝ} (hR0 : 0 ≤ R)
      (hjet :
        letI : Bundle.RiemannianBundle
            (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
        ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ≤ R),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 4 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
      Real.sqrt (g₀.inner x
          (covDerivRaisedKoszulVec (I := I) g₀ g₁ X Y Z x)
          (covDerivRaisedKoszulVec (I := I) g₀ g₁ X Y Z x)) ≤
        Carm * (1 + R) *
          Real.sqrt (‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
                Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 +
              ‖((iteratedCovGrad (I := I) g₀ 0 2 2 T).toSection x :
                Tensor0SBundle.TensorRSSpace 0 4 I x)‖ ^ 2) := by
  classical
  letI inst3 : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  letI inst4 : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 4 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
  obtain ⟨Cendo, hCendo0, hendo⟩ :=
    sqrt_inner_endoCov_sharpFlatRaiseEndo_apply_le (I := I) (M := M) g₀ hδ₀0 hδ₀
  obtain ⟨Cconn, hCconn0, hconn⟩ :=
    connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one (I := I) (M := M) g₀ hδ₀0 hδ₀
  obtain ⟨Ccdc, hCcdc0, hcdc⟩ :=
    sqrt_inner_covDerivConnDiff_le (I := I) (M := M) g₀ hδ₀0 hδ₀
  refine ⟨Cendo * Cconn + (1 + δ₀) * Ccdc, by positivity, ?_⟩
  intro g₁ T h δ hδ hδ0 hbound x X Y Z hX hY hZ R hR0 hjet
  set G1 : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG1_def
  set G2 : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 2 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 4 I x)‖ with hG2_def
  have hG1_nn : 0 ≤ G1 := norm_nonneg _
  have hG2_nn : 0 ≤ G2 := norm_nonneg _
  set Q : ℝ := Real.sqrt (G1 ^ 2 + G2 ^ 2) with hQ_def
  have hQ_nn : 0 ≤ Q := Real.sqrt_nonneg _
  have hG1_le_Q : G1 ≤ Q := by
    rw [hQ_def]
    have : G1 = Real.sqrt (G1 ^ 2) := by rw [Real.sqrt_sq hG1_nn]
    rw [this]
    exact Real.sqrt_le_sqrt (by nlinarith [hG2_nn])
  have hjet' : G1 ≤ R := hjet
  have hR1_nn : 0 ≤ 1 + R := by linarith
  set A : TangentSpace I x :=
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁) x (X x))
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x)) with hA_def
  set B : TangentSpace I x :=
    sharpFlatRaiseEndo (I := I) g₀ g₁ x
      (covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x)
    with hB_def
  have hsplit : covDerivRaisedKoszulVec (I := I) g₀ g₁ X Y Z x = A + B := by
    rw [hA_def, hB_def]
    exact covDerivRaisedKoszulVec_eq_endoCov_add_sharpFlat (I := I) (M := M) g₀ g₁ X Y Z x
  set NA : ℝ := Real.sqrt (g₀.inner x A A) with hNA_def
  have hNA_le : NA ≤ Cendo * Cconn * G1 ^ 2 := by
    have hAbound := hendo g₁ T h hδ hδ0 hbound x (X x)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x))
    rw [← hA_def, ← hG1_def] at hAbound
    rw [hX, Real.sqrt_one, mul_one] at hAbound
    have hcn := hconn g₁ T h hδ hδ0 hbound x (Y x) (Z x)
    rw [← hG1_def, hY, hZ, Real.sqrt_one, mul_one, mul_one] at hcn
    have hcd_nn : 0 ≤ Real.sqrt (g₀.inner x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x))) := Real.sqrt_nonneg _
    rw [hNA_def]
    calc Real.sqrt (g₀.inner x A A)
        ≤ Cendo * G1 * Real.sqrt (g₀.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x))
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x))) := hAbound
      _ ≤ Cendo * G1 * (Cconn * G1) := by
          refine mul_le_mul_of_nonneg_left hcn (mul_nonneg hCendo0 hG1_nn)
      _ = Cendo * Cconn * G1 ^ 2 := by ring
  set NB : ℝ := Real.sqrt (g₀.inner x B B) with hNB_def
  have hNB_le : NB ≤ (1 + δ₀) * Ccdc * Q := by
    set D : TangentSpace I x :=
      covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x with hD_def
    have hBeq : B = sharpFlatRaiseEndo (I := I) g₀ g₁ x D := by rw [hB_def, hD_def]
    have hneumann := sqrt_inner_sharpFlatRaiseEndo_le (I := I) g₀ g₁ T h hδ0 hbound x D
    rw [← hBeq] at hneumann
    have hDbound := hcdc g₁ T h hδ hδ0 hbound x X Y Z
    rw [← hD_def, ← hG1_def, ← hG2_def, ← hQ_def, hX, hY, hZ, Real.sqrt_one,
      mul_one, mul_one, mul_one] at hDbound
    have hD_sqrt_nn : 0 ≤ Real.sqrt (g₀.inner x D D) := Real.sqrt_nonneg _
    have h1delta_nn : 0 ≤ 1 + δ := by linarith
    rw [hNB_def]
    calc Real.sqrt (g₀.inner x B B)
        ≤ (1 + δ) * Real.sqrt (g₀.inner x D D) := hneumann
      _ ≤ (1 + δ) * (Ccdc * Q) := mul_le_mul_of_nonneg_left hDbound h1delta_nn
      _ ≤ (1 + δ₀) * (Ccdc * Q) := by
          refine mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hCcdc0 hQ_nn)
      _ = (1 + δ₀) * Ccdc * Q := by ring
  have htri : Real.sqrt (g₀.inner x (A + B) (A + B)) ≤ NA + NB := by
    rw [hNA_def, hNB_def]
    exact sqrt_g0_inner_add_le_arm (I := I) (M := M) g₀ x A B
  rw [hsplit]
  refine htri.trans ?_
  have hδ₀1_nn : 0 ≤ 1 + δ₀ := by linarith
  have hCcdc_Q_nn : 0 ≤ (1 + δ₀) * Ccdc * Q := by positivity
  have hG1sq_le : G1 ^ 2 ≤ (1 + R) * Q := by
    have hG1_le_R1Q : G1 ≤ (1 + R) := le_trans hjet' (by linarith)
    have : G1 * G1 ≤ (1 + R) * Q := by
      refine mul_le_mul hG1_le_R1Q ?_ hG1_nn hR1_nn
      exact hG1_le_Q
    nlinarith [this]
  calc NA + NB
      ≤ Cendo * Cconn * G1 ^ 2 + (1 + δ₀) * Ccdc * Q := add_le_add hNA_le hNB_le
    _ ≤ Cendo * Cconn * ((1 + R) * Q) + (1 + δ₀) * Ccdc * ((1 + R) * Q) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left hG1sq_le (by positivity)
        · have hQ_le : Q ≤ (1 + R) * Q := by
            nlinarith [hQ_nn, hR0]
          exact mul_le_mul_of_nonneg_left hQ_le (by positivity)
    _ = (Cendo * Cconn + (1 + δ₀) * Ccdc) * (1 + R) * Q := by ring

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem rfns_iteratedCovGrad_one_raisedKoszul_le_of_lt_one
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      (h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      {δ : ℝ} (hδ : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
      (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M) {R : ℝ} (hR0 : 0 ≤ R)
      (hjet :
        letI : Bundle.RiemannianBundle
            (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
        ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ≤ R),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 4 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + 1) x
          ((iteratedCovGrad (I := I) g₀ 1 2 1 (raisedKoszul (I := I) g₀ g₁)).toSection x) ≤
        C ^ 2 * (1 + R) ^ 2 *
          (‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
                Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 +
            ‖((iteratedCovGrad (I := I) g₀ 0 2 2 T).toSection x :
              Tensor0SBundle.TensorRSSpace 0 4 I x)‖ ^ 2) := by
  classical
  letI inst3 : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  letI inst4 : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 4 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
  obtain ⟨Carm, hCarm0, harm⟩ :=
    sqrt_inner_covDerivRaisedKoszulVec_le (I := I) (M := M) g₀ hδ₀0 hδ₀
  refine ⟨Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 4) * Carm, by positivity, ?_⟩
  intro g₁ T h δ hδ hδ0 hbound x R hR0 hjet
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  set G1 : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG1_def
  set G2 : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 2 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 4 I x)‖ with hG2_def
  have hG1_nn : 0 ≤ G1 := norm_nonneg _
  have hG2_nn : 0 ≤ G2 := norm_nonneg _
  have hjet' : G1 ≤ R := hjet
  have hQ_nn : (0 : ℝ) ≤ G1 ^ 2 + G2 ^ 2 := by positivity
  have hiter1 : iteratedCovGrad (I := I) g₀ 1 2 1 (raisedKoszul (I := I) g₀ g₁) =
      covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
  rw [hiter1]
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 3 x
    ((covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁)).toSection x)
    e bse hnE hbse horth]
  have hR1_nn : 0 ≤ 1 + R := by linarith
  have heach : ∀ (K : Fin 1 → Fin n) (J : Fin 3 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 1 3
        ((covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁)).toSection x) n e K J) ^ 2 ≤
        (Carm * (1 + R)) ^ 2 * (G1 ^ 2 + G2 ^ 2) := by
    intro K J
    obtain ⟨X, hXx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x (e (J 0))
    obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x (e (J 1))
    obtain ⟨Z, hZx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x (e (J 2))
    rw [fiberNormSqComponent_covGrad_raisedKoszul (I := I) (M := M) g₀ g₁ x e K J X Y Z hXx hYx hZx]
    set u : TangentSpace I x := covDerivRaisedKoszulVec (I := I) g₀ g₁ X Y Z x with hu_def
    have hcs := metric_inner_cauchy_schwarz_sq (I := I) (M := M) g₀ x (e (K 0)) u
    have hKK : g₀.inner x (e (K 0)) (e (K 0)) = 1 := by rw [horth (K 0) (K 0)]; simp
    rw [hKK, one_mul] at hcs
    have hXX : g₀.inner x (X x) (X x) = 1 := by rw [hXx, horth (J 0) (J 0)]; simp
    have hYY : g₀.inner x (Y x) (Y x) = 1 := by rw [hYx, horth (J 1) (J 1)]; simp
    have hZZ : g₀.inner x (Z x) (Z x) = 1 := by rw [hZx, horth (J 2) (J 2)]; simp
    have hroot := harm g₁ T h hδ hδ0 hbound x X Y Z hXX hYY hZZ hR0 hjet
    rw [← hu_def, ← hG1_def, ← hG2_def] at hroot
    have huu_nn : 0 ≤ g₀.inner x u u := metric_inner_self_nonneg (I := I) (M := M) g₀ x u
    have hsqrt_eq : Real.sqrt (g₀.inner x u u) ^ 2 = g₀.inner x u u := Real.sq_sqrt huu_nn
    have hsqrt_nn : 0 ≤ Real.sqrt (g₀.inner x u u) := Real.sqrt_nonneg _
    have hrhs_nn : 0 ≤ Carm * (1 + R) * Real.sqrt (G1 ^ 2 + G2 ^ 2) :=
      mul_nonneg (mul_nonneg hCarm0 hR1_nn) (Real.sqrt_nonneg _)
    have hsqrtQ_sq : Real.sqrt (G1 ^ 2 + G2 ^ 2) ^ 2 = G1 ^ 2 + G2 ^ 2 :=
      Real.sq_sqrt hQ_nn
    have huu_le : g₀.inner x u u ≤ (Carm * (1 + R)) ^ 2 * (G1 ^ 2 + G2 ^ 2) := by
      rw [← hsqrt_eq]
      have hmul := mul_self_le_mul_self hsqrt_nn hroot
      have hexpand : (Carm * (1 + R) * Real.sqrt (G1 ^ 2 + G2 ^ 2)) *
          (Carm * (1 + R) * Real.sqrt (G1 ^ 2 + G2 ^ 2)) =
          (Carm * (1 + R)) ^ 2 * (G1 ^ 2 + G2 ^ 2) := by
        rw [show (Carm * (1 + R) * Real.sqrt (G1 ^ 2 + G2 ^ 2)) *
              (Carm * (1 + R) * Real.sqrt (G1 ^ 2 + G2 ^ 2)) =
            (Carm * (1 + R)) ^ 2 *
              (Real.sqrt (G1 ^ 2 + G2 ^ 2) * Real.sqrt (G1 ^ 2 + G2 ^ 2)) from by ring]
        rw [show Real.sqrt (G1 ^ 2 + G2 ^ 2) * Real.sqrt (G1 ^ 2 + G2 ^ 2) =
            Real.sqrt (G1 ^ 2 + G2 ^ 2) ^ 2 from by ring, hsqrtQ_sq]
      rw [hexpand] at hmul
      nlinarith [hmul, hsqrt_nn, hroot]
    calc (g₀.inner x (e (K 0)) u) ^ 2
        ≤ g₀.inner x u u := hcs
      _ ≤ (Carm * (1 + R)) ^ 2 * (G1 ^ 2 + G2 ^ 2) := huu_le
  calc ∑ K : Fin 1 → Fin n, ∑ J : Fin 3 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 1 3
          ((covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁)).toSection x) n e K J) ^ 2
      ≤ ∑ K : Fin 1 → Fin n, ∑ J : Fin 3 → Fin n,
          (Carm * (1 + R)) ^ 2 * (G1 ^ 2 + G2 ^ 2) :=
        Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => heach K J))
    _ = (Fintype.card (Fin 1 → Fin n) : ℝ) * (Fintype.card (Fin 3 → Fin n) : ℝ) *
        ((Carm * (1 + R)) ^ 2 * (G1 ^ 2 + G2 ^ 2)) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
        ring
    _ = (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 4) * Carm) ^ 2 * (1 + R) ^ 2 *
          (G1 ^ 2 + G2 ^ 2) := by
        have hcard : (Fintype.card (Fin 1 → Fin n) : ℝ) * (Fintype.card (Fin 3 → Fin n) : ℝ)
            = (n : ℝ) ^ 4 := by
          rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
            Fintype.card_fin]
          push_cast
          ring
        rw [hcard, ← hnE]
        have hsq : Real.sqrt ((n : ℝ) ^ 4) ^ 2 = (n : ℝ) ^ 4 :=
          Real.sq_sqrt (by positivity)
        rw [show (Real.sqrt ((n : ℝ) ^ 4) * Carm) ^ 2 * (1 + R) ^ 2 * (G1 ^ 2 + G2 ^ 2)
            = Real.sqrt ((n : ℝ) ^ 4) ^ 2 *
                ((Carm * (1 + R)) ^ 2 * (G1 ^ 2 + G2 ^ 2)) from by ring]
        rw [hsq]

set_option linter.unusedSectionVars false in
private lemma fiberNormSqComponent_flatArmCc
    (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool) (x : M) {n : ℕ}
    (e : Fin n → TangentSpace I x)
    (K : Fin 1 → Fin n) (J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 1 2
        ((flatArmCc (I := I) g₀ g₁ kind).toSection x) n e K J =
      g₀.inner x
        (flatArmVec (I := I) g₀ g₁ kind x (g0FlatCLM (I := I) g₀ x (e (K 0))) (e (J 0)))
        (e (J 1)) := by
  rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 1 2
        ((flatArmCc (I := I) g₀ g₁ kind).toSection x) n e K J =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          (flatArmCc (I := I) g₀ g₁ kind).toSection x)
        (coframeS (I := I) (M := M) g₀ x 1 e K))
        (fun k => e (J k)) from rfl]
  rw [coframeS_one_eq_g0FlatCLM (I := I) (M := M) g₀ x e K]
  rw [flatArmCc_toSection]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        flatArmFib (I := I) g₀ g₁ kind x) (g0FlatCLM (I := I) g₀ x (e (K 0)))
      = flatArmPairing (I := I) g₀ g₁ kind x (g0FlatCLM (I := I) g₀ x (e (K 0))) from rfl]
  rw [show (flatArmPairing (I := I) g₀ g₁ kind x (g0FlatCLM (I := I) g₀ x (e (K 0))))
        (fun k => e (J k))
      = g₀.inner x
          (flatArmVec (I := I) g₀ g₁ kind x (g0FlatCLM (I := I) g₀ x (e (K 0))) (e (J 0)))
          (e (J 1)) from flatArmPairing_apply (I := I) g₀ g₁ kind x _ _]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
private lemma sqrt_inner_flatArmVec_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ Carm : ℝ, 0 ≤ Carm ∧ ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
      (h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      {δ : ℝ} (hδ : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
      (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (kind : Bool) (x : M) (v0 w : TangentSpace I x)
      (hw : g₀.inner x w w = 1),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      Real.sqrt (g₀.inner x
          (flatArmVec (I := I) g₀ g₁ kind x (g0FlatCLM (I := I) g₀ x w) v0)
          (flatArmVec (I := I) g₀ g₁ kind x (g0FlatCLM (I := I) g₀ x w) v0)) ≤
        Carm *
          ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
              Tensor0SBundle.TensorRSSpace 0 3 I x)‖ *
          Real.sqrt (g₀.inner x v0 v0) := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  obtain ⟨C₀, hC₀0, hpw⟩ :=
    connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one (I := I) (M := M) g₀ hδ₀0 hδ₀
  refine ⟨(1 / (1 - δ₀)) ^ 2 * C₀, by positivity, ?_⟩
  intro g₁ T h δ hδ hδ0 hbound kind x v0 w hw
  have hg₁ : ∀ (b : M) (u₁ u₂ : TangentSpace I b),
      g₁.inner b u₁ u₂ = g₀.inner b u₁ u₂ + ccTensorBilinSymm (I := I) g₀ T b u₁ u₂ :=
    fun b u₁ u₂ => h b u₁ u₂
  have hceil0 : 0 < 1 - δ₀ := by linarith
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG_def
  have hG_nn : 0 ≤ G := norm_nonneg _
  set Nv0 : ℝ := Real.sqrt (g₀.inner x v0 v0) with hNv0_def
  have hNv0_nn : 0 ≤ Nv0 := Real.sqrt_nonneg _
  set s : TangentSpace I x :=
    inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x w) with hs_def
  have hs_sqrt : Real.sqrt (g₀.inner x s s) ≤ (1 / (1 - δ₀)) := by
    have hsfib := sqrt_inner_inverseMetricSharpFib_g0FlatCLM_le
      (I := I) g₀ g₁ (ccTensorBilinSymm (I := I) g₀ T) hg₁
      (by linarith : δ < 1) hδ0 hbound x w
    rw [hw, Real.sqrt_one, mul_one] at hsfib
    rw [← hs_def] at hsfib
    have hinv_le : 1 / (1 - δ) ≤ 1 / (1 - δ₀) := by
      have hcoeff : 0 < 1 - δ := by linarith
      rw [div_le_div_iff₀ hcoeff hceil0]; linarith
    exact le_trans hsfib hinv_le
  have hge1 : (1 : ℝ) ≤ 1 / (1 - δ₀) := by
    rw [le_div_iff₀ hceil0]; linarith
  have hbound_target : Real.sqrt (g₀.inner x
      (flatArmVec (I := I) g₀ g₁ kind x (g0FlatCLM (I := I) g₀ x w) v0)
      (flatArmVec (I := I) g₀ g₁ kind x (g0FlatCLM (I := I) g₀ x w) v0)) ≤
      C₀ * G * (1 / (1 - δ₀)) ^ 2 * Nv0 := by
    cases kind with
    | true =>
        have hval : flatArmVec (I := I) g₀ g₁ true x (g0FlatCLM (I := I) g₀ x w) v0 =
            - PDE.DeTurck.connDiff (I := I) g₁ g₀ x s v0 := by
          rw [flatArmVec, if_pos rfl, hs_def]
        rw [hval]
        rw [show g₀.inner x (- PDE.DeTurck.connDiff (I := I) g₁ g₀ x s v0)
              (- PDE.DeTurck.connDiff (I := I) g₁ g₀ x s v0) =
            g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x s v0)
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x s v0) from by
          simp only [map_neg, ContinuousLinearMap.neg_apply, neg_neg]]
        have hconn := hpw g₁ T h hδ hδ0 hbound x s v0
        rw [← hG_def, ← hNv0_def] at hconn
        refine hconn.trans ?_
        have hss_sqrt_le : Real.sqrt (g₀.inner x s s) ≤ (1 / (1 - δ₀)) ^ 2 := by
          have hsq_ge : 1 / (1 - δ₀) ≤ (1 / (1 - δ₀)) ^ 2 := by nlinarith [hge1]
          exact le_trans hs_sqrt hsq_ge
        have hC₀G_nn : 0 ≤ C₀ * G := mul_nonneg hC₀0 hG_nn
        calc C₀ * G * Real.sqrt (g₀.inner x s s) * Nv0
            ≤ C₀ * G * ((1 / (1 - δ₀)) ^ 2) * Nv0 := by
              refine mul_le_mul_of_nonneg_right ?_ hNv0_nn
              exact mul_le_mul_of_nonneg_left hss_sqrt_le hC₀G_nn
    | false =>
        set Dfun : TangentSpace I x →L[ℝ] ℝ :=
          (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x w)).comp
              ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v0)) with hDfun_def
        have hval : flatArmVec (I := I) g₀ g₁ false x (g0FlatCLM (I := I) g₀ x w) v0 =
            inverseMetricSharpFib (I := I) g₁ x (dualToCotangent (I := I) Dfun.toLinearMap) := by
          rw [flatArmVec, if_neg (by decide : ¬ (false = true)), hDfun_def]
        rw [hval]
        set p : TangentSpace I x :=
          inverseMetricSharpFib (I := I) g₀ x (dualToCotangent (I := I) Dfun.toLinearMap)
          with hp_def
        set q : TangentSpace I x :=
          inverseMetricSharpFib (I := I) g₁ x (dualToCotangent (I := I) Dfun.toLinearMap)
          with hq_def
        have hqeq : q = inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x p) := by
          rw [hq_def]
          congr 1
          exact (g0FlatCLM_inverseMetricSharpFib (I := I) g₀ x
            (dualToCotangent (I := I) Dfun.toLinearMap)).symm
        set Np : ℝ := Real.sqrt (g₀.inner x p p) with hNpdef
        have hNp_nn : 0 ≤ Np := Real.sqrt_nonneg _
        have hpp_nn : 0 ≤ g₀.inner x p p := metric_inner_self_nonneg (I := I) (M := M) g₀ x p
        have hNp_sq : Np ^ 2 = g₀.inner x p p := Real.sq_sqrt hpp_nn
        have hDval : ∀ z : TangentSpace I x, Dfun z =
            - g₀.inner x w (PDE.DeTurck.connDiff (I := I) g₁ g₀ x z v0) := by
          intro z
          rw [hDfun_def, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.flip_apply]
          change - cotangentToDual (I := I) (g0FlatCLM (I := I) g₀ x w)
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x z v0) = _
          rw [cotangentToDual_g0FlatCLM]
        have hpz : ∀ z : TangentSpace I x, g₀.inner x p z = Dfun z := by
          intro z
          rw [hp_def, inverseMetricSharpFib_inner (I := I) g₀ x
            (dualToCotangent (I := I) Dfun.toLinearMap) z]
          rw [cotangentToDualLinear_apply, cotangentToDual_dualToCotangent]
          rfl
        have hpp_val : g₀.inner x p p =
            - g₀.inner x w (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0) := by
          rw [hpz p, hDval p]
        have hconn_p := hpw g₁ T h hδ hδ0 hbound x p v0
        rw [← hG_def, ← hNpdef, ← hNv0_def] at hconn_p
        have hcs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x w
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0)
        rw [hw, Real.sqrt_one, one_mul] at hcs
        have hKnn : 0 ≤ C₀ * G * Nv0 :=
          mul_nonneg (mul_nonneg hC₀0 hG_nn) hNv0_nn
        have hNp_le : Np ≤ C₀ * G * (1 / (1 - δ₀)) * Nv0 := by
          have hpp_le : g₀.inner x p p ≤
              Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0)
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0)) := by
            rw [hpp_val]
            calc - g₀.inner x w (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0)
                ≤ |g₀.inner x w (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0)| := neg_le_abs _
              _ ≤ Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0)
                  (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0)) := hcs
          have hconnG : Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0)
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0)) ≤ C₀ * G * Np * Nv0 := hconn_p
          have hpp_le2 : g₀.inner x p p ≤ (C₀ * G * Nv0) * Np := by
            refine hpp_le.trans (hconnG.trans ?_)
            nlinarith [hNp_nn, hKnn]
          have hNp_le0 : Np ≤ C₀ * G * Nv0 := by
            nlinarith [hNp_sq, hNp_nn, hpp_le2, hKnn]
          have hstep : C₀ * G * Nv0 ≤ C₀ * G * (1 / (1 - δ₀)) * Nv0 := by
            nlinarith [mul_le_mul_of_nonneg_left hge1 (mul_nonneg hC₀0 hG_nn), hNv0_nn, hKnn]
          exact hNp_le0.trans hstep
        have hsharp := sqrt_inner_inverseMetricSharpFib_g0FlatCLM_le (I := I) g₀ g₁
          (ccTensorBilinSymm (I := I) g₀ T) hg₁
          (by linarith : δ < 1) hδ0 hbound x p
        rw [← hNpdef] at hsharp
        rw [hqeq]
        refine hsharp.trans ?_
        have hinv_le : 1 / (1 - δ) ≤ 1 / (1 - δ₀) := by
          have hcoeff : 0 < 1 - δ := by linarith
          rw [div_le_div_iff₀ hcoeff hceil0]; linarith
        have hstep : (1 / (1 - δ)) * Np ≤ (1 / (1 - δ₀)) * Np :=
          mul_le_mul_of_nonneg_right hinv_le hNp_nn
        refine hstep.trans ?_
        have hinv₀_nn : 0 ≤ 1 / (1 - δ₀) := by positivity
        calc (1 / (1 - δ₀)) * Np
            ≤ (1 / (1 - δ₀)) * (C₀ * G * (1 / (1 - δ₀)) * Nv0) :=
              mul_le_mul_of_nonneg_left hNp_le hinv₀_nn
          _ = C₀ * G * (1 / (1 - δ₀)) ^ 2 * Nv0 := by ring
  refine hbound_target.trans ?_
  rw [hG_def, hNv0_def]
  apply le_of_eq; ring

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem rfns_flatArmCc_le_of_lt_one
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) (kind : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      (h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      {δ : ℝ} (hδ : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
      (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((flatArmCc (I := I) g₀ g₁ kind).toSection x) ≤
        C ^ 2 * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  obtain ⟨Carm, hCarm0, harm⟩ :=
    sqrt_inner_flatArmVec_le (I := I) (M := M) g₀ hδ₀0 hδ₀
  refine ⟨Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) * Carm, by positivity, ?_⟩
  intro g₁ T h δ hδ hδ0 hbound x
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG_def
  have hG_nn : 0 ≤ G := norm_nonneg _
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 2 x
    ((flatArmCc (I := I) g₀ g₁ kind).toSection x) e bse hnE hbse horth]
  have heach : ∀ (K : Fin 1 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 1 2
        ((flatArmCc (I := I) g₀ g₁ kind).toSection x) n e K J) ^ 2 ≤
        Carm ^ 2 * G ^ 2 := by
    intro K J
    rw [fiberNormSqComponent_flatArmCc (I := I) g₀ g₁ kind x e K J]
    set u : TangentSpace I x :=
      flatArmVec (I := I) g₀ g₁ kind x (g0FlatCLM (I := I) g₀ x (e (K 0))) (e (J 0))
      with hu_def
    have hcs := metric_inner_cauchy_schwarz_sq (I := I) (M := M) g₀ x u (e (J 1))
    have hJ1 : g₀.inner x (e (J 1)) (e (J 1)) = 1 := by rw [horth (J 1) (J 1)]; simp
    rw [hJ1, mul_one] at hcs
    have hKK : g₀.inner x (e (K 0)) (e (K 0)) = 1 := by rw [horth (K 0) (K 0)]; simp
    have hJ0 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by rw [horth (J 0) (J 0)]; simp
    have hroot := harm g₁ T h hδ hδ0 hbound kind x (e (J 0)) (e (K 0)) hKK
    rw [← hu_def, hJ0, Real.sqrt_one, mul_one, ← hG_def] at hroot
    have huu_nn : 0 ≤ g₀.inner x u u := metric_inner_self_nonneg (I := I) (M := M) g₀ x u
    have hsqrt_eq : Real.sqrt (g₀.inner x u u) ^ 2 = g₀.inner x u u := Real.sq_sqrt huu_nn
    have hsqrt_nn : 0 ≤ Real.sqrt (g₀.inner x u u) := Real.sqrt_nonneg _
    have hrhs_nn : 0 ≤ Carm * G := mul_nonneg hCarm0 hG_nn
    have huu_le : g₀.inner x u u ≤ (Carm * G) ^ 2 := by
      rw [← hsqrt_eq]
      have := mul_self_le_mul_self hsqrt_nn hroot
      nlinarith [this, hroot, hrhs_nn]
    calc (g₀.inner x u (e (J 1))) ^ 2
        ≤ g₀.inner x u u := hcs
      _ ≤ (Carm * G) ^ 2 := huu_le
      _ = Carm ^ 2 * G ^ 2 := by ring
  calc ∑ K : Fin 1 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 1 2
          ((flatArmCc (I := I) g₀ g₁ kind).toSection x) n e K J) ^ 2
      ≤ ∑ K : Fin 1 → Fin n, ∑ J : Fin 2 → Fin n, Carm ^ 2 * G ^ 2 :=
        Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => heach K J))
    _ = (Fintype.card (Fin 1 → Fin n) : ℝ) * (Fintype.card (Fin 2 → Fin n) : ℝ) *
        (Carm ^ 2 * G ^ 2) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
        ring
    _ = (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) * Carm) ^ 2 * G ^ 2 := by
        have hcard : (Fintype.card (Fin 1 → Fin n) : ℝ) * (Fintype.card (Fin 2 → Fin n) : ℝ)
            = (n : ℝ) ^ 3 := by
          rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
            Fintype.card_fin]
          push_cast
          ring
        rw [hcard, ← hnE]
        have hsq : Real.sqrt ((n : ℝ) ^ 3) ^ 2 = (n : ℝ) ^ 3 :=
          Real.sq_sqrt (by positivity)
        rw [show (Real.sqrt ((n : ℝ) ^ 3) * Carm) ^ 2 * G ^ 2
            = Real.sqrt ((n : ℝ) ^ 3) ^ 2 * (Carm ^ 2 * G ^ 2) from by ring]
        rw [hsq]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem rfns_iteratedCovGrad_one_sharpFlatEndoCc_le_of_lt_one
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      (h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      {δ : ℝ} (hδ : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
      (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + 1) x
          ((iteratedCovGrad (I := I) g₀ 1 1 1 (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
        C ^ 2 * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  obtain ⟨Ctrue, hCtrue0, harmTrue⟩ :=
    rfns_flatArmCc_le_of_lt_one (I := I) (M := M) g₀ hδ₀0 hδ₀ true
  obtain ⟨Cfalse, hCfalse0, harmFalse⟩ :=
    rfns_flatArmCc_le_of_lt_one (I := I) (M := M) g₀ hδ₀0 hδ₀ false
  refine ⟨Real.sqrt (2 * Ctrue ^ 2 + 2 * Cfalse ^ 2), by positivity, ?_⟩
  intro g₁ T h δ hδ hδ0 hbound x
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG_def
  have hG_nn : 0 ≤ G := norm_nonneg _
  have harms := rfns_iteratedCovGrad_sharpFlatEndoCc_succ_le_arms (I := I) (M := M) g₀ g₁ 0 x
  rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at harms
  have hbtrue := harmTrue g₁ T h hδ hδ0 hbound x
  have hbfalse := harmFalse g₁ T h hδ hδ0 hbound x
  rw [← hG_def] at hbtrue hbfalse
  refine harms.trans ?_
  have hcombine : 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((1 + 1) + 0) x
        ((flatArmCc (I := I) g₀ g₁ true).toSection x) +
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((1 + 1) + 0) x
        ((flatArmCc (I := I) g₀ g₁ false).toSection x) ≤
      2 * (Ctrue ^ 2 * G ^ 2) + 2 * (Cfalse ^ 2 * G ^ 2) := by
    have hbtrue' : riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((1 + 1) + 0) x
        ((flatArmCc (I := I) g₀ g₁ true).toSection x) ≤ Ctrue ^ 2 * G ^ 2 := hbtrue
    have hbfalse' : riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((1 + 1) + 0) x
        ((flatArmCc (I := I) g₀ g₁ false).toSection x) ≤ Cfalse ^ 2 * G ^ 2 := hbfalse
    linarith [hbtrue', hbfalse']
  refine hcombine.trans ?_
  have hCsq : Real.sqrt (2 * Ctrue ^ 2 + 2 * Cfalse ^ 2) ^ 2 = 2 * Ctrue ^ 2 + 2 * Cfalse ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [hCsq]
  ring_nf
  rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
