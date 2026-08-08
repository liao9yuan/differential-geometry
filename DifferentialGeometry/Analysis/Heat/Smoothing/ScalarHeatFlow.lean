import DifferentialGeometry.Analysis.Heat.Smoothing.SpectralBridge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.ScalarPathReconstruct
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.ScalarWeyl
import DifferentialGeometry.Analysis.Heat.Semigroup.Mass
import DifferentialGeometry.Analysis.Parabolic.ScalarTimeDependent

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

noncomputable def scalarHeatCoeff
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (i : TensorEigenIdx00 g) (t : ℝ) : ℝ :=
  Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
    tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) u₀ i

noncomputable def scalarHeatFlow
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g) : ℝ → M → ℝ :=
  fun t x => scalarSpecSum (I := I) (M := M) g
    (fun i s => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t x

theorem scalarHeatCoeff_iteratedDeriv
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (i : TensorEigenIdx00 g) (t : ℝ) (j : ℕ) :
    iteratedDeriv j (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t =
      (-TensorEigenIdx.lambda (I := I) (M := M) i) ^ j *
        scalarHeatCoeff (I := I) (M := M) g u₀ i t := by
  let lam : ℝ := TensorEigenIdx.lambda (I := I) (M := M) i
  let d : ℝ := tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) u₀ i
  have hfun : (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) =
      fun s : ℝ => Real.exp ((-lam) * s) * d := by
    funext s
    rfl
  have hmain : iteratedDeriv j (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t =
      (-lam) ^ j * (Real.exp ((-lam) * t) * d) := by
    rw [hfun]
    rw [iteratedDeriv_mul_const_field]
    rw [iteratedDeriv_exp_const_mul]
    ring
  simpa [scalarHeatCoeff] using hmain

theorem scalarHeatCoeff_deriv
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (i : TensorEigenIdx00 g) (t : ℝ) :
    deriv (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t =
      -TensorEigenIdx.lambda (I := I) (M := M) i *
        scalarHeatCoeff (I := I) (M := M) g u₀ i t := by
  have h1 : deriv (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t =
      iteratedDeriv 1 (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t :=
    congrFun (iteratedDeriv_one (f := fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s)).symm t
  have h2 : iteratedDeriv 1 (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t =
      -TensorEigenIdx.lambda (I := I) (M := M) i *
        scalarHeatCoeff (I := I) (M := M) g u₀ i t := by
    simpa using scalarHeatCoeff_iteratedDeriv (I := I) (M := M) g u₀ i t 1
  exact h1.trans h2

theorem scalarHeatCoeff_hasDerivAt
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (i : TensorEigenIdx00 g) (t : ℝ) :
    HasDerivAt (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s)
      (-TensorEigenIdx.lambda (I := I) (M := M) i *
        scalarHeatCoeff (I := I) (M := M) g u₀ i t) t := by
  have hcd : ContDiff ℝ ∞ (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) := by
    dsimp [scalarHeatCoeff]
    exact (Real.contDiff_exp.comp
      ((contDiff_const.mul contDiff_id) : ContDiff ℝ ∞
        (fun s : ℝ => -TensorEigenIdx.lambda (I := I) (M := M) i * s))).mul
      contDiff_const
  exact ((hcd.differentiable (by norm_num) t).hasDerivAt).congr_deriv
    (scalarHeatCoeff_deriv (I := I) (M := M) g u₀ i t)

omit [NeZero (Module.finrank ℝ E)] in
lemma exists_pow_mul_exp_neg_bddAbove (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 0 ≤ x → x ^ n * Real.exp (-x) ≤ M := by
  classical
  let f : ℝ → ℝ := fun x => x ^ n * Real.exp (-x)
  have hcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hzero : Tendsto f atTop (𝓝 0) := by
    dsimp [f]
    exact Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n
  have hev : ∃ R : ℝ, 0 ≤ R ∧ ∀ x : ℝ, R ≤ x → f x ≤ 1 := by
    have h := (hzero.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one))
    obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp h
    have hR0 : 0 ≤ max R 0 := le_max_right _ _
    refine ⟨max R 0, hR0, ?_⟩
    intro x hx
    have hxR : R ≤ x := le_trans (le_max_left _ _) hx
    have hx0 : 0 ≤ x := le_trans hR0 hx
    have hdist : |f x - 0| < 1 := hR x hxR
    have hnonneg : 0 ≤ f x := by
      dsimp [f]
      exact mul_nonneg (pow_nonneg hx0 _) (Real.exp_pos _).le
    have hlt : f x < 1 := (abs_lt.mp (by simpa using hdist)).2
    exact hlt.le
  obtain ⟨R, hR0, hR⟩ := hev
  let K : Set ℝ := Set.Icc 0 R
  have hK : IsCompact K := isCompact_Icc
  have hKbdd : BddAbove (f '' K) := by
    exact (hK.image hcont).bddAbove
  obtain ⟨M₁, hM₁⟩ := hKbdd
  refine ⟨max M₁ 1, le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro x hx0
  by_cases hxR : x ≤ R
  · have hxK : x ∈ K := ⟨hx0, hxR⟩
    have hy : f x ∈ f '' K := ⟨x, hxK, rfl⟩
    exact le_trans (hM₁ hy) (le_max_left _ _)
  · have hRx : R ≤ x := le_of_not_ge hxR
    exact le_trans (hR x hRx) (le_max_right _ _)

omit [NeZero (Module.finrank ℝ E)] in
lemma exists_pow_mul_exp_neg_mul_bddAbove (a : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 0 ≤ x → x ^ n * Real.exp (-(2 * a * x)) ≤ M := by
  classical
  obtain ⟨M₀, hM₀, hbdd⟩ := exists_pow_mul_exp_neg_bddAbove n
  have h2a : 0 < 2 * a := mul_pos zero_lt_two ha
  refine ⟨((2 * a) ^ n)⁻¹ * M₀, mul_nonneg (inv_nonneg.mpr (pow_nonneg h2a.le _)) hM₀, ?_⟩
  intro x hx0
  have hy : 0 ≤ 2 * a * x := mul_nonneg h2a.le hx0
  have hb := hbdd (2 * a * x) hy
  have hne : (2 * a) ^ n ≠ 0 := pow_ne_zero _ h2a.ne'
  calc
    x ^ n * Real.exp (-(2 * a * x))
        = ((2 * a) ^ n)⁻¹ * ((2 * a * x) ^ n * Real.exp (-(2 * a * x))) := by
          rw [show (2 * a * x) ^ n = (2 * a) ^ n * x ^ n by ring]
          field_simp [hne]
    _ ≤ ((2 * a) ^ n)⁻¹ * M₀ := by
      exact mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (pow_nonneg h2a.le _))

omit [NeZero (Module.finrank ℝ E)] in
lemma exists_pow_add_mul_exp_neg_mul_bddAbove (a : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 0 ≤ x → (1 + x) ^ n * Real.exp (-(2 * a * x)) ≤ M := by
  classical
  obtain ⟨M₀, hM₀, hbdd⟩ := exists_pow_mul_exp_neg_mul_bddAbove a ha n
  refine ⟨max ((2 ^ n : ℝ) * M₀) (2 ^ n),
    le_trans (mul_nonneg (by positivity) hM₀) (le_max_left _ _), ?_⟩
  intro x hx0
  by_cases hx1 : x ≤ 1
  · have hle : (1 + x) ^ n ≤ 2 ^ n := by
      exact pow_le_pow_left₀ (by linarith) (by linarith) n
    calc
      (1 + x) ^ n * Real.exp (-(2 * a * x)) ≤ 2 ^ n * Real.exp (-(2 * a * x)) :=
        mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
      _ ≤ 2 ^ n := by
        rw [mul_comm]
        exact mul_le_of_le_one_left (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith))
      _ ≤ max ((2 ^ n : ℝ) * M₀) (2 ^ n) := le_max_right _ _
  · have h1x : 1 ≤ x := le_of_not_ge hx1
    have hle : (1 + x) ^ n ≤ (2 * x) ^ n := by
      exact pow_le_pow_left₀ (by nlinarith) (by nlinarith) n
    calc
      (1 + x) ^ n * Real.exp (-(2 * a * x)) ≤ (2 * x) ^ n * Real.exp (-(2 * a * x)) :=
        mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
      _ ≤ (2 ^ n : ℝ) * M₀ := by
        have h := hbdd x hx0
        have hm : 0 ≤ (2 ^ n : ℝ) := pow_nonneg (by norm_num) n
        calc
          (2 * x) ^ n * Real.exp (-(2 * a * x))
              = (2 ^ n : ℝ) * (x ^ n * Real.exp (-(2 * a * x))) := by
                rw [show (2 * x) ^ n = (2 ^ n : ℝ) * x ^ n by ring]
                ring
          _ ≤ (2 ^ n : ℝ) * M₀ := mul_le_mul_of_nonneg_left h hm
      _ ≤ max ((2 ^ n : ℝ) * M₀) (2 ^ n) := le_max_left _ _

lemma scalarHeatCoeff_deriv_sq
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (i : TensorEigenIdx00 g) (t : ℝ) (j : ℕ) :
    (iteratedDeriv j (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t) ^ 2 =
      TensorEigenIdx.lambda (I := I) (M := M) i ^ (2 * j) *
        Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
        (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) u₀ i) ^ 2 := by
  classical
  set lam : ℝ := TensorEigenIdx.lambda (I := I) (M := M) i
  set d : ℝ := tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) u₀ i
  have hfun : (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) =
      fun s : ℝ => Real.exp ((-lam) * s) * d := by
    funext s
    rfl
  have hpow : ((-lam) ^ j) ^ 2 = lam ^ (2 * j) := by
    rw [show ((-lam) ^ j) ^ 2 = (-lam) ^ (2 * j) by
      rw [← pow_mul]
      ring_nf]
    rw [show (-lam) ^ (2 * j) = ((-lam) ^ 2) ^ j by
      rw [pow_mul]]
    rw [neg_sq]
    rw [← pow_mul]
  have hmain :
      (iteratedDeriv j (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t) ^ 2 =
        lam ^ (2 * j) * Real.exp (-(2 * lam * t)) * d ^ 2 := by
    rw [hfun]
    rw [iteratedDeriv_mul_const_field]
    rw [iteratedDeriv_exp_const_mul]
    change ((-lam) ^ j * Real.exp ((-lam) * t) * d) ^ 2 =
        lam ^ (2 * j) * Real.exp (-(2 * lam * t)) * d ^ 2
    have hexp : (Real.exp ((-lam) * t)) ^ 2 = Real.exp (-(2 * lam * t)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    calc
      ((-lam) ^ j * Real.exp ((-lam) * t) * d) ^ 2
          = ((-lam) ^ j) ^ 2 * (Real.exp ((-lam) * t)) ^ 2 * d ^ 2 := by
              rw [mul_pow, mul_pow]
      _ = lam ^ (2 * j) * (Real.exp ((-lam) * t)) ^ 2 * d ^ 2 := by
              rw [hpow]
      _ = lam ^ (2 * j) * Real.exp (-(2 * lam * t)) * d ^ 2 := by
              rw [hexp]
  simp [hmain]

lemma scalarHeatCoeff_weighted_deriv_sq_le
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    {a : ℝ} (ha : 0 < a) (j m : ℕ) :
    ∃ C : TensorEigenIdx00 g → ℝ, Summable C ∧
      ∀ i t, t ∈ Set.Icc a b →
        tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
          (iteratedDeriv j (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t) ^ 2 ≤
          C i := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0
  let N : ℕ := m + 2 * j
  obtain ⟨CM, hCM0, hbdd⟩ := exists_pow_add_mul_exp_neg_mul_bddAbove a ha N
  refine ⟨fun i => CM * (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2, ?_, ?_⟩
  · exact Summable.mul_left CM (tensorL2Coeff_summable_sq hc u₀)
  · intro i t ht
    have hlam0 : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
      tensor_lambda_nonneg (I := I) (M := M) i
    have ht_le : a ≤ t := (Set.mem_Icc.mp ht).1
    have hexp : Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) ≤
        Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * a)) := by
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hb := hbdd (TensorEigenIdx.lambda (I := I) (M := M) i) hlam0
    have hbase_pos : 0 < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
      linarith [hlam0]
    have hb2 : (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (N : ℝ) *
          Real.exp (-(2 * a * TensorEigenIdx.lambda (I := I) (M := M) i)) ≤ CM := by
      simpa [Real.rpow_natCast] using hb
    have hle0 : TensorEigenIdx.lambda (I := I) (M := M) i ^ (2 * j) ≤
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) := by
      exact pow_le_pow_left₀ hlam0 (by linarith) (2 * j)
    have hw : tensorSobolevWeight (I := I) (M := M) i (m : ℝ) =
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (m : ℝ) := rfl
    have hprod :
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (m : ℝ) *
            (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) =
          (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (N : ℝ) := by
      rw [← Real.rpow_natCast (1 + TensorEigenIdx.lambda (I := I) (M := M) i) (2 * j)]
      rw [← Real.rpow_add hbase_pos]
      congr 1
      norm_num [N]
    have hd2 : 0 ≤ (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2 := sq_nonneg _
    have hw0 : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (m : ℝ) :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i (m : ℝ)
    have hexp_arg : -(2 * TensorEigenIdx.lambda (I := I) (M := M) i * a) =
        -(2 * a * TensorEigenIdx.lambda (I := I) (M := M) i) := by ring
    have hmain :
        tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
            (TensorEigenIdx.lambda (I := I) (M := M) i ^ (2 * j) *
              Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
              (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2) ≤
          CM * (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2 := by
      calc
        tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
            (TensorEigenIdx.lambda (I := I) (M := M) i ^ (2 * j) *
              Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
              (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2)
            ≤ tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
                ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) *
                  Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
                  (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2) := by
              have h1 :
                  TensorEigenIdx.lambda (I := I) (M := M) i ^ (2 * j) *
                      Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
                      (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2 ≤
                    (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) *
                      Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
                      (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2 := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hle0 (Real.exp_pos _).le) hd2
              exact mul_le_mul_of_nonneg_left h1 hw0
        _ ≤ tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
                ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) *
                  Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * a)) *
                  (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2) := by
              have h02 : 0 ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) *
                  (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2 := by positivity
              have hleq :
                  (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) *
                    Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
                    (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2 ≤
                  (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) *
                    Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * a)) *
                    (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2 := by
                calc
                  (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) *
                      Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
                      (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2
                      = (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) *
                          (Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
                            (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2) := by ring
                  _ ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) *
                          (Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * a)) *
                            (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2) := by
                        exact mul_le_mul_of_nonneg_left
                          (mul_le_mul_of_nonneg_right hexp hd2) (by positivity)
                  _ = (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) *
                          Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * a)) *
                          (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2 := by ring
              exact mul_le_mul_of_nonneg_left hleq hw0
        _ = (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (N : ℝ) *
              Real.exp (-(2 * a * TensorEigenIdx.lambda (I := I) (M := M) i)) *
              (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2 := by
              rw [hw]
              have hx :
                  (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (m : ℝ) *
                    (((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j)) *
                      Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * a)) *
                      (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2) =
                  ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (m : ℝ) *
                    (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j)) *
                    (Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * a)) *
                      (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2) := by ring
              rw [hx, hprod]
              have heqexp : Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * a)) =
                  Real.exp (-(2 * a * TensorEigenIdx.lambda (I := I) (M := M) i)) := by
                rw [hexp_arg]
              rw [heqexp]
              ring_nf
        _ ≤ CM * (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2 := by
              exact mul_le_mul_of_nonneg_right hb2 hd2
    calc
      tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
          (iteratedDeriv j (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t) ^ 2
          = tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
              (TensorEigenIdx.lambda (I := I) (M := M) i ^ (2 * j) *
                Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
                (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2) := by
            rw [scalarHeatCoeff_deriv_sq]
      _ ≤ CM * (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2 := by
              exact hmain
end HeatEquation
end Analysis
end DifferentialGeometry

end
