import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonDeTurckPullbackFlat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.EvaluationFormChainRule
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ParabolicInteriorSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.SpectralWeylCounting
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.WeylEigenvalueCountingBound
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartOverlapUniqueness
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.BareFlowFromJointC1
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.FlatIdentity
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open MeasureTheory Set

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## The interior heat-trace summability (the single Weyl-dependent input)

The classical local Weyl law (`weyl_eigenvalue_counting_bound_of_closed`, the one
deferred analytic input of the development) reduces — via the proven chain
`EigenvalueCountingBound ⟹ EigenvalueTailSummable` — to the existence of an
exponent `p > 0` with `∑ᵢ (1 + λᵢ)^{-p}` summable.  From this single fact the
**interior heat-trace summability** `∑ᵢ (1 + λᵢ)^σ · e^{-2 λᵢ ε} < ∞` follows for
every `σ` and every `ε > 0`: the heat factor `e^{-2 λᵢ ε}` overwhelms any
polynomial weight, so `(1 + λᵢ)^σ e^{-2 λᵢ ε} ≤ C · (1 + λᵢ)^{-p}` (a
`λ`-uniform polynomial-times-exponential bound), and comparison with the
summable tail closes it. -/

/-- **Interior heat-trace summability from eigenvalue-tail summability.**
For every `σ ≥ 0` and `ε > 0`, the heat-weighted spectral family
`i ↦ (1 + λᵢ)^σ · e^{-2 λᵢ ε}` is summable.  This is the finiteness of
`tr(e^{2εΔ} (1 − Δ)^σ)`, derived from the eigenvalue tail
`∑ᵢ (1 + λᵢ)^{-p} < ∞` by the `λ`-uniform smoothing bound
`(1 + λᵢ)^{σ+p} e^{-2 λᵢ ε} ≤ tensorSmoothingConst (σ+p) · (min ε 1)^{-(σ+p)}`. -/
theorem heatTraceWeighted_summable_of_tailSummable
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (htail : EigenvalueTailSummable (I := I) (M := M) g r s)
    (σ : ℝ) (hσ : 0 ≤ σ) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i σ *
        Real.exp (-(2 * (TensorEigenIdx.lambda (I := I) (M := M) i) * ε))) := by
  obtain ⟨p, hp_pos, htp⟩ := htail
  set C : ℝ := tensorSmoothingConst (σ + p) * (min ε 1) ^ (-(σ + p)) with hC
  have hC_nn : 0 ≤ C := by
    apply mul_nonneg (tensorSmoothingConst_nonneg _)
    exact Real.rpow_nonneg (le_of_lt (lt_min hε one_pos)) _
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (htp.mul_left C)
  · exact mul_nonneg (tensorSobolevWeight_nonneg _ _) (Real.exp_pos _).le
  · set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam
    have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
    have hbase_pos : (0 : ℝ) < 1 + lam := by linarith
    have hsplit : tensorSobolevWeight (I := I) (M := M) i σ =
        ((1 + lam) ^ (σ + p)) * ((1 + lam) ^ (-p)) := by
      unfold tensorSobolevWeight
      rw [hlam, ← Real.rpow_add hbase_pos]; congr 1; ring
    have hbound := tensorSmoothingScalarBound_of_pos
      (μ := σ + p) (by linarith) (t := ε) hε (lam := lam) hlam_nn
    calc tensorSobolevWeight (I := I) (M := M) i σ *
            Real.exp (-(2 * lam * ε))
        = ((1 + lam) ^ (σ + p) * Real.exp (-(2 * lam * ε))) * ((1 + lam) ^ (-p)) := by
          rw [hsplit]; ring
      _ ≤ C * ((1 + lam) ^ (-p)) := by
          apply mul_le_mul_of_nonneg_right hbound
          exact Real.rpow_nonneg hbase_pos.le _

omit [BoundarylessManifold I M] in
private theorem hom_integral_eq
    {g : SmoothRiemannianMetric I M} {a : ℝ} {T : ℝ}
    (u₀ : tensorHs (I := I) (M := M) g 0 2 (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) T) :
    (∫ τ in (0:ℝ)..s, (homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) τ)
      = (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * s) - 1) * u₀.coeff i := by
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  set c := u₀.coeff i with hc_def
  have hderiv : ⇑(homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) =ᵐ[timeMeasure T]
      fun t => -lam * (Real.exp (-lam * t) * c) :=
    coeFn_ofContinuousOn _
  have hint_congr : (∫ τ in (0:ℝ)..s, (homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) τ)
      = ∫ τ in (0:ℝ)..s, -lam * (Real.exp (-lam * τ) * c) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hsub : Set.uIoc (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) T :=
      (Set.uIoc_subset_uIcc).trans (uIcc_subset_Icc ⟨le_rfl, hs.1.trans hs.2⟩ hs)
    have hae := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hderiv
    rw [ae_restrict_iff' measurableSet_uIoc] at hae
    filter_upwards [hae] with τ hτ using hτ
  rw [hint_congr]
  have hF : ∀ τ : ℝ, HasDerivAt (fun τ => Real.exp (-lam * τ) * c)
      (-lam * (Real.exp (-lam * τ) * c)) τ := by
    intro τ
    have hlin : HasDerivAt (fun τ : ℝ => -lam * τ) (-lam) τ := by
      simpa using (hasDerivAt_id τ).const_mul (-lam)
    have hexp : HasDerivAt (fun τ => Real.exp (-lam * τ))
        (Real.exp (-lam * τ) * (-lam)) τ := hlin.exp
    have := hexp.mul_const c
    convert this using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hF τ)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [mul_zero, Real.exp_zero, one_mul]
  ring

omit [BoundarylessManifold I M] in
theorem coeffFun_u_eq
    {g_bg : SmoothRiemannianMetric I M} {a : ℝ} {T : ℝ}
    (u₀ : tensorHs (I := I) (M := M) g_bg 0 2 (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g_bg 0 2 a) T)
    (hT : 0 < T) (hT1 : T ≤ 1)
    (i : TensorEigenIdx (I := I) (M := M) g_bg 0 2)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) T) :
    (timeH1.toFun (maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce) s).coeff i
      = Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * s) * u₀.coeff i
        + ∫ τ in (0:ℝ)..s, (derivModeCoeff (I := I) (M := M) (a := a) hT.le gforce i) τ := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hs.1.trans hs.2⟩
  set u := maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce with hu_def
  have hcomm : (coeffCLM (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) (σ := a) i)
        (∫ τ in (0:ℝ)..s, u.deriv τ)
      = ∫ τ in (0:ℝ)..s, (u.deriv τ).coeff i := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm
      (coeffCLM (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) (σ := a) i)
      (u.intervalIntegrable_deriv h0 hs)]
    rfl
  have hval : (timeH1.toFun u s).coeff i =
      (u.init).coeff i + ∫ τ in (0:ℝ)..s, (u.deriv τ).coeff i := by
    have he : (timeH1.toFun u s).coeff i =
        (coeffCLM (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) (σ := a) i) (timeH1.toFun u s) := rfl
    rw [he, timeH1.toFun_apply, map_add, hcomm]
    rfl
  rw [hval]
  have hinit : (u.init).coeff i = u₀.coeff i := by
    rw [hu_def, maxRegDuhamelMap_init]; rfl
  rw [hinit]
  have hsplit_ae := maxRegDuhamelMap_deriv_coeff_ae (I := I) (M := M)
    (h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g_bg 0 2)
    (a := a) hT hT1 u₀ gforce i
  have hint_split : (∫ τ in (0:ℝ)..s, (u.deriv τ).coeff i)
      = (∫ τ in (0:ℝ)..s, (homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) τ)
        + ∫ τ in (0:ℝ)..s, (derivModeCoeff (I := I) (M := M) (a := a) hT.le gforce i) τ := by
    have hint_hom : IntervalIntegrable
        (fun τ => (homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) τ) volume 0 s :=
      ((integrableOn (homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i)).mono_set
        (uIcc_subset_Icc h0 hs)).intervalIntegrable
    have hint_duh : IntervalIntegrable
        (fun τ => (derivModeCoeff (I := I) (M := M) (a := a) hT.le gforce i) τ) volume 0 s :=
      ((integrableOn (derivModeCoeff (I := I) (M := M) (a := a) hT.le gforce i)).mono_set
        (uIcc_subset_Icc h0 hs)).intervalIntegrable
    rw [← intervalIntegral.integral_add hint_hom hint_duh]
    refine intervalIntegral.integral_congr_ae ?_
    have hsub : Set.uIoc (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) T :=
      (Set.uIoc_subset_uIcc).trans (uIcc_subset_Icc h0 hs)
    have hae := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hsplit_ae
    rw [ae_restrict_iff' measurableSet_uIoc] at hae
    filter_upwards [hae] with τ hτ hτmem
    exact (hτ hτmem)
  rw [hint_split, hom_integral_eq (I := I) (M := M) u₀ i hs]
  ring

omit [BoundarylessManifold I M] in
theorem duhamel_integral_abs_le
    {g : SmoothRiemannianMetric I M} {a : ℝ} {T : ℝ} (hT : 0 ≤ T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) T) :
    |∫ τ in (0:ℝ)..s, (derivModeCoeff (I := I) (M := M) (a := a) hT gforce i) τ|
      ≤ Real.sqrt T * ‖derivModeCoeff (I := I) (M := M) (a := a) hT gforce i‖ := by
  set v := derivModeCoeff (I := I) (M := M) (a := a) hT gforce i with hv_def
  set w := timeH1.mk (0:ℝ) v with hw_def
  have hval : (∫ τ in (0:ℝ)..s, (v) τ) = w.toFun s := by
    rw [timeH1.toFun_apply, hw_def, timeH1.init_mk,
      timeH1.deriv_mk, zero_add]
  have hbound := timeH1.norm_toFun_le w hs
  rw [timeH1.trace0_apply, timeH1.timeDeriv_apply,
    hw_def, timeH1.init_mk, timeH1.deriv_mk, norm_zero, zero_add] at hbound
  rw [hval, ← Real.norm_eq_abs]
  exact hbound

omit [BoundarylessManifold I M] in
private theorem u0_coeff_sq_summable
    {g : SmoothRiemannianMetric I M} {a : ℝ} (ha2 : 0 ≤ a + 2)
    (u₀ : tensorHs (I := I) (M := M) g 0 2 (a + 2)) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 => (u₀.coeff i) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) u₀.weighted_summable
  have hw : (1:ℝ) ≤ tensorSobolevWeight (I := I) (M := M) i (a + 2) := by
    rw [tensorSobolevWeight]
    exact Real.one_le_rpow (one_le_one_add_lambda (I := I) (M := M) i) ha2
  calc (u₀.coeff i)^2 = 1 * (u₀.coeff i)^2 := by ring
    _ ≤ tensorSobolevWeight (I := I) (M := M) i (a + 2) * (u₀.coeff i)^2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)

omit [BoundarylessManifold I M] in
private theorem hom_majorant_summable
    {g : SmoothRiemannianMetric I M} {a : ℝ} (ha2 : 0 ≤ a + 2)
    (u₀ : tensorHs (I := I) (M := M) g 0 2 (a + 2))
    (htail : EigenvalueTailSummable (I := I) (M := M) g 0 2)
    {σ : ℝ} (hσ : 0 ≤ σ) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ)
        * Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * ε) * |u₀.coeff i|) := by
  have hheat := heatTraceWeighted_summable_of_tailSummable (I := I) (M := M) htail σ hσ hε
  have hu0 := u0_coeff_sq_summable (I := I) (M := M) ha2 u₀
  have hmaj : Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
      (1/2 : ℝ) * (tensorSobolevWeight (I := I) (M := M) i σ
          * Real.exp (-(2 * (TensorEigenIdx.lambda (I := I) (M := M) i) * ε)) + (u₀.coeff i)^2)) :=
    ((hheat.add hu0).mul_left (1/2))
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hmaj
  · positivity
  · set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam
    set wσ := tensorSobolevWeight (I := I) (M := M) i σ with hwσ
    have hwσ_nn : 0 ≤ wσ := tensorSobolevWeight_nonneg (I := I) (M := M) i σ
    set A : ℝ := Real.sqrt (wσ * Real.exp (-(2 * lam * ε))) with hA
    set B : ℝ := |u₀.coeff i| with hB
    have hexp_sqrt : Real.sqrt (Real.exp (-(2 * lam * ε))) = Real.exp (-lam * ε) := by
      have he2 : Real.exp (-(2 * lam * ε)) = (Real.exp (-lam * ε))^2 := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [he2, Real.sqrt_sq (Real.exp_pos _).le]
    have hAB_eq : Real.sqrt wσ * Real.exp (-lam * ε) * B = A * B := by
      rw [hA, Real.sqrt_mul hwσ_nn, hexp_sqrt]
    rw [hAB_eq]
    have hAnn : 0 ≤ A := Real.sqrt_nonneg _
    have hBnn : 0 ≤ B := abs_nonneg _
    have hkey : 2 * A * B ≤ A^2 + B^2 := two_mul_le_add_sq A B
    have hA2 : A^2 = wσ * Real.exp (-(2 * lam * ε)) := by
      rw [hA, Real.sq_sqrt (by positivity)]
    have hB2 : B^2 = (u₀.coeff i)^2 := by rw [hB, sq_abs]
    nlinarith [hkey, hA2, hB2]

omit [BoundarylessManifold I M] in
private theorem norm_derivModeCoeff_le
    {g : SmoothRiemannianMetric I M} {a : ℝ} {T : ℝ} (hT : 0 ≤ T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    ‖derivModeCoeff (I := I) (M := M) (a := a) hT gforce i‖
      ≤ 2 * ‖timeModeCoeff (I := I) (M := M) gforce i‖ := by
  rw [derivModeCoeff]
  exact perModeConvDerivL2_sq_le _ (tensor_lambda_nonneg (I := I) (M := M) i) hT _

omit [BoundarylessManifold I M] in
theorem duhamel_majorant_summable
    {g : SmoothRiemannianMetric I M} {a : ℝ} {T : ℝ}
    (gforce : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T)
    (htail : EigenvalueTailSummable (I := I) (M := M) g 0 2)
    (hforce : ∀ d : ℝ, Summable (forcingMass (I := I) (M := M) gforce d))
    {σ : ℝ} :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ)
        * (Real.sqrt T * (2 * ‖timeModeCoeff (I := I) (M := M) gforce i‖))) := by
  obtain ⟨p, hp_pos, htp⟩ := htail
  have hfm := hforce (σ + p)
  have hmaj : Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
      Real.sqrt T * (forcingMass (I := I) (M := M) gforce (σ + p) i
        + (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-p))) :=
    (hfm.add htp).mul_left (Real.sqrt T)
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hmaj
  · positivity
  · set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam
    set wσ := tensorSobolevWeight (I := I) (M := M) i σ with hwσ
    set nm := ‖timeModeCoeff (I := I) (M := M) gforce i‖ with hnm
    have hbase_pos : (0:ℝ) < 1 + lam := by
      have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
    set A : ℝ := Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (σ + p)) * nm with hA
    set B : ℝ := Real.sqrt ((1 + lam) ^ (-p)) with hB
    have hw_split : tensorSobolevWeight (I := I) (M := M) i (σ + p) * (1 + lam) ^ (-p) = wσ := by
      rw [hwσ, tensorSobolevWeight, tensorSobolevWeight, hlam, ← Real.rpow_add hbase_pos]
      congr 1; ring
    have hAB_eq : Real.sqrt wσ * nm = A * B := by
      rw [hA, hB]
      rw [show Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (σ + p)) * nm
            * Real.sqrt ((1 + lam) ^ (-p))
          = (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (σ + p))
              * Real.sqrt ((1 + lam) ^ (-p))) * nm by ring,
        ← Real.sqrt_mul (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ+p)) ((1+lam)^(-p)),
        hw_split]
    have hAnn : 0 ≤ A :=
      mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    have hBnn : 0 ≤ B := Real.sqrt_nonneg _
    have hkey : 2 * A * B ≤ A^2 + B^2 := two_mul_le_add_sq A B
    have hA2 : A^2 = forcingMass (I := I) (M := M) gforce (σ + p) i := by
      rw [hA, mul_pow, Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ+p)),
        forcingMass, hnm]
    have hB2 : B^2 = (1 + lam) ^ (-p) := by
      rw [hB, Real.sq_sqrt (Real.rpow_nonneg hbase_pos.le _)]
    have hexpand : Real.sqrt wσ * (Real.sqrt T * (2 * nm)) = Real.sqrt T * (2 * (A * B)) := by
      rw [← hAB_eq]; ring
    rw [hexpand]
    have hTnn : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
    have h2ab : 2 * (A * B) ≤ A^2 + B^2 := by nlinarith [hkey]
    calc Real.sqrt T * (2 * (A * B))
        ≤ Real.sqrt T * (A^2 + B^2) := mul_le_mul_of_nonneg_left h2ab hTnn
      _ = Real.sqrt T * (forcingMass (I := I) (M := M) gforce (σ + p) i
            + (1 + lam) ^ (-p)) := by rw [hA2, hB2]

omit [BoundarylessManifold I M] in
theorem tsum_singleModeCLM_coeff
    {g : SmoothRiemannianMetric I M} {σ : ℝ}
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (hsum : Summable (fun j => singleModeCLM (I := I) (M := M) (g := g) (r := 0) (s := 2) (σ := σ) j (c j)))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    (∑' j, singleModeCLM (I := I) (M := M) (g := g) (r := 0) (s := 2) (σ := σ) j (c j)).coeff i = c i := by
  classical
  have hmap := ContinuousLinearMap.map_tsum
    (coeffCLM (I := I) (M := M) (g := g) (r := 0) (s := 2) (σ := σ) i) hsum
  have hlhs : (∑' j, singleModeCLM (I := I) (M := M) (g := g) (r := 0) (s := 2) (σ := σ) j (c j)).coeff i
      = (coeffCLM (I := I) (M := M) (g := g) (r := 0) (s := 2) (σ := σ) i)
          (∑' j, singleModeCLM (I := I) (M := M) (g := g) (r := 0) (s := 2) (σ := σ) j (c j)) := rfl
  rw [hlhs, hmap]
  have hterm : ∀ j, (coeffCLM (I := I) (M := M) (g := g) (r := 0) (s := 2) (σ := σ) i)
      (singleModeCLM (I := I) (M := M) (g := g) (r := 0) (s := 2) (σ := σ) j (c j))
      = (if j = i then c j else 0) := by
    intro j
    rw [coeffCLM_apply, singleModeCLM_coeff]
    by_cases h : j = i
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hc => h hc.symm)]
  rw [tsum_congr hterm, tsum_ite_eq i c]

omit [BoundarylessManifold I M] in
theorem continuousOn_coeffFun_u
    {g_bg : SmoothRiemannianMetric I M} {a : ℝ} {T : ℝ}
    (u : MaxRegSolutionSpace (I := I) (M := M) a T)
    (i : TensorEigenIdx (I := I) (M := M) g_bg 0 2) :
    ContinuousOn (fun s => (timeH1.toFun u s).coeff i) (Set.Icc (0:ℝ) T) := by
  have hcomp : ContinuousOn
      (fun s => coeffCLM (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) (σ := a) i (timeH1.toFun u s))
      (Set.Icc (0:ℝ) T) :=
    (coeffCLM (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) (σ := a) i).continuous.comp_continuousOn
      u.continuousOn_toFun
  simpa only [coeffCLM_apply] using hcomp

omit [BoundarylessManifold I M] in
theorem norm_singleModeCLM_eq
    {g : SmoothRiemannianMetric I M} {σ : ℝ}
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) (c : ℝ) :
    ‖singleModeCLM (I := I) (M := M) (g := g) (r := 0) (s := 2) (σ := σ) i c‖
      = Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * |c| := by
  rw [singleModeCLM_apply, norm_smul, norm_tensorHsBasisVec (I := I) (M := M) i,
    Real.norm_eq_abs, mul_comm]

/-- **All-scale interior time-continuity of the maximal-regularity solution.**

The conclusion asks for a pointwise-in-time, `Hˢ`-valued continuous path `uσ`
on `[ε, T]` agreeing (after the spectral inclusion) with the base-scale
represented path `timeH1.toFun u`.  The witness is synthesised mode-by-mode: `uσ s`
is the `Hˢ` element with eigen-coordinates `i ↦ (timeH1.toFun u s).coeff i`, which
is the unconditional sum `∑ᵢ ((toFun u s).coeff i) • bᵢ` of single-mode fields.
Strong `Hˢ`-continuity on `[ε, T]` is the Weierstrass `M`-test
(`continuousOn_tsum`): each single-mode summand is continuous in time and the
mode-series of `Hˢ`-norms is dominated, uniformly on `[ε, T]`, by a summable
family whose finiteness is the **interior heat-trace summability**
`heatTraceWeighted_summable_of_tailSummable`, the sole Weyl-dependent input. -/
theorem interior_allscale_time_continuity
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (u₀ : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)) T)
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (hu : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1 u₀ gforce)
    (hcouple : ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT.le gforce (d + 1)) →
        Summable (forcingMass (I := I) (M := M) gforce d))
    (hbase : Summable (solFieldMass (I := I) (M := M) hT.le gforce (a : ℝ)))
    (σ : ℝ) (haσ : (a : ℝ) ≤ σ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ uσ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 σ,
        ContinuousOn uσ (Set.Icc ε T) ∧
          ∀ s ∈ Set.Icc ε T,
            tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) haσ
              (uσ s) = timeH1.toFun u s := by
  intro ε hε
  have ha0 : (0:ℝ) ≤ (a:ℝ) := Nat.cast_nonneg a
  have hσ0 : (0:ℝ) ≤ σ := le_trans ha0 haσ
  have ha2 : (0:ℝ) ≤ (a:ℝ) + 2 := by linarith
  have htail : EigenvalueTailSummable (I := I) (M := M) g_bg 0 2 :=
    eigenvalueTailSummable_of_countingBound (I := I) (M := M) g_bg 0 2
      (weyl_eigenvalue_counting_bound_of_closed (I := I) (M := M) g_bg 0 2)
  have hforce : ∀ d : ℝ, Summable (forcingMass (I := I) (M := M) gforce d) := by
    intro d
    exact hcouple d (solFieldMass_summable_all (I := I) (M := M) hT.le gforce hcouple hbase (d + 1))
  set cfun : TensorEigenIdx (I := I) (M := M) g_bg 0 2 → ℝ → ℝ :=
    fun i s => (timeH1.toFun u s).coeff i with hcfun_def
  set Mhom : TensorEigenIdx (I := I) (M := M) g_bg 0 2 → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ)
      * Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * ε) * |u₀.coeff i| with hMhom_def
  set Mduh : TensorEigenIdx (I := I) (M := M) g_bg 0 2 → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ)
      * (Real.sqrt T * (2 * ‖timeModeCoeff (I := I) (M := M) gforce i‖)) with hMduh_def
  have hMhom_sum : Summable Mhom :=
    hom_majorant_summable (I := I) (M := M) ha2 u₀ htail hσ0 hε
  have hMduh_sum : Summable Mduh :=
    duhamel_majorant_summable (I := I) (M := M) gforce htail hforce
  set Maj : TensorEigenIdx (I := I) (M := M) g_bg 0 2 → ℝ := fun i => Mhom i + Mduh i with hMaj_def
  have hMaj_sum : Summable Maj := hMhom_sum.add hMduh_sum
  have hbound : ∀ i, ∀ s ∈ Set.Icc ε T,
      ‖singleModeCLM (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) (σ := σ) i (cfun i s)‖ ≤ Maj i := by
    intro i s hsεT
    have hsT : s ∈ Set.Icc (0:ℝ) T := ⟨le_trans hε.le hsεT.1, hsεT.2⟩
    set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam
    have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
    have hval : cfun i s
        = Real.exp (-lam * s) * u₀.coeff i
          + ∫ τ in (0:ℝ)..s, (derivModeCoeff (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i) τ := by
      rw [hcfun_def, hu]
      exact coeffFun_u_eq (I := I) (M := M) u₀ gforce hT hT1 i hsT
    rw [norm_singleModeCLM_eq]
    set wσsqrt := Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) with hwσsqrt
    have hwσsqrt_nn : 0 ≤ wσsqrt := Real.sqrt_nonneg _
    have hexp_mono : Real.exp (-lam * s) ≤ Real.exp (-lam * ε) := by
      apply Real.exp_le_exp.mpr
      have : lam * ε ≤ lam * s := mul_le_mul_of_nonneg_left hsεT.1 hlam_nn
      nlinarith
    have hexp_nn : 0 ≤ Real.exp (-lam * s) := (Real.exp_pos _).le
    have habs : |cfun i s|
        ≤ Real.exp (-lam * ε) * |u₀.coeff i|
          + Real.sqrt T * (2 * ‖timeModeCoeff (I := I) (M := M) gforce i‖) := by
      rw [hval]
      refine le_trans (abs_add_le _ _) ?_
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg hexp_nn]
        exact mul_le_mul_of_nonneg_right hexp_mono (abs_nonneg _)
      · have h1 := duhamel_integral_abs_le (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i hsT
        have h2 := norm_derivModeCoeff_le (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i
        have hTnn : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
        calc |∫ τ in (0:ℝ)..s, (derivModeCoeff (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i) τ|
            ≤ Real.sqrt T * ‖derivModeCoeff (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i‖ := h1
          _ ≤ Real.sqrt T * (2 * ‖timeModeCoeff (I := I) (M := M) gforce i‖) :=
              mul_le_mul_of_nonneg_left h2 hTnn
    calc wσsqrt * |cfun i s|
        ≤ wσsqrt * (Real.exp (-lam * ε) * |u₀.coeff i|
            + Real.sqrt T * (2 * ‖timeModeCoeff (I := I) (M := M) gforce i‖)) :=
          mul_le_mul_of_nonneg_left habs hwσsqrt_nn
      _ = Maj i := by rw [hMaj_def, hMhom_def, hMduh_def, hwσsqrt]; ring
  have hsummable : ∀ s ∈ Set.Icc ε T,
      Summable (fun i => singleModeCLM (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) (σ := σ) i (cfun i s)) := by
    intro s hs
    exact Summable.of_norm_bounded hMaj_sum (fun i => hbound i s hs)
  refine ⟨fun s => ∑' i, singleModeCLM (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) (σ := σ) i (cfun i s), ?_, ?_⟩
  · refine continuousOn_tsum ?_ hMaj_sum (fun i s hs => hbound i s hs)
    intro i
    have hcfcont : ContinuousOn (fun s => cfun i s) (Set.Icc ε T) :=
      (continuousOn_coeffFun_u (I := I) (M := M) u i).mono
        (fun s hs => ⟨le_trans hε.le hs.1, hs.2⟩)
    exact (singleModeCLM (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) (σ := σ) i).continuous.comp_continuousOn hcfcont
  · intro s hs
    refine tensorHs.ext ?_
    funext i
    rw [tensorHsInclusion_coeff_apply,
      tsum_singleModeCLM_coeff (I := I) (M := M) (fun j => cfun j s) (hsummable s hs) i]

/-- **Up-to-`t = 0` all-scale time-continuity of the maximal-regularity solution with
smooth initial datum `0`.**

This is the `u₀ = 0` strengthening of `interior_allscale_time_continuity`: for the
smooth initial datum `0` the homogeneous majorant `Mhom` vanishes identically (it is
`Real.sqrt (weight σ) · exp (-λ ε) · |u₀.coeff i|` with `u₀ = 0`), so the only majorant
is the `ε`-independent Duhamel majorant `Mduh`; the Weierstrass `M`-test therefore
applies uniformly on the *closed* interval `[0, T]` (down to `t = 0`), not merely on
`[ε, T]`.  The witness `uσ s := ∑ᵢ ((toFun u s).coeff i) • bᵢ` is the same mode-by-mode
synthesis, and the everywhere bridge `ι (uσ s) = timeH1.toFun u s` holds for every
`s ∈ [0, T]`.

The first-order coupling `hcouple` (solution masses summable at order `d + 1` ⟹ forcing
masses summable at order `d`) supplies the forcing smoothness needed for the Duhamel
majorant; it is the genuine parabolic first-order-loss property of the nonlinearity, not
the continuity conclusion. -/
theorem zeroDatum_allscale_continuity_uptoZero
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (gforce : timeL2 (tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)) T)
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (hu : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2)) gforce)
    (hcouple : ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT.le gforce (d + 1)) →
        Summable (forcingMass (I := I) (M := M) gforce d))
    (σ : ℝ) (haσ : (a : ℝ) ≤ σ) :
    ∃ uσ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 σ,
      ContinuousOn uσ (Set.Icc (0 : ℝ) T) ∧
        ∀ s ∈ Set.Icc (0 : ℝ) T,
          tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) haσ
            (uσ s) = timeH1.toFun u s := by
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hσ0 : (0 : ℝ) ≤ σ := le_trans ha0 haσ
  have htail : EigenvalueTailSummable (I := I) (M := M) g_bg 0 2 :=
    eigenvalueTailSummable_of_countingBound (I := I) (M := M) g_bg 0 2
      (weyl_eigenvalue_counting_bound_of_closed (I := I) (M := M) g_bg 0 2)
  have hforce : ∀ d : ℝ, Summable (forcingMass (I := I) (M := M) gforce d) := by
    intro d
    exact hcouple d (solFieldMass_summable_all (I := I) (M := M) hT.le gforce hcouple
      (by
        -- base regularity at order `a` is free: `forcingMass gforce a` is summable, and
        -- the two-derivative gain bumps it to a solution-field bound at order `a + 2 ≥ a`.
        have hfm : Summable (forcingMass (I := I) (M := M) gforce ((a : ℝ) - 2)) := by
          have := summable_weight_mul_norm_timeModeCoeff_sq (I := I) (M := M) gforce
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g_bg 0 2)
          refine Summable.of_nonneg_of_le
            (fun i => forcingMass_nonneg (I := I) (M := M) gforce ((a : ℝ) - 2) i)
            (fun i => ?_) this
          have hbase_ge : (1 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
            one_le_one_add_lambda (I := I) (M := M) i
          have hwle : tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) - 2) ≤
              tensorSobolevWeight (I := I) (M := M) i (a : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hbase_ge (by linarith)
          simpa only [forcingMass] using
            mul_le_mul_of_nonneg_right hwle (sq_nonneg _)
        have hgain := solFieldMass_summable_of_forcingMass_summable (I := I) (M := M)
          hT.le gforce ((a : ℝ) - 2) hfm
        have hrw : (a : ℝ) - 2 + 2 = (a : ℝ) := by ring
        rw [hrw] at hgain
        exact hgain)
      (d + 1))
  set cfun : TensorEigenIdx (I := I) (M := M) g_bg 0 2 → ℝ → ℝ :=
    fun i s => (timeH1.toFun u s).coeff i with hcfun_def
  set Mduh : TensorEigenIdx (I := I) (M := M) g_bg 0 2 → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ)
      * (Real.sqrt T * (2 * ‖timeModeCoeff (I := I) (M := M) gforce i‖)) with hMduh_def
  have hMduh_sum : Summable Mduh :=
    duhamel_majorant_summable (I := I) (M := M) gforce htail hforce
  have hbound : ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖singleModeCLM (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) (σ := σ) i
        (cfun i s)‖ ≤ Mduh i := by
    intro i s hsT
    set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam
    have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
    have hval : cfun i s
        = ∫ τ in (0:ℝ)..s, (derivModeCoeff (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i) τ := by
      have hc : cfun i s = (timeH1.toFun u s).coeff i := rfl
      rw [hc, hu]
      have h := coeffFun_u_eq (I := I) (M := M)
        (0 : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2)) gforce hT hT1 i hsT
      rw [h]
      simp only [tensorHs.zero_coeff, mul_zero, zero_add]
    rw [norm_singleModeCLM_eq]
    set wσsqrt := Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) with hwσsqrt
    have hwσsqrt_nn : 0 ≤ wσsqrt := Real.sqrt_nonneg _
    have habs : |cfun i s|
        ≤ Real.sqrt T * (2 * ‖timeModeCoeff (I := I) (M := M) gforce i‖) := by
      rw [hval]
      have h1 := duhamel_integral_abs_le (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i hsT
      have h2 := norm_derivModeCoeff_le (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i
      have hTnn : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
      calc |∫ τ in (0:ℝ)..s, (derivModeCoeff (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i) τ|
          ≤ Real.sqrt T * ‖derivModeCoeff (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i‖ := h1
        _ ≤ Real.sqrt T * (2 * ‖timeModeCoeff (I := I) (M := M) gforce i‖) :=
            mul_le_mul_of_nonneg_left h2 hTnn
    calc wσsqrt * |cfun i s|
        ≤ wσsqrt * (Real.sqrt T * (2 * ‖timeModeCoeff (I := I) (M := M) gforce i‖)) :=
          mul_le_mul_of_nonneg_left habs hwσsqrt_nn
      _ = Mduh i := by rw [hMduh_def, hwσsqrt]
  have hsummable : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => singleModeCLM (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
        (σ := σ) i (cfun i s)) := by
    intro s hs
    exact Summable.of_norm_bounded hMduh_sum (fun i => hbound i s hs)
  refine ⟨fun s => ∑' i, singleModeCLM (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
    (σ := σ) i (cfun i s), ?_, ?_⟩
  · refine continuousOn_tsum ?_ hMduh_sum (fun i s hs => hbound i s hs)
    intro i
    exact (singleModeCLM (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) (σ := σ)
      i).continuous.comp_continuousOn (continuousOn_coeffFun_u (I := I) (M := M) u i)
  · intro s hs
    refine tensorHs.ext ?_
    funext i
    rw [tensorHsInclusion_coeff_apply,
      tsum_singleModeCLM_coeff (I := I) (M := M) (fun j => cfun j s) (hsummable s hs) i]

/-- **Per-mode square-sum domination of the smooth-datum (`u₀ = 0`) carrier.**

For the carrier `s ↦ timeH1.toFun u s` of the `u₀ = 0` Duhamel solution and any spatial
order `c`, the weighted squared eigen-coordinate is dominated, uniformly over `s ∈ [0,T]`,
by `4 · T · forcingMass gforce c i`.  The pointwise carrier coordinate is the indefinite
integral `∫₀ˢ derivModeCoeff gforce i` (the `u₀ = 0` case of `coeffFun_u_eq`), whose
absolute value is at most `√T · ‖derivModeCoeff‖` (`duhamel_integral_abs_le`), and the
derivative-mode norm is at most `2 · ‖timeModeCoeff gforce i‖` (`norm_derivModeCoeff_le`). -/
theorem zeroDatum_carrier_weighted_coeff_sq_le
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (gforce : timeL2 (tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)) T)
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (hu : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2)) gforce)
    (c : ℝ) (i : TensorEigenIdx (I := I) (M := M) g_bg 0 2)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    tensorSobolevWeight (I := I) (M := M) i c * (timeH1.toFun u s).coeff i ^ 2 ≤
      4 * T * forcingMass (I := I) (M := M) gforce c i := by
  have hT0 : (0 : ℝ) ≤ T := hT.le
  have hval : (timeH1.toFun u s).coeff i
      = ∫ τ in (0:ℝ)..s, (derivModeCoeff (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i) τ := by
    rw [hu]
    have h := coeffFun_u_eq (I := I) (M := M)
      (0 : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2)) gforce hT hT1 i hs
    rw [h]
    simp only [tensorHs.zero_coeff, mul_zero, zero_add]
  have hwc_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i c :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i c
  have hintabs := duhamel_integral_abs_le (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i hs
  have hderivnorm := norm_derivModeCoeff_le (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i
  have hcoeff_sq : (timeH1.toFun u s).coeff i ^ 2 ≤
      T * ‖derivModeCoeff (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i‖ ^ 2 := by
    have hsqrt_nn : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
    have hnn : 0 ≤ ‖derivModeCoeff (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i‖ :=
      norm_nonneg _
    have hsq : |∫ τ in (0:ℝ)..s, (derivModeCoeff (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i) τ| ^ 2
        ≤ (Real.sqrt T * ‖derivModeCoeff (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i‖) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hintabs 2
    rw [hval]
    calc (∫ τ in (0:ℝ)..s, (derivModeCoeff (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i) τ) ^ 2
        = |∫ τ in (0:ℝ)..s, (derivModeCoeff (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i) τ| ^ 2 := by
          rw [sq_abs]
      _ ≤ (Real.sqrt T * ‖derivModeCoeff (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i‖) ^ 2 := hsq
      _ = Real.sqrt T ^ 2 * ‖derivModeCoeff (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i‖ ^ 2 := by
          rw [mul_pow]
      _ = T * ‖derivModeCoeff (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i‖ ^ 2 := by
          rw [Real.sq_sqrt hT0]
  have htime_nn : 0 ≤ ‖timeModeCoeff (I := I) (M := M) gforce i‖ := norm_nonneg _
  have hderiv_sq : ‖derivModeCoeff (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i‖ ^ 2 ≤
      4 * ‖timeModeCoeff (I := I) (M := M) gforce i‖ ^ 2 := by
    have hnn : 0 ≤ ‖derivModeCoeff (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i‖ :=
      norm_nonneg _
    nlinarith [hderivnorm, hnn, htime_nn]
  calc tensorSobolevWeight (I := I) (M := M) i c * (timeH1.toFun u s).coeff i ^ 2
      ≤ tensorSobolevWeight (I := I) (M := M) i c *
          (T * ‖derivModeCoeff (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcoeff_sq hwc_nn
    _ ≤ tensorSobolevWeight (I := I) (M := M) i c *
          (T * (4 * ‖timeModeCoeff (I := I) (M := M) gforce i‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hwc_nn
        exact mul_le_mul_of_nonneg_left hderiv_sq hT0
    _ = 4 * T * forcingMass (I := I) (M := M) gforce c i := by
        rw [forcingMass]; ring

set_option maxHeartbeats 800000 in
/-- **Up-to-`t = 0` spectral decay of the smooth-datum (`u₀ = 0`) carrier.**

For the carrier `s ↦ timeH1.toFun u s` of the `u₀ = 0` Duhamel solution and any spatial
order `c` whose forcing mass is summable, the order-`c` weighted square-sum of the carrier
eigen-coordinates tends to `0` as `s → 0⁺`:

  `∑ᵢ (1 + λᵢ)^c · ((toFun u s).coeff i)² → 0`   as `s → 0⁺`.

This is the dominated-convergence (Tannery) limit: each summand
`(1 + λᵢ)^c · ((toFun u s).coeff i)²` tends to `0` (the carrier coordinate
`(toFun u s).coeff i → (toFun u 0).coeff i = u₀.coeff i = 0` by continuity, since the
initial datum is `0`), and is dominated uniformly over `s ∈ [0,T]` by the summable family
`4 · T · forcingMass gforce c i` (`zeroDatum_carrier_weighted_coeff_sq_le`). -/
theorem zeroDatum_carrier_weighted_tsum_tendsto_zero
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (gforce : timeL2 (tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)) T)
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (hu : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2)) gforce)
    (c : ℝ) (hc : Summable (forcingMass (I := I) (M := M) gforce c)) :
    Filter.Tendsto
      (fun s : ℝ => ∑' i : TensorEigenIdx (I := I) (M := M) g_bg 0 2,
        tensorSobolevWeight (I := I) (M := M) i c * (timeH1.toFun u s).coeff i ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  classical
  -- The pointwise limit of each summand is `0` as `s → 0⁺`.
  have hcoeff0 : ∀ i : TensorEigenIdx (I := I) (M := M) g_bg 0 2,
      (timeH1.toFun u 0).coeff i = 0 := by
    intro i
    rw [hu]
    have h := coeffFun_u_eq (I := I) (M := M)
      (0 : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2)) gforce hT hT1 i
      (⟨le_rfl, hT.le⟩ : (0:ℝ) ∈ Set.Icc (0:ℝ) T)
    rw [h]
    simp only [tensorHs.zero_coeff, mul_zero, zero_add, intervalIntegral.integral_same]
  have hab : ∀ i : TensorEigenIdx (I := I) (M := M) g_bg 0 2,
      Filter.Tendsto
        (fun s : ℝ => tensorSobolevWeight (I := I) (M := M) i c * (timeH1.toFun u s).coeff i ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    intro i
    have hcont : ContinuousWithinAt (fun s => (timeH1.toFun u s).coeff i)
        (Set.Icc (0:ℝ) T) 0 :=
      (continuousOn_coeffFun_u (I := I) (M := M) u i) 0 ⟨le_rfl, hT.le⟩
    -- The right-neighbourhood filter at `0` refines the `Icc 0 T`-within filter at `0`,
    -- because `Icc 0 T ⊇ Ioi 0 ∩ Iio T` is a neighbourhood of `0` within `Ioi 0`.
    have hIcc_mem : Set.Icc (0:ℝ) T ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) := by
      rw [mem_nhdsWithin]
      refine ⟨Set.Iio T, isOpen_Iio, hT, ?_⟩
      rintro x ⟨hxlt, hxgt⟩
      exact ⟨le_of_lt hxgt, le_of_lt hxlt⟩
    have hfilt : nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ nhdsWithin (0:ℝ) (Set.Icc (0:ℝ) T) :=
      nhdsWithin_le_iff.mpr hIcc_mem
    have htend0 : Filter.Tendsto (fun s => (timeH1.toFun u s).coeff i)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds ((timeH1.toFun u 0).coeff i)) :=
      hcont.tendsto.mono_left hfilt
    rw [hcoeff0 i] at htend0
    have : Filter.Tendsto
        (fun s : ℝ => tensorSobolevWeight (I := I) (M := M) i c * (timeH1.toFun u s).coeff i ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (tensorSobolevWeight (I := I) (M := M) i c * (0:ℝ) ^ 2)) :=
      (tendsto_const_nhds.mul (htend0.pow 2))
    simpa using this
  have hbound : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ i : TensorEigenIdx (I := I) (M := M) g_bg 0 2,
        ‖tensorSobolevWeight (I := I) (M := M) i c * (timeH1.toFun u s).coeff i ^ 2‖ ≤
          4 * T * forcingMass (I := I) (M := M) gforce c i := by
    have hmem : Set.Icc (0:ℝ) T ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) := by
      rw [mem_nhdsWithin]
      refine ⟨Set.Iio T, isOpen_Iio, hT, ?_⟩
      rintro x ⟨hxlt, hxgt⟩
      exact ⟨le_of_lt hxgt, le_of_lt hxlt⟩
    filter_upwards [hmem] with s hsmem i
    have hnn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i c * (timeH1.toFun u s).coeff i ^ 2 :=
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i c) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact zeroDatum_carrier_weighted_coeff_sq_le (I := I) (M := M) g_bg a gforce hT hT1
      u hu c i hsmem
  have hmaj : Summable (fun i : TensorEigenIdx (I := I) (M := M) g_bg 0 2 =>
      4 * T * forcingMass (I := I) (M := M) gforce c i) := hc.mul_left (4 * T)
  have := tendsto_tsum_of_dominated_convergence (𝓕 := nhdsWithin (0:ℝ) (Set.Ioi 0))
    (f := fun s i => tensorSobolevWeight (I := I) (M := M) i c * (timeH1.toFun u s).coeff i ^ 2)
    (g := fun _ => (0:ℝ))
    (bound := fun i => 4 * T * forcingMass (I := I) (M := M) gforce c i)
    hmaj hab hbound
  simpa using this

end DifferentialGeometry.PDE.RicciFlow
