import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.NLCEndpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.CurvatureBound

/-!
# Reusable core for controlled-ball reduced-volume bounds

This module separates the pointwise action and density estimates, the
parametrized good-source estimate, and the final good/bad integral split from
the short-scale choices made by noncollapsing consumers.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.HCGCompactness

universe u uE uH

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A minimizing regularized L-ray contained in a curvature-controlled moving
ball has the scale-normalized reduced-length lower bound. -/
theorem lRedLen_of_range
    {F : Type uE} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [FiniteDimensional Real F] [NeZero (Module.finrank Real F)]
    {G : Type uH} [TopologicalSpace G]
    {J : ModelWithCorners Real F G} [J.Boundaryless]
    {N : Type u} [PseudoMetricSpace N] [ChartedSpace G N]
    [IsManifold J ∞ N] [T2Space N] [CompactSpace N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := J) (M := N) D) (hS : IsSolutionOn (I := J) S)
    (time : RealTimeInterval.FlowTime D) {eps : Real} (heps : 0 < eps)
    (heps1 : eps ≤ 1)
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    (Z : TangentSpace J B.center)
    (hZinj : Z ∈ lInjDomain S (time : Real) B.center
      (eps * B.radius ^ 2))
    (hrange :
      let b := Real.sqrt eps * B.radius
      ∀ s ∈ Icc (0 : Real) b,
        lRegCurve S (time : Real) B.center Z s ∈
          B.setAt ((time : Real) - s ^ 2)) :
    -((Module.finrank Real F : Real) ^ 2 * eps) ≤
      redLength S (time : Real) B.center
        (lExp S (time : Real) B.center Z (eps * B.radius ^ 2))
        (eps * B.radius ^ 2) := by
  let tau : Real := eps * B.radius ^ 2
  let b : Real := Real.sqrt eps * B.radius
  let n : Real := Module.finrank Real F
  let K : Real := n ^ 2 * Real.sqrt (1 / B.radius ^ 4)
  have htau : 0 < tau := mul_pos heps (sq_pos_of_pos B.radius_pos)
  have hb : Real.sqrt tau = b := by
    dsimp only [tau, b]
    rw [Real.sqrt_mul heps.le, Real.sqrt_sq_eq_abs, abs_of_pos B.radius_pos]
  have hbpos : 0 < b := by rw [← hb]; exact Real.sqrt_pos.2 htau
  have hbSq : b ^ 2 = tau := by rw [← hb, Real.sq_sqrt htau.le]
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg n) (Real.sqrt_nonneg _)
  have hrange' := hrange
  dsimp only at hrange'
  obtain ⟨sigma, hsigma, hmin⟩ := hZinj
  have hminTau : (Z, tau) ∈ lMinDomain S (time : Real) B.center := by
    exact lMinDomain_down S hS (time : Real) B.center Z hmin htau
      (by simpa only [tau] using hsigma.le)
  have hdomTau : (Z, tau) ∈ lExpPosDom S (time : Real) B.center :=
    ((mem_lMinDomain S (time : Real) B.center Z tau).1 hminTau).1
  have hbdom : b ∈ lRegDomain S (time : Real) B.center Z := by
    rcases (mem_lExpPosDom S (time : Real) B.center Z tau).1 hdomTau with
      ⟨_, _, hdom⟩
    simpa only [hb] using hdom
  let alpha : Real → N := lRegCurve S (time : Real) B.center Z
  have halpha : ContMDiffOn (modelWithCornersSelf Real Real) J 1 alpha
      (Icc (0 : Real) b) := by
    simpa only [alpha] using
      lRegCurve_c1On S hS (time : Real) B.center Z hbdom
  have hregRay : ∀ s ∈ Icc (0 : Real) b,
      (time : Real) - s ^ 2 ∈ D.regular := by
    intro s hs
    exact lRegDomain_reg S (time : Real) B.center Z
      (lRegDomain_seg S (time : Real) B.center Z hbdom hs.1 hs.2)
  have hLagInt : IntervalIntegrable (lRegLag S (time : Real) alpha) volume 0 b :=
    lRegLag_int_c1 S hS.smoothMetric ⟨hS.scalarCont⟩ (time : Real) 0 b
      hbpos.le alpha halpha hregRay
  have hconstInt : IntervalIntegrable (fun _ : Real ↦ -2 * b ^ 2 * K)
      volume 0 b := intervalIntegrable_const
  have hLagLower : ∀ s ∈ Icc (0 : Real) b,
      -2 * b ^ 2 * K ≤ lRegLag S (time : Real) alpha s := by
    intro s hs
    have hsSq : s ^ 2 ≤ b ^ 2 :=
      (sq_le_sq₀ hs.1 hbpos.le).2 hs.2
    have hbRad : b ^ 2 ≤ B.radius ^ 2 := by
      rw [hbSq]
      dsimp only [tau]
      nlinarith [sq_nonneg B.radius]
    have htimeB : (time : Real) - s ^ 2 ∈
        Icc ((time : Real) - B.radius ^ 2) (time : Real) :=
      ⟨by linarith, by nlinarith [sq_nonneg s]⟩
    have hsc : -K ≤ S.scalar ((time : Real) - s ^ 2) (alpha s) := by
      simpa only [K, n, alpha, SolutionOn.scalar, SolutionFamily.scalar] using
        scalar_ge_of_rm (I := J) B hB htimeB (hrange' s hs)
    have hkin : 0 ≤ (1 / 2 : Real) *
        (S.base.metric ((time : Real) - s ^ 2)).inner (alpha s)
          (lVelocity (I := J) alpha s) (lVelocity (I := J) alpha s) := by
      apply mul_nonneg (by norm_num)
      by_cases hv : lVelocity (I := J) alpha s = 0
      · rw [hv]
        rw [((S.base.metric ((time : Real) - s ^ 2)).inner (alpha s)).map_zero,
          ContinuousLinearMap.zero_apply]
      · exact ((S.base.metric ((time : Real) - s ^ 2)).pos
          (alpha s) (lVelocity (I := J) alpha s) hv).le
    have hscalar : -2 * b ^ 2 * K ≤
        2 * s ^ 2 * S.scalar ((time : Real) - s ^ 2) (alpha s) := by
      have h₁ : -2 * b ^ 2 * K ≤ -2 * s ^ 2 * K := by
        nlinarith
      have h₂ : -2 * s ^ 2 * K ≤
          2 * s ^ 2 * S.scalar ((time : Real) - s ^ 2) (alpha s) := by
        nlinarith [sq_nonneg s]
      exact h₁.trans h₂
    dsimp only [lRegLag]
    linarith
  have haction : -2 * b ^ 2 * K * b ≤
      lRegAction S (time : Real) alpha 0 b := by
    unfold lRegAction
    have hmono := intervalIntegral.integral_mono_on hbpos.le hconstInt hLagInt hLagLower
    calc
      -2 * b ^ 2 * K * b = b * (-2 * b ^ 2 * K) := by ring
      _ ≤ lRegAction S (time : Real) alpha 0 b := by
        simpa only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] using hmono
  have hcost : lCost S (time : Real) B.center
      (lExp S (time : Real) B.center Z tau) tau =
        lRegAction S (time : Real) alpha 0 b := by
    have hlen : lLength S (time : Real)
        (fun r : Real ↦ lExp S (time : Real) B.center Z r) 0 tau =
          lRegAction S (time : Real) alpha 0 b := by
      simpa only [alpha, lExp, sqrtReparam, hb] using
        lLength_sqrt (I := J) S (time : Real) alpha tau htau.le
    exact (((mem_lMinDomain S (time : Real) B.center Z tau).1 hminTau).2.symm).trans hlen
  have hscaleK : B.radius ^ 2 * K = n ^ 2 := by
    dsimp only [K, n]
    have hr2 : 0 < B.radius ^ 2 := sq_pos_of_pos B.radius_pos
    rw [show B.radius ^ 4 = (B.radius ^ 2) ^ 2 by ring]
    rw [show 1 / (B.radius ^ 2) ^ 2 = (1 / B.radius ^ 2) ^ 2 by field_simp]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hr2)]
    field_simp [B.radius_pos.ne']
  have hb2K : b ^ 2 * K = n ^ 2 * eps := by
    rw [hbSq]
    dsimp only [tau]
    calc
      eps * B.radius ^ 2 * K = eps * (B.radius ^ 2 * K) := by ring
      _ = eps * n ^ 2 := by rw [hscaleK]
      _ = n ^ 2 * eps := by ring
  rw [redLength, hcost, hb]
  have hden : 0 < 2 * b := mul_pos (by norm_num) hbpos
  apply (le_div_iff₀ hden).2
  calc
    -(n ^ 2 * eps) * (2 * b) = -2 * (n ^ 2 * eps) * b := by ring
    _ = -2 * (b ^ 2 * K) * b := by rw [hb2K]
    _ = -2 * b ^ 2 * K * b := by ring
    _ ≤ lRegAction S (time : Real) alpha 0 b := haction

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A reduced-length lower bound gives the corresponding pointwise reduced-density upper bound. -/
theorem lRedDen_of_len
    {F : Type uE} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [FiniteDimensional Real F]
    {G : Type uH} [TopologicalSpace G]
    {J : ModelWithCorners Real F G} [J.Boundaryless]
    {N : Type u} [PseudoMetricSpace N] [ChartedSpace G N]
    [IsManifold J ∞ N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := J) (M := N) D) (T : Real) (x y : N)
    (tau C : Real) (hlen : -C ≤ redLength S T x y tau) :
    redDensity S T x y tau ≤
      Real.exp
        (C - ((Module.finrank Real F : Real) / 2) * Real.log tau -
          ((Module.finrank Real F : Real) / 2) * Real.log (4 * Real.pi)) := by
  unfold redDensity
  apply Real.exp_le_exp.mpr
  linarith

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Change of variables bounds the pulled-back reduced density on any measurable
good-source set whose L-exponential image lies in a prescribed target set. -/
theorem lRedJac_set_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {tau : Real} (htau : 0 < tau)
    (A : Set E) (K : Set M) (hAmeas : MeasurableSet A)
    (hAinj : A ⊆ lInjDomain S T x tau) (c : Real)
    (hImage : ∀ Z ∈ A, lExp S T x Z tau ∈ K)
    (hden : ∀ Z ∈ A, redDensity S T x (lExp S T x Z tau) tau ≤ c) :
    (∫⁻ Z in A,
        ENNReal.ofReal (lRedJac S T x Z tau * lSrcDensity S T x)
        ∂(modelHaar (E := E))) ≤
      ENNReal.ofReal c *
        riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric (T - tau)) K := by
  let Ψ := lExpPartial S hS T x tau htau
  have hAsource : A ⊆ Ψ.source := by
    dsimp only [Ψ]
    rw [lExpPartial_source S hS T x tau htau]
    exact hAinj
  have hImageMeas : MeasurableSet (Ψ '' A) :=
    measurableSet_image_param_global (I := I) Ψ hAmeas hAsource
  have hImageK : Ψ '' A ⊆ K := by
    rintro y ⟨Z, hZA, rfl⟩
    dsimp only [Ψ]
    rw [lExpPartial_apply S hS T x tau htau (hAinj hZA)]
    exact hImage Z hZA
  have hImageDen : ∀ y ∈ Ψ '' A,
      ENNReal.ofReal (redDensity S T x y tau) ≤ ENNReal.ofReal c := by
    rintro y ⟨Z, hZA, rfl⟩
    dsimp only [Ψ]
    rw [lExpPartial_apply S hS T x tau htau (hAinj hZA)]
    exact ENNReal.ofReal_le_ofReal (hden Z hZA)
  have hparam :
      (∫⁻ y in Ψ '' A,
          ENNReal.ofReal (redDensity S T x y tau)
          ∂riemannianVolumeMeasure (I := I) (M := M)
            (S.base.metric (T - tau))) =
        ∫⁻ Z in A,
          ENNReal.ofReal (paramDensity (S.base.metric (T - tau)) Ψ Z) *
            ENNReal.ofReal (redDensity S T x (Ψ Z) tau)
          ∂modelHaar (E := E) :=
    riemVol_param_lint (I := I) (S.base.metric (T - tau)) Ψ
      (fun y ↦ ENNReal.ofReal (redDensity S T x y tau)) hAmeas hAsource
  have hsmallEq :
      (∫⁻ Z in A,
          ENNReal.ofReal (lRedJac S T x Z tau * lSrcDensity S T x)
          ∂modelHaar (E := E)) =
        ∫⁻ y in Ψ '' A,
          ENNReal.ofReal (redDensity S T x y tau)
          ∂riemannianVolumeMeasure (I := I) (M := M)
            (S.base.metric (T - tau)) := by
    rw [hparam]
    refine MeasureTheory.setLIntegral_congr_fun hAmeas ?_
    intro Z hZA
    dsimp only [Ψ]
    rw [lExpPartial_density S hS T x tau htau (hAinj hZA),
      lExpPartial_apply S hS T x tau htau (hAinj hZA)]
    rw [← ENNReal.ofReal_mul (lExpDensity_pos S hS T x htau (hAinj hZA)).le]
    exact congrArg ENNReal.ofReal
      (lRedJac_mul_src S hS T x htau (hAinj hZA))
  calc
    (∫⁻ Z in A,
        ENNReal.ofReal (lRedJac S T x Z tau * lSrcDensity S T x)
        ∂modelHaar (E := E)) =
      ∫⁻ y in Ψ '' A,
        ENNReal.ofReal (redDensity S T x y tau)
        ∂riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric (T - tau)) := hsmallEq
    _ ≤ ∫⁻ _y in Ψ '' A, ENNReal.ofReal c
        ∂riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric (T - tau)) :=
      MeasureTheory.setLIntegral_mono' hImageMeas hImageDen
    _ ≤ ∫⁻ _y in K, ENNReal.ofReal c
        ∂riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric (T - tau)) :=
      MeasureTheory.lintegral_mono_set hImageK
    _ = ENNReal.ofReal c *
        riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric (T - tau)) K := by
      rw [MeasureTheory.setLIntegral_const]

omit [NeZero (Module.finrank Real E)] in
/-- A good/bad measurable partition combines its two pulled-back
reduced-volume estimates. -/
theorem redVolume_split
    {U A C : Set E} {f : E → ENNReal} {a c : ENNReal}
    (hCmeas : MeasurableSet C) (hunion : A ∪ C = U)
    (hdisj : Disjoint A C)
    (hsmall : (∫⁻ Z in A, f Z ∂(modelHaar (E := E))) ≤ a)
    (htail : (∫⁻ Z in C, f Z ∂(modelHaar (E := E))) ≤ c) :
    (∫⁻ Z in U, f Z ∂(modelHaar (E := E))) ≤ a + c := by
  rw [← hunion]
  calc
    (∫⁻ Z in A ∪ C, f Z ∂(modelHaar (E := E))) =
        (∫⁻ Z in A, f Z ∂(modelHaar (E := E))) +
          ∫⁻ Z in C, f Z ∂(modelHaar (E := E)) :=
      MeasureTheory.lintegral_union hCmeas hdisj
    _ ≤ a + c := add_le_add hsmall htail

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
