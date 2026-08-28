import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian

set_option autoImplicit false

/-!
# Small-time L-Jacobian limits

This file records the first-order normalization of the regularized L-Jacobi
fields at square-root time zero.  It is the scalar-coordinate input for the
small-time Gram determinant limit.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace Real E] [CompactSpace M] in
/-- In a fixed tangent trivialization, a regularized L-Jacobi field divided by
`2s` converges to its prescribed initial tangent vector as `s → 0+`. -/
theorem lJacCoord_zero_lim
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z V : TangentSpace I x) (hT : T ∈ D.regular) :
    Tendsto
      (fun s : Real ↦ (2 * s)⁻¹ •
        chartRepAtBase (I := I) x (lRegCurve S T x Z)
          (lRegJacobiField S T x Z V) s)
      (nhdsWithin (0 : Real) (Ioi 0))
      (nhds ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt
        Real x V)) := by
  let gamma : Real → M := lRegCurve S T x Z
  let Y : ∀ s, TangentSpace I (gamma s) := lRegJacobiField S T x Z V
  let e := trivializationAt E (TangentSpace I) x
  let rep : Real → E := chartRepAtBase (I := I) x gamma Y
  have h0dom : (0 : Real) ∈ lRegDomain S T x Z :=
    zero_mem_lRegDomain S hS T x Z hT
  have hJac : HasLRegJacobiAt S T gamma Y 0 := by
    exact lRegCurve_jacobi S hS T x Z V (lRegDomain S T x Z)
      (fun _ hs ↦ hs) 0 h0dom
  have hgamma : MDifferentiableAt (modelWithCornersSelf Real Real) I gamma 0 := hJac.1
  have hY : DifferentiableAt Real
      (chartRepAt (I := I) gamma Y 0) 0 := hJac.2.1
  have hxchart : gamma 0 ∈ (chartAt H x).source := by
    simpa only [gamma, lRegCurve_zero] using mem_chart_source H x
  have hrepDiff : DifferentiableAt Real rep 0 := by
    exact chartRep_base_diff (I := I) gamma Y 0 x hgamma hxchart hY
  have hcov := covDeriv_chartAt (I := I) (S.base.metric T) gamma Y 0 x
    hgamma hxchart hY
  have hrep0 : rep 0 = 0 := by
    simp only [rep, chartRepAtBase_apply, Y, gamma, lRegJacobi_zero, map_zero]
  have hchartCov :
      chartCovDerivAlong (I := I) (S.base.metric T) x gamma rep 0 =
        deriv rep 0 := by
    rw [chartCovDerivAlong_def, hrep0,
      ChartChristoffel.contraction_zero_right, add_zero]
  have hcov' : e.symmL Real x (deriv rep 0) = (2 : Real) • V := by
    have hd0 := lRegJacobi_d0 (I := I) S hS T x Z V hT
    rw [show gamma 0 = x by simp only [gamma, lRegCurve_zero], hchartCov] at hcov
    simpa only [gamma, Y, e] using hcov.trans hd0
  have hxbase : x ∈ e.baseSet := by
    exact FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  have hderiv : deriv rep 0 = (2 : Real) • e.continuousLinearMapAt Real x V := by
    have h := congrArg (e.continuousLinearMapAt Real x) hcov'
    rw [e.continuousLinearMapAt_symmL (R := Real) hxbase,
      map_smul] at h
    exact h
  have hslope := (hrepDiff.hasDerivAt.congr_deriv hderiv).tendsto_slope_zero_right
  have hhalf : Tendsto
      (fun s : Real ↦ (1 / 2 : Real) • (s⁻¹ • (rep (0 + s) - rep 0)))
      (nhdsWithin (0 : Real) (Ioi 0))
      (nhds (e.continuousLinearMapAt Real x V)) := by
    simpa [smul_smul] using
      hslope.const_smul (1 / 2 : Real)
  refine hhalf.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := ne_of_gt hs
  simp only [zero_add, hrep0, sub_zero, smul_smul]
  change ((1 / 2 : Real) * s⁻¹) • rep s =
    (2 * s)⁻¹ • rep s
  congr 1
  field_simp [hs0]

section GramLimit

universe v vE vH

variable {F : Type vE} [NormedAddCommGroup F] [InnerProductSpace Real F]
  [FiniteDimensional Real F] [NeZero (Module.finrank Real F)]
variable {JH : Type vH} [TopologicalSpace JH]
variable {J : ModelWithCorners Real F JH} [J.Boundaryless]
variable {N : Type v} [PseudoMetricSpace N] [ChartedSpace JH N]
  [IsManifold J ∞ N] [T2Space N] [CompactSpace N]
variable {K : RealTimeInterval}

/-- The square-root-time Gram matrix after normalizing each regularized
L-Jacobi field by `2s`. -/
private noncomputable def lNormGram
    (S : SolutionOn (I := J) (M := N) K) (T : Real) (x : N)
    (Z : TangentSpace J x) (s : Real) :
    Matrix (Fin (Module.finrank Real F)) (Fin (Module.finrank Real F)) Real :=
  Matrix.of fun i j ↦
    (S.base.metric (T - s ^ 2)).inner (lRegCurve S T x Z s)
      ((2 * s)⁻¹ • lRegJacobiField S T x Z ((chartModelBasis F) i) s)
      ((2 * s)⁻¹ • lRegJacobiField S T x Z ((chartModelBasis F) j) s)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompactSpace N] in
private theorem lNormGram_lim
    (S : SolutionOn (I := J) (M := N) K) (hS : IsSolutionOn (I := J) S)
    (T : Real) (x : N) (Z : TangentSpace J x) (hT : T ∈ K.regular) :
    Tendsto (lNormGram S T x Z)
      (nhdsWithin (0 : Real) (Ioi 0))
      (nhds (lSrcGram S T x)) := by
  classical
  let gamma : Real → N := lRegCurve S T x Z
  let e := trivializationAt F (TangentSpace J) x
  let Y (V : TangentSpace J x) : ∀ s, TangentSpace J (gamma s) :=
    lRegJacobiField S T x Z V
  let U (V : TangentSpace J x) (s : Real) : F :=
    if s = 0 then e.continuousLinearMapAt Real x V
    else (2 * s)⁻¹ • chartRepAtBase (I := J) x gamma (Y V) s
  let W (V : TangentSpace J x) (s : Real) : TangentSpace J (gamma s) :=
    e.symmL Real (gamma s) (U V s)
  have hgamma : ContinuousAt gamma 0 := by
    have hjoint := (lRegCurve_smoothAt (I := J) (M := N) S hS T x Z hT).continuousAt
    exact hjoint.comp (continuousAt_const.prodMk continuousAt_id)
  have hgamma0 : gamma 0 = x := by
    simp only [gamma, lRegCurve_zero]
  have hxbase : x ∈ e.baseSet := by
    exact FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) x
  have hbase : ∀ᶠ s in nhds 0, gamma s ∈ e.baseSet := by
    have hgamma' : Tendsto gamma (nhds 0) (nhds x) := by
      change Tendsto gamma (nhds 0) (nhds (gamma 0)) at hgamma
      rw [hgamma0] at hgamma
      exact hgamma
    exact hgamma'.eventually (e.open_baseSet.mem_nhds hxbase)
  have hU (V : TangentSpace J x) :
      ContinuousWithinAt (U V) (Ioi 0) 0 := by
    change Tendsto (U V) (nhdsWithin (0 : Real) (Ioi 0)) (nhds (U V 0))
    have hU0 : U V 0 = e.continuousLinearMapAt Real x V := by
      simp only [U, if_pos]
    rw [hU0]
    refine (lJacCoord_zero_lim S hS T x Z V hT).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s := hs
    have hs0 : s ≠ 0 := ne_of_gt hspos
    simp only [U, hs0, if_false, Y, gamma]
  have hW (V : TangentSpace J x) : ContinuousWithinAt
      (fun s ↦ (TotalSpace.mk' F (gamma s) (W V s) : TangentBundle J N))
      (Ioi 0) 0 := by
    rw [FiberBundle.continuousWithinAt_totalSpace]
    refine ⟨hgamma.continuousWithinAt, ?_⟩
    have heq :
        (fun s ↦ ((trivializationAt F (TangentSpace J) (gamma 0))
          (TotalSpace.mk' F (gamma s) (W V s))).2) =ᶠ[nhdsWithin 0 (Ioi 0)]
          U V := by
      have hbase' : ∀ᶠ s in nhdsWithin 0 (Ioi 0), gamma s ∈ e.baseSet :=
        hbase.filter_mono inf_le_left
      filter_upwards [hbase'] with s hs
      rw [hgamma0]
      have hcoord :
          ((trivializationAt F (TangentSpace J) x)
            (TotalSpace.mk' F (gamma s) (W V s))).2 =
            e.continuousLinearMapAt Real (gamma s) (W V s) := by
        symm
        rw [e.continuousLinearMapAt_apply (R := Real)]
        rw [e.coe_linearMapAt_of_mem hs]
      rw [hcoord]
      exact e.continuousLinearMapAt_symmL (R := Real) hs (U V s)
    have heq0 :
        ((trivializationAt F (TangentSpace J) (gamma 0))
          (TotalSpace.mk' F (gamma 0) (W V 0))).2 = U V 0 := by
      rw [hgamma0]
      have hcoord :
          ((trivializationAt F (TangentSpace J) x)
            (TotalSpace.mk' F x (W V 0))).2 =
            e.continuousLinearMapAt Real x (W V 0) := by
        symm
        rw [e.continuousLinearMapAt_apply (R := Real)]
        rw [e.coe_linearMapAt_of_mem hxbase]
      rw [hcoord]
      have hW0 : W V 0 = e.symmL Real x (U V 0) := by
        simp only [W]
        rw [hgamma0]
      rw [hW0]
      exact e.continuousLinearMapAt_symmL (R := Real) hxbase (U V 0)
    exact (hU V).congr_of_eventuallyEq heq heq0
  refine tendsto_pi_nhds.2 ?_
  intro i
  refine tendsto_pi_nhds.2 ?_
  intro j
  let q : Real → Real × N := fun s ↦ (T - s ^ 2, gamma s)
  have hq : ContinuousAt q 0 := by
    exact (continuousAt_const.sub (continuousAt_id.pow 2)).prodMk hgamma
  have hmetric₀ := hS.smoothMetric.metricCLMSmoothAt
    (t := T) (x := gamma 0) (K.regular_isOpen.mem_nhds hT)
  have hmetric : ContinuousAt
      (fun s ↦ TotalSpace.mk' (F →L[Real] F →L[Real] Real)
        (E := fun y ↦ TangentSpace J y →L[Real]
          TangentSpace J y →L[Real] Real)
        (gamma s) ((S.base.metric (T - s ^ 2)).inner (gamma s))) 0 := by
    have hcomp := ContinuousAt.comp_of_eq
      (f := q)
      (g := fun p : Real × N ↦
        TotalSpace.mk' (F →L[Real] F →L[Real] Real)
          (E := fun y ↦ TangentSpace J y →L[Real]
            TangentSpace J y →L[Real] Real)
          p.2 ((S.family.metric p.1).inner p.2))
      hmetric₀.continuousAt hq (by norm_num [q])
    simpa only [SolutionOn.family_metric, q, zero_pow, sub_zero] using
      hcomp
  have htotal := ContinuousWithinAt.clm_bundle_apply₂
    (E₁ := fun y : N ↦ TangentSpace J y)
    (E₂ := fun y : N ↦ TangentSpace J y)
    (E₃ := fun _ : N ↦ Real)
    hmetric.continuousWithinAt (hW ((chartModelBasis F) i))
      (hW ((chartModelBasis F) j))
  rw [FiberBundle.continuousWithinAt_totalSpace] at htotal
  have hscalar : ContinuousWithinAt
      (fun s ↦ (S.base.metric (T - s ^ 2)).inner (gamma s)
        (W ((chartModelBasis F) i) s) (W ((chartModelBasis F) j) s))
      (Ioi 0) 0 := by
    let eR := trivializationAt Real (Bundle.Trivial N Real) (gamma 0)
    have heqR : ∀ s : Real,
        (eR (TotalSpace.mk' Real (gamma s)
          ((S.base.metric (T - s ^ 2)).inner (gamma s)
            (W ((chartModelBasis F) i) s) (W ((chartModelBasis F) j) s)))).2 =
          (S.base.metric (T - s ^ 2)).inner (gamma s)
            (W ((chartModelBasis F) i) s) (W ((chartModelBasis F) j) s) := by
      intro s
      simp only [eR, Trivial.fiberBundle_trivializationAt']
      rfl
    exact htotal.2.congr_of_eventuallyEq
      (Filter.Eventually.of_forall heqR) (heqR 0)
  have hlim : Tendsto
      (fun s ↦ (S.base.metric (T - s ^ 2)).inner (gamma s)
        (W ((chartModelBasis F) i) s) (W ((chartModelBasis F) j) s))
      (nhdsWithin (0 : Real) (Ioi 0))
      (nhds ((S.base.metric T).inner x
        ((chartModelBasis F) i) ((chartModelBasis F) j))) := by
    change Tendsto _ (nhdsWithin (0 : Real) (Ioi 0))
      (nhds ((S.base.metric T).inner x
        ((chartModelBasis F) i) ((chartModelBasis F) j)))
    change Tendsto _ (nhdsWithin (0 : Real) (Ioi 0))
      (nhds ((S.base.metric (T - 0 ^ 2)).inner (gamma 0)
        (W ((chartModelBasis F) i) 0) (W ((chartModelBasis F) j) 0))) at hscalar
    have hval :
        (S.base.metric (T - 0 ^ 2)).inner (gamma 0)
          (W ((chartModelBasis F) i) 0) (W ((chartModelBasis F) j) 0) =
        (S.base.metric T).inner x
          ((chartModelBasis F) i) ((chartModelBasis F) j) := by
      norm_num only [zero_pow, sub_zero]
      rw [hgamma0]
      simp only [W, U, if_pos]
      rw [hgamma0]
      rw [e.symmL_continuousLinearMapAt (R := Real) hxbase,
        e.symmL_continuousLinearMapAt (R := Real) hxbase]
    rw [hval] at hscalar
    exact hscalar
  refine hlim.congr' ?_
  have hbase' : ∀ᶠ s in nhdsWithin 0 (Ioi 0), gamma s ∈ e.baseSet :=
    hbase.filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hbase'] with s hs hsbase
  have hs0 : s ≠ 0 := ne_of_gt hs
  simp only [lNormGram, Matrix.of_apply, W, U, hs0, if_false]
  change (S.base.metric (T - s ^ 2)).inner (gamma s)
      (e.symmL Real (gamma s)
        ((2 * s)⁻¹ • e.continuousLinearMapAt Real (gamma s)
          (Y ((chartModelBasis F) i) s)))
      (e.symmL Real (gamma s)
        ((2 * s)⁻¹ • e.continuousLinearMapAt Real (gamma s)
          (Y ((chartModelBasis F) j) s))) = _
  have hWi : e.symmL Real (gamma s)
      ((2 * s)⁻¹ • e.continuousLinearMapAt Real (gamma s)
        (Y ((chartModelBasis F) i) s)) =
      (2 * s)⁻¹ • Y ((chartModelBasis F) i) s := by
    rw [map_smul, e.symmL_continuousLinearMapAt (R := Real) hsbase]
  have hWj : e.symmL Real (gamma s)
      ((2 * s)⁻¹ • e.continuousLinearMapAt Real (gamma s)
        (Y ((chartModelBasis F) j) s)) =
      (2 * s)⁻¹ • Y ((chartModelBasis F) j) s := by
    rw [map_smul, e.symmL_continuousLinearMapAt (R := Real) hsbase]
  rw [hWi, hWj]

omit [CompactSpace N] [NeZero (Module.finrank Real F)] in
private theorem lNormGram_eq
    (S : SolutionOn (I := J) (M := N) K) (T : Real) (x : N)
    (Z : TangentSpace J x) {s : Real} (hs : 0 < s) :
    lNormGram S T x Z s =
      ((2 * s)⁻¹ ^ 2) • lExpGram S T x Z (s ^ 2) := by
  classical
  ext i j
  simp only [lNormGram, lExpGram, lGram, Matrix.of_apply,
    Matrix.smul_apply, lExpField]
  rw [lExpJacobi_eq, lExpJacobi_eq, lExp, Real.sqrt_sq hs.le]
  simp only [smul_eq_mul]
  let beta := (S.base.metric (T - s ^ 2)).inner (lRegCurve S T x Z s)
  let Xi := lRegJacobiField S T x Z ((chartModelBasis F) i) s
  let Xj := lRegJacobiField S T x Z ((chartModelBasis F) j) s
  change beta ((2 * s)⁻¹ • Xi) ((2 * s)⁻¹ • Xj) =
    ((2 * s)⁻¹ ^ 2) * beta Xi Xj
  have hleft : beta ((2 * s)⁻¹ • Xi) ((2 * s)⁻¹ • Xj) =
      (2 * s)⁻¹ * beta Xi ((2 * s)⁻¹ • Xj) := by
    have h := congrArg
      (fun L : TangentSpace J (lRegCurve S T x Z s) →L[Real] Real ↦
        L ((2 * s)⁻¹ • Xj))
      (beta.map_smul (2 * s)⁻¹ Xi)
    simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using h
  have hright : beta Xi ((2 * s)⁻¹ • Xj) =
      (2 * s)⁻¹ * beta Xi Xj := by
    simpa only [smul_eq_mul] using (beta Xi).map_smul (2 * s)⁻¹ Xj
  rw [hleft, hright, pow_two]
  ring

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompactSpace N] in
/-- The L-exponential density has the Euclidean `s^n` source-density
asymptotic in square-root backward time. -/
theorem lExpDen_zero_lim
    (S : SolutionOn (I := J) (M := N) K) (hS : IsSolutionOn (I := J) S)
    (T : Real) (x : N) (Z : TangentSpace J x) (hT : T ∈ K.regular) :
    Tendsto
      (fun s : Real ↦ lExpDensity S T x Z (s ^ 2) /
        (2 * s) ^ (Module.finrank Real F))
      (nhdsWithin (0 : Real) (Ioi 0))
      (nhds (lSrcDensity S T x)) := by
  have hmatrix := lNormGram_lim S hS T x Z hT
  have hdet : Tendsto (fun s ↦ (lNormGram S T x Z s).det)
      (nhdsWithin (0 : Real) (Ioi 0))
      (nhds (lSrcGram S T x).det) := by
    simpa using (continuous_id.matrix_det.continuousAt.tendsto.comp hmatrix)
  have hsqrt : Tendsto (fun s ↦ Real.sqrt (lNormGram S T x Z s).det)
      (nhdsWithin (0 : Real) (Ioi 0))
      (nhds (lSrcDensity S T x)) := by
    simpa only [lSrcDensity] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hdet)
  refine hsqrt.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hspos : 0 < s := hs
  have h2s : 0 < 2 * s := mul_pos (by norm_num) hspos
  have hinv : 0 < (2 * s)⁻¹ := inv_pos.mpr h2s
  have hinvpow : 0 < (2 * s)⁻¹ ^ (Module.finrank Real F) :=
    pow_pos hinv _
  simp only [lExpDensity]
  rw [lNormGram_eq S T x Z hspos, Matrix.det_smul, Fintype.card_fin]
  have hpow :
      (((2 * s)⁻¹ ^ 2) ^ (Module.finrank Real F)) =
        ((2 * s)⁻¹ ^ (Module.finrank Real F)) ^ 2 := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [hpow,
    Real.sqrt_mul (sq_nonneg ((2 * s)⁻¹ ^ (Module.finrank Real F))),
    Real.sqrt_sq_eq_abs, abs_of_pos hinvpow]
  rw [div_eq_mul_inv, inv_pow]
  ring

end GramLimit

end DifferentialGeometry.PDE.RicciFlow.Perelman
