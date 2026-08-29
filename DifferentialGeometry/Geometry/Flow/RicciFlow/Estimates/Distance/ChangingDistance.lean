import DifferentialGeometry.Geometry.Comparison.GeodesicConvexity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.RicciFlow

set_option autoImplicit false

/-!
# Short endpoint changing-distance support

This file gives the short-distance branch of Perelman's endpoint
changing-distance estimate for a complete smooth Ricci flow.  A minimizing
geodesic at the base time supplies a differentiable upper support for the
later backward-time distance.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Manifold MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped Manifold ContDiff Topology Bundle ENNReal

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

omit [NeZero (Module.finrank Real E)] [IsManifold I 2 M]
  [SigmaCompactSpace M] in
private theorem backPath_deriv_le
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b T tau A : Real}
    (hab : a ≤ b)
    (ht : T - tau ∈ D.regular)
    (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I 1 gamma)
    (hvel : ∀ u ∈ Icc a b,
      mfderiv 𝓘(Real, Real) I gamma u (1 : Real) ≠ 0)
    (hRic : ∀ u ∈ Icc a b,
      ricciTensor (I := I) (S.base.metric (T - tau)) (gamma u)
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real)) ≤
        A * (S.base.metric (T - tau)).inner (gamma u)
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))) :
    ∃ d : Real,
      HasDerivAt
        (fun s ↦ Variation.arcLength
          (I := I) (S.base.metric (T - s)) gamma a b) d tau ∧
      d ≤ A * Variation.arcLength
        (I := I) (S.base.metric (T - tau)) gamma a b := by
  classical
  let t : Real := T - tau
  let v : (u : Real) → TangentSpace I (gamma u) :=
    fun u ↦ mfderiv 𝓘(Real, Real) I gamma u (1 : Real)
  let G : Real → Real :=
    fun u ↦ (S.base.metric t).inner (gamma u) (v u) (v u)
  let Ric : Real → Real :=
    fun u ↦ ricciTensor (I := I) (S.base.metric t) (gamma u) (v u) (v u)
  let Q : Real → Real := fun u ↦ -Ric u / Real.sqrt (G u)
  have hvLift : Continuous (fun u : Real ↦
      TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
        (gamma u) (v u)) := by
    have h :=
      DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.continuous_tangentMap_unitLift
        (I := I) (M := M) (γ := gamma) (by norm_num) hgamma
    simpa only [v, tangentMap] using h
  have hGcont : ContinuousOn G (Icc a b) := by
    rw [continuousOn_iff_continuous_restrict]
    have hbase : Continuous (fun u : ↥(Icc a b) ↦ gamma (u : Real)) :=
      hgamma.continuous.comp continuous_subtype_val
    have hvec : ∀ _i : Fin 2, Continuous (fun u : ↥(Icc a b) ↦
        TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
          (gamma (u : Real)) (v (u : Real))) :=
      fun _i ↦ hvLift.comp continuous_subtype_val
    have heval :=
      hS.smoothMetric.metricTensor_cont.eval_continuous
        (P := ↥(Icc a b))
        (τ := fun _u ↦ t)
        (b := fun u ↦ gamma (u : Real))
        continuous_const
        (fun _u ↦ D.regular_subset (by simpa only [t] using ht))
        hbase
        (v := fun _i u ↦ v (u : Real))
        hvec
    refine heval.congr (fun u ↦ ?_)
    rw [Tensor0SBundle.metricTensorField_apply]
    rfl
  have hRicAtCont :
      ContinuousOn
        (fun u ↦ S.ricciAt t (gamma u) (vec2 (I := I) (v u) (v u)))
        (Icc a b) := by
    rw [continuousOn_iff_continuous_restrict]
    have hbase : Continuous (fun u : ↥(Icc a b) ↦ gamma (u : Real)) :=
      hgamma.continuous.comp continuous_subtype_val
    have hvec : ∀ _i : Fin 2, Continuous (fun u : ↥(Icc a b) ↦
        TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
          (gamma (u : Real)) (v (u : Real))) :=
      fun _i ↦ hvLift.comp continuous_subtype_val
    have heval :=
      hS.ricciCont.eval_continuous
        (P := ↥(Icc a b))
        (τ := fun _u ↦ t)
        (b := fun u ↦ gamma (u : Real))
        continuous_const
        (fun _u ↦ D.regular_subset (by simpa only [t] using ht))
        hbase
        (v := fun _i u ↦ v (u : Real))
        hvec
    refine heval.congr (fun u ↦ ?_)
    simp only [SolutionOn.ricci, SolutionFamily.ricci_apply,
      SolutionFamily.ricciAt]
    change
      metricRicciAt (I := I) (S.base.metric t) (gamma (u : Real))
          (fun _i : Fin 2 ↦ v (u : Real)) =
        metricRicciAt (I := I) (S.base.metric t) (gamma (u : Real))
          (vec2 (I := I) (v (u : Real)) (v (u : Real)))
    congr 1
    funext i
    fin_cases i <;> rfl
  have hRicCont : ContinuousOn Ric (Icc a b) := by
    refine hRicAtCont.congr (fun u _hu ↦ ?_)
    simpa only [Ric, SolutionOn.ricciAt, SolutionFamily.ricciAt] using
      (metricRicciAt_apply_eq_ricciTensor
        (I := I) (S.base.metric t) (gamma u) (v u) (v u)).symm
  have hspeedCont : ContinuousOn (fun u ↦ Real.sqrt (G u)) (Icc a b) :=
    Real.continuous_sqrt.comp_continuousOn hGcont
  have hQcont : ContinuousOn Q (Icc a b) := by
    change ContinuousOn (fun u ↦ -Ric u / Real.sqrt (G u)) (Icc a b)
    apply ContinuousOn.div hRicCont.neg hspeedCont
    intro u hu
    exact ne_of_gt (Real.sqrt_pos.2
      ((S.base.metric t).pos (gamma u) (v u) (hvel u hu)))
  have hleftInt : IntervalIntegrable
      (fun u ↦ -A * Real.sqrt (G u)) volume a b :=
    (continuousOn_const.mul hspeedCont).intervalIntegrable_of_Icc hab
  have hrightInt : IntervalIntegrable Q volume a b :=
    hQcont.intervalIntegrable_of_Icc hab
  have hpoint : ∀ u ∈ Icc a b, -A * Real.sqrt (G u) ≤ Q u := by
    intro u hu
    have hGpos : 0 < G u :=
      (S.base.metric t).pos (gamma u) (v u) (hvel u hu)
    have hRicLe : Ric u ≤ A * G u := by
      simpa only [Ric, G, v, t] using hRic u hu
    dsimp only [Q]
    rw [le_div_iff₀ (Real.sqrt_pos.2 hGpos)]
    rw [mul_assoc, Real.mul_self_sqrt hGpos.le]
    linarith
  have hmono :
      (∫ u in a..b, -A * Real.sqrt (G u)) ≤ ∫ u in a..b, Q u :=
    intervalIntegral.integral_mono_on hab hleftInt hrightInt hpoint
  have hforward :=
    pathLength_timeDeriv_of_ricciFlow
      (I := I) S hS hab (by simpa only [t] using ht) gamma hgamma hvel
  have hforwardQ :
      HasDerivAt
        (fun s ↦ Variation.arcLength (I := I) (S.base.metric s) gamma a b)
        (∫ u in a..b, Q u) t := by
    simpa only [Q, Ric, G, v, t] using hforward
  have hsub : HasDerivAt (fun s : Real ↦ T - s) (-1) tau := by
    simpa only [sub_eq_add_neg, Pi.add_apply, Pi.neg_apply, id_eq, zero_add] using
      (hasDerivAt_const (x := tau) (c := T)).sub (hasDerivAt_id (x := tau))
  let d : Real := (∫ u in a..b, Q u) * (-1)
  refine ⟨d, ?_, ?_⟩
  · simpa only [d, Function.comp_apply, t] using hforwardQ.comp tau hsub
  · have hforwardLower :
        -A * Variation.arcLength
            (I := I) (S.base.metric t) gamma a b ≤
          ∫ u in a..b, Q u := by
      rw [Variation.arcLength, ← intervalIntegral.integral_const_mul]
      exact hmono
    dsimp only [d]
    dsimp only [t] at hforwardLower ⊢
    linarith

omit [IsManifold I 2 M] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- If a base-time minimizing geodesic has length less than twice the endpoint
radius, endpoint-ball Ricci upper bounds produce a differentiable upper
support for its backward-time distance with the sharp short-case derivative
bound. -/
theorem dist_short_support
    [T2Space (TangentBundle I M)] [ConnectedSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T tau K r : Real}
    (ht : T - tau ∈ D.regular)
    (hcomplete : RiemannianMetricComplete
      (I := I) (S.base.metric (T - tau)))
    (hK : 0 ≤ K) (hr : 0 < r)
    (x y : M)
    (hshort :
      (riemannianEDistOf
        (I := I) (S.base.metric (T - tau)) x y).toReal < 2 * r)
    (hRic : ∀ z : M, ∀ w : TangentSpace I z,
      (riemannianEDistOf
          (I := I) (S.base.metric (T - tau)) x z < ENNReal.ofReal r ∨
        riemannianEDistOf
          (I := I) (S.base.metric (T - tau)) y z < ENNReal.ofReal r) →
      ricciTensor (I := I) (S.base.metric (T - tau)) z w w ≤
        ((Module.finrank Real E : Real) - 1) * K *
          (S.base.metric (T - tau)).inner z w w) :
    ∃ phi : Real → Real, ∃ d : Real,
      phi tau =
          (riemannianEDistOf
            (I := I) (S.base.metric (T - tau)) x y).toReal ∧
      (fun s ↦
          (riemannianEDistOf
            (I := I) (S.base.metric (T - s)) x y).toReal) ≤ᶠ[𝓝[>] tau] phi ∧
      HasDerivAt phi d tau ∧
      d ≤ 2 * ((Module.finrank Real E : Real) - 1) * K * r := by
  classical
  have hnNat : 1 ≤ Module.finrank Real E :=
    Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hn : 0 ≤ (Module.finrank Real E : Real) - 1 := by
    exact sub_nonneg.mpr (by exact_mod_cast hnNat)
  by_cases hxy : x = y
  · subst y
    refine ⟨fun _ ↦ 0, 0, ?_, ?_, hasDerivAt_const tau 0, ?_⟩
    · simp only [riemannianEDistOf_self, ENNReal.toReal_zero]
    · exact Filter.Eventually.of_forall (fun _ ↦ by
        simp only [riemannianEDistOf_self, ENNReal.toReal_zero, le_refl])
    · positivity
  let g : SmoothRiemannianMetric I M := S.base.metric (T - tau)
  letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  letI : T3Space M := inferInstance
  letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : M ↦ TangentSpace I z) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro z v w; rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : CompleteSpace M := by
    simpa only [g] using hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro z w
    rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
    congr 2
  have hdist : riemannianEDistOf (I := I) g x y = riemannianEDist I x y :=
    riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm x y
  let ell : Real := (riemannianEDist I x y).toReal
  have hell_short : ell < 2 * r := by
    simpa only [g, hdist, ell] using hshort
  let v : TangentSpace I x := minimizingVec (I := I) g hEnorm x y
  let gamma : Real → M := intrinsicGeodesic (I := I) g hEnorm x v
  have hv : v ≠ 0 := by
    intro hv0
    have hexp := minimizingVec_exp (I := I) g hEnorm x y
    dsimp only [v] at hv0
    rw [hv0, expMapIntrinsic_zero] at hexp
    exact hxy hexp
  have hgamma : ContMDiff 𝓘(Real, Real) I 1 gamma :=
    contMDiffOn_univ.mp
      (intrinsicGeodesic_contMDiffOn (I := I) g hEnorm x v)
  have hvel : ∀ u ∈ Icc (0 : Real) 1,
      mfderiv 𝓘(Real, Real) I gamma u (1 : Real) ≠ 0 := by
    intro u _hu
    exact intrGeo_vel_ne (I := I) g hEnorm x v hv u
  have hgamma0 : gamma 0 = x :=
    intrinsicGeodesic_zero (I := I) g hEnorm x v
  have hgamma1 : gamma 1 = y := by
    simpa only [gamma, v, expMapIntrinsic_def] using
      minimizingVec_exp (I := I) g hEnorm x y
  have hcover : ∀ u ∈ Icc (0 : Real) 1,
      riemannianEDistOf (I := I) g x (gamma u) < ENNReal.ofReal r ∨
        riemannianEDistOf (I := I) g y (gamma u) < ENNReal.ofReal r := by
    intro u hu
    by_cases hleft : ell * u < r
    · left
      rw [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
      have hseg := minJoin_edist_le (I := I) g hEnorm x y hu.1
      have hseg' :
          riemannianEDist I x (gamma u) ≤ ENNReal.ofReal (ell * u) := by
        simpa only [gamma, v, minJoin, ell] using hseg
      exact hseg'.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).2 hleft)
    · right
      have hright : ell * (1 - u) < r := by
        have hleft' : r ≤ ell * u := le_of_not_gt hleft
        have heq : ell * (1 - u) = ell - ell * u := by ring
        rw [heq]
        linarith
      rw [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
      have hseg := intrinsicGeodesic_riemannianEDist_le
        (I := I) g hEnorm x v (s := u) (t := 1) hu.2
      have hseg' :
          riemannianEDist I (gamma u) (gamma 1) ≤
            ENNReal.ofReal (ell * (1 - u)) := by
        simpa only [gamma, v, ell, minimizingVec_len] using hseg
      have hseg'' :
          riemannianEDist I y (gamma u) ≤
            ENNReal.ofReal (ell * (1 - u)) := by
        rw [riemannianEDist_comm, ← hgamma1]
        exact hseg'
      exact hseg''.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).2 hright)
  let A : Real := ((Module.finrank Real E : Real) - 1) * K
  have hA : 0 ≤ A := mul_nonneg hn hK
  have hRicGamma : ∀ u ∈ Icc (0 : Real) 1,
      ricciTensor (I := I) g (gamma u)
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real)) ≤
        A * g.inner (gamma u)
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real)) := by
    intro u hu
    simpa only [g, A] using
      hRic (gamma u) (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))
        (by simpa only [g] using hcover u hu)
  let phi : Real → Real := fun s ↦
    Variation.arcLength (I := I) (S.base.metric (T - s)) gamma 0 1
  have hpath : Variation.arcLength (I := I) g gamma 0 1 = ell := by
    have hgammaMin : gamma = minJoin (I := I) g hEnorm x y := by
      funext u
      rfl
    rw [hgammaMin, minJoin_arcLength (I := I) g hEnorm x y]
  have hcontact : phi tau = ell := by
    simpa only [phi, g] using hpath
  have hupper :
      (fun s ↦
          (riemannianEDistOf
            (I := I) (S.base.metric (T - s)) x y).toReal) ≤ᶠ[𝓝[>] tau] phi := by
    exact Filter.Eventually.of_forall (fun s ↦ by
      have hedist := edistOf_le_arcLength
        (I := I) (S.base.metric (T - s)) zero_le_one hgamma.contMDiffOn
      rw [hgamma0, hgamma1] at hedist
      have hphi_nonneg : 0 ≤ phi s := by
        dsimp only [phi, Variation.arcLength]
        exact intervalIntegral.integral_nonneg zero_le_one
          (fun _ _ ↦ Real.sqrt_nonneg _)
      have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hedist
      rw [ENNReal.toReal_ofReal hphi_nonneg] at hreal
      exact hreal)
  obtain ⟨d, hphiDeriv, hd⟩ :=
    backPath_deriv_le
      (I := I) S hS zero_le_one ht gamma hgamma hvel
        (A := A) (by simpa only [g] using hRicGamma)
  refine ⟨phi, d, ?_, hupper, ?_, ?_⟩
  · calc
      phi tau = ell := hcontact
      _ = (riemannianEDist I x y).toReal := rfl
      _ = (riemannianEDistOf (I := I) g x y).toReal :=
        congrArg ENNReal.toReal hdist.symm
      _ = (riemannianEDistOf
          (I := I) (S.base.metric (T - tau)) x y).toReal := rfl
  · simpa only [phi] using hphiDeriv
  · calc
      d ≤ A * Variation.arcLength (I := I) g gamma 0 1 := by
        simpa only [g] using hd
      _ = A * ell := by rw [hpath]
      _ ≤ A * (2 * r) := mul_le_mul_of_nonneg_left hell_short.le hA
      _ = 2 * ((Module.finrank Real E : Real) - 1) * K * r := by
        simp only [A]
        ring

end DifferentialGeometry.PDE.RicciFlow
