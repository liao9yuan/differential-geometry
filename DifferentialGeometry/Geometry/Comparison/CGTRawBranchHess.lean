import DifferentialGeometry.Geometry.Comparison.CGTRawExtDistance
import DifferentialGeometry.Geometry.Comparison.Variation.EndpointPositive
import DifferentialGeometry.Geometry.Exponential.EndpointShape
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Metric Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CGT

open Exponential Geodesic NormalCoordinates
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

section BranchEnergy

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

omit [T2Space (TangentBundle I M)] in
private theorem branchEnergy_inf
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : ExpInvBranch (I := I) g hEnorm p) :
    ContMDiffOn I 𝓘(Real, Real) ∞
      (branchEnergy (I := I) g B) B.dom := by
  let gp : E →L[Real] E →L[Real] Real := g.inner p
  have hgp : ContMDiffOn I
      𝓘(Real, E →L[Real] E →L[Real] Real) ∞
      (fun _ : M => gp) B.dom :=
    contMDiffOn_const
  have hinv : ContMDiffOn I 𝓘(Real, E) ∞ B.inv B.dom :=
    B.inv_inf
  have hinner : ContMDiffOn I 𝓘(Real, Real) ∞
      (fun z : M => g.inner p (B.inv z) (B.inv z)) B.dom := by
    simpa only [gp] using (hgp.clm_apply hinv).clm_apply hinv
  simpa only [branchEnergy] using
    (contMDiffOn_const.mul hinner)

private theorem quad_deriv2 (c t : Real) :
    (deriv^[2] (fun s : Real => (1 / 2 : Real) * s ^ 2 * c)) t = c := by
  have hfirst :
      deriv (fun s : Real => (1 / 2 : Real) * s ^ 2 * c) =
        fun s : Real => s * c := by
    funext s
    have hd :
        HasDerivAt (fun r : Real => (1 / 2 : Real) * r ^ 2 * c)
          (s * c) s := by
      convert
        (((hasDerivAt_id s).pow 2).const_mul (1 / 2 : Real)).mul_const c
          using 1
      all_goals simp only [id_eq]
      all_goals ring
    exact hd.deriv
  change
    deriv (deriv (fun s : Real => (1 / 2 : Real) * s ^ 2 * c)) t = c
  rw [hfirst]
  simpa only [one_mul] using ((hasDerivAt_id t).mul_const c).deriv

private theorem rawBranch_hess_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (B : ExpInvBranch (I := I) g hEnorm p)
    (hzero : (0 : E) ∈ B.hom.source) (Y : TangentSpace I p) :
    hessFun (I := I) g (branchEnergy (I := I) g B) p Y Y =
      g.inner p Y Y := by
  classical
  let γ : Real → M :=
    intrinsicGeodesic (I := I) g hEnorm p (0 : TangentSpace I p)
  let J : TangentSpace I p → ∀ t, TangentSpace I (γ t) := fun W =>
    intrinsicJacobi (I := I) g hEnorm p (0 : TangentSpace I p) W
  have hγ (t : Real) : γ t = p := by
    have hs :=
      intrinsicGeodesic_smul
        (I := I) g hEnorm p (0 : TangentSpace I p) t
    rw [smul_zero] at hs
    have hzero :
        intrinsicGeodesic (I := I) g hEnorm p
            (0 : TangentSpace I p) 1 = p := by
      simpa only [expMapIntrinsic_def] using
        expMapIntrinsic_zero (I := I) g hEnorm p
    exact hs.symm.trans hzero
  have hJ (W : TangentSpace I p) (t : Real) :
      (J W t : E) = t • (W : E) := by
    have hraw :=
      intrinsic_jacobi_at
        (I := I) g hEnorm p (0 : E) (W : E) t
    rw [smul_zero] at hraw
    change
      (J W t : E) =
        (mfderiv 𝓘(Real, E) I
          (fun v : E =>
            expMapIntrinsic (I := I) g hEnorm p
              (show TangentSpace I p from v))
          (0 : E)) (t • (W : E)) at hraw
    rw [mfderiv_expMapIntrinsic_at_zero
      (I := I) g hEnorm p] at hraw
    simpa only [ContinuousLinearMap.id_apply] using hraw
  have hcurve :
      γ =ᶠ[𝓝 (1 : Real)] fun _ : Real => p :=
    Filter.Eventually.of_forall hγ
  have hfield :
      ∀ᶠ t in 𝓝 (1 : Real),
        (J Y t : E) =
          ((show TangentSpace I p from t • (Y : E)) : E) :=
    Filter.Eventually.of_forall (hJ Y)
  have hcongr :=
    covDerivAlong_congr_curve
      (I := I) g (J Y)
        (fun t : Real => show TangentSpace I p from t • (Y : E))
        hcurve hfield
  have hline :
      HasDerivAt (fun t : Real => t • (Y : E)) (Y : E) 1 := by
    simpa only [one_smul] using
      ((hasDerivAt_id (1 : Real)).smul_const (Y : E))
  have hconst :=
    covDerivAlong_const
      (I := I) g p
        (fun t : Real => show TangentSpace I p from t • (Y : E))
        1 hline.differentiableAt
  have hcov :
      (covDerivAlong (I := I) g γ (J Y) 1 : E) = (Y : E) :=
    hcongr.trans (hconst.trans hline.deriv)
  have hh :=
    branchEnergy_hess
      (I := I) B (u := (0 : TangentSpace I p))
        (w₁ := Y) (w₂ := Y) hzero
  change
    hessFun (I := I) g (branchEnergy (I := I) g B)
        (γ 1) (J Y 1) (J Y 1) =
      g.inner (γ 1) (covDerivAlong (I := I) g γ (J Y) 1) (J Y 1) at hh
  rw [hγ 1, hJ Y 1, one_smul, hcov] at hh
  exact hh

end BranchEnergy

noncomputable local instance {R : Real} :
    SigmaCompactSpace (rawPullBall (E := E) R) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen
      𝓘(Real, E) (rawPullBall (E := E) R).isOpen)

noncomputable local instance {R : Real} :
    SigmaCompactSpace (rawAgree (E := E) R) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen
      𝓘(Real, E) (rawAgree (E := E) R).isOpen)

omit [NeZero (Module.finrank Real E)] in
/-- The complete raw-extension geodesic launched from `x` in direction `v`. -/
def rawExtLaunch
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (x : E) (v : TangentSpace 𝓘(Real, E) x) : Real → E := by
  let gExt := rawExtMetric (I := I) g p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w u; rfl⟩
  letI : PseudoEMetricSpace E :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (rawExt_complete (I := I) g p hR hloc).complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  exact intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x v

omit [NeZero (Module.finrank Real E)] [T2Space M] [SigmaCompactSpace M] in
private theorem rawExt_quad_le
    (g : SmoothRiemannianMetric I M) (p : M) {R K : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    {z : E} (hz : ‖z‖ < 3 * R / 4)
    (hRm :
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (framedExpMap (I := I) g p z) 4
        (Geometry.Curvature.metricRm04At
          (I := I) (M := M) g (framedExpMap (I := I) g p z))) ≤ K)
    (J V : E) :
    let gExt := rawExtMetric (I := I) g p hR hloc
    gExt.inner z
        (Geometry.Curvature.riemannOp
          (Geometry.Connection.LeviCivita (I := 𝓘(Real, E)) gExt)
          z J V V)
        J ≤
      K * gExt.inner z J J * gExt.inner z V V := by
  let U := rawPullBall (E := E) R
  let Vopen := rawAgree (E := E) R
  let gExt := rawExtMetric (I := I) g p hR hloc
  let gPull := rawPullMetric (I := I) g p hloc
  have hzBall : z ∈ Metric.ball (0 : E) (3 * R / 4) := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hzClosed : z ∈ Metric.closedBall (0 : E) (3 * R / 4) :=
    Metric.ball_subset_closedBall hzBall
  let zU : U := ⟨z, Metric.closedBall_subset_ball (by linarith) hzClosed⟩
  let zV : Vopen := ⟨zU, hzBall⟩
  have hmetric :
      ((gExt.restrictOpen (I := 𝓘(Real, E)) U).restrictOpen
          (I := 𝓘(Real, E)) Vopen) =
        gPull.restrictOpen (I := 𝓘(Real, E)) Vopen := by
    simpa only [U, Vopen, gExt, gPull] using
      rawExt_restrict (I := I) g p hR hloc
  have hquad :=
    rawPull_quad_le (I := I) g p hloc zU hRm J V
  dsimp only at hquad
  calc
    gExt.inner z
          (Geometry.Curvature.riemannOp
            (Geometry.Connection.LeviCivita (I := 𝓘(Real, E)) gExt)
            z J V V)
          J =
        gExt.inner z J
          (Geometry.Curvature.riemannOp
            (Geometry.Connection.LeviCivita (I := 𝓘(Real, E)) gExt)
            z J V V) := gExt.symm _ _ _
    _ = Geometry.Curvature.metricRm04StdAt
          (I := 𝓘(Real, E)) (M := E) gExt z J V V J := by
      rw [Integral.Connection.rm04_eq_inner]
    _ = Geometry.Curvature.metricRm04StdAt
          (I := 𝓘(Real, E)) (M := U)
          (gExt.restrictOpen (I := 𝓘(Real, E)) U) zU J V V J :=
      (Geometry.Curvature.metricRm04StdAt_restrictOpen
        (I := 𝓘(Real, E)) gExt U zU J V V J).symm
    _ = Geometry.Curvature.metricRm04StdAt
          (I := 𝓘(Real, E)) (M := Vopen)
          ((gExt.restrictOpen (I := 𝓘(Real, E)) U).restrictOpen
            (I := 𝓘(Real, E)) Vopen) zV J V V J :=
      (Geometry.Curvature.metricRm04StdAt_restrictOpen
        (I := 𝓘(Real, E))
        (gExt.restrictOpen (I := 𝓘(Real, E)) U)
        Vopen zV J V V J).symm
    _ = Geometry.Curvature.metricRm04StdAt
          (I := 𝓘(Real, E)) (M := Vopen)
          (gPull.restrictOpen (I := 𝓘(Real, E)) Vopen)
          zV J V V J := by rw [hmetric]
    _ = Geometry.Curvature.metricRm04StdAt
          (I := 𝓘(Real, E)) (M := U) gPull zU J V V J :=
      Geometry.Curvature.metricRm04StdAt_restrictOpen
        (I := 𝓘(Real, E)) gPull Vopen zV J V V J
    _ = gPull.inner zU J
          (Geometry.Curvature.riemannOp
            (Geometry.Connection.LeviCivita (I := 𝓘(Real, E)) gPull)
            zU J V V) := by
      rw [Integral.Connection.rm04_eq_inner]
    _ = gPull.inner zU
          (Geometry.Curvature.riemannOp
            (Geometry.Connection.LeviCivita (I := 𝓘(Real, E)) gPull)
            zU J V V)
          J := gPull.symm _ _ _
    _ ≤ K * gPull.inner zU J J * gPull.inner zU V V := hquad
    _ = K * gExt.inner z J J * gExt.inner z V V := by
      rw [rawExt_inner (I := I) g p hR hloc hzClosed J J,
        rawExt_inner (I := I) g p hR hloc hzClosed V V]

omit [T2Space M] [SigmaCompactSpace M] in
/-- The positive-dimensional Jacobi argument for raw complete-extension
nonconjugacy. -/
private theorem rawExt_no_conj_pos
    (g : SmoothRiemannianMetric I M) (p : M) {R K L : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    {x : E} (v : TangentSpace 𝓘(Real, E) x)
    (hfence : ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖rawExtLaunch (I := I) g p hR hloc x v t‖ < 3 * R / 4)
    (hv : Real.sqrt ((rawExtMetric (I := I) g p hR hloc).inner x v v) ≤ L)
    (hK : 0 ≤ K)
    (hRm : ∀ z : E, ‖z‖ < 3 * R / 4 →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (framedExpMap (I := I) g p z) 4
        (Geometry.Curvature.metricRm04At (I := I) (M := M) g
          (framedExpMap (I := I) g p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2) :
    let gExt := rawExtMetric (I := I) g p hR hloc
    letI : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w u; rfl⟩
    letI : PseudoEMetricSpace E :=
      PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    letI : CompleteSpace E := (rawExt_complete (I := I) g p hR hloc).complete
    let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
      fun z w => tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
    ¬ IsConjVec (I := 𝓘(Real, E)) gExt hExt x (v : E) := by
  classical
  let gExt := rawExtMetric (I := I) g p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) := inferInstance
  letI (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) := inferInstance
  letI : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w u; rfl⟩
  letI : PseudoEMetricSpace E :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E := (rawExt_complete (I := I) g p hR hloc).complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w => tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := 𝓘(Real, E)) gExt z w
  change ¬ IsConjVec (I := 𝓘(Real, E)) gExt hExt x (v : E)
  have hzero : ¬ IsConjVec (I := 𝓘(Real, E)) gExt hExt x (0 : E) := by
    simpa only [IsConjVec, not_not,
      mfderiv_expMapIntrinsic_at_zero (I := 𝓘(Real, E)) gExt hExt x] using
      (Function.injective_id : Function.Injective (fun z : E => z))
  intro hconj
  have hvne : (v : E) ≠ 0 := by
    intro hv0
    apply hzero
    simpa only [hv0] using hconj
  rw [isConjVec_iff_jacobi (I := 𝓘(Real, E)) gExt hExt x (v : E)] at hconj
  obtain ⟨w, hw, hwend⟩ := hconj
  let γ : Real → E := intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x v
  let J : Real → E := intrinsicJacobi (I := 𝓘(Real, E)) gExt hExt x v w
  let DJ : Real → E := fun t => CovariantDerivativeAlong.covDerivAlong
    (I := 𝓘(Real, E)) gExt γ J t
  let f : Real → Real := fun t => gExt.inner (γ t) (J t) (J t)
  have hγ : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ := by
    simpa only [γ] using
      intrinsicGeodesic_contMDiff (I := 𝓘(Real, E)) gExt hExt x v
  have hJ0 : J 0 = 0 := by
    simpa only [J] using intrinsicJacobi_zero
      (I := 𝓘(Real, E)) gExt hExt x v w
  have hJ1 : J 1 = 0 := by
    simpa only [J, intrinsicJacobi] using hwend
  obtain ⟨B0, hB0⟩ := branch_of_not_conj (I := 𝓘(Real, E)) gExt hExt hzero
  have hline : Continuous (fun t : Real => t • (v : E)) :=
    continuous_id.smul continuous_const
  have hsrc_ev : ∀ᶠ t in 𝓝 (0 : Real), t • (v : E) ∈ B0.hom.source := by
    have hsrc0 : (0 : Real) • (v : E) ∈ B0.hom.source := by
      simpa only [zero_smul] using hB0
    exact hline.continuousAt (B0.hom.open_source.mem_nhds hsrc0)
  have hsrc_gt : ∀ᶠ t in 𝓝[>] (0 : Real), t • (v : E) ∈ B0.hom.source :=
    hsrc_ev.filter_mono inf_le_left
  have hIoo : ∀ᶠ t in 𝓝[>] (0 : Real), t ∈ Set.Ioo (0 : Real) 1 :=
    Ioo_mem_nhdsGT zero_lt_one
  obtain ⟨t0, ht0src, ht0⟩ := (hsrc_gt.and hIoo).exists
  have ht0inj : Function.Injective
      (mfderiv 𝓘(Real, E) 𝓘(Real, E)
        (fun z : E => expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x
          (show TangentSpace 𝓘(Real, E) x from z)) (t0 • (v : E))) := by
    simpa only [IsConjVec, not_not] using B0.not_conj ht0src
  have hJt0 : J t0 ≠ 0 := by
    intro hJt0
    have hjat : J t0 = mfderiv 𝓘(Real, E) 𝓘(Real, E)
        (fun z : E => expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x
          (show TangentSpace 𝓘(Real, E) x from z))
        (t0 • (v : E)) (t0 • w) := by
      simpa only [J, intrinsicJacobi] using intrinsic_jacobi_at
        (I := 𝓘(Real, E)) gExt hExt x (v : E) w t0
    have hker : mfderiv 𝓘(Real, E) 𝓘(Real, E)
        (fun z : E => expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x
          (show TangentSpace 𝓘(Real, E) x from z))
        (t0 • (v : E)) (t0 • w) = 0 := by
      rw [← hjat]
      exact hJt0
    have htw : t0 • w = 0 := by
      apply ht0inj
      rw [hker]
      exact (map_zero _).symm
    exact hw ((smul_eq_zero.mp htw).resolve_left ht0.1.ne')
  have hJdiff (t : Real) : DifferentiableAt Real
      (CovariantDerivativeAlong.chartRepAt (I := 𝓘(Real, E)) γ J t) t := by
    simpa only [γ, J] using
      (intrJacobi_diff (I := 𝓘(Real, E)) gExt hExt x v w t).1
  have hfderiv (t : Real) : HasDerivAt f
      (gExt.inner (γ t) (DJ t) (J t) +
        gExt.inner (γ t) (J t) (DJ t)) t := by
    simpa only [f, DJ] using Variation.metric_compat_hasDerivAt_inner
      (I := 𝓘(Real, E)) (n := ∞) (by simp) gExt γ J J t hγ
      (hJdiff t) (hJdiff t)
  have hfcont : Continuous f :=
    continuous_iff_continuousAt.mpr fun t => (hfderiv t).continuousAt
  obtain ⟨c, hc, hcmax⟩ :=
    (isCompact_Icc (a := (0 : Real)) (b := 1)).exists_isMaxOn
      (Set.nonempty_Icc.2 zero_le_one) hfcont.continuousOn
  have hft0pos : 0 < f t0 := gExt.pos (γ t0) (J t0) hJt0
  have hfcpos : 0 < f c := hft0pos.trans_le
    (Filter.eventually_principal.mp hcmax t0 ⟨ht0.1.le, ht0.2.le⟩)
  have hinner00 (z : E) : gExt.inner z (0 : E) (0 : E) = 0 :=
    (gExt.inner z (0 : E)).map_zero
  have hc0 : c ≠ 0 := by
    intro hc0
    subst c
    simp only [f, hJ0, hinner00] at hfcpos
    exact lt_irrefl (0 : Real) hfcpos
  have hc1 : c ≠ 1 := by
    intro hc1
    subst c
    simp only [f, hJ1, hinner00] at hfcpos
    exact lt_irrefl (0 : Real) hfcpos
  have hcIoo : c ∈ Set.Ioo (0 : Real) 1 :=
    ⟨lt_of_le_of_ne hc.1 (Ne.symm hc0), lt_of_le_of_ne hc.2 hc1⟩
  have hJc : J c ≠ 0 := by
    intro hJc
    simp only [f, hJc, hinner00] at hfcpos
    exact lt_irrefl (0 : Real) hfcpos
  have hlocal : IsLocalMax f c := by
    filter_upwards [Icc_mem_nhds hcIoo.1 hcIoo.2] with t ht
    exact Filter.eventually_principal.mp hcmax t ht
  have hsum0 : gExt.inner (γ c) (DJ c) (J c) +
      gExt.inner (γ c) (J c) (DJ c) = 0 :=
    hlocal.hasDerivAt_eq_zero (hfderiv c)
  have hpair0 : gExt.inner (γ c) (DJ c) (J c) = 0 := by
    rw [gExt.symm (γ c) (J c) (DJ c)] at hsum0
    linarith
  have hperp : gExt.inner x v w = 0 := by
    have hp := intrinsicJacobi_perp (I := 𝓘(Real, E)) gExt hExt x v w
    have hJ1' : intrinsicJacobi (I := 𝓘(Real, E)) gExt hExt x v w 1 = 0 := by
      simpa only [J] using hJ1
    rw [hJ1'] at hp
    have hz : gExt.inner
        (intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x v 1)
        (intrinsicVelocityLift (I := 𝓘(Real, E)) gExt hExt x v 1).snd
        (0 : E) = 0 :=
      (gExt.inner
        (intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x v 1)
        (intrinsicVelocityLift (I := 𝓘(Real, E)) gExt hExt x v 1).snd).map_zero
    exact hp.symm.trans hz
  let γc : Real → E := intrinsicGeodesic
    (I := 𝓘(Real, E)) gExt hExt x (c • v)
  let Jc : Real → E := intrinsicJacobi
    (I := 𝓘(Real, E)) gExt hExt x (c • v) (c • w)
  have hGeoScale (t : Real) : γc t = γ (c * t) := by
    dsimp only [γc, γ]
    calc
      intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x (c • v) t =
          intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x
            (t • (c • v)) 1 :=
        (intrinsicGeodesic_smul
          (I := 𝓘(Real, E)) gExt hExt x (c • v) t).symm
      _ = intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x
            ((c * t) • v) 1 := by
        rw [smul_smul, mul_comm]
      _ = intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x v (c * t) :=
        intrinsicGeodesic_smul (I := 𝓘(Real, E)) gExt hExt x v (c * t)
  have hJacScale (t : Real) : Jc t = J (c * t) := by
    have hleft := intrinsic_jacobi_at
      (I := 𝓘(Real, E)) gExt hExt x (c • (v : E)) (c • w) t
    have hright := intrinsic_jacobi_at
      (I := 𝓘(Real, E)) gExt hExt x (v : E) w (c * t)
    have hleft' : Jc t = mfderiv 𝓘(Real, E) 𝓘(Real, E)
        (fun z : E => expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x
          (show TangentSpace 𝓘(Real, E) x from z))
        (t • (c • (v : E))) (t • (c • w)) := by
      simpa only [Jc, intrinsicJacobi] using hleft
    have hright' : J (c * t) = mfderiv 𝓘(Real, E) 𝓘(Real, E)
        (fun z : E => expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x
          (show TangentSpace 𝓘(Real, E) x from z))
        ((c * t) • (v : E)) ((c * t) • w) := by
      simpa only [J, intrinsicJacobi] using hright
    have hbase : t • (c • (v : E)) = (c * t) • (v : E) := by module
    have hdir : t • (c • w) = (c * t) • w := by module
    rw [hbase, hdir] at hleft'
    exact hleft'.trans hright'.symm
  have hγc : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γc := by
    simpa only [γc] using
      intrinsicGeodesic_contMDiff (I := 𝓘(Real, E)) gExt hExt x (c • v)
  have hgeoc : IsGeodesicOn (I := 𝓘(Real, E)) gExt γc
      (Set.Icc (0 : Real) 1) := by
    simpa only [γc] using
      (intrinsicGeodesic_isGeodesic
        (I := 𝓘(Real, E)) gExt hExt x (c • v)).isGeodesicOn
          (Set.Icc (0 : Real) 1)
  have hJcdiff (t : Real) : DifferentiableAt Real
      (CovariantDerivativeAlong.chartRepAt (I := 𝓘(Real, E)) γc Jc t) t := by
    simpa only [γc, Jc] using
      (intrJacobi_diff (I := 𝓘(Real, E)) gExt hExt x (c • v) (c • w) t).1
  have hDJcdiff (t : Real) : DifferentiableAt Real
      (CovariantDerivativeAlong.chartRepAt (I := 𝓘(Real, E)) γc
        (fun s => CovariantDerivativeAlong.covDerivAlong
          (I := 𝓘(Real, E)) gExt γc Jc s) t) t := by
    simpa only [γc, Jc] using
      (intrJacobi_diff (I := 𝓘(Real, E)) gExt hExt x (c • v) (c • w) t).2
  have hJacc : Variation.IsJacobiAlong
      (I := 𝓘(Real, E)) gExt γc Jc := by
    simpa only [γc, Jc, intrinsicJacobi] using intrinsic_jacobi
      (I := 𝓘(Real, E)) gExt hExt x (c • (v : E)) (c • w)
  have hJc0 : Jc 0 = 0 := by
    simpa only [Jc] using intrinsicJacobi_zero
      (I := 𝓘(Real, E)) gExt hExt x (c • v) (c • w)
  have hJc1 : Jc 1 ≠ 0 := by
    intro hz
    apply hJc
    calc
      J c = J (c * 1) := by rw [mul_one]
      _ = Jc 1 := (hJacScale 1).symm
      _ = 0 := hz
  have hscaledPerp : gExt.inner x (c • v) (c • w) = 0 := by
    calc
      gExt.inner x (c • v) (c • w) = c * gExt.inner x v (c • w) := by
        rw [map_smul (gExt.inner x), ContinuousLinearMap.smul_apply,
          smul_eq_mul]
      _ = c * (c * gExt.inner x v w) := by
        exact congrArg (fun r : Real => c * r)
          (by simpa only [smul_eq_mul] using (gExt.inner x v).map_smul c w)
      _ = 0 := by rw [hperp]; ring
  have hJperpc : ∀ t ∈ Set.Icc (0 : Real) 1,
      gExt.inner (γc t) (Jc t)
        (Variation.curveVelocity (I := 𝓘(Real, E)) γc t) = 0 := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      rw [hJc0, gExt.symm]
      exact (gExt.inner (γc 0)
        (Variation.curveVelocity (I := 𝓘(Real, E)) γc 0)).map_zero
    · rw [gExt.symm]
      exact intrJacobi_perp_ne
        (I := 𝓘(Real, E)) gExt hExt x (c • v) (c • w) ht0 hscaledPerp
  have hcvne : (c • v : E) ≠ 0 := smul_ne_zero hcIoo.1.ne' hvne
  have hspeedc : ∀ t ∈ Set.Icc (0 : Real) 1,
      0 < gExt.inner (γc t)
        (Variation.curveVelocity (I := 𝓘(Real, E)) γc t)
        (Variation.curveVelocity (I := 𝓘(Real, E)) γc t) := by
    intro t _ht
    change 0 < gExt.inner
      (intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x (c • v) t)
      (mfderiv 𝓘(Real, Real) 𝓘(Real, E)
        (intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x (c • v)) t 1)
      (mfderiv 𝓘(Real, Real) 𝓘(Real, E)
        (intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x (c • v)) t 1)
    rw [intrinsicGeodesic_speedSq_eq
      (I := 𝓘(Real, E)) gExt hExt x (c • v) t]
    exact gExt.pos x (c • v) hcvne
  let ell : Real := Real.sqrt (gExt.inner x v v)
  have hell0 : 0 ≤ ell := Real.sqrt_nonneg _
  have hellL : ell ≤ L := by
    simpa only [ell, gExt] using hv
  have hcell0 : 0 ≤ c * ell := mul_nonneg hcIoo.1.le hell0
  have hcellL : c * ell ≤ L := by
    calc
      c * ell ≤ 1 * ell := mul_le_mul_of_nonneg_right hc.2 hell0
      _ = ell := one_mul ell
      _ ≤ L := hellL
  have hsqLe : (c * ell) ^ 2 ≤ L ^ 2 := by nlinarith
  have hvnn : 0 ≤ gExt.inner x v v := (gExt.pos x v hvne).le
  have hscaleSq : gExt.inner x (c • v) (c • v) = (c * ell) ^ 2 := by
    calc
      gExt.inner x (c • v) (c • v) = c * gExt.inner x v (c • v) := by
        rw [map_smul (gExt.inner x), ContinuousLinearMap.smul_apply,
          smul_eq_mul]
      _ = c * (c * gExt.inner x v v) := by
        exact congrArg (fun r : Real => c * r)
          (by simpa only [smul_eq_mul] using (gExt.inner x v).map_smul c v)
      _ = (c * ell) ^ 2 := by
        rw [← Real.sq_sqrt hvnn]
        dsimp only [ell]
        ring
  let κ : Real := K * (c * ell) ^ 2
  have hκ0 : 0 ≤ κ := mul_nonneg hK (sq_nonneg _)
  have hκπ : κ < (Real.pi / 2) ^ 2 :=
    (mul_le_mul_of_nonneg_left hsqLe hK).trans_lt hsmall
  have hfenceγ : ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖γ t‖ < 3 * R / 4 := by
    intro t ht
    simpa only [γ, gExt, hExt, rawExtLaunch] using hfence t ht
  have hcurvc : ∀ t ∈ Set.Icc (0 : Real) 1,
      gExt.inner (γc t)
          (Geometry.Curvature.riemannOp
            (Geometry.Connection.LeviCivita (I := 𝓘(Real, E)) gExt)
            (γc t) (Jc t)
            (Variation.curveVelocity (I := 𝓘(Real, E)) γc t)
            (Variation.curveVelocity (I := 𝓘(Real, E)) γc t))
          (Jc t) ≤ κ * gExt.inner (γc t) (Jc t) (Jc t) := by
    intro t ht
    have hct : c * t ∈ Set.Icc (0 : Real) 1 :=
      ⟨mul_nonneg hcIoo.1.le ht.1, mul_le_one₀ hc.2 ht.1 ht.2⟩
    have hz : ‖γc t‖ < 3 * R / 4 := by
      rw [hGeoScale t]
      exact hfenceγ (c * t) hct
    have hquad := rawExt_quad_le
      (I := I) g p hR hloc hz (hRm (γc t) hz) (Jc t)
        (Variation.curveVelocity (I := 𝓘(Real, E)) γc t)
    have hspeedEq : gExt.inner (γc t)
        (Variation.curveVelocity (I := 𝓘(Real, E)) γc t)
        (Variation.curveVelocity (I := 𝓘(Real, E)) γc t) =
          gExt.inner x (c • v) (c • v) := by
      simpa only [γc, Variation.curveVelocity] using
        intrinsicGeodesic_speedSq_eq
          (I := 𝓘(Real, E)) gExt hExt x (c • v) t
    calc
      _ ≤ K * gExt.inner (γc t) (Jc t) (Jc t) *
          gExt.inner (γc t)
            (Variation.curveVelocity (I := 𝓘(Real, E)) γc t)
            (Variation.curveVelocity (I := 𝓘(Real, E)) γc t) := by
        simpa only [gExt] using hquad
      _ = κ * gExt.inner (γc t) (Jc t) (Jc t) := by
        rw [hspeedEq, hscaleSq]
        dsimp only [κ]
        ring
  have hpos := Variation.jacobi_pair_pos
    (I := 𝓘(Real, E)) gExt γc Jc hγc hgeoc hJcdiff hDJcdiff
    (fun t ht => hJacc t) hJc0 hJc1 hspeedc hJperpc hκ0 hκπ hcurvc
  have hγcfun : γc = fun t : Real => γ (c * t + 0) := by
    funext t
    simpa only [add_zero] using hGeoScale t
  have hJcfun : Jc = fun t : Real => J (c * t + 0) := by
    funext t
    simpa only [add_zero] using hJacScale t
  have hDscale : CovariantDerivativeAlong.covDerivAlong
      (I := 𝓘(Real, E)) gExt γc Jc 1 = c • DJ c := by
    rw [hγcfun, hJcfun]
    have haff := covDeriv_comp_affine
      (I := 𝓘(Real, E)) gExt γ J c 0 1
    have hc10 : c * 1 + 0 = c := by ring
    rw [hc10] at haff
    simpa only [DJ] using haff
  have hγc1 : γc 1 = γ c := by
    simpa only [mul_one] using hGeoScale 1
  have hJc1eq : Jc 1 = J c := by
    simpa only [mul_one] using hJacScale 1
  have hpos' : 0 < c * gExt.inner (γ c) (DJ c) (J c) := by
    calc
      0 < gExt.inner (γc 1)
          (CovariantDerivativeAlong.covDerivAlong
            (I := 𝓘(Real, E)) gExt γc Jc 1)
          (Jc 1) := hpos
      _ = c * gExt.inner (γ c) (DJ c) (J c) := by
        rw [hγc1, hDscale, hJc1eq]
        calc
          gExt.inner (γ c) (c • DJ c) (J c) =
              (c • gExt.inner (γ c) (DJ c)) (J c) :=
            congrArg (fun A : E →L[Real] Real => A (J c))
              ((gExt.inner (γ c)).map_smul c (DJ c))
          _ = c * gExt.inner (γ c) (DJ c) (J c) := by
            rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hpairpos : 0 < gExt.inner (γ c) (DJ c) (J c) := by
    nlinarith [hcIoo.1]
  exact (ne_of_gt hpairpos) hpair0

omit [T2Space M] [SigmaCompactSpace M] in
/-- A fenced raw complete-extension geodesic below the curvature conjugacy
scale has no conjugate endpoint. -/
theorem rawExt_no_conj
    (g : SmoothRiemannianMetric I M) (p : M) {R K L : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    {x : E} (v : TangentSpace 𝓘(Real, E) x)
    (hfence : ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖rawExtLaunch (I := I) g p hR hloc x v t‖ < 3 * R / 4)
    (hv : Real.sqrt ((rawExtMetric (I := I) g p hR hloc).inner x v v) ≤ L)
    (hK : 0 ≤ K)
    (hRm : ∀ z : E, ‖z‖ < 3 * R / 4 →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (framedExpMap (I := I) g p z) 4
        (Geometry.Curvature.metricRm04At (I := I) (M := M) g
          (framedExpMap (I := I) g p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2) :
    let gExt := rawExtMetric (I := I) g p hR hloc
    letI : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w u; rfl⟩
    letI : PseudoEMetricSpace E :=
      PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    letI : CompleteSpace E := (rawExt_complete (I := I) g p hR hloc).complete
    let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
      fun z w => tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
    ¬ IsConjVec (I := 𝓘(Real, E)) gExt hExt x (v : E) := by
  classical
  let gExt := rawExtMetric (I := I) g p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) := inferInstance
  letI (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) := inferInstance
  letI : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w u; rfl⟩
  letI : PseudoEMetricSpace E :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E := (rawExt_complete (I := I) g p hR hloc).complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w => tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := 𝓘(Real, E)) gExt z w
  change ¬ IsConjVec (I := 𝓘(Real, E)) gExt hExt x (v : E)
  exact rawExt_no_conj_pos
    (I := I) g p hR hloc v hfence hv hK hRm hsmall

omit [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private theorem rawBranch_pair_pos
    (g : SmoothRiemannianMetric I M) (p : M) {R K L : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    {x : E} (u w : TangentSpace 𝓘(Real, E) x)
    (hfence :
      ∀ t ∈ Set.Icc (0 : Real) 1,
        ‖rawExtLaunch (I := I) g p hR hloc x u t‖ < 3 * R / 4)
    (hu : Real.sqrt ((rawExtMetric (I := I) g p hR hloc).inner x u u) ≤ L)
    (hune : (u : E) ≠ 0) (hwne : (w : E) ≠ 0)
    (hperp : (rawExtMetric (I := I) g p hR hloc).inner x u w = 0)
    (hK : 0 ≤ K)
    (hRm : ∀ z : E, ‖z‖ < 3 * R / 4 →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (framedExpMap (I := I) g p z) 4
        (Geometry.Curvature.metricRm04At
          (I := I) (M := M) g (framedExpMap (I := I) g p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2) :
    let gExt := rawExtMetric (I := I) g p hR hloc
    letI : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v₁ v₂; rfl⟩
    letI : PseudoEMetricSpace E :=
      PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    letI : CompleteSpace E :=
      (rawExt_complete (I := I) g p hR hloc).complete
    let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
      fun z v =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z v
    let γ : Real → E :=
      intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x u
    let J : Real → E :=
      intrinsicJacobi (I := 𝓘(Real, E)) gExt hExt x u w
    ∀ (B : ExpInvBranch (I := 𝓘(Real, E)) gExt hExt x),
      (u : E) ∈ B.hom.source →
      0 < gExt.inner (γ 1)
        (CovariantDerivativeAlong.covDerivAlong
          (I := 𝓘(Real, E)) gExt γ J 1) (J 1) := by
  classical
  let gExt := rawExtMetric (I := I) g p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v₁ v₂; rfl⟩
  letI : PseudoEMetricSpace E :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (rawExt_complete (I := I) g p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
  let γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x u
  let J : Real → E :=
    intrinsicJacobi (I := 𝓘(Real, E)) gExt hExt x u w
  change
    ∀ (B : ExpInvBranch (I := 𝓘(Real, E)) gExt hExt x),
      (u : E) ∈ B.hom.source →
      0 < gExt.inner (γ 1)
        (CovariantDerivativeAlong.covDerivAlong
          (I := 𝓘(Real, E)) gExt γ J 1) (J 1)
  intro B huB
  have hnot : ¬ IsConjVec (I := 𝓘(Real, E)) gExt hExt x (u : E) := by
    simpa only [gExt, hExt] using ExpInvBranch.not_conj B huB
  have hJ1 : J 1 ≠ 0 := by
    intro hzero
    apply hnot
    rw [isConjVec_iff_jacobi
      (I := 𝓘(Real, E)) gExt hExt x (u : E)]
    refine ⟨w, hwne, ?_⟩
    simpa only [J, intrinsicJacobi] using hzero
  have hγ : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ := by
    simpa only [γ] using
      intrinsicGeodesic_contMDiff (I := 𝓘(Real, E)) gExt hExt x u
  have hgeo : IsGeodesicOn (I := 𝓘(Real, E)) gExt γ
      (Set.Icc (0 : Real) 1) := by
    simpa only [γ] using
      (intrinsicGeodesic_isGeodesic
        (I := 𝓘(Real, E)) gExt hExt x u).isGeodesicOn
          (Set.Icc (0 : Real) 1)
  have hJdiff (t : Real) : DifferentiableAt Real
      (CovariantDerivativeAlong.chartRepAt
        (I := 𝓘(Real, E)) γ J t) t := by
    simpa only [γ, J] using
      (intrJacobi_diff (I := 𝓘(Real, E)) gExt hExt x u w t).1
  have hDJdiff (t : Real) : DifferentiableAt Real
      (CovariantDerivativeAlong.chartRepAt
        (I := 𝓘(Real, E)) γ
        (fun s => CovariantDerivativeAlong.covDerivAlong
          (I := 𝓘(Real, E)) gExt γ J s) t) t := by
    simpa only [γ, J] using
      (intrJacobi_diff (I := 𝓘(Real, E)) gExt hExt x u w t).2
  have hJac : Variation.IsJacobiAlong (I := 𝓘(Real, E)) gExt γ J := by
    simpa only [γ, J, intrinsicJacobi] using
      intrinsic_jacobi (I := 𝓘(Real, E)) gExt hExt x (u : E) (w : E)
  have hJ0 : J 0 = 0 := by
    simpa only [J] using
      intrinsicJacobi_zero (I := 𝓘(Real, E)) gExt hExt x u w
  have hJperp : ∀ t ∈ Set.Icc (0 : Real) 1,
      gExt.inner (γ t) (J t)
        (Variation.curveVelocity (I := 𝓘(Real, E)) γ t) = 0 := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      rw [hJ0, gExt.symm]
      exact (gExt.inner (γ 0)
        (Variation.curveVelocity (I := 𝓘(Real, E)) γ 0)).map_zero
    · rw [gExt.symm]
      exact intrJacobi_perp_ne
        (I := 𝓘(Real, E)) gExt hExt x u w ht0 hperp
  have hspeed : ∀ t ∈ Set.Icc (0 : Real) 1,
      0 < gExt.inner (γ t)
        (Variation.curveVelocity (I := 𝓘(Real, E)) γ t)
        (Variation.curveVelocity (I := 𝓘(Real, E)) γ t) := by
    intro t _ht
    change 0 < gExt.inner
      (intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x u t)
      (mfderiv 𝓘(Real, Real) 𝓘(Real, E)
        (intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x u) t 1)
      (mfderiv 𝓘(Real, Real) 𝓘(Real, E)
        (intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x u) t 1)
    rw [intrinsicGeodesic_speedSq_eq
      (I := 𝓘(Real, E)) gExt hExt x u t]
    exact gExt.pos x u hune
  let ell : Real := Real.sqrt (gExt.inner x u u)
  have hell0 : 0 ≤ ell := Real.sqrt_nonneg _
  have hellL : ell ≤ L := by
    simpa only [ell, gExt] using hu
  have hvnn : 0 ≤ gExt.inner x u u := (gExt.pos x u hune).le
  have hsqLe : ell ^ 2 ≤ L ^ 2 := by
    have hL0 : 0 ≤ L := hell0.trans hellL
    nlinarith
  have hellSq : gExt.inner x u u = ell ^ 2 := by
    dsimp only [ell]
    exact (Real.sq_sqrt hvnn).symm
  let κ : Real := K * ell ^ 2
  have hκ0 : 0 ≤ κ := mul_nonneg hK (sq_nonneg ell)
  have hκπ : κ < (Real.pi / 2) ^ 2 :=
    (mul_le_mul_of_nonneg_left hsqLe hK).trans_lt hsmall
  have hcurv : ∀ t ∈ Set.Icc (0 : Real) 1,
      gExt.inner (γ t)
          (Geometry.Curvature.riemannOp
            (Geometry.Connection.LeviCivita
              (I := 𝓘(Real, E)) gExt)
            (γ t) (J t)
            (Variation.curveVelocity (I := 𝓘(Real, E)) γ t)
            (Variation.curveVelocity (I := 𝓘(Real, E)) γ t))
          (J t) ≤ κ * gExt.inner (γ t) (J t) (J t) := by
    intro t ht
    have hz : ‖γ t‖ < 3 * R / 4 := by
      simpa only [γ, gExt, hExt, rawExtLaunch] using hfence t ht
    have hquad := rawExt_quad_le
      (I := I) g p hR hloc hz (hRm (γ t) hz)
        (J t) (Variation.curveVelocity (I := 𝓘(Real, E)) γ t)
    have hspeedEq : gExt.inner (γ t)
        (Variation.curveVelocity (I := 𝓘(Real, E)) γ t)
        (Variation.curveVelocity (I := 𝓘(Real, E)) γ t) =
          gExt.inner x u u := by
      simpa only [γ, Variation.curveVelocity] using
        intrinsicGeodesic_speedSq_eq
          (I := 𝓘(Real, E)) gExt hExt x u t
    calc
      _ ≤ K * gExt.inner (γ t) (J t) (J t) * gExt.inner (γ t)
          (Variation.curveVelocity (I := 𝓘(Real, E)) γ t)
          (Variation.curveVelocity (I := 𝓘(Real, E)) γ t) := by
        simpa only [gExt] using hquad
      _ = κ * gExt.inner (γ t) (J t) (J t) := by
        rw [hspeedEq, hellSq]
        dsimp only [κ]
        ring
  exact Variation.jacobi_pair_pos
    (I := 𝓘(Real, E)) gExt γ J hγ hgeo hJdiff hDJdiff
    (fun t _ht => hJac t) hJ0 hJ1 hspeed hJperp hκ0 hκπ hcurv

omit [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
/-- Branch energy has positive Hessian off zero along a fenced raw extension. -/
theorem rawBranch_hess_pos
    (g : SmoothRiemannianMetric I M)
    (p : M) {R K L : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (framedExpMap (I := I) g p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (framedExpMap (I := I) g p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (framedExpMap (I := I) g p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2)
    {x : E} (u : E)
    (hfence :
      ∀ t ∈ Set.Icc (0 : Real) 1,
        ‖rawExtLaunch (I := I) g p hR hloc x u t‖ <
          3 * R / 4)
    (huL :
      Real.sqrt
          ((rawExtMetric (I := I) g p hR hloc).inner x u u) ≤
        L) :
    let gExt := rawExtMetric (I := I) g p hR hloc
    letI : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
    letI : PseudoEMetricSpace E :=
      PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    letI : CompleteSpace E :=
      (rawExt_complete (I := I) g p hR hloc).complete
    let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
      fun z v =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z v
    ∀ (B : ExpInvBranch (I := 𝓘(Real, E)) gExt hExt x),
      (u : E) ∈ B.hom.source →
      ∀ {Y : E}, Y ≠ 0 →
        0 < hessFun (I := 𝓘(Real, E)) gExt
          (branchEnergy (I := 𝓘(Real, E)) gExt B)
          (expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x u) Y Y := by
  classical
  let gExt := rawExtMetric (I := I) g p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : PseudoEMetricSpace E :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (rawExt_complete (I := I) g p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z v
  change
    ∀ (B : ExpInvBranch (I := 𝓘(Real, E)) gExt hExt x),
      u ∈ B.hom.source →
      ∀ {Y : E}, Y ≠ 0 →
        0 < hessFun (I := 𝓘(Real, E)) gExt
          (branchEnergy (I := 𝓘(Real, E)) gExt B)
          (expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x u) Y Y
  intro B huB Y hY
  have hzeroCase :
      u = 0 →
        0 < hessFun (I := 𝓘(Real, E)) gExt
          (branchEnergy (I := 𝓘(Real, E)) gExt B)
          (expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x u) Y Y := by
    intro hu0
    subst u
    have hh :=
      rawBranch_hess_zero
        (I := 𝓘(Real, E)) gExt hExt x B huB Y
    have hpos :
        0 < hessFun (I := 𝓘(Real, E)) gExt
          (branchEnergy (I := 𝓘(Real, E)) gExt B) x Y Y := by
      rw [hh]
      exact gExt.pos x Y hY
    have hexp :
        expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x
            (0 : TangentSpace 𝓘(Real, E) x) =
          x :=
      expMapIntrinsic_zero (I := 𝓘(Real, E)) gExt hExt x
    exact Eq.mpr
      (congrArg
        (fun z : E =>
          0 < hessFun (I := 𝓘(Real, E)) gExt
            (branchEnergy (I := 𝓘(Real, E)) gExt B) z Y Y)
        hexp)
      hpos
  let γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x u
  let J : E → Real → E := fun W =>
    intrinsicJacobi (I := 𝓘(Real, E)) gExt hExt x u W
  let q : E :=
    expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x u
  have hq :
      q = intrinsicGeodesic
        (I := 𝓘(Real, E)) gExt hExt x u 1 := by
    rfl
  have hqDom : q ∈ B.dom := by
    rw [show q = B.hom (u : E) by
      exact B.hom_eq huB]
    exact B.hom.map_source huB
  have hsmooth :
      ContMDiffOn 𝓘(Real, E) 𝓘(Real, Real) ∞
        (branchEnergy (I := 𝓘(Real, E)) gExt B) B.dom :=
    branchEnergy_inf (I := 𝓘(Real, E)) B
  obtain ⟨F, hF, hFgerm⟩ :=
    DifferentialGeometry.exists_smooth_germ
      (I := 𝓘(Real, E)) B.hom.open_target hqDom hsmooth
  let expf : E → E := fun v =>
    expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x v
  let D : E →L[Real] E :=
    mfderiv 𝓘(Real, E) 𝓘(Real, E) expf u
  let w : E :=
    mfderiv 𝓘(Real, E) 𝓘(Real, E) B.inv q Y
  have hJone (V : E) :
      J V 1 = D V := by
    have hraw :=
      intrinsic_jacobi_one
        (I := 𝓘(Real, E)) gExt hExt x (u : E) V
    simpa only [J, intrinsicJacobi, expf, D] using hraw
  have hJw : J w 1 = Y := by
    have hright :=
      exp_inv_mfderiv
        (I := 𝓘(Real, E)) B hqDom Y
    have hinv : B.inv q = (u : E) := by
      change
        B.inv
            (expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x
              (show TangentSpace 𝓘(Real, E) x from u)) =
          u
      exact B.left_inv huB
    have hright' :
        mfderiv 𝓘(Real, E) 𝓘(Real, E) expf (B.inv q) w = Y := by
      simpa only [expf, w] using hright
    have hbase :
        D w =
          mfderiv 𝓘(Real, E) 𝓘(Real, E) expf (B.inv q) w := by
      dsimp only [D]
      rw [hinv]
      rfl
    exact (hJone w).trans (hbase.trans hright')
  have hwne : w ≠ 0 := by
    intro hw
    apply hY
    calc
      Y = J w 1 := hJw.symm
      _ = J 0 1 := congrArg (fun V : E => J V 1) hw
      _ = D 0 := hJone 0
      _ = 0 := map_zero _
  by_cases hu0 : (u : E) = 0
  · exact hzeroCase hu0
  · let uE : E := u
    let d : Real := gExt.inner x u u
    let α : Real := gExt.inner x u w / d
    let W : E := w - α • uE
    have hdpos : 0 < d := by
      dsimp only [d]
      exact gExt.pos x u hu0
    have hperp : gExt.inner x u W = 0 := by
      calc
        gExt.inner x u W =
            gExt.inner x u w - gExt.inner x u (α • uE) := by
          exact (gExt.inner x u).map_sub w (α • uE)
        _ = gExt.inner x u w - α * gExt.inner x u uE := by
          exact congrArg (fun z : Real => gExt.inner x u w - z)
            (by
              simpa only [smul_eq_mul] using
                (gExt.inner x u).map_smul α uE)
        _ = 0 := by
          change
            gExt.inner x u w -
                (gExt.inner x u w / d) * d =
              0
          rw [div_mul_cancel₀ _ (ne_of_gt hdpos), sub_self]
    have hwdecomp : w = W + α • uE := by
      dsimp only [W]
      abel
    have hYdecomp :
        Y = J W 1 + α • J uE 1 := by
      calc
        Y = J w 1 := hJw.symm
        _ = D w := hJone w
        _ = D (W + α • uE) := by rw [← hwdecomp]
        _ =
            D W + α • D uE := by
          calc
            _ = D W + D (α • uE) := D.map_add W (α • uE)
            _ = _ := congrArg
              (fun z : E => D W + z) (D.map_smul α uE)
        _ = J W 1 + α • J uE 1 := by
          rw [hJone W, hJone uE]
    have hγsmooth :
        ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ :=
      intrinsicGeodesic_contMDiff
        (I := 𝓘(Real, E)) gExt hExt x u
    have hlineCont :
        ContinuousAt (fun t : Real => t • uE) 1 :=
      (continuous_id.smul continuous_const).continuousAt
    have hsrc :
        ∀ᶠ t in 𝓝 (1 : Real), t • uE ∈ B.hom.source := by
      have hnhds := B.hom.open_source.mem_nhds huB
      have hnhds' :
          B.hom.source ∈ 𝓝 ((fun t : Real => t • uE) 1) := by
        simpa only [uE, one_smul] using hnhds
      exact hlineCont hnhds'
    have henergy :
        (branchEnergy (I := 𝓘(Real, E)) gExt B) ∘ γ =ᶠ[𝓝 (1 : Real)]
          fun t : Real => (1 / 2 : Real) * t ^ 2 * gExt.inner x u u := by
      filter_upwards [hsrc] with t ht
      calc
        branchEnergy (I := 𝓘(Real, E)) gExt B (γ t) =
            branchEnergy (I := 𝓘(Real, E)) gExt B
              (expMapIntrinsic
                (I := 𝓘(Real, E)) gExt hExt x (t • u)) := by
          exact congrArg
            (branchEnergy (I := 𝓘(Real, E)) gExt B)
            (intrinsicGeodesic_smul
              (I := 𝓘(Real, E)) gExt hExt x u t).symm
        _ = (1 / 2 : Real) * gExt.inner x (t • u) (t • u) :=
          branchEnergy_exp (I := 𝓘(Real, E)) B ht
        _ = (1 / 2 : Real) * t ^ 2 * gExt.inner x u u := by
          have hleftMap := (gExt.inner x).map_smul t u
          have hleft :
              gExt.inner x (t • u) (t • u) =
                t * gExt.inner x u (t • u) := by
            calc
              _ = (t • gExt.inner x u) (t • u) :=
                congrArg
                  (fun L : TangentSpace 𝓘(Real, E) x →L[Real] Real =>
                    L (t • u))
                  hleftMap
              _ = _ := by
                simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
          have hright := (gExt.inner x u).map_smul t u
          calc
            _ = (1 / 2 : Real) *
                (t * gExt.inner x u (t • u)) := by
              exact congrArg (fun r : Real => (1 / 2 : Real) * r)
                hleft
            _ = (1 / 2 : Real) *
                (t * (t * gExt.inner x u u)) := by
              exact congrArg (fun r : Real => (1 / 2 : Real) * (t * r))
                (by simpa only [smul_eq_mul] using hright)
            _ = _ := by ring
    have hd2Energy :
        (deriv^[2]
          ((branchEnergy (I := 𝓘(Real, E)) gExt B) ∘ γ)) 1 =
            gExt.inner x u u := by
      exact
        (Filter.EventuallyEq.deriv_eq henergy.deriv).trans
          (quad_deriv2 (gExt.inner x u u) 1)
    have hd2Geo :=
      deriv2_geo_on_at
        (I := 𝓘(Real, E)) gExt B.hom.open_target hsmooth hγsmooth
          ((intrinsicGeodesic_isGeodesic
            (I := 𝓘(Real, E)) gExt hExt x u) 1) hqDom
    have hJu :
        J uE 1 =
          Variation.curveVelocity (I := 𝓘(Real, E)) γ 1 := by
      simpa only [γ, J, uE] using
        intrJacobi_self
          (I := 𝓘(Real, E)) gExt hExt x u
    have hdiag :
        hessFun (I := 𝓘(Real, E)) gExt
            (branchEnergy (I := 𝓘(Real, E)) gExt B)
            q (J uE 1) (J uE 1) =
          gExt.inner x u u := by
      rw [hJu]
      have hd2Geo' :
          (deriv^[2]
              ((branchEnergy (I := 𝓘(Real, E)) gExt B) ∘ γ)) 1 =
            hessFun (I := 𝓘(Real, E)) gExt
              (branchEnergy (I := 𝓘(Real, E)) gExt B)
              q
              (Variation.curveVelocity (I := 𝓘(Real, E)) γ 1)
              (Variation.curveVelocity (I := 𝓘(Real, E)) γ 1) := by
        simpa only [γ, q, expMapIntrinsic_def] using hd2Geo
      exact hd2Geo'.symm.trans hd2Energy
    have hcross :
        hessFun (I := 𝓘(Real, E)) gExt
            (branchEnergy (I := 𝓘(Real, E)) gExt B)
            q (J W 1) (J uE 1) = 0 := by
      have hh :=
        branchEnergy_hess
          (I := 𝓘(Real, E)) B
            (u := u) (w₁ := W) (w₂ := uE) huB
      dsimp only at hh
      have hdperp :=
        intrJacobi_dperp
          (I := 𝓘(Real, E)) gExt hExt x u W one_ne_zero hperp
      have hpair :
          gExt.inner (γ 1)
              (CovariantDerivativeAlong.covDerivAlong
                (I := 𝓘(Real, E)) gExt γ (J W) 1)
              (J uE 1) = 0 := by
        rw [hJu, gExt.symm]
        simpa only [γ, J] using hdperp
      simpa only [γ, J, q, expMapIntrinsic_def] using hh.trans hpair
    have hcross' :
        hessFun (I := 𝓘(Real, E)) gExt
            (branchEnergy (I := 𝓘(Real, E)) gExt B)
            q (J uE 1) (J W 1) = 0 := by
      calc
        _ = hessFun (I := 𝓘(Real, E)) gExt F q
              (J uE 1) (J W 1) := by
          rw [hessFun_congr (I := 𝓘(Real, E)) gExt hFgerm]
        _ = hessFun (I := 𝓘(Real, E)) gExt F q
              (J W 1) (J uE 1) :=
          hessFun_symm_of_boundaryless
            (I := 𝓘(Real, E)) gExt hF q (J uE 1) (J W 1)
        _ = hessFun (I := 𝓘(Real, E)) gExt
              (branchEnergy (I := 𝓘(Real, E)) gExt B)
              q (J W 1) (J uE 1) := by
          rw [hessFun_congr (I := 𝓘(Real, E)) gExt hFgerm]
        _ = 0 := hcross
    have hscale :
        hessFun (I := 𝓘(Real, E)) gExt
            (branchEnergy (I := 𝓘(Real, E)) gExt B) q
            (α • J uE 1) (α • J uE 1) =
          α ^ 2 *
            hessFun (I := 𝓘(Real, E)) gExt
              (branchEnergy (I := 𝓘(Real, E)) gExt B) q
              (J uE 1) (J uE 1) := by
      have hleft :=
        LinearMap.map_smul₂
            (hessFun (I := 𝓘(Real, E)) gExt
              (branchEnergy (I := 𝓘(Real, E)) gExt B) q)
          α (J uE 1) (α • J uE 1)
      have hright :=
          (hessFun (I := 𝓘(Real, E)) gExt
            (branchEnergy (I := 𝓘(Real, E)) gExt B) q
            (J uE 1)).map_smul α (J uE 1)
      calc
        _ = α * hessFun (I := 𝓘(Real, E)) gExt
              (branchEnergy (I := 𝓘(Real, E)) gExt B) q
              (J uE 1) (α • J uE 1) := by
          simpa only [smul_eq_mul] using hleft
        _ = α * (α * hessFun (I := 𝓘(Real, E)) gExt
              (branchEnergy (I := 𝓘(Real, E)) gExt B) q
              (J uE 1) (J uE 1)) := by
          exact congrArg (fun r : Real => α * r)
            (by simpa only [smul_eq_mul] using hright)
        _ = _ := by ring
    change
      0 < hessFun (I := 𝓘(Real, E)) gExt
        (branchEnergy (I := 𝓘(Real, E)) gExt B) q Y Y
    have hJzero : J 0 1 = 0 := by
      exact (hJone 0).trans (D.map_zero)
    by_cases hW : W = 0
    · have hα : α ≠ 0 := by
        intro hα
        apply hY
        rw [hYdecomp, hW, hJzero, hα, zero_smul, add_zero]
      rw [hYdecomp, hW, hJzero, zero_add, hscale, hdiag]
      exact mul_pos (sq_pos_of_ne_zero hα) hdpos
    · have hpair :=
        rawBranch_pair_pos
          (I := I) g p hR hloc u W hfence huL
            hu0 hW hperp hK hRm hsmall B huB
      have hh :=
        branchEnergy_hess
          (I := 𝓘(Real, E)) B
            (u := u) (w₁ := W) (w₂ := W) huB
      have hWW :
          0 < hessFun (I := 𝓘(Real, E)) gExt
            (branchEnergy (I := 𝓘(Real, E)) gExt B)
            q (J W 1) (J W 1) := by
        dsimp only at hh hpair
        simpa only [γ, J, q, expMapIntrinsic_def] using hh.symm ▸ hpair
      have hcrossA :
          hessFun (I := 𝓘(Real, E)) gExt
              (branchEnergy (I := 𝓘(Real, E)) gExt B) q
              (J W 1) (α • J uE 1) = 0 := by
        have hs :=
          (hessFun (I := 𝓘(Real, E)) gExt
            (branchEnergy (I := 𝓘(Real, E)) gExt B) q
            (J W 1)).map_smul α (J uE 1)
        calc
          _ = α * hessFun (I := 𝓘(Real, E)) gExt
                (branchEnergy (I := 𝓘(Real, E)) gExt B) q
                (J W 1) (J uE 1) := by
            simpa only [smul_eq_mul] using hs
          _ = 0 := by rw [hcross, mul_zero]
      have hcrossA' :
          hessFun (I := 𝓘(Real, E)) gExt
              (branchEnergy (I := 𝓘(Real, E)) gExt B) q
              (α • J uE 1) (J W 1) = 0 := by
        have hs :=
          LinearMap.map_smul₂
            (hessFun (I := 𝓘(Real, E)) gExt
              (branchEnergy (I := 𝓘(Real, E)) gExt B) q)
            α (J uE 1) (J W 1)
        calc
          _ = α * hessFun (I := 𝓘(Real, E)) gExt
                (branchEnergy (I := 𝓘(Real, E)) gExt B) q
                (J uE 1) (J W 1) := by
            simpa only [smul_eq_mul] using hs
          _ = 0 := by rw [hcross', mul_zero]
      have hexpand :
          hessFun (I := 𝓘(Real, E)) gExt
              (branchEnergy (I := 𝓘(Real, E)) gExt B) q
              (J W 1 + α • J uE 1)
              (J W 1 + α • J uE 1) =
            (hessFun (I := 𝓘(Real, E)) gExt
                (branchEnergy (I := 𝓘(Real, E)) gExt B) q
                (J W 1) (J W 1) +
              hessFun (I := 𝓘(Real, E)) gExt
                (branchEnergy (I := 𝓘(Real, E)) gExt B) q
                (J W 1) (α • J uE 1)) +
            (hessFun (I := 𝓘(Real, E)) gExt
                (branchEnergy (I := 𝓘(Real, E)) gExt B) q
                (α • J uE 1) (J W 1) +
              hessFun (I := 𝓘(Real, E)) gExt
                (branchEnergy (I := 𝓘(Real, E)) gExt B) q
                (α • J uE 1) (α • J uE 1)) := by
        have hleft :=
          LinearMap.map_add₂
            (hessFun (I := 𝓘(Real, E)) gExt
              (branchEnergy (I := 𝓘(Real, E)) gExt B) q)
            (J W 1) (α • J uE 1)
            (J W 1 + α • J uE 1)
        have hrightW :=
          (hessFun (I := 𝓘(Real, E)) gExt
            (branchEnergy (I := 𝓘(Real, E)) gExt B) q
            (J W 1)).map_add (J W 1) (α • J uE 1)
        have hrightA :=
          (hessFun (I := 𝓘(Real, E)) gExt
            (branchEnergy (I := 𝓘(Real, E)) gExt B) q
            (α • J uE 1)).map_add
              (J W 1) (α • J uE 1)
        exact hleft.trans
          (congrArg₂ (fun a b : Real => a + b) hrightW hrightA)
      have hrad : 0 ≤ α ^ 2 * gExt.inner x u u :=
        mul_nonneg (sq_nonneg α) hdpos.le
      rw [hYdecomp, hexpand, hcrossA, hcrossA', hscale, hdiag,
        add_zero, zero_add]
      exact add_pos_of_pos_of_nonneg hWW hrad


end CGT
end Riemannian
end Geometry
end DifferentialGeometry
