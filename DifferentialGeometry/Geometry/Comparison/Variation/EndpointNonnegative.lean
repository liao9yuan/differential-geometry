import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariationMinimiser
import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrameIndex
import DifferentialGeometry.Geometry.Curvature.MetricSectional

set_option autoImplicit false

open Set Function Manifold Bundle MeasureTheory intervalIntegral
open scoped Topology Manifold ContDiff RealInnerProductSpace Bundle

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem jacobi_pair_le_flat
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (γ : ℝ → M) (J : ∀ t : ℝ, TangentSpace I (γ t))
    {L : ℝ} (hL : 0 < L)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hJbundle : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t) (J t)))
    (hDJdiff : ∀ t, DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 L))
    (hmin : ∀ η : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 L) →
      η 0 = γ 0 → η L = γ L →
      arcLength (I := I) g γ 0 L ≤ arcLength (I := I) g η 0 L)
    (hunit : ∀ t ∈ Icc (0 : ℝ) L,
      g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 1)
    (hJac : ∀ t ∈ Icc (0 : ℝ) L, IsJacobiAt (I := I) g γ J t)
    (hJ0 : J 0 = 0)
    (hperp : ∀ t ∈ Icc (0 : ℝ) L,
      g.inner (γ t) (J t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 0)
    (hsec : NonnegSecMetric (I := I) (M := M) g) :
    g.inner (γ L) (covDerivAlong (I := I) g γ J L) (J L) ≤
      g.inner (γ L) (J L) (J L) / L := by
  classical
  let DJ : ∀ t : ℝ, TangentSpace I (γ t) :=
    fun t => covDerivAlong (I := I) g γ J t
  obtain ⟨F, hFdiff, hFpar, hON, hFperp, hFbundle⟩ :=
    exists_parallel_perp_frame (I := I) g γ hγ hL hgeo
      (hunit 0 ⟨le_rfl, hL.le⟩)
  let e : Fin (Module.finrank ℝ E - 1) →
      ∀ t : ℝ, TangentSpace I (γ t) :=
    fun i => (F i).toFun
  let R : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    perpCurvOp (I := I) g γ e
  let y : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    perpCoeff (I := I) g e J
  let v : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    perpCoeff (I := I) g e DJ
  have hJdiff (t : ℝ) :
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t :=
    chartRep_diff (I := I) γ J hJbundle t
  have hode (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      HasDerivAt y (v t) t ∧ HasDerivAt v (-(R t) (y t)) t := by
    simpa only [y, v, R, e, DJ] using
      perpCoeff_ode (I := I) (n := ∞) (by simp) g γ e J t
        hγ.contMDiffAt
        (fun i => hFdiff i t ht)
        (hJdiff t) (hDJdiff t)
        (fun i => hFpar i t ht)
        (hJac t ht) (by simp)
        (by rw [show g.inner (γ t) (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t) = 1 by
              simpa only [curveVelocity] using hunit t ht]
            norm_num)
        (fun i => by simpa only [curveVelocity] using hFperp t ht i)
        (by simpa only [curveVelocity] using hperp t ht)
        (fun i j => hON t ht i j)
  have hsol : IsJacobiSolOn R 0 L y v :=
    { deriv_fst := fun t ht => (hode t ht).1.hasDerivWithinAt
      deriv_snd := fun t ht => (hode t ht).2.hasDerivWithinAt }
  have hRcont : ContinuousOn R (Icc (0 : ℝ) L) := by
    exact (perpCurv_smooth (I := I) g γ hγ e
      (fun i => hFbundle i)).continuous.continuousOn
  have hySmooth : ContDiff ℝ ∞ y := by
    exact perpCoeff_smooth (I := I) g e J
      (fun i => hFbundle i) hJbundle
  have hy0 : y 0 = 0 :=
    perpCoeff_zero (I := I) g e J 0 hJ0
  let z : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    fun t => (t * L⁻¹) • y L
  let w : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    fun _ => L⁻¹ • y L
  have hzDeriv (t : ℝ) : HasDerivAt z (w t) t := by
    simpa only [z, w, one_mul] using
      ((hasDerivAt_id t).mul_const L⁻¹).smul_const (y L)
  have hzSmooth : ContDiff ℝ ∞ z := by
    exact (contDiff_id.mul contDiff_const).smul_const (y L)
  have hwCont : Continuous w := by
    exact continuous_const
  have hz0 : z 0 = 0 := by
    simp only [z, zero_mul, zero_smul]
  have hzL : z L = y L := by
    simp only [z, mul_inv_cancel₀ hL.ne', one_smul]
  let q : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    y - z
  let r : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    v - w
  have hqSmooth : ContDiff ℝ ∞ q := by
    exact hySmooth.sub hzSmooth
  have hqDeriv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      HasDerivAt q (r t) t := by
    simpa only [q, r, Pi.sub_apply] using (hode t ht).1.sub (hzDeriv t)
  have hq0 : q 0 = 0 := by
    simp only [q, Pi.sub_apply, hy0, hz0, sub_self]
  have hqL : q L = 0 := by
    simp only [q, Pi.sub_apply, hzL, sub_self]
  have hqBundle : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t)
          (perpFrameLift (I := I) e q t)) := by
    exact perpLift_smooth (I := I) hγ e q hqSmooth
      (fun i => hFbundle i)
  have hgeomNonneg :
      0 ≤ indexForm (I := I) g γ 0 L
        (fun t => perpFrameLift (I := I) e q t)
        (fun t => perpFrameLift (I := I) e q t) := by
    apply indexForm_nonneg_of_minimising_geodesic
      (I := I) g hEnorm γ L
        (fun t => perpFrameLift (I := I) e q t)
        hL hγ hqBundle hgeo hmin hunit
    · intro t ht
      simpa only [curveVelocity] using
        perpLift_perp (I := I) g e q t
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          (fun i => by simpa only [curveVelocity] using hFperp t ht i)
    · exact perpLift_zero (I := I) e q 0 hq0
    · exact perpLift_zero (I := I) e q L hqL
  have hlift := perpLift_indexForm (I := I) g γ e q q 0 L
      (fun t _ => hqSmooth.differentiable (by simp) t)
      (fun t _ => hqSmooth.differentiable (by simp) t)
      (fun i t ht => by
        rw [uIcc_of_le hL.le] at ht
        exact hFdiff i t ht)
      (fun i t ht => by
        rw [uIcc_of_le hL.le] at ht
        exact hFpar i t ht)
      (fun t ht i j => by
        rw [uIcc_of_le hL.le] at ht
        exact hON t ht i j)
  have hqIndexDeriv :
      DifferentialGeometry.Analysis.ODE.indexForm R 0 L
          q (deriv q) q (deriv q) =
        DifferentialGeometry.Analysis.ODE.indexForm R 0 L q r q r := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hL.le] at ht
    have hd := (hqDeriv t ht).deriv
    simp only [DifferentialGeometry.Analysis.ODE.indexIntegrand, hd]
  have hqNonneg :
      0 ≤ DifferentialGeometry.Analysis.ODE.indexForm R 0 L q r q r := by
    rw [hlift, hqIndexDeriv] at hgeomNonneg
    exact hgeomNonneg
  have hyyInt : IntervalIntegrable
      (DifferentialGeometry.Analysis.ODE.indexIntegrand R y v y v)
      volume 0 L := by
    apply intInt_indexIntegrand
    · simpa only [uIcc_of_le hL.le] using hRcont
    · simpa only [uIcc_of_le hL.le] using hsol.contOn_fst
    · simpa only [uIcc_of_le hL.le] using hsol.contOn_snd
    · simpa only [uIcc_of_le hL.le] using hsol.contOn_fst
    · simpa only [uIcc_of_le hL.le] using hsol.contOn_snd
  have hyzInt : IntervalIntegrable
      (DifferentialGeometry.Analysis.ODE.indexIntegrand R y v z w)
      volume 0 L := by
    apply intInt_indexIntegrand
    · simpa only [uIcc_of_le hL.le] using hRcont
    · simpa only [uIcc_of_le hL.le] using hsol.contOn_fst
    · simpa only [uIcc_of_le hL.le] using hsol.contOn_snd
    · simpa only [uIcc_of_le hL.le] using hzSmooth.continuous.continuousOn
    · simpa only [uIcc_of_le hL.le] using hwCont.continuousOn
  have hzzInt : IntervalIntegrable
      (DifferentialGeometry.Analysis.ODE.indexIntegrand R z w z w)
      volume 0 L := by
    apply intInt_indexIntegrand
    · simpa only [uIcc_of_le hL.le] using hRcont
    · simpa only [uIcc_of_le hL.le] using hzSmooth.continuous.continuousOn
    · simpa only [uIcc_of_le hL.le] using hwCont.continuousOn
    · simpa only [uIcc_of_le hL.le] using hzSmooth.continuous.continuousOn
    · simpa only [uIcc_of_le hL.le] using hwCont.continuousOn
  have hRsymm : ∀ t, ∀ a b : EuclideanSpace ℝ
      (Fin (Module.finrank ℝ E - 1)),
      inner ℝ (R t a) b = inner ℝ a (R t b) := by
    intro t a b
    exact perpCurv_symm (I := I) g γ e t a b
  have hexpand := indexForm_add_smul hRsymm hyyInt hyzInt hzzInt (-1 : ℝ)
  have hqExpand :
      DifferentialGeometry.Analysis.ODE.indexForm R 0 L q r q r =
        DifferentialGeometry.Analysis.ODE.indexForm R 0 L y v y v +
          (-2) * DifferentialGeometry.Analysis.ODE.indexForm R 0 L y v z w +
          DifferentialGeometry.Analysis.ODE.indexForm R 0 L z w z w := by
    norm_num [q, r, sub_eq_add_neg] at hexpand ⊢
    exact hexpand
  have hyyEq :
      DifferentialGeometry.Analysis.ODE.indexForm R 0 L y v y v =
        inner ℝ (v L) (y L) := by
    rw [hsol.indexForm_eq_sub hL.le hRcont hsol.deriv_fst hsol.contOn_snd,
      hy0]
    simp
  have hyzEq :
      DifferentialGeometry.Analysis.ODE.indexForm R 0 L y v z w =
        inner ℝ (v L) (y L) := by
    rw [hsol.indexForm_eq_sub hL.le hRcont
      (fun t ht => (hzDeriv t).hasDerivWithinAt) hwCont.continuousOn,
      hzL, hz0]
    simp
  have hindexLe :
      DifferentialGeometry.Analysis.ODE.indexForm R 0 L y v y v ≤
        DifferentialGeometry.Analysis.ODE.indexForm R 0 L z w z w := by
    rw [hqExpand, hyyEq, hyzEq] at hqNonneg
    rw [hyyEq]
    linarith
  have hcurvNonneg (t : ℝ) : 0 ≤ inner ℝ (R t (z t)) (z t) := by
    rw [perpCurv_inner (I := I) g γ e (z t) (z t) t]
    exact hsec.riemann (γ t)
      (∑ i, z t i • e i t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
  have hwSqInt : IntervalIntegrable
      (fun _ : ℝ => inner ℝ (w 0) (w 0)) volume 0 L :=
    _root_.intervalIntegrable_const
  have htrialLe :
      DifferentialGeometry.Analysis.ODE.indexForm R 0 L z w z w ≤
        inner ℝ (y L) (y L) / L := by
    calc
      DifferentialGeometry.Analysis.ODE.indexForm R 0 L z w z w =
          ∫ t in (0 : ℝ)..L,
            DifferentialGeometry.Analysis.ODE.indexIntegrand R z w z w t := rfl
      _ ≤ ∫ _t in (0 : ℝ)..L, inner ℝ (w 0) (w 0) := by
        apply intervalIntegral.integral_mono_on hL.le hzzInt hwSqInt
        intro t _
        simp only [DifferentialGeometry.Analysis.ODE.indexIntegrand, w]
        exact sub_le_self _ (hcurvNonneg t)
      _ = inner ℝ (y L) (y L) / L := by
        rw [intervalIntegral.integral_const]
        simp only [sub_zero, w, real_inner_smul_left, real_inner_smul_right,
          smul_eq_mul]
        field_simp [hL.ne']
  have hpair : inner ℝ (v L) (y L) ≤ inner ℝ (y L) (y L) / L := by
    rw [← hyyEq]
    exact hindexLe.trans htrialLe
  have hJL : perpFrameLift (I := I) e y L = J L := by
    exact perpLift_coeff (I := I) g e J L (by simp)
      (by rw [show g.inner (γ L) (curveVelocity (I := I) γ L)
          (curveVelocity (I := I) γ L) = 1 by
            simpa only [curveVelocity] using hunit L ⟨hL.le, le_rfl⟩]
          norm_num)
      (fun i => by simpa only [curveVelocity] using hFperp L ⟨hL.le, le_rfl⟩ i)
      (by simpa only [curveVelocity] using hperp L ⟨hL.le, le_rfl⟩)
      (fun i j => hON L ⟨hL.le, le_rfl⟩ i j)
  have hJLsum : (∑ i, y L i • e i L) = J L := by
    simpa only [perpFrameLift] using hJL
  have hreadPair :
      g.inner (γ L) (DJ L) (J L) = inner ℝ (v L) (y L) := by
    rw [← hJLsum, map_sum, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show v L i = g.inner (γ L) (e i L) (DJ L) by
        simp only [v, perpCoeff_apply],
      g.symm (γ L) (e i L) (DJ L)]
    rw [map_smul]
    simp [real_inner_eq_re_inner, RCLike.inner_apply]
  have hreadNorm :
      g.inner (γ L) (J L) (J L) = inner ℝ (y L) (y L) := by
    rw [← hJLsum]
    exact perpLift_inner (I := I) g e (y L) (y L) L
      (fun i j => hON L ⟨hL.le, le_rfl⟩ i j)
  rw [hreadPair, hreadNorm]
  exact hpair

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
