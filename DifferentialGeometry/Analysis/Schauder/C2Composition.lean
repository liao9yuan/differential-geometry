import DifferentialGeometry.Analysis.Schauder.Composition

noncomputable section

open Filter
open scoped ContDiff

namespace DifferentialGeometry.Analysis.Schauder

variable {V W F : Type*}
  [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup W] [NormedSpace Real W]
  [NormedAddCommGroup F] [NormedSpace Real F]

def c1PullbackGradient
    (Dphi : V →L[Real] W) (Du : W →L[Real] F) : V →L[Real] F :=
  Du.comp Dphi

theorem norm_c1PullbackGradient_le
    (Dphi : V →L[Real] W) (Du : W →L[Real] F) :
    ‖c1PullbackGradient Dphi Du‖ ≤ ‖Du‖ * ‖Dphi‖ :=
  ContinuousLinearMap.opNorm_comp_le _ _

theorem continuousMultilinearCurryFin1_iteratedFDeriv_one_comp
    {f : W → F} {phi : V → W} {x : V}
    (hf : DifferentiableAt Real f (phi x))
    (hphi : DifferentiableAt Real phi x) :
    continuousMultilinearCurryFin1 Real V F
        (iteratedFDeriv Real 1 (f ∘ phi) x) =
      c1PullbackGradient (fderiv Real phi x) (fderiv Real f (phi x)) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply,
    fderiv_comp x hf hphi]
  rfl

def c2PullbackHessian
    (Dphi : V →L[Real] W) (D2phi : V →L[Real] V →L[Real] W)
    (Du : W →L[Real] F) (D2u : W →L[Real] W →L[Real] F) :
    V →L[Real] V →L[Real] F :=
  (ContinuousLinearMap.compL Real V W F Du).comp D2phi +
    ((ContinuousLinearMap.compL Real V W F).flip Dphi).comp
      (D2u.comp Dphi)

theorem norm_c2PullbackHessian_le
    (Dphi : V →L[Real] W) (D2phi : V →L[Real] V →L[Real] W)
    (Du : W →L[Real] F) (D2u : W →L[Real] W →L[Real] F) :
    ‖c2PullbackHessian Dphi D2phi Du D2u‖ ≤
      ‖Du‖ * ‖D2phi‖ + ‖D2u‖ * ‖Dphi‖ ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound₂
  · positivity
  intro a b
  simp only [c2PullbackHessian, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply]
  have hfirst : ‖Du (D2phi a b)‖ ≤
      ‖Du‖ * (‖D2phi‖ * ‖a‖ * ‖b‖) := by
    calc
      ‖Du (D2phi a b)‖ ≤ ‖Du‖ * ‖D2phi a b‖ := Du.le_opNorm _
      _ ≤ ‖Du‖ * (‖D2phi‖ * ‖a‖ * ‖b‖) :=
        mul_le_mul_of_nonneg_left (D2phi.le_opNorm₂ a b) (norm_nonneg Du)
  have hsecond : ‖D2u (Dphi a) (Dphi b)‖ ≤
      ‖D2u‖ * (‖Dphi‖ * ‖a‖) * (‖Dphi‖ * ‖b‖) := by
    calc
      ‖D2u (Dphi a) (Dphi b)‖ ≤
          ‖D2u‖ * ‖Dphi a‖ * ‖Dphi b‖ :=
        D2u.le_opNorm₂ (Dphi a) (Dphi b)
      _ ≤ ‖D2u‖ * (‖Dphi‖ * ‖a‖) * (‖Dphi‖ * ‖b‖) := by
        gcongr
        · exact Dphi.le_opNorm a
        · exact Dphi.le_opNorm b
  calc
    ‖Du (D2phi a b) + D2u (Dphi a) (Dphi b)‖ ≤
        ‖Du (D2phi a b)‖ + ‖D2u (Dphi a) (Dphi b)‖ :=
      norm_add_le _ _
    _ ≤ ‖Du‖ * (‖D2phi‖ * ‖a‖ * ‖b‖) +
        (‖D2u‖ * (‖Dphi‖ * ‖a‖) * (‖Dphi‖ * ‖b‖)) :=
      add_le_add hfirst hsecond
    _ = (‖Du‖ * ‖D2phi‖ + ‖D2u‖ * ‖Dphi‖ ^ 2) *
        ‖a‖ * ‖b‖ := by ring

theorem hessianCurryEquiv_iteratedFDeriv_two_comp
    {f : W → F} {phi : V → W} {x : V}
    (hf : ContDiffAt Real 2 f (phi x))
    (hphi : ContDiffAt Real 2 phi x) :
    hessianCurryEquiv V F (iteratedFDeriv Real 2 (f ∘ phi) x) =
      c2PullbackHessian (fderiv Real phi x)
        (hessianCurryEquiv V W (iteratedFDeriv Real 2 phi x))
        (fderiv Real f (phi x))
        (hessianCurryEquiv W F (iteratedFDeriv Real 2 f (phi x))) := by
  rw [hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv]
  have hfdiff : DifferentiableAt Real (fderiv Real f) (phi x) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hphidiff : DifferentiableAt Real phi x :=
    hphi.differentiableAt (by norm_num)
  have hDphidiff : DifferentiableAt Real (fderiv Real phi) x :=
    (hphi.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcompdiff : DifferentiableAt Real
      (fun y => fderiv Real f (phi y)) x :=
    hfdiff.comp x hphidiff
  have hphieventually : ∀ᶠ y in nhds x, ContDiffAt Real 2 phi y :=
    hphi.eventually (by norm_num)
  have hfeventually : ∀ᶠ y in nhds x, ContDiffAt Real 2 f (phi y) :=
    hphi.continuousAt (hf.eventually (by norm_num))
  have hfirst : fderiv Real (f ∘ phi) =ᶠ[nhds x]
      fun y => (fderiv Real f (phi y)).comp (fderiv Real phi y) := by
    filter_upwards [hphieventually, hfeventually] with y hyphi hyf
    exact fderiv_comp y (hyf.differentiableAt (by norm_num))
      (hyphi.differentiableAt (by norm_num))
  rw [hfirst.fderiv_eq, fderiv_clm_comp hcompdiff hDphidiff]
  unfold c2PullbackHessian
  rw [hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv,
    hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv]
  have hchain : fderiv Real (fun y => fderiv Real f (phi y)) x =
      (fderiv Real (fderiv Real f) (phi x)).comp
        (fderiv Real phi x) := by
    simpa only [Function.comp_apply] using
      fderiv_comp x hfdiff hphidiff
  rw [hchain]

end DifferentialGeometry.Analysis.Schauder
