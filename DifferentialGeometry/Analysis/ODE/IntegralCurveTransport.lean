import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open MeasureTheory
open scoped Manifold Topology

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H}

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_f_comp_integralCurve [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hdf : ∀ x, (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) (t : ℝ) :
    HasDerivAt (f ∘ γ) (-1) t := by
  have hγmd : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t := (hγ t).mdifferentiableAt
  have hfmd : MDifferentiableAt I 𝓘(ℝ, ℝ) f (γ t) :=
    (hf (γ t)).mdifferentiableAt (by norm_num : (⊤ : WithTop ℕ∞) ≠ 0)
  have hγder : mfderiv 𝓘(ℝ, ℝ) I γ t = (1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)) :=
    (hγ t).mfderiv
  have hcomp := mfderiv_comp (x := t) (g := f) (f := γ) (hg := hfmd) (hf := hγmd)
  have hD : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ γ) t =
      (mfderiv I 𝓘(ℝ, ℝ) f (γ t)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t))) := by
    rw [hcomp, hγder]
  have hf' : HasMFDerivAt I 𝓘(ℝ, ℝ) f (γ t) (mfderiv I 𝓘(ℝ, ℝ) f (γ t)) :=
    MDifferentiableAt.hasMFDerivAt hfmd
  have hfd' : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ γ) t
      ((mfderiv I 𝓘(ℝ, ℝ) f (γ t)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)))) :=
    HasMFDerivAt.comp t (g := f) (f := γ) (hg := hf') (hf := hγ t)
  have hfd'' : HasFDerivAt (f ∘ γ)
      ((mfderiv I 𝓘(ℝ, ℝ) f (γ t)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)))) t :=
    (hasMFDerivAt_iff_hasFDerivAt.mp hfd')
  have hfd : HasFDerivAt (f ∘ γ) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ γ) t) t := by
    rw [hD]
    exact hfd''
  have hcomposed1 : ((mfderiv I 𝓘(ℝ, ℝ) f (γ t)).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)))) (1 : ℝ) = (-1 : ℝ) := by
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    simpa using hdf (γ t)
  have hD1v : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ γ) t) (1 : ℝ) = (-1 : ℝ) := by
    have hh := congrArg (fun L : (TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) ((f ∘ γ) t)) =>
      L (1 : ℝ)) hD.symm
    exact (hh.symm.trans hcomposed1)
  have hDlsmul : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ γ) t =
      (ContinuousLinearMap.toSpanSingleton ℝ (-1) : ℝ →L[ℝ] ℝ) := by
    apply ContinuousLinearMap.ext
    intro (r : ℝ)
    have hlin : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ γ) t) r =
        r • (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ γ) t) (1 : ℝ) := by
      rw [← map_smul]
      congr 1
      simp [smul_eq_mul]
    calc
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ γ) t) r
          = r • (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ γ) t) (1 : ℝ) := hlin
      _ = r • (-1 : ℝ) := by rw [hD1v]
      _ = (ContinuousLinearMap.toSpanSingleton ℝ (-1) : ℝ →L[ℝ] ℝ) r := by
        simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  rw [hasDerivAt_iff_hasFDerivAt]
  rwa [← hDlsmul]

set_option backward.isDefEq.respectTransparency false in
theorem f_eq_sub_of_integralCurve [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hdf : ∀ x, (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) (t : ℝ) :
    f (γ t) = f (γ 0) - t := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) t, HasDerivAt (f ∘ γ) (-1) x := fun x hx =>
    hasDerivAt_f_comp_integralCurve f hf v hdf hγ x
  have hint : IntervalIntegrable (fun _ : ℝ => (-1 : ℝ)) volume (0 : ℝ) t :=
    intervalIntegrable_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := f ∘ γ)
    (f' := fun _ : ℝ => (-1 : ℝ)) hderiv hint
  have hconst : (∫ x in (0 : ℝ)..t, (-1 : ℝ)) = (0 : ℝ) - t := by
    simp
  rw [hconst] at hftc
  calc
    f (γ t) = f (γ 0) + (f (γ t) - f (γ 0)) := by ring
    _ = f (γ 0) - t := by
      have h2 : f (γ t) - f (γ 0) = (0 : ℝ) - t := hftc.symm
      rw [h2]
      ring

theorem integralCurve_eq_of_agree [IsManifold I (⊤ : WithTop ℕ∞) M] [BoundarylessManifold I M]
    [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : CMDiff 1 (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    {γ γ' : ℝ → M} (hγ : IsMIntegralCurve γ v) (hγ' : IsMIntegralCurve γ' v)
    {t₀ : ℝ} (h : γ t₀ = γ' t₀) : γ = γ' :=
  isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hv hγ hγ' h

theorem integralCurve_eq_of_agree_zero [IsManifold I (⊤ : WithTop ℕ∞) M] [BoundarylessManifold I M]
    [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : CMDiff 1 (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    {γ γ' : ℝ → M} (hγ : IsMIntegralCurve γ v) (hγ' : IsMIntegralCurve γ' v)
    (h : γ 0 = γ' 0) : γ = γ' :=
  integralCurve_eq_of_agree v hv hγ hγ' h

end DifferentialGeometry.Analysis.ODE
