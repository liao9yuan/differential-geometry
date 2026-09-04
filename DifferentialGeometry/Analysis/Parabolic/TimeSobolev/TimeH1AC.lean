import DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1

set_option autoImplicit false

/-!
# Absolutely continuous representatives in time H1

This file realizes a finite-dimensional absolutely continuous curve whose
ordinary derivative is square integrable as a `timeH1` curve.  It is the
low-level bridge needed before manifold curves can enter the existing chart
`timeH1` density machinery.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped Interval Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace Real X]
  [FiniteDimensional Real X]

private theorem int_deriv_eq_sub
    {f : Real → X} {a b : Real}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hderiv : IntervalIntegrable (_root_.deriv f) volume a b) :
    ∫ t in a..b, _root_.deriv f t = f b - f a := by
  let A := (Module.Basis.ofVectorSpace Real X).equivFun.toContinuousLinearEquiv
  apply A.injective
  ext i
  let L : X →L[Real] Real :=
    LinearMap.toContinuousLinearMap ((LinearMap.proj i).comp A.toLinearMap)
  have hLac : AbsolutelyContinuousOnInterval (L ∘ f) a b :=
    AbsolutelyContinuousOnInterval.comp_lipschitzOn
      L.lipschitz.lipschitzOnWith hf (mapsTo_univ f (uIcc a b))
  have hdiff : ∀ᵐ t, t ∈ uIcc a b → DifferentiableAt Real f t :=
    hf.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  have hcomp : (fun t ↦ _root_.deriv (L ∘ f) t) =ᵐ[volume.restrict (Ι a b)]
      fun t ↦ L (_root_.deriv f t) := by
    change ∀ᵐ t ∂volume.restrict (Ι a b),
      _root_.deriv (L ∘ f) t = L (_root_.deriv f t)
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hdiff] with t ht htab
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      ((L.hasFDerivAt.comp t
        (ht (uIoc_subset_uIcc htab)).hasDerivAt.hasFDerivAt).hasDerivAt).deriv
  change L (∫ t in a..b, _root_.deriv f t) = L (f b - f a)
  calc
    L (∫ t in a..b, _root_.deriv f t) =
        ∫ t in a..b, L (_root_.deriv f t) :=
      (L.intervalIntegral_comp_comm hderiv).symm
    _ = ∫ t in a..b, _root_.deriv (L ∘ f) t :=
      intervalIntegral.integral_congr_ae_restrict hcomp.symm
    _ = L (f b) - L (f a) := by
      simpa only [Function.comp_apply] using hLac.integral_deriv_eq_sub
    _ = L (f b - f a) := (L.map_sub _ _).symm

namespace timeH1

/-- A finite-dimensional absolutely continuous curve with square-integrable
ordinary derivative has a time-`H1` realization with the same continuous
representative and weak derivative. -/
theorem exists_ofAC {T : Real} (hT : 0 ≤ T) (f : Real → X)
    (hf : AbsolutelyContinuousOnInterval f 0 T)
    (hderiv : MemLp (_root_.deriv f) 2 (timeMeasure T)) :
    ∃ u : timeH1 X T,
      EqOn u.toFun f (Icc (0 : Real) T) ∧
        u.deriv =ᵐ[timeMeasure T] _root_.deriv f := by
  let u : timeH1 X T := mk (f 0) (hderiv.toLp (_root_.deriv f))
  have huDeriv : u.deriv =ᵐ[timeMeasure T] _root_.deriv f :=
    hderiv.coeFn_toLp
  refine ⟨u, ?_, huDeriv⟩
  intro t ht
  have hInt : IntervalIntegrable (_root_.deriv f) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
    simpa only [timeMeasure] using hderiv.integrable (by norm_num)
  have hsub : Ι (0 : Real) t ⊆ Icc (0 : Real) T := by
    rw [uIoc_of_le ht.1]
    exact Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht.2)
  have hae : (fun s ↦ u.deriv s) =ᵐ[volume.restrict (Ι 0 t)]
      _root_.deriv f := by
    exact ae_mono (Measure.restrict_mono hsub le_rfl) (by
      simpa only [timeMeasure] using huDeriv)
  have hIntSub : IntervalIntegrable (_root_.deriv f) volume 0 t :=
    hInt.mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl ht.2)
  rw [toFun_apply, show u.init = f 0 by rfl,
    intervalIntegral.integral_congr_ae_restrict hae]
  have hft : AbsolutelyContinuousOnInterval f 0 t :=
    hf.mono (by
      rw [uIcc_of_le ht.1, uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl ht.2)
  rw [int_deriv_eq_sub hft hIntSub]
  abel

end timeH1

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
