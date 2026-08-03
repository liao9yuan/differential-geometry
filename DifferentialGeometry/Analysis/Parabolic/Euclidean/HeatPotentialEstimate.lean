import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatPotentialTimeRealization

noncomputable section

open MeasureTheory Real Set
open scoped Interval NNReal RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

def heatPotentialSchauderConst
    (alpha K B Csource : NNReal) (T : Real) : ENNReal :=
  heatPotentialC2HolderGaugeConst (V := V) alpha K B Csource
    (Real.toNNReal (T * (B : Real)))
    (Real.toNNReal (2 * (B : Real) * heatC1 V * Real.sqrt T)) T

omit [CompleteSpace F] in
theorem heatDuhGradientMap_norm_le
    {t : Real} (ht : 0 < t) {B : NNReal}
    (f : Real → BoundedContinuousFunction V F)
    (hbound : ∀ s ∈ Icc (0 : Real) t, ‖f s‖ ≤ B)
    (x : V)
    (hmeas : AEStronglyMeasurable
      (fun s : Real => heatSupGradient (t - s) (f s) x)
      (volume.restrict (uIoc (0 : Real) t))) :
    ‖heatDuhGradientMap t f x‖ ≤
      2 * (B : Real) * heatC1 V * Real.sqrt t := by
  have hint := heatDuhGradient_int (V := V) ht f hbound x hmeas
  have hmajor := heatDuhGradientMajor_intble (V := V) ht B
  unfold heatDuhGradientMap
  calc
    ‖∫ s : Real in 0..t, heatSupGradient (t - s) (f s) x‖ ≤
        ∫ s : Real in 0..t, ‖heatSupGradient (t - s) (f s) x‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.le
    _ ≤ ∫ s : Real in 0..t, heatDuhGradientMajor (V := V) B t s := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo ht.le hint.norm hmajor
      intro s hs
      have hpos : 0 < t - s := sub_pos.mpr hs.2
      calc
        ‖heatSupGradient (t - s) (f s) x‖ ≤
            (heatScale (t - s))⁻¹ * heatC1 V * ‖f s‖ :=
          heatSupGradient_norm_le hpos (f s) x
        _ ≤ (heatScale (t - s))⁻¹ * heatC1 V * (B : Real) :=
          mul_le_mul_of_nonneg_left (hbound s ⟨hs.1.le, hs.2.le⟩)
            (mul_nonneg (inv_nonneg.mpr (heatScale_pos hpos).le)
              (heatC1_nonneg (V := V)))
        _ = heatDuhGradientMajor (V := V) B t s := by
          rw [← heatScale12_eq hpos]
          unfold heatDuhGradientMajor
          ring
    _ = 2 * (B : Real) * heatC1 V * Real.sqrt t := by
      unfold heatDuhGradientMajor
      rw [intervalIntegral.integral_const_mul, timeScale12_int ht,
        Real.sqrt_eq_rpow]
      ring

omit [CompleteSpace F] in
theorem heatDuh_fderiv_norm_le
    {t : Real} (ht : 0 < t) {B : NNReal}
    (f : Real → BoundedContinuousFunction V F)
    (hbound : ∀ s ∈ Icc (0 : Real) t, ‖f s‖ ≤ B)
    (hmeas0 : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatSup (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (hmeas1 : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatSupGradient (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (x : V) :
    ‖fderiv Real (heatDuh t f) x‖ ≤
      2 * (B : Real) * heatC1 V * Real.sqrt t := by
  rw [(heatDuh_hasFDerivAt ht f hbound hmeas0 hmeas1 x).fderiv]
  exact heatDuhGradientMap_norm_le ht f hbound x (hmeas1 x)

theorem heatDuh_schauder_estimate
    {alpha K B Csource : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (f : Real → BoundedContinuousFunction V F)
    (hbound : ∀ r ∈ Icc (0 : Real) S, ‖f r‖ ≤ B)
    (hf : ∀ r ∈ Icc (0 : Real) S, HolderWith K alpha (f r))
    (hsource : HolderWith Csource alpha
      ((parabolicCylinder (Ioc (0 : Real) S) Set.univ).restrict
        (fun p => f p.time p.space)))
    (hmeas0 : ∀ t ∈ Ioc (0 : Real) S, ∀ z : V,
      AEStronglyMeasurable
        (fun s : Real => heatSup (t - s) (f s) z)
        (volume.restrict (uIoc (0 : Real) t)))
    (hmeas1 : ∀ t ∈ Ioc (0 : Real) S, ∀ z : V,
      AEStronglyMeasurable
        (fun s : Real => heatSupGradient (t - s) (f s) z)
        (volume.restrict (uIoc (0 : Real) t)))
    (hmeas2 : ∀ t ∈ Ioc (0 : Real) S, ∀ z : V,
      AEStronglyMeasurable
        (fun s : Real => heatSupHessian (t - s) (f s) z)
        (volume.restrict (uIoc (0 : Real) t))) :
    eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ)
      (fun t x => heatDuh t f x) ≤
      heatPotentialSchauderConst (V := V) alpha K B Csource T := by
  apply eParabolicC2HolderGaugeOn_heatDuh_le_of_lower_jets
    halpha0 halpha1 hT hTS f
  · intro p hp
    unfold parabolicSpatialJet
    rw [norm_iteratedFDeriv_zero]
    have hbound' : ∀ s ∈ Icc (0 : Real) p.time, ‖f s‖ ≤ B := by
      intro s hs
      exact hbound s ⟨hs.1, hs.2.trans (hp.1.2.trans hTS.le)⟩
    have hraw := heatDuh_norm hp.1.1 f hbound' p.space
      (hmeas0 p.time ⟨hp.1.1, hp.1.2.trans hTS.le⟩ p.space)
    have hTB : 0 ≤ T * (B : Real) := mul_nonneg hT B.coe_nonneg
    rw [Real.coe_toNNReal _ hTB]
    exact hraw.trans
      (mul_le_mul_of_nonneg_right hp.1.2 B.coe_nonneg)
  · intro p hp
    unfold parabolicSpatialJet
    rw [norm_iteratedFDeriv_one]
    have hbound' : ∀ s ∈ Icc (0 : Real) p.time, ‖f s‖ ≤ B := by
      intro s hs
      exact hbound s ⟨hs.1, hs.2.trans (hp.1.2.trans hTS.le)⟩
    have hraw := heatDuh_fderiv_norm_le hp.1.1 f hbound'
      (hmeas0 p.time ⟨hp.1.1, hp.1.2.trans hTS.le⟩)
      (hmeas1 p.time ⟨hp.1.1, hp.1.2.trans hTS.le⟩) p.space
    have hcoef : 0 ≤ 2 * (B : Real) * heatC1 V :=
      mul_nonneg (mul_nonneg (by positivity) B.coe_nonneg)
        (heatC1_nonneg (V := V))
    have hC : 0 ≤ 2 * (B : Real) * heatC1 V * Real.sqrt T :=
      mul_nonneg hcoef (Real.sqrt_nonneg T)
    rw [Real.coe_toNNReal _ hC]
    exact hraw.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt hp.1.2) hcoef)
  · exact hbound
  · exact hf
  · exact hsource
  · exact hmeas0
  · exact hmeas1
  · exact hmeas2

theorem heatDuh_schauder_estimate_of_parabolic_holder
    {alpha K B : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (f : Real → BoundedContinuousFunction V F)
    (hbound : ∀ r ∈ Icc (0 : Real) S, ‖f r‖ ≤ B)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p => f p.time p.space)))
    (hmeas0 : ∀ t ∈ Ioc (0 : Real) S, ∀ z : V,
      AEStronglyMeasurable
        (fun s : Real => heatSup (t - s) (f s) z)
        (volume.restrict (uIoc (0 : Real) t)))
    (hmeas1 : ∀ t ∈ Ioc (0 : Real) S, ∀ z : V,
      AEStronglyMeasurable
        (fun s : Real => heatSupGradient (t - s) (f s) z)
        (volume.restrict (uIoc (0 : Real) t)))
    (hmeas2 : ∀ t ∈ Ioc (0 : Real) S, ∀ z : V,
      AEStronglyMeasurable
        (fun s : Real => heatSupHessian (t - s) (f s) z)
        (volume.restrict (uIoc (0 : Real) t))) :
    eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ)
      (fun t x => heatDuh t f x) ≤
      heatPotentialSchauderConst (V := V) alpha K B K T := by
  have hf : ∀ r ∈ Icc (0 : Real) S, HolderWith K alpha (f r) :=
    fun r hr => holderWith_slice_of_parabolicCylinder
      (f := fun s x => f s x) hsource hr
  have hsource' : HolderWith K alpha
      ((parabolicCylinder (Ioc (0 : Real) S) Set.univ).restrict
        (fun p => f p.time p.space)) := by
    rw [HolderWith.restrict_iff] at hsource ⊢
    exact hsource.mono fun p hp => ⟨⟨hp.1.1.le, hp.1.2⟩, hp.2⟩
  exact heatDuh_schauder_estimate halpha0 halpha1 hT hTS f hbound hf
    hsource' hmeas0 hmeas1 hmeas2

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
