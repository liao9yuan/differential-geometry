import DifferentialGeometry.Analysis.Parabolic.Euclidean.CutoffClassicalSchauder
import DifferentialGeometry.Analysis.Schauder.ParabolicBallCutoff

noncomputable section

open Matrix Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

def parabolicBallInteriorSchauderConst
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (alpha : NNReal) (aTime t₀ t₁ bTime r R : Real)
    (Ksource Kcomm Bsource Bcomm X : NNReal)
    (Ka omega : n → n → NNReal) (T : Real) : NNReal :=
  spdHeatPotentialSchauderConst (fun i j ↦ a i j p0) hA alpha
    (parabolicCutoffSourceHolderConst
        (parabolicBallCutoffHolderConst aTime t₀ t₁ bTime r R)
        Ksource Kcomm 1 Bsource +
      X * parabolicMatrixFreezeHolderConst Ka omega)
    (parabolicCutoffSourceSupConst 1 Bsource Bcomm +
      X * parabolicMatrixFreezeSupConst omega) T

def parabolicBallCutoffOperatorCommutatorSupConst
    (aTime t₀ t₁ bTime r R : Real) (A : n → n → NNReal)
    (Mdu Mu : NNReal) : NNReal :=
  parabolicCutoffOperatorCommutatorSupConst A
    (intervalCutoffDerivSupConst aTime t₀ t₁ bTime)
    (parabolicBallCutoffSpatialFDerivSupConst r R) Mdu
    (parabolicBallCutoffSpatialFDeriv2SupConst r R) Mu

def parabolicBallCutoffOperatorCommutatorHolderConst
    (aTime t₀ t₁ bTime : Real) (center : Euc n)
    {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (A Ka : n → n → NNReal) (Kdu Ku Mdu Mu : NNReal) : NNReal :=
  parabolicCutoffOperatorCommutatorHolderConst A Ka
    (parabolicBallCutoffTimeDerivativeHolderConst
      aTime t₀ t₁ bTime r R)
    (parabolicBallCutoffSpatialFDerivHolderConst
      aTime t₀ t₁ bTime r R)
    Kdu
    (parabolicBallCutoffSpatialFDeriv2HolderConst
      aTime t₀ t₁ bTime center hr hrR)
    Ku (intervalCutoffDerivSupConst aTime t₀ t₁ bTime)
    (parabolicBallCutoffSpatialFDerivSupConst r R) Mdu
    (parabolicBallCutoffSpatialFDeriv2SupConst r R) Mu

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem norm_parabolicBallCutoffOperatorCommutator_le
    {J : Set Real}
    (aTime t₀ t₁ bTime : Real) (hat₀ : aTime < t₀)
    (ht₀t₁ : t₀ ≤ t₁) (ht₁b : t₁ < bTime)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (A : n → n → NNReal) (Mdu Mu : NNReal)
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder J Set.univ → ‖a i j p‖ ≤ A i j)
    (hduNorm : ∀ p,
      p ∈ parabolicCylinder J Set.univ → ‖du p‖ ≤ Mdu)
    (huNorm : ∀ p,
      p ∈ parabolicCylinder J Set.univ → ‖u p.time p.space‖ ≤ Mu)
    (p : ParabolicPoint (Euc n))
    (hp : p ∈ parabolicCylinder J Set.univ) :
    ‖parabolicCutoffOperatorCommutator a
      (fun q ↦ parabolicBallCutoffTimeDerivative
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
          q.time q.space)
      (fun q ↦ parabolicBallCutoffSpatialFDeriv
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
          q.time q.space)
      (fun q ↦ parabolicBallCutoffSpatialFDeriv2
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
          q.time q.space)
      u du p‖ ≤
        parabolicBallCutoffOperatorCommutatorSupConst
          aTime t₀ t₁ bTime r R A Mdu Mu := by
  apply norm_parabolicCutoffOperatorCommutator_le
    a
    (fun q ↦ parabolicBallCutoffTimeDerivative
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space)
    (fun q ↦ parabolicBallCutoffSpatialFDeriv
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space)
    (fun q ↦ parabolicBallCutoffSpatialFDeriv2
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space)
    u du A (intervalCutoffDerivSupConst aTime t₀ t₁ bTime)
      (parabolicBallCutoffSpatialFDerivSupConst r R) Mdu
      (parabolicBallCutoffSpatialFDeriv2SupConst r R) Mu haNorm
  · intro q _hq
    exact norm_parabolicBallCutoffTimeDerivative_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  · intro q _hq
    exact norm_parabolicBallCutoffSpatialFDeriv_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  · exact hduNorm
  · intro q _hq
    exact norm_parabolicBallCutoffSpatialFDeriv2_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  · exact huNorm
  · exact hp

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem parabolicBallCutoffOperatorCommutator_holderWith_restrict
    {J : Set Real} {alpha Kdu Ku : NNReal}
    (halpha1 : alpha ≤ 1)
    (aTime t₀ t₁ bTime : Real) (hat₀ : aTime < t₀)
    (ht₀t₁ : t₀ ≤ t₁) (ht₁b : t₁ < bTime)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (A Ka : n → n → NNReal) (Mdu Mu : NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder J Set.univ).restrict (a i j)))
    (hdu : HolderWith Kdu alpha
      ((parabolicCylinder J Set.univ).restrict du))
    (hu : HolderWith Ku alpha
      ((parabolicCylinder J Set.univ).restrict
        (fun p ↦ u p.time p.space)))
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder J Set.univ → ‖a i j p‖ ≤ A i j)
    (hduNorm : ∀ p,
      p ∈ parabolicCylinder J Set.univ → ‖du p‖ ≤ Mdu)
    (huNorm : ∀ p,
      p ∈ parabolicCylinder J Set.univ → ‖u p.time p.space‖ ≤ Mu) :
    HolderWith
      (parabolicBallCutoffOperatorCommutatorHolderConst
        aTime t₀ t₁ bTime center hr hrR A Ka Kdu Ku Mdu Mu)
      alpha ((parabolicCylinder J Set.univ).restrict
        (parabolicCutoffOperatorCommutator a
          (fun q ↦ parabolicBallCutoffTimeDerivative
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          (fun q ↦ parabolicBallCutoffSpatialFDeriv
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          (fun q ↦ parabolicBallCutoffSpatialFDeriv2
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          u du)) := by
  apply parabolicCutoffOperatorCommutator_holderWith_restrict
    a
    (fun q ↦ parabolicBallCutoffTimeDerivative
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space)
    (fun q ↦ parabolicBallCutoffSpatialFDeriv
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space)
    (fun q ↦ parabolicBallCutoffSpatialFDeriv2
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space)
    u du A Ka (intervalCutoffDerivSupConst aTime t₀ t₁ bTime)
      (parabolicBallCutoffSpatialFDerivSupConst r R) Mdu
      (parabolicBallCutoffSpatialFDeriv2SupConst r R) Mu ha
  · exact parabolicBallCutoffTimeDerivative_holderWith_restrict
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR halpha1 J
  · exact parabolicBallCutoffSpatialFDeriv_holderWith_restrict
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR halpha1 J
  · exact hdu
  · exact parabolicBallCutoffSpatialFDeriv2_holderWith_restrict
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR halpha1 J
  · exact hu
  · exact haNorm
  · intro q _hq
    exact norm_parabolicBallCutoffTimeDerivative_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  · intro q _hq
    exact norm_parabolicBallCutoffSpatialFDeriv_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  · exact hduNorm
  · intro q _hq
    exact norm_parabolicBallCutoffSpatialFDeriv2_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  · exact huNorm

theorem parabolic_variable_coefficient_ball_interior_schauder_estimate_of_cutoff_source_estimates
    {alpha Ksource Kcomm Bsource Bcomm X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 ≤ aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (ht₁T : t₁ ≤ T)
    (hT : 0 ≤ T) (hTS : T < S)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicVariableMatrixOperator a (fun t x ↦ u t x))))
    (hcommHolder : HolderWith Kcomm alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicCutoffOperatorCommutator a
          (fun p ↦ parabolicBallCutoffTimeDerivative
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              p.time p.space)
          (fun p ↦ parabolicBallCutoffSpatialFDeriv
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              p.time p.space)
          (fun p ↦ parabolicBallCutoffSpatialFDeriv2
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              p.time p.space)
          (fun t x ↦ u t x) (fun p ↦ du p.time p.space))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicVariableMatrixOperator a (fun t x ↦ u t x) p‖ ≤ Bsource)
    (hcommNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicCutoffOperatorCommutator a
          (fun q ↦ parabolicBallCutoffTimeDerivative
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          (fun q ↦ parabolicBallCutoffSpatialFDeriv
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          (fun q ↦ parabolicBallCutoffSpatialFDeriv2
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          (fun t x ↦ u t x) (fun q ↦ du q.time q.space) p‖ ≤ Bcomm)
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hcutoffGauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (fun t x ↦ parabolicBallCutoff
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR t x •
          u t x) ≤ X) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r))
        (fun t x ↦ u t x) ≤
      parabolicBallInteriorSchauderConst a p0 hA alpha
        aTime t₀ t₁ bTime r R Ksource Kcomm Bsource Bcomm X
        Ka omega T := by
  let chi := parabolicBallCutoff
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
  let dtimeChi := parabolicBallCutoffTimeDerivative
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
  let dchi := parabolicBallCutoffSpatialFDeriv
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
  let d2chi := parabolicBallCutoffSpatialFDeriv2
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
  let Q := parabolicCylinder (Icc (0 : Real) S) (Set.univ : Set (Euc n))
  let U := parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r)
  let W : Real → Euc n → F := fun t x ↦ chi t x • u t x
  have hchiTime : ∀ s ∈ Icc (0 : Real) S,
      HasDerivAt chi (dtimeChi s) s := by
    intro s _hs
    exact parabolicBallCutoff_hasDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR s
  have hchi : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (chi s : Euc n → Real) (dchi s x) x := by
    intro s _hs x
    exact parabolicBallCutoff_hasFDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR s x
  have hdchi : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (dchi s : Euc n → Euc n →L[Real] Real)
        (d2chi s x) x := by
    intro s _hs x
    exact parabolicBallCutoffSpatialFDeriv_hasFDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR s x
  have hchiCont : Continuous chi := by
    rw [continuous_iff_continuousAt]
    intro s
    exact (parabolicBallCutoff_hasDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR s).continuousAt
  have hchi0 : chi 0 = 0 := by
    exact parabolicBallCutoff_eq_zero_of_time_not_mem
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        (fun hmem ↦ (not_lt_of_ge haTime) hmem.1)
  have hchiHolder : HolderWith
      (parabolicBallCutoffHolderConst aTime t₀ t₁ bTime r R) alpha
      (Q.restrict (fun p ↦ chi p.time p.space)) := by
    exact parabolicBallCutoff_holderWith_restrict
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        halpha1.le (Icc (0 : Real) S)
  have hchiNorm : ∀ p, p ∈ Q → ‖chi p.time p.space‖ ≤ (1 : NNReal) := by
    intro p _hp
    exact norm_parabolicBallCutoff_le_one
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        p.time p.space
  have hraw : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ) W ≤
        parabolicBallInteriorSchauderConst a p0 hA alpha
          aTime t₀ t₁ bTime r R Ksource Kcomm Bsource Bcomm X
          Ka omega T := by
    simpa only [Q, chi, dtimeChi, dchi, d2chi, W,
      parabolicBallInteriorSchauderConst] using
      (parabolic_variable_coefficient_schauder_estimate_of_cutoff_source_estimates
        halpha0 halpha1 hT hTS a p0 hA chi dtimeChi dchi d2chi
        u dtimeU du d2u hchiTime huTime hchi hdchi hu hdu hchiCont huCont
        hchi0 hchiHolder hsourceHolder hcommHolder hchiNorm hsourceNorm
        hcommNorm Ka omega ha homega hcutoffGauge)
  have hUOpen : IsOpen U :=
    isOpen_parabolicCylinder isOpen_Ioo Metric.isOpen_ball
  have hUOut : U ⊆ parabolicCylinder (Ioc (0 : Real) T) Set.univ := by
    intro p hp
    exact ⟨⟨lt_of_le_of_lt haTime (hat₀.trans hp.1.1),
      hp.1.2.le.trans ht₁T⟩, Set.mem_univ p.space⟩
  have heq : Set.EqOn (fun p ↦ u p.time p.space)
      (fun p ↦ W p.time p.space) U := by
    intro p hp
    change u p.time p.space = chi p.time p.space • u p.time p.space
    rw [show chi p.time p.space = 1 from
      parabolicBallCutoff_eq_one
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        ⟨hp.1.1.le, hp.1.2.le⟩ (Metric.ball_subset_closedBall hp.2), one_smul]
  calc
    eParabolicC2HolderGaugeOn alpha U (fun t x ↦ u t x) =
        eParabolicC2HolderGaugeOn alpha U W :=
      eParabolicC2HolderGaugeOn_congr_of_eqOn_open
        hUOpen Set.Subset.rfl heq alpha
    _ ≤ eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioc (0 : Real) T) Set.univ) W :=
      eParabolicC2HolderGaugeOn_mono hUOut alpha W
    _ ≤ parabolicBallInteriorSchauderConst a p0 hA alpha
        aTime t₀ t₁ bTime r R Ksource Kcomm Bsource Bcomm X
        Ka omega T := hraw

theorem parabolic_variable_coefficient_ball_interior_schauder_estimate_of_source_and_solution_estimates
    {alpha Ksource Kdu Ku Bsource Mdu Mu X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 ≤ aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (ht₁T : t₁ ≤ T)
    (hT : 0 ≤ T) (hTS : T < S)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicVariableMatrixOperator a (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicVariableMatrixOperator a (fun t x ↦ u t x) p‖ ≤ Bsource)
    (A Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p‖ ≤ A i j)
    (hduHolder : HolderWith Kdu alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ du p.time p.space)))
    (huHolder : HolderWith Ku alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ u p.time p.space)))
    (hduNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖du p.time p.space‖ ≤ Mdu)
    (huNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖u p.time p.space‖ ≤ Mu)
    (hcutoffGauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (fun t x ↦ parabolicBallCutoff
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR t x •
          u t x) ≤ X) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r))
        (fun t x ↦ u t x) ≤
      parabolicBallInteriorSchauderConst a p0 hA alpha
        aTime t₀ t₁ bTime r R Ksource
        (parabolicBallCutoffOperatorCommutatorHolderConst
          aTime t₀ t₁ bTime center hr hrR A Ka Kdu Ku Mdu Mu)
        Bsource
        (parabolicBallCutoffOperatorCommutatorSupConst
          aTime t₀ t₁ bTime r R A Mdu Mu)
        X Ka omega T := by
  let Q := parabolicCylinder (Icc (0 : Real) S) (Set.univ : Set (Euc n))
  let dtimeChi : ParabolicPoint (Euc n) → Real := fun q ↦
    parabolicBallCutoffTimeDerivative
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  let dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real := fun q ↦
    parabolicBallCutoffSpatialFDeriv
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  let d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real := fun q ↦
    parabolicBallCutoffSpatialFDeriv2
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  have hcommHolder : HolderWith
      (parabolicBallCutoffOperatorCommutatorHolderConst
        aTime t₀ t₁ bTime center hr hrR A Ka Kdu Ku Mdu Mu)
      alpha (Q.restrict
        (parabolicCutoffOperatorCommutator a dtimeChi dchi d2chi
          (fun t x ↦ u t x) (fun p ↦ du p.time p.space))) := by
    exact parabolicBallCutoffOperatorCommutator_holderWith_restrict
      halpha1.le aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
      a (fun t x ↦ u t x) (fun p ↦ du p.time p.space)
      A Ka Mdu Mu ha hduHolder huHolder haNorm hduNorm huNorm
  have hcommNorm : ∀ p, p ∈ Q →
      ‖parabolicCutoffOperatorCommutator a dtimeChi dchi d2chi
        (fun t x ↦ u t x) (fun q ↦ du q.time q.space) p‖ ≤
          parabolicBallCutoffOperatorCommutatorSupConst
            aTime t₀ t₁ bTime r R A Mdu Mu := by
    intro p hp
    exact norm_parabolicBallCutoffOperatorCommutator_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
      a (fun t x ↦ u t x) (fun q ↦ du q.time q.space)
      A Mdu Mu haNorm hduNorm huNorm p hp
  exact parabolic_variable_coefficient_ball_interior_schauder_estimate_of_cutoff_source_estimates
    halpha0 halpha1 haTime hat₀ ht₀t₁ ht₁b ht₁T hT hTS center hr hrR
    a p0 hA u dtimeU du d2u huTime hu hdu huCont hsourceHolder
    (by simpa only [Q, dtimeChi, dchi, d2chi] using hcommHolder)
    hsourceNorm (by simpa only [Q, dtimeChi, dchi, d2chi] using hcommNorm)
    Ka omega ha homega hcutoffGauge

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
