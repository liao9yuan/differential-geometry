import DifferentialGeometry.Analysis.Schauder.C2Composition

noncomputable section

open Set
open scoped ContDiff ENNReal NNReal

namespace DifferentialGeometry.Analysis.Schauder

variable {V W F : Type*}
  [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup W] [NormedSpace Real W]
  [NormedAddCommGroup F] [NormedSpace Real F]

def parabolicSpatialPullback
    (phi : V → W) (u : Real → W → F) : Real → V → F :=
  fun t x => u t (phi x)

omit [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup W] [NormedSpace Real W]
  [NormedAddCommGroup F] [NormedSpace Real F] in
@[simp]
theorem parabolicSpatialPullback_apply
    (phi : V → W) (u : Real → W → F) (t : Real) (x : V) :
    parabolicSpatialPullback phi u t x = u t (phi x) :=
  rfl

theorem isParabolicC2On_parabolicSpatialPullback
    {Q : Set (ParabolicPoint V)} {R : Set (ParabolicPoint W)}
    {phi : V → W} {u : Real → W → F}
    (hQR : MapsTo (parabolicMap phi) Q R)
    (hphi : ∀ p ∈ Q, ContDiffAt Real 2 phi p.space)
    (hu : IsParabolicC2On R u) :
    IsParabolicC2On Q (parabolicSpatialPullback phi u) := by
  constructor
  · intro p hp
    exact (hu.1 (parabolicMap phi p) (hQR hp)).comp p.space (hphi p hp)
  · intro p hp
    simpa only [parabolicSpatialPullback_apply] using
      hu.2 (parabolicMap phi p) (hQR hp)

omit [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup W] [NormedSpace Real W] in
@[simp]
theorem parabolicTimeDerivative_parabolicSpatialPullback
    (phi : V → W) (u : Real → W → F) (p : ParabolicPoint V) :
    parabolicTimeDerivative (parabolicSpatialPullback phi u) p =
      parabolicTimeDerivative u (parabolicMap phi p) :=
  rfl

theorem continuousMultilinearCurryFin1_parabolicSpatialJet_one_parabolicSpatialPullback
    {phi : V → W} {u : Real → W → F} {p : ParabolicPoint V}
    (hu : DifferentiableAt Real (u p.time) (phi p.space))
    (hphi : DifferentiableAt Real phi p.space) :
    continuousMultilinearCurryFin1 Real V F
        (parabolicSpatialJet 1 (parabolicSpatialPullback phi u) p) =
      c1PullbackGradient
        (fderiv Real phi p.space)
        (continuousMultilinearCurryFin1 Real W F
          (parabolicSpatialJet 1 u (parabolicMap phi p))) := by
  change continuousMultilinearCurryFin1 Real V F
      (iteratedFDeriv Real 1 (u p.time ∘ phi) p.space) =
    c1PullbackGradient (fderiv Real phi p.space)
      (continuousMultilinearCurryFin1 Real W F
        (iteratedFDeriv Real 1 (u p.time) (phi p.space)))
  rw [continuousMultilinearCurryFin1_iteratedFDeriv_one_eq_fderiv
    (f := u p.time) (x := phi p.space)]
  exact continuousMultilinearCurryFin1_iteratedFDeriv_one_comp hu hphi

theorem hessianCurryEquiv_parabolicSpatialJet_two_parabolicSpatialPullback
    {phi : V → W} {u : Real → W → F} {p : ParabolicPoint V}
    (hu : ContDiffAt Real 2 (u p.time) (phi p.space))
    (hphi : ContDiffAt Real 2 phi p.space) :
    hessianCurryEquiv V F
        (parabolicSpatialJet 2 (parabolicSpatialPullback phi u) p) =
      c2PullbackHessian
        (fderiv Real phi p.space)
        (hessianCurryEquiv V W (iteratedFDeriv Real 2 phi p.space))
        (continuousMultilinearCurryFin1 Real W F
          (parabolicSpatialJet 1 u (parabolicMap phi p)))
        (hessianCurryEquiv W F
          (parabolicSpatialJet 2 u (parabolicMap phi p))) := by
  change hessianCurryEquiv V F
      (iteratedFDeriv Real 2 (u p.time ∘ phi) p.space) =
    c2PullbackHessian
      (fderiv Real phi p.space)
      (hessianCurryEquiv V W (iteratedFDeriv Real 2 phi p.space))
      (continuousMultilinearCurryFin1 Real W F
        (iteratedFDeriv Real 1 (u p.time) (phi p.space)))
      (hessianCurryEquiv W F
        (iteratedFDeriv Real 2 (u p.time) (phi p.space)))
  rw [continuousMultilinearCurryFin1_iteratedFDeriv_one_eq_fderiv
    (f := u p.time) (x := phi p.space)]
  exact hessianCurryEquiv_iteratedFDeriv_two_comp hu hphi

theorem holderWith_continuousMultilinearCurryFin1_parabolicSpatialJet_one
    {R : Set (ParabolicPoint W)} {u : Real → W → F}
    {K alpha : NNReal}
    (h : HolderWith K alpha (R.restrict (parabolicSpatialJet 1 u))) :
    HolderWith K alpha
      (R.restrict (fun p => continuousMultilinearCurryFin1 Real W F
        (parabolicSpatialJet 1 u p))) := by
  have hcomp :=
    (continuousMultilinearCurryFin1 Real W F).lipschitz.holderWith.comp h
  simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul,
    Function.comp_apply, Set.restrict_apply] using hcomp

theorem holderWith_hessianCurryEquiv_parabolicSpatialJet_two
    {R : Set (ParabolicPoint W)} {u : Real → W → F}
    {K alpha : NNReal}
    (h : HolderWith K alpha (R.restrict (parabolicSpatialJet 2 u))) :
    HolderWith K alpha
      (R.restrict (fun p => hessianCurryEquiv W F
        (parabolicSpatialJet 2 u p))) := by
  have hcomp := (hessianCurryEquiv W F).lipschitz.holderWith.comp h
  simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul,
    Function.comp_apply, Set.restrict_apply] using hcomp

def parabolicSpatialPullbackGaugeConst
    (alpha L C K1 K2 M1 M2 : NNReal) : NNReal :=
  C + C * M1 + (C * M2 + C * M1 ^ 2) + C +
    c2PullbackHessianHolderConst K1 K2
      (C * L ^ (alpha : Real)) (C * L ^ (alpha : Real))
      M1 M2 C C +
    C * L ^ (alpha : Real)

def parabolicSpatialPullbackGaugeWithLowerJetsConst
    (alpha L C K1 K2 M1 M2 : NNReal) : NNReal :=
  parabolicSpatialPullbackGaugeConst alpha L C K1 K2 M1 M2 +
    C * L ^ (alpha : Real) +
    c1PullbackGradientHolderConst K1 (C * L ^ (alpha : Real)) M1 C

theorem eParabolicC2HolderGaugeWithLowerJetsOn_parabolicSpatialPullback_le
    {Q : Set (ParabolicPoint V)} {R : Set (ParabolicPoint W)}
    {phi : V → W} {u : Real → W → F}
    {alpha L C K1 K2 M1 M2 : NNReal}
    (hQR : MapsTo (parabolicMap phi) Q R)
    (hmapLip : LipschitzWith L
      (fun p : Q => (⟨parabolicMap phi p.1, hQR p.2⟩ : R)))
    (hphi : ∀ p ∈ Q, ContDiffAt Real 2 phi p.space)
    (hDphiHolder : HolderWith K1 alpha
      (Q.restrict (fun p => fderiv Real phi p.space)))
    (hD2phiHolder : HolderWith K2 alpha
      (Q.restrict (fun p => hessianCurryEquiv V W
        (iteratedFDeriv Real 2 phi p.space))))
    (hDphiNorm : ∀ p ∈ Q, ‖fderiv Real phi p.space‖ ≤ M1)
    (hD2phiNorm : ∀ p ∈ Q,
      ‖hessianCurryEquiv V W (iteratedFDeriv Real 2 phi p.space)‖ ≤ M2)
    (hu : IsParabolicC2On R u)
    (hsource : eParabolicC2HolderGaugeWithLowerJetsOn alpha R u ≤ C) :
    eParabolicC2HolderGaugeWithLowerJetsOn alpha Q
        (parabolicSpatialPullback phi u) ≤
      parabolicSpatialPullbackGaugeWithLowerJetsConst
        alpha L C K1 K2 M1 M2 := by
  let w := parabolicSpatialPullback phi u
  have hbase : eParabolicC2HolderGaugeOn alpha R u ≤ C :=
    (eParabolicC2HolderGaugeOn_le_with_lower_jets alpha R u).trans hsource
  have hDuR : HolderWith C alpha
      (R.restrict (fun p => continuousMultilinearCurryFin1 Real W F
        (parabolicSpatialJet 1 u p))) :=
    holderWith_continuousMultilinearCurryFin1_parabolicSpatialJet_one
      (parabolicSpatialGradient_holderWith_restrict_of_lower_jets hsource)
  have hD2uR : HolderWith C alpha
      (R.restrict (fun p => hessianCurryEquiv W F
        (parabolicSpatialJet 2 u p))) :=
    holderWith_hessianCurryEquiv_parabolicSpatialJet_two
      (parabolicSpatialJet_holderWith_restrict hbase)
  have hDuQ : HolderWith (C * L ^ (alpha : Real)) alpha
      (fun p : Q => continuousMultilinearCurryFin1 Real W F
        (parabolicSpatialJet 1 u (parabolicMap phi p.1))) := by
    simpa only [Function.comp_apply, Set.restrict_apply, mul_one] using
      hDuR.comp hmapLip.holderWith
  have hD2uQ : HolderWith (C * L ^ (alpha : Real)) alpha
      (fun p : Q => hessianCurryEquiv W F
        (parabolicSpatialJet 2 u (parabolicMap phi p.1))) := by
    simpa only [Function.comp_apply, Set.restrict_apply, mul_one] using
      hD2uR.comp hmapLip.holderWith
  have hDuNorm : ∀ p : Q,
      ‖continuousMultilinearCurryFin1 Real W F
        (parabolicSpatialJet 1 u (parabolicMap phi p.1))‖ ≤ C := by
    intro p
    rw [(continuousMultilinearCurryFin1 Real W F).norm_map]
    exact parabolicSpatialJet_norm_le hbase (by norm_num) (hQR p.2)
  have hD2uNorm : ∀ p : Q,
      ‖hessianCurryEquiv W F
        (parabolicSpatialJet 2 u (parabolicMap phi p.1))‖ ≤ C := by
    intro p
    rw [(hessianCurryEquiv W F).norm_map]
    exact parabolicSpatialJet_norm_le hbase (by norm_num) (hQR p.2)
  have hgradientCurry : HolderWith
      (c1PullbackGradientHolderConst K1
        (C * L ^ (alpha : Real)) M1 C) alpha
      (fun p : Q => c1PullbackGradient
        (fderiv Real phi p.1.space)
        (continuousMultilinearCurryFin1 Real W F
          (parabolicSpatialJet 1 u (parabolicMap phi p.1)))) := by
    exact holderWith_c1PullbackGradient hDphiHolder hDuQ
      (fun p => hDphiNorm p.1 p.2) hDuNorm
  have hhessianCurry : HolderWith
      (c2PullbackHessianHolderConst K1 K2
        (C * L ^ (alpha : Real)) (C * L ^ (alpha : Real))
        M1 M2 C C) alpha
      (fun p : Q => c2PullbackHessian
        (fderiv Real phi p.1.space)
        (hessianCurryEquiv V W
          (iteratedFDeriv Real 2 phi p.1.space))
        (continuousMultilinearCurryFin1 Real W F
          (parabolicSpatialJet 1 u (parabolicMap phi p.1)))
        (hessianCurryEquiv W F
          (parabolicSpatialJet 2 u (parabolicMap phi p.1)))) := by
    exact holderWith_c2PullbackHessian hDphiHolder hD2phiHolder
      hDuQ hD2uQ (fun p => hDphiNorm p.1 p.2)
      (fun p => hD2phiNorm p.1 p.2) hDuNorm hD2uNorm
  have hgradient : HolderWith
      (c1PullbackGradientHolderConst K1
        (C * L ^ (alpha : Real)) M1 C) alpha
      (Q.restrict (parabolicSpatialJet 1 w)) := by
    have hcomp :=
      (continuousMultilinearCurryFin1 Real V F).symm.lipschitz.holderWith.comp
        hgradientCurry
    have hcomp' : HolderWith
        (c1PullbackGradientHolderConst K1
          (C * L ^ (alpha : Real)) M1 C) alpha
        ((continuousMultilinearCurryFin1 Real V F).symm ∘
          fun p : Q => c1PullbackGradient
            (fderiv Real phi p.1.space)
            (continuousMultilinearCurryFin1 Real W F
              (parabolicSpatialJet 1 u (parabolicMap phi p.1)))) := by
      simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul] using hcomp
    convert hcomp' using 1
    funext p
    apply (continuousMultilinearCurryFin1 Real V F).injective
    simp only [Function.comp_apply, Set.restrict_apply,
      LinearIsometryEquiv.apply_symm_apply]
    exact
      continuousMultilinearCurryFin1_parabolicSpatialJet_one_parabolicSpatialPullback
        ((hu.1 (parabolicMap phi p.1) (hQR p.2)).differentiableAt
          (by norm_num))
        ((hphi p.1 p.2).differentiableAt (by norm_num))
  have hhessian : HolderWith
      (c2PullbackHessianHolderConst K1 K2
        (C * L ^ (alpha : Real)) (C * L ^ (alpha : Real))
        M1 M2 C C) alpha
      (Q.restrict (parabolicSpatialJet 2 w)) := by
    have hcomp := (hessianCurryEquiv V F).symm.lipschitz.holderWith.comp
      hhessianCurry
    have hcomp' : HolderWith
        (c2PullbackHessianHolderConst K1 K2
          (C * L ^ (alpha : Real)) (C * L ^ (alpha : Real))
          M1 M2 C C) alpha
        ((hessianCurryEquiv V F).symm ∘
          fun p : Q => c2PullbackHessian
            (fderiv Real phi p.1.space)
            (hessianCurryEquiv V W
              (iteratedFDeriv Real 2 phi p.1.space))
            (continuousMultilinearCurryFin1 Real W F
              (parabolicSpatialJet 1 u (parabolicMap phi p.1)))
            (hessianCurryEquiv W F
              (parabolicSpatialJet 2 u (parabolicMap phi p.1)))) := by
      simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul] using hcomp
    convert hcomp' using 1
    funext p
    apply (hessianCurryEquiv V F).injective
    simp only [Function.comp_apply, Set.restrict_apply,
      LinearIsometryEquiv.apply_symm_apply]
    exact hessianCurryEquiv_parabolicSpatialJet_two_parabolicSpatialPullback
      (hu.1 (parabolicMap phi p.1) (hQR p.2)) (hphi p.1 p.2)
  have hvalue : HolderWith (C * L ^ (alpha : Real)) alpha
      (Q.restrict (fun p => w p.time p.space)) := by
    simpa only [w, parabolicSpatialPullback_apply, Function.comp_apply,
      Set.restrict_apply, mul_one] using
      (parabolicValue_holderWith_restrict_of_lower_jets hsource).comp
        hmapLip.holderWith
  have htimeHolder : HolderWith (C * L ^ (alpha : Real)) alpha
      (Q.restrict (parabolicTimeDerivative w)) := by
    simpa only [w, parabolicTimeDerivative_parabolicSpatialPullback,
      Function.comp_apply, Set.restrict_apply, mul_one] using
      (parabolicTimeDerivative_holderWith_restrict hbase).comp
        hmapLip.holderWith
  let Cspatial : Nat → NNReal := fun j => match j with
    | 0 => C
    | 1 => C * M1
    | 2 => C * M2 + C * M1 ^ 2
    | _ => 0
  have hspatial : ∀ j < 3, ∀ p ∈ Q,
      ‖parabolicSpatialJet j w p‖ ≤ Cspatial j := by
    intro j hj p hp
    interval_cases j
    · dsimp only [Cspatial]
      unfold parabolicSpatialJet w parabolicSpatialPullback
      rw [norm_iteratedFDeriv_zero]
      simpa only [parabolicSpatialJet, parabolicMap_time,
        parabolicMap_space, norm_iteratedFDeriv_zero] using
        parabolicSpatialJet_norm_le (j := 0) hbase (by norm_num) (hQR hp)
    · dsimp only [Cspatial]
      rw [← (continuousMultilinearCurryFin1 Real V F).norm_map,
        continuousMultilinearCurryFin1_parabolicSpatialJet_one_parabolicSpatialPullback
          ((hu.1 (parabolicMap phi p) (hQR hp)).differentiableAt
            (by norm_num))
          ((hphi p hp).differentiableAt (by norm_num))]
      exact (norm_c1PullbackGradient_le _ _).trans (by
        change _ ≤ (C : Real) * (M1 : Real)
        gcongr
        · exact hDuNorm ⟨p, hp⟩
        · exact hDphiNorm p hp)
    · dsimp only [Cspatial]
      rw [← (hessianCurryEquiv V F).norm_map,
        hessianCurryEquiv_parabolicSpatialJet_two_parabolicSpatialPullback
          (hu.1 (parabolicMap phi p) (hQR hp)) (hphi p hp)]
      exact (norm_c2PullbackHessian_le _ _ _ _).trans (by
        change _ ≤ (C : Real) * (M2 : Real) +
          (C : Real) * (M1 : Real) ^ 2
        gcongr
        · exact hDuNorm ⟨p, hp⟩
        · exact hD2phiNorm p hp
        · exact hD2uNorm ⟨p, hp⟩
        · exact hDphiNorm p hp)
  have htime : ∀ p ∈ Q, ‖parabolicTimeDerivative w p‖ ≤ C := by
    intro p hp
    dsimp only [w]
    rw [parabolicTimeDerivative_parabolicSpatialPullback]
    exact parabolicTimeDerivative_norm_le hbase (hQR hp)
  have hgaugeRaw := eParabolicC2HolderGaugeOn_le Cspatial C
    (c2PullbackHessianHolderConst K1 K2
      (C * L ^ (alpha : Real)) (C * L ^ (alpha : Real))
      M1 M2 C C)
    (C * L ^ (alpha : Real)) hspatial htime hhessian htimeHolder
  have hgauge : eParabolicC2HolderGaugeOn alpha Q w ≤
      parabolicSpatialPullbackGaugeConst alpha L C K1 K2 M1 M2 := by
    refine hgaugeRaw.trans_eq ?_
    unfold Cspatial parabolicSpatialPullbackGaugeConst
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    ring
  have hlower := eParabolicC2HolderGaugeWithLowerJetsOn_le
    (parabolicSpatialPullbackGaugeConst alpha L C K1 K2 M1 M2)
    (C * L ^ (alpha : Real))
    (c1PullbackGradientHolderConst K1
      (C * L ^ (alpha : Real)) M1 C)
    hgauge hvalue hgradient
  simpa only [w, parabolicSpatialPullbackGaugeWithLowerJetsConst] using hlower

theorem eParabolicC2HolderGaugeWithLowerJetsOn_parabolicSpatialPullback_le_of_lipschitzWith
    {Q : Set (ParabolicPoint V)} {R : Set (ParabolicPoint W)}
    {phi : V → W} {u : Real → W → F}
    {alpha L C K1 K2 M1 M2 : NNReal}
    (hL : 1 ≤ L)
    (hphiLip : LipschitzWith L phi)
    (hQR : MapsTo (parabolicMap phi) Q R)
    (hphi : ∀ p ∈ Q, ContDiffAt Real 2 phi p.space)
    (hDphiHolder : HolderWith K1 alpha
      (Q.restrict (fun p => fderiv Real phi p.space)))
    (hD2phiHolder : HolderWith K2 alpha
      (Q.restrict (fun p => hessianCurryEquiv V W
        (iteratedFDeriv Real 2 phi p.space))))
    (hDphiNorm : ∀ p ∈ Q, ‖fderiv Real phi p.space‖ ≤ M1)
    (hD2phiNorm : ∀ p ∈ Q,
      ‖hessianCurryEquiv V W (iteratedFDeriv Real 2 phi p.space)‖ ≤ M2)
    (hu : IsParabolicC2On R u)
    (hsource : eParabolicC2HolderGaugeWithLowerJetsOn alpha R u ≤ C) :
    eParabolicC2HolderGaugeWithLowerJetsOn alpha Q
        (parabolicSpatialPullback phi u) ≤
      parabolicSpatialPullbackGaugeWithLowerJetsConst
        alpha L C K1 K2 M1 M2 := by
  have hmapLip : LipschitzWith L
      (fun p : Q => (⟨parabolicMap phi p.1, hQR p.2⟩ : R)) := by
    exact LipschitzWith.subtype_mk
      ((lipschitzWith_parabolicMap hL hphiLip).restrict Q)
      (fun p => hQR p.2)
  exact eParabolicC2HolderGaugeWithLowerJetsOn_parabolicSpatialPullback_le
    hQR hmapLip hphi hDphiHolder hD2phiHolder hDphiNorm hD2phiNorm hu hsource

end DifferentialGeometry.Analysis.Schauder

end
