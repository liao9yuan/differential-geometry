import DifferentialGeometry.Analysis.Schauder.HolderNormedSpace
import Mathlib.Topology.ContinuousMap.Bounded.Normed

noncomputable section

open Set
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Schauder

section Map

variable {X F G : Type*} [MetricSpace X]
  [NormedAddCommGroup F] [NormedSpace Real F]
  [NormedAddCommGroup G] [NormedSpace Real G]

omit [MetricSpace X] in
theorem eSupNormOn_comp_continuousLinearMap_le
    (L : F →L[Real] G) (f : X → F) :
    eSupNormOn Set.univ (fun x ↦ L (f x)) ≤
      (‖L‖₊ : ENNReal) * eSupNormOn Set.univ f := by
  rw [eSupNormOn_le]
  intro x _hx
  calc
    ENNReal.ofReal ‖L (f x)‖ ≤ ENNReal.ofReal (‖L‖ * ‖f x‖) :=
      ENNReal.ofReal_le_ofReal (L.le_opNorm (f x))
    _ = (‖L‖₊ : ENNReal) * ENNReal.ofReal ‖f x‖ := by
      rw [ENNReal.ofReal_mul (norm_nonneg L), ofReal_norm_eq_enorm,
        enorm_eq_nnnorm]
    _ ≤ (‖L‖₊ : ENNReal) * eSupNormOn Set.univ f :=
      mul_le_mul_right
        (norm_le_eSupNormOn Set.univ f x (Set.mem_univ x)) _

theorem eHolderNorm_comp_continuousLinearMap_le
    {alpha : NNReal} (L : F →L[Real] G) {f : X → F}
    (hf : MemHolder alpha f) :
    eHolderNorm alpha (fun x ↦ L (f x)) ≤
      (‖L‖₊ : ENNReal) * eHolderNorm alpha f := by
  have hcomp := L.lipschitz.holderWith.comp hf.holderWith
  calc
    eHolderNorm alpha (fun x ↦ L (f x)) ≤
        ((‖L‖₊ * nnHolderNorm alpha f : NNReal) : ENNReal) := by
      simpa only [Function.comp_apply, NNReal.coe_one, NNReal.rpow_one,
        mul_one, one_mul] using hcomp.eHolderNorm_le
    _ = (‖L‖₊ : ENNReal) * (nnHolderNorm alpha f : ENNReal) := by
      rw [ENNReal.coe_mul]
    _ ≤ (‖L‖₊ : ENNReal) * eHolderNorm alpha f :=
      mul_le_mul_right coe_nnHolderNorm_le_eHolderNorm _

theorem eHolderGauge_comp_continuousLinearMap_le
    {alpha : NNReal} (L : F →L[Real] G) {f : X → F}
    (hf : IsBoundedHolder alpha f) :
    eHolderGauge alpha (fun x ↦ L (f x)) ≤
      (‖L‖₊ : ENNReal) * eHolderGauge alpha f := by
  unfold eHolderGauge
  calc
    eSupNormOn Set.univ (fun x ↦ L (f x)) +
        eHolderNorm alpha (fun x ↦ L (f x)) ≤
      (‖L‖₊ : ENNReal) * eSupNormOn Set.univ f +
        (‖L‖₊ : ENNReal) * eHolderNorm alpha f :=
      add_le_add (eSupNormOn_comp_continuousLinearMap_le L f)
        (eHolderNorm_comp_continuousLinearMap_le L hf.memHolder)
    _ = (‖L‖₊ : ENNReal) *
        (eSupNormOn Set.univ f + eHolderNorm alpha f) := by
      rw [mul_add]

private def boundedHolderSpaceMapLinearMap
    (alpha : NNReal) (L : F →L[Real] G) :
    BoundedHolderSpace (X := X) (F := F) alpha →ₗ[Real]
      BoundedHolderSpace (X := X) (F := G) alpha where
  toFun f := ⟨fun x ↦ L (f x), by
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top f.2)
      (eHolderGauge_comp_continuousLinearMap_le L f.2)⟩
  map_add' f g := by
    apply boundedHolderSpace_ext
    intro x
    exact L.map_add (f x) (g x)
  map_smul' c f := by
    apply boundedHolderSpace_ext
    intro x
    exact L.map_smul c (f x)

private theorem norm_boundedHolderSpaceMapLinearMap_le
    {alpha : NNReal} (L : F →L[Real] G)
    (f : BoundedHolderSpace (X := X) (F := F) alpha) :
    ‖boundedHolderSpaceMapLinearMap alpha L f‖ ≤ ‖L‖ * ‖f‖ := by
  rw [norm_boundedHolderSpace_eq, norm_boundedHolderSpace_eq]
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top f.2)
    (eHolderGauge_comp_continuousLinearMap_le L f.2)
  simpa only [ENNReal.toReal_mul, ofReal_norm_eq_enorm, enorm_eq_nnnorm]
    using hreal

def boundedHolderSpaceMap (alpha : NNReal) (L : F →L[Real] G) :
    BoundedHolderSpace (X := X) (F := F) alpha →L[Real]
      BoundedHolderSpace (X := X) (F := G) alpha :=
  LinearMap.mkContinuous (boundedHolderSpaceMapLinearMap alpha L) ‖L‖
    (norm_boundedHolderSpaceMapLinearMap_le L)

@[simp]
theorem boundedHolderSpaceMap_apply
    (alpha : NNReal) (L : F →L[Real] G)
    (f : BoundedHolderSpace (X := X) (F := F) alpha) (x : X) :
    boundedHolderSpaceMap alpha L f x = L (f x) :=
  rfl

theorem norm_boundedHolderSpaceMap_le
    (alpha : NNReal) (L : F →L[Real] G) :
    ‖boundedHolderSpaceMap (X := X) alpha L‖ ≤ ‖L‖ := by
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg L)
    (norm_boundedHolderSpaceMapLinearMap_le L)

end Map

section BoundedContinuousFunction

variable {X F : Type*} [MetricSpace X]
  [NormedAddCommGroup F] [NormedSpace Real F]

private def boundedHolderSpaceToBoundedContinuousFunctionLinearMap
    (alpha : NNReal) (halpha : 0 < alpha) :
    BoundedHolderSpace (X := X) (F := F) alpha →ₗ[Real]
      BoundedContinuousFunction X F where
  toFun f :=
    ⟨⟨boundedHolderSpaceFun f,
        (boundedHolderSpace_holderWith f).continuous halpha⟩,
      ⟨2 * ‖f‖, fun x y ↦ by
        rw [dist_eq_norm]
        exact (norm_sub_le (f x) (f y)).trans
          ((add_le_add (norm_boundedHolderSpace_apply_le f x)
            (norm_boundedHolderSpace_apply_le f y)).trans_eq (by ring))⟩⟩
  map_add' f g := by
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  map_smul' c f := by
    apply BoundedContinuousFunction.ext
    intro x
    rfl

private theorem norm_boundedHolderSpaceToBoundedContinuousFunctionLinearMap_le
    {alpha : NNReal} (halpha : 0 < alpha)
    (f : BoundedHolderSpace (X := X) (F := F) alpha) :
    ‖boundedHolderSpaceToBoundedContinuousFunctionLinearMap alpha halpha f‖ ≤
      ‖f‖ := by
  rw [BoundedContinuousFunction.norm_le (norm_nonneg f)]
  intro x
  exact norm_boundedHolderSpace_apply_le f x

def boundedHolderSpaceToBoundedContinuousFunction
    (alpha : NNReal) (halpha : 0 < alpha) :
    BoundedHolderSpace (X := X) (F := F) alpha →L[Real]
      BoundedContinuousFunction X F :=
  LinearMap.mkContinuous
    (boundedHolderSpaceToBoundedContinuousFunctionLinearMap alpha halpha) 1
    (fun f ↦ by simpa using
      norm_boundedHolderSpaceToBoundedContinuousFunctionLinearMap_le halpha f)

@[simp]
theorem boundedHolderSpaceToBoundedContinuousFunction_apply
    (alpha : NNReal) (halpha : 0 < alpha)
    (f : BoundedHolderSpace (X := X) (F := F) alpha) (x : X) :
    boundedHolderSpaceToBoundedContinuousFunction alpha halpha f x = f x :=
  rfl

theorem norm_boundedHolderSpaceToBoundedContinuousFunction_le
    (alpha : NNReal) (halpha : 0 < alpha) :
    ‖boundedHolderSpaceToBoundedContinuousFunction
      (X := X) (F := F) alpha halpha‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ zero_le_one
    (fun f ↦ by simpa using
      norm_boundedHolderSpaceToBoundedContinuousFunctionLinearMap_le halpha f)

end BoundedContinuousFunction

section EllipticBoundedContinuousFunction

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

private def contDiffHolderSpaceToBoundedContinuousFunctionLinearMap
    (k : Nat) (alpha : NNReal) :
    ContDiffHolderSpace (V := V) (F := F) k alpha →ₗ[Real]
      BoundedContinuousFunction V F where
  toFun f := BoundedContinuousFunction.ofNormedAddCommGroup
    (contDiffHolderSpaceFun f)
    (by
      have hf : ContDiff Real k (contDiffHolderSpaceFun f) := by
        rw [contDiff_iff_contDiffAt]
        intro x
        exact f.2.1.1 x (Set.mem_univ x)
      exact hf.continuous)
    ‖f‖ (norm_contDiffHolderSpace_apply_le f)
  map_add' f g := by
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  map_smul' c f := by
    apply BoundedContinuousFunction.ext
    intro x
    rfl

private theorem norm_contDiffHolderSpaceToBoundedContinuousFunctionLinearMap_le
    {k : Nat} {alpha : NNReal}
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) :
    ‖contDiffHolderSpaceToBoundedContinuousFunctionLinearMap k alpha f‖ ≤
      ‖f‖ := by
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
    (norm_nonneg f) (norm_contDiffHolderSpace_apply_le f)

def contDiffHolderSpaceToBoundedContinuousFunction
    (k : Nat) (alpha : NNReal) :
    ContDiffHolderSpace (V := V) (F := F) k alpha →L[Real]
      BoundedContinuousFunction V F :=
  LinearMap.mkContinuous
    (contDiffHolderSpaceToBoundedContinuousFunctionLinearMap k alpha) 1
    (fun f ↦ by simpa using
      norm_contDiffHolderSpaceToBoundedContinuousFunctionLinearMap_le f)

@[simp]
theorem contDiffHolderSpaceToBoundedContinuousFunction_apply
    (k : Nat) (alpha : NNReal)
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    contDiffHolderSpaceToBoundedContinuousFunction k alpha f x = f x :=
  rfl

theorem norm_contDiffHolderSpaceToBoundedContinuousFunction_le
    (k : Nat) (alpha : NNReal) :
    ‖contDiffHolderSpaceToBoundedContinuousFunction
      (V := V) (F := F) k alpha‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ zero_le_one
    (fun f ↦ by simpa using
      norm_contDiffHolderSpaceToBoundedContinuousFunctionLinearMap_le f)

private def contDiffHolderSpaceJetLinearMap
    (k : Nat) (alpha : NNReal) (j : Nat) (hj : j ≤ k) :
    ContDiffHolderSpace (V := V) (F := F) k alpha →ₗ[Real]
      BoundedContinuousFunction V (V [×j]→L[Real] F) where
  toFun f := BoundedContinuousFunction.ofNormedAddCommGroup
    (iteratedFDeriv Real j (contDiffHolderSpaceFun f))
    (by
      have hf : ContDiff Real k (contDiffHolderSpaceFun f) := by
        rw [contDiff_iff_contDiffAt]
        intro x
        exact f.2.1.1 x (Set.mem_univ x)
      exact hf.continuous_iteratedFDeriv (by exact_mod_cast hj))
    ‖f‖ (contDiffHolderSpace_iteratedFDeriv_norm_le f hj)
  map_add' f g := by
    apply BoundedContinuousFunction.ext
    intro x
    exact iteratedFDeriv_add_apply
      ((f.2.1.1 x (Set.mem_univ x)).of_le (by exact_mod_cast hj))
      ((g.2.1.1 x (Set.mem_univ x)).of_le (by exact_mod_cast hj))
  map_smul' c f := by
    apply BoundedContinuousFunction.ext
    intro x
    exact iteratedFDeriv_const_smul_apply
      ((f.2.1.1 x (Set.mem_univ x)).of_le (by exact_mod_cast hj))

private theorem norm_contDiffHolderSpaceJetLinearMap_le
    {k : Nat} {alpha : NNReal} {j : Nat} (hj : j ≤ k)
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) :
    ‖contDiffHolderSpaceJetLinearMap k alpha j hj f‖ ≤ ‖f‖ := by
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
    (norm_nonneg f) (contDiffHolderSpace_iteratedFDeriv_norm_le f hj)

def contDiffHolderSpaceJet
    (k : Nat) (alpha : NNReal) (j : Nat) (hj : j ≤ k) :
    ContDiffHolderSpace (V := V) (F := F) k alpha →L[Real]
      BoundedContinuousFunction V (V [×j]→L[Real] F) :=
  LinearMap.mkContinuous
    (contDiffHolderSpaceJetLinearMap k alpha j hj) 1
    (fun f ↦ by simpa using
      norm_contDiffHolderSpaceJetLinearMap_le hj f)

@[simp]
theorem contDiffHolderSpaceJet_apply
    (k : Nat) (alpha : NNReal) (j : Nat) (hj : j ≤ k)
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    contDiffHolderSpaceJet k alpha j hj f x =
      iteratedFDeriv Real j (contDiffHolderSpaceFun f) x :=
  rfl

theorem norm_contDiffHolderSpaceJet_le
    (k : Nat) (alpha : NNReal) (j : Nat) (hj : j ≤ k) :
    ‖contDiffHolderSpaceJet (V := V) (F := F) k alpha j hj‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ zero_le_one
    (fun f ↦ by simpa using norm_contDiffHolderSpaceJetLinearMap_le hj f)

def contDiffHolderSpaceFDeriv
    (k : Nat) (alpha : NNReal) (hk : 1 ≤ k) :
    ContDiffHolderSpace (V := V) (F := F) k alpha →L[Real]
      BoundedContinuousFunction V (V →L[Real] F) :=
  (((continuousMultilinearCurryFin1 Real V F).toContinuousLinearEquiv.toContinuousLinearMap
    ).compLeftContinuousBounded V).comp
    (contDiffHolderSpaceJet k alpha 1 hk)

@[simp]
theorem contDiffHolderSpaceFDeriv_apply
    (k : Nat) (alpha : NNReal) (hk : 1 ≤ k)
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    contDiffHolderSpaceFDeriv k alpha hk f x =
      fderiv Real (contDiffHolderSpaceFun f) x := by
  apply ContinuousLinearMap.ext
  intro v
  change continuousMultilinearCurryFin1 Real V F
      (iteratedFDeriv Real 1 (contDiffHolderSpaceFun f) x) v = _
  simp only [continuousMultilinearCurryFin1_apply,
    iteratedFDeriv_one_apply, Fin.snoc_zero]

def contDiffHolderSpaceHessian
    (k : Nat) (alpha : NNReal) (hk : 2 ≤ k) :
    ContDiffHolderSpace (V := V) (F := F) k alpha →L[Real]
      BoundedContinuousFunction V (V →L[Real] V →L[Real] F) :=
  (((hessianCurryEquiv V F).toContinuousLinearEquiv.toContinuousLinearMap
    ).compLeftContinuousBounded V).comp
    (contDiffHolderSpaceJet k alpha 2 hk)

@[simp]
theorem contDiffHolderSpaceHessian_apply
    (k : Nat) (alpha : NNReal) (hk : 2 ≤ k)
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    contDiffHolderSpaceHessian k alpha hk f x =
      fderiv Real (fderiv Real (contDiffHolderSpaceFun f)) x := by
  simp only [contDiffHolderSpaceHessian, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compLeftContinuousBounded_apply,
    contDiffHolderSpaceJet_apply]
  exact hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv _ _

end EllipticBoundedContinuousFunction

section RestrictUniv

variable {X F : Type*} [MetricSpace X]
  [NormedAddCommGroup F]

theorem eHolderNorm_le_eHolderSeminormOn_univ
    {alpha : NNReal} {f : X → F}
    (hf : MemHolder alpha (Set.univ.restrict f)) :
    eHolderNorm alpha f ≤ eHolderSeminormOn alpha Set.univ f := by
  have hglobal : HolderWith
      (nnHolderNorm alpha (Set.univ.restrict f)) alpha f := by
    intro x y
    exact hf.holderWith ⟨x, Set.mem_univ x⟩ ⟨y, Set.mem_univ y⟩
  exact hglobal.eHolderNorm_le.trans coe_nnHolderNorm_le_eHolderNorm

end RestrictUniv

section EllipticJet

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

theorem eHolderGauge_iteratedFDeriv_le
    {k : Nat} {alpha : NNReal}
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) :
    eHolderGauge alpha
        (iteratedFDeriv Real k (contDiffHolderSpaceFun f)) ≤
      eContDiffHolderGaugeOn k alpha Set.univ
        (contDiffHolderSpaceFun f) := by
  have hsup : eSupNormOn Set.univ
      (iteratedFDeriv Real k (contDiffHolderSpaceFun f)) ≤
      ∑ j ∈ Finset.range (k + 1),
        eSupNormOn Set.univ
          (iteratedFDeriv Real j (contDiffHolderSpaceFun f)) :=
    Finset.single_le_sum
      (fun j _ ↦ zero_le (eSupNormOn Set.univ
        (iteratedFDeriv Real j (contDiffHolderSpaceFun f))))
      (Finset.mem_range.mpr (Nat.lt_succ_self k))
  have hholder : eHolderNorm alpha
      (iteratedFDeriv Real k (contDiffHolderSpaceFun f)) ≤
      eHolderSeminormOn alpha Set.univ
        (iteratedFDeriv Real k (contDiffHolderSpaceFun f)) :=
    eHolderNorm_le_eHolderSeminormOn_univ f.2.1.2
  unfold eHolderGauge eContDiffHolderGaugeOn
  exact add_le_add hsup hholder

private def contDiffHolderSpaceTopJetLinearMap
    (k : Nat) (alpha : NNReal) :
    ContDiffHolderSpace (V := V) (F := F) k alpha →ₗ[Real]
      BoundedHolderSpace (X := V) (F := V [×k]→L[Real] F) alpha where
  toFun f := ⟨iteratedFDeriv Real k (contDiffHolderSpaceFun f),
    ne_top_of_le_ne_top f.2.2 (eHolderGauge_iteratedFDeriv_le f)⟩
  map_add' f g := by
    apply boundedHolderSpace_ext
    intro x
    exact iteratedFDeriv_add_apply
      (f.2.1.1 x (Set.mem_univ x))
      (g.2.1.1 x (Set.mem_univ x))
  map_smul' c f := by
    apply boundedHolderSpace_ext
    intro x
    exact iteratedFDeriv_const_smul_apply
      (f.2.1.1 x (Set.mem_univ x))

private theorem norm_contDiffHolderSpaceTopJetLinearMap_le
    {k : Nat} {alpha : NNReal}
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) :
    ‖contDiffHolderSpaceTopJetLinearMap k alpha f‖ ≤ ‖f‖ := by
  rw [norm_boundedHolderSpace_eq, norm_contDiffHolderSpace_eq]
  exact ENNReal.toReal_mono f.2.2 (eHolderGauge_iteratedFDeriv_le f)

def contDiffHolderSpaceTopJet (k : Nat) (alpha : NNReal) :
    ContDiffHolderSpace (V := V) (F := F) k alpha →L[Real]
      BoundedHolderSpace (X := V) (F := V [×k]→L[Real] F) alpha :=
  LinearMap.mkContinuous (contDiffHolderSpaceTopJetLinearMap k alpha) 1
    (fun f ↦ by simpa using norm_contDiffHolderSpaceTopJetLinearMap_le f)

@[simp]
theorem contDiffHolderSpaceTopJet_apply
    (k : Nat) (alpha : NNReal)
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    contDiffHolderSpaceTopJet k alpha f x =
      iteratedFDeriv Real k (contDiffHolderSpaceFun f) x :=
  rfl

theorem norm_contDiffHolderSpaceTopJet_le (k : Nat) (alpha : NNReal) :
    ‖contDiffHolderSpaceTopJet (V := V) (F := F) k alpha‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ zero_le_one
    (fun f ↦ by simpa using norm_contDiffHolderSpaceTopJetLinearMap_le f)

end EllipticJet

section ParabolicJet

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

theorem eHolderGauge_parabolicSpatialHessian_le
    {alpha : NNReal}
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha) :
    eHolderGauge alpha
        (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) ≤
      eParabolicC2HolderGaugeOn alpha Set.univ
        (parabolicC2HolderSpaceFun u) := by
  have hsup : eSupNormOn Set.univ
      (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) ≤
      ∑ j ∈ Finset.range 3,
        eSupNormOn Set.univ
          (parabolicSpatialJet j (parabolicC2HolderSpaceFun u)) :=
    Finset.single_le_sum
      (fun j _ ↦ zero_le (eSupNormOn Set.univ
        (parabolicSpatialJet j (parabolicC2HolderSpaceFun u))))
      (Finset.mem_range.mpr (by omega))
  have hholder : eHolderNorm alpha
      (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) ≤
      eHolderSeminormOn alpha Set.univ
        (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) :=
    eHolderNorm_le_eHolderSeminormOn_univ u.2.1.2.1
  unfold eHolderGauge
  calc
    eSupNormOn Set.univ
          (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) +
        eHolderNorm alpha
          (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) ≤
      eSupNormOn Set.univ
          (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) +
        eHolderSeminormOn alpha Set.univ
          (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) :=
      add_le_add le_rfl hholder
    _ ≤ (∑ j ∈ Finset.range 3,
          eSupNormOn Set.univ
            (parabolicSpatialJet j (parabolicC2HolderSpaceFun u))) +
        eHolderSeminormOn alpha Set.univ
          (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) :=
      add_le_add hsup le_rfl
    _ ≤ eParabolicC2HolderGaugeOn alpha Set.univ
        (parabolicC2HolderSpaceFun u) := by
      unfold eParabolicC2HolderGaugeOn
      calc
        (∑ j ∈ Finset.range 3,
              eSupNormOn Set.univ
                (parabolicSpatialJet j (parabolicC2HolderSpaceFun u))) +
            eHolderSeminormOn alpha Set.univ
              (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) ≤
          ((∑ j ∈ Finset.range 3,
              eSupNormOn Set.univ
                (parabolicSpatialJet j (parabolicC2HolderSpaceFun u))) +
            eHolderSeminormOn alpha Set.univ
              (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u))) +
            (eSupNormOn Set.univ
              (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) +
            eHolderSeminormOn alpha Set.univ
              (parabolicTimeDerivative (parabolicC2HolderSpaceFun u))) :=
          le_add_right le_rfl
        _ = (∑ j ∈ Finset.range 3,
              eSupNormOn Set.univ
                (parabolicSpatialJet j (parabolicC2HolderSpaceFun u))) +
            eSupNormOn Set.univ
              (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) +
            eHolderSeminormOn alpha Set.univ
              (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) +
            eHolderSeminormOn alpha Set.univ
              (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) := by
          abel

theorem eHolderGauge_parabolicTimeDerivative_le
    {alpha : NNReal}
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha) :
    eHolderGauge alpha
        (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) ≤
      eParabolicC2HolderGaugeOn alpha Set.univ
        (parabolicC2HolderSpaceFun u) := by
  have hholder : eHolderNorm alpha
      (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) ≤
      eHolderSeminormOn alpha Set.univ
        (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) :=
    eHolderNorm_le_eHolderSeminormOn_univ u.2.1.2.2
  unfold eHolderGauge
  calc
    eSupNormOn Set.univ
          (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) +
        eHolderNorm alpha
          (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) ≤
      eSupNormOn Set.univ
          (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) +
        eHolderSeminormOn alpha Set.univ
          (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) :=
      add_le_add le_rfl hholder
    _ ≤ eParabolicC2HolderGaugeOn alpha Set.univ
        (parabolicC2HolderSpaceFun u) := by
      unfold eParabolicC2HolderGaugeOn
      calc
        eSupNormOn Set.univ
              (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) +
            eHolderSeminormOn alpha Set.univ
              (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) ≤
          ((∑ j ∈ Finset.range 3,
              eSupNormOn Set.univ
                (parabolicSpatialJet j (parabolicC2HolderSpaceFun u))) +
            eHolderSeminormOn alpha Set.univ
              (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u))) +
            (eSupNormOn Set.univ
              (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) +
            eHolderSeminormOn alpha Set.univ
              (parabolicTimeDerivative (parabolicC2HolderSpaceFun u))) :=
          le_add_left le_rfl
        _ = (∑ j ∈ Finset.range 3,
              eSupNormOn Set.univ
                (parabolicSpatialJet j (parabolicC2HolderSpaceFun u))) +
            eSupNormOn Set.univ
              (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) +
            eHolderSeminormOn alpha Set.univ
              (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u)) +
            eHolderSeminormOn alpha Set.univ
              (parabolicTimeDerivative (parabolicC2HolderSpaceFun u)) := by
          abel

private def parabolicC2HolderSpaceSpatialHessianLinearMap
    (alpha : NNReal) :
    ParabolicC2HolderSpace (V := V) (F := F) alpha →ₗ[Real]
      ParabolicHolderSpace (V := V) (F := V [×2]→L[Real] F) alpha where
  toFun u := ⟨parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u),
    ne_top_of_le_ne_top u.2.2
      (eHolderGauge_parabolicSpatialHessian_le u)⟩
  map_add' u v := by
    apply boundedHolderSpace_ext
    intro p
    exact parabolicSpatialJet_add 2 _ _ p
      (u.2.1.1.1 p (Set.mem_univ p))
      (v.2.1.1.1 p (Set.mem_univ p))
  map_smul' c u := by
    apply boundedHolderSpace_ext
    intro p
    exact parabolicSpatialJet_const_smul 2 _ p c
      (u.2.1.1.1 p (Set.mem_univ p))

private theorem norm_parabolicC2HolderSpaceSpatialHessianLinearMap_le
    {alpha : NNReal}
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha) :
    ‖parabolicC2HolderSpaceSpatialHessianLinearMap alpha u‖ ≤ ‖u‖ := by
  rw [norm_boundedHolderSpace_eq, norm_parabolicC2HolderSpace_eq]
  exact ENNReal.toReal_mono u.2.2
    (eHolderGauge_parabolicSpatialHessian_le u)

def parabolicC2HolderSpaceSpatialHessian (alpha : NNReal) :
    ParabolicC2HolderSpace (V := V) (F := F) alpha →L[Real]
      ParabolicHolderSpace (V := V) (F := V [×2]→L[Real] F) alpha :=
  LinearMap.mkContinuous
    (parabolicC2HolderSpaceSpatialHessianLinearMap alpha) 1
    (fun u ↦ by simpa using
      norm_parabolicC2HolderSpaceSpatialHessianLinearMap_le u)

@[simp]
theorem parabolicC2HolderSpaceSpatialHessian_apply
    (alpha : NNReal)
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha)
    (p : ParabolicPoint V) :
    parabolicC2HolderSpaceSpatialHessian alpha u p =
      parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u) p :=
  rfl

theorem norm_parabolicC2HolderSpaceSpatialHessian_le (alpha : NNReal) :
    ‖parabolicC2HolderSpaceSpatialHessian (V := V) (F := F) alpha‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ zero_le_one
    (fun u ↦ by simpa using
      norm_parabolicC2HolderSpaceSpatialHessianLinearMap_le u)

private def parabolicC2HolderSpaceTimeDerivativeLinearMap
    (alpha : NNReal) :
    ParabolicC2HolderSpace (V := V) (F := F) alpha →ₗ[Real]
      ParabolicHolderSpace (V := V) (F := F) alpha where
  toFun u := ⟨parabolicTimeDerivative (parabolicC2HolderSpaceFun u),
    ne_top_of_le_ne_top u.2.2
      (eHolderGauge_parabolicTimeDerivative_le u)⟩
  map_add' u v := by
    apply boundedHolderSpace_ext
    intro p
    exact parabolicTimeDerivative_add _ _ p
      (u.2.1.1.2 p (Set.mem_univ p))
      (v.2.1.1.2 p (Set.mem_univ p))
  map_smul' c u := by
    apply boundedHolderSpace_ext
    intro p
    exact parabolicTimeDerivative_const_smul _ p c
      (u.2.1.1.2 p (Set.mem_univ p))

private theorem norm_parabolicC2HolderSpaceTimeDerivativeLinearMap_le
    {alpha : NNReal}
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha) :
    ‖parabolicC2HolderSpaceTimeDerivativeLinearMap alpha u‖ ≤ ‖u‖ := by
  rw [norm_boundedHolderSpace_eq, norm_parabolicC2HolderSpace_eq]
  exact ENNReal.toReal_mono u.2.2
    (eHolderGauge_parabolicTimeDerivative_le u)

def parabolicC2HolderSpaceTimeDerivative (alpha : NNReal) :
    ParabolicC2HolderSpace (V := V) (F := F) alpha →L[Real]
      ParabolicHolderSpace (V := V) (F := F) alpha :=
  LinearMap.mkContinuous
    (parabolicC2HolderSpaceTimeDerivativeLinearMap alpha) 1
    (fun u ↦ by simpa using
      norm_parabolicC2HolderSpaceTimeDerivativeLinearMap_le u)

@[simp]
theorem parabolicC2HolderSpaceTimeDerivative_apply
    (alpha : NNReal)
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha)
    (p : ParabolicPoint V) :
    parabolicC2HolderSpaceTimeDerivative alpha u p =
      parabolicTimeDerivative (parabolicC2HolderSpaceFun u) p :=
  rfl

theorem norm_parabolicC2HolderSpaceTimeDerivative_le (alpha : NNReal) :
    ‖parabolicC2HolderSpaceTimeDerivative (V := V) (F := F) alpha‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ zero_le_one
    (fun u ↦ by simpa using
      norm_parabolicC2HolderSpaceTimeDerivativeLinearMap_le u)

end ParabolicJet

end DifferentialGeometry.Analysis.Schauder
