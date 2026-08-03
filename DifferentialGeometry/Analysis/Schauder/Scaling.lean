import DifferentialGeometry.Analysis.Schauder.Holder

noncomputable section

open Set
open scoped NNReal

namespace DifferentialGeometry.Analysis.Schauder

def parabolicDilation {V : Type*} [SMul Real V]
    (r : NNReal) (p : ParabolicPoint V) : ParabolicPoint V :=
  parabolicPoint ((r : Real) ^ 2 * p.time) ((r : Real) • p.space)

@[simp]
theorem parabolicDilation_time {V : Type*} [SMul Real V]
    (r : NNReal) (p : ParabolicPoint V) :
    (parabolicDilation r p).time = (r : Real) ^ 2 * p.time := rfl

@[simp]
theorem parabolicDilation_space {V : Type*} [SMul Real V]
    (r : NNReal) (p : ParabolicPoint V) :
    (parabolicDilation r p).space = (r : Real) • p.space := rfl

@[simp]
theorem parabolicDilation_zero {V : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] (p : ParabolicPoint V) :
    parabolicDilation 0 p = parabolicPoint 0 0 := by
  rcases p with ⟨⟨t⟩, x⟩
  apply Prod.ext
  · apply Metric.Snowflaking.ext
    change (0 : Real) ^ 2 * t = 0
    norm_num
  · change (0 : Real) • x = 0
    simp

@[simp]
theorem parabolicDilation_one {V : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] (p : ParabolicPoint V) :
    parabolicDilation 1 p = p := by
  rcases p with ⟨⟨t⟩, x⟩
  apply Prod.ext
  · apply Metric.Snowflaking.ext
    change (1 : Real) ^ 2 * t = t
    ring
  · change (1 : Real) • x = x
    simp

theorem dist_parabolicDilation {V : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] (r : NNReal) (p q : ParabolicPoint V) :
    dist (parabolicDilation r p) (parabolicDilation r q) =
      (r : Real) * dist p q := by
  rcases p with ⟨⟨t⟩, x⟩
  rcases q with ⟨⟨s⟩, y⟩
  change dist (parabolicPoint ((r : Real) ^ 2 * t) ((r : Real) • x))
      (parabolicPoint ((r : Real) ^ 2 * s) ((r : Real) • y)) =
    (r : Real) * dist (parabolicPoint t x) (parabolicPoint s y)
  rw [dist_parabolicPoint, dist_parabolicPoint, dist_smul₀]
  have htime : |(r : Real) ^ 2 * t - (r : Real) ^ 2 * s| ^ (1 / 2 : Real) =
      (r : Real) * |t - s| ^ (1 / 2 : Real) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg (r : Real)),
      ← Real.sqrt_eq_rpow, Real.sqrt_mul (sq_nonneg (r : Real)),
      Real.sqrt_sq_eq_abs, abs_of_nonneg r.coe_nonneg, Real.sqrt_eq_rpow]
  rw [htime, Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg,
    ← mul_max_of_nonneg _ _ r.coe_nonneg]

def parabolicPreimage {V : Type*} [SMul Real V]
    (r : NNReal) (Q : Set (ParabolicPoint V)) : Set (ParabolicPoint V) :=
  parabolicDilation r ⁻¹' Q

theorem parabolicDilation_mapsTo_preimage {V : Type*} [SMul Real V]
    (r : NNReal) (Q : Set (ParabolicPoint V)) :
    MapsTo (parabolicDilation r) (parabolicPreimage r Q) Q :=
  fun _ hp => hp

theorem parabolicHolder_dilation
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [MetricSpace F] {alpha C : NNReal} {Q : Set (ParabolicPoint V)}
    {f : ParabolicPoint V → F} (r : NNReal)
    (hf : HolderWith C alpha (Q.restrict f)) :
    HolderWith (C * r ^ (alpha : Real)) alpha
      ((parabolicPreimage r Q).restrict (f ∘ parabolicDilation r)) := by
  intro p q
  change edist (f (parabolicDilation r p.1)) (f (parabolicDilation r q.1)) ≤ _
  have hpQ : parabolicDilation r p.1 ∈ Q := p.2
  have hqQ : parabolicDilation r q.1 ∈ Q := q.2
  have hdist := hf.edist_le
    (x := ⟨parabolicDilation r p.1, hpQ⟩)
    (y := ⟨parabolicDilation r q.1, hqQ⟩)
  change edist (f (parabolicDilation r p.1)) (f (parabolicDilation r q.1)) ≤
    (C : ENNReal) * edist (parabolicDilation r p.1)
      (parabolicDilation r q.1) ^ (alpha : Real) at hdist
  rw [edist_dist, edist_dist, dist_parabolicDilation r] at hdist
  rw [edist_dist, edist_dist]
  change ENNReal.ofReal (dist (f (parabolicDilation r p.1))
      (f (parabolicDilation r q.1))) ≤
    (C * r ^ (alpha : Real) : NNReal) *
      ENNReal.ofReal (dist p.1 q.1) ^ (alpha : Real)
  simp only [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ alpha.coe_nonneg]
  calc
    ENNReal.ofReal (dist (f (parabolicDilation r p.1))
      (f (parabolicDilation r q.1))) ≤
        C * ENNReal.ofReal ((r : Real) * dist p.1 q.1) ^ (alpha : Real) := hdist
    _ = (C * (r : ENNReal) ^ (alpha : Real)) *
        ENNReal.ofReal (dist p.1 q.1) ^ (alpha : Real) := by
      rw [ENNReal.ofReal_mul r.coe_nonneg, ENNReal.ofReal_coe_nnreal,
        ENNReal.mul_rpow_of_nonneg _ _ alpha.coe_nonneg]
      ring

def parabolicLinearMap {V : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] (L : V →L[Real] V)
    (p : ParabolicPoint V) : ParabolicPoint V :=
  parabolicPoint p.time (L p.space)

@[simp]
theorem parabolicLinearMap_time {V : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] (L : V →L[Real] V) (p : ParabolicPoint V) :
    (parabolicLinearMap L p).time = p.time := rfl

@[simp]
theorem parabolicLinearMap_space {V : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] (L : V →L[Real] V) (p : ParabolicPoint V) :
    (parabolicLinearMap L p).space = L p.space := rfl

theorem dist_parabolicLinearMap_le {V : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] (L : V →L[Real] V) (p q : ParabolicPoint V) :
    dist (parabolicLinearMap L p) (parabolicLinearMap L q) ≤
      max 1 ‖L‖ * dist p q := by
  rcases p with ⟨⟨t⟩, x⟩
  rcases q with ⟨⟨s⟩, y⟩
  change dist (parabolicPoint t (L x)) (parabolicPoint s (L y)) ≤
    max 1 ‖L‖ * dist (parabolicPoint t x) (parabolicPoint s y)
  rw [dist_parabolicPoint, dist_parabolicPoint]
  let D : Real := max (|t - s| ^ (1 / 2 : Real)) (dist x y)
  have hD0 : 0 ≤ D :=
    (Real.rpow_nonneg (abs_nonneg _) _).trans (le_max_left _ _)
  have htime : |t - s| ^ (1 / 2 : Real) ≤ max 1 ‖L‖ * D := by
    calc
      |t - s| ^ (1 / 2 : Real) ≤ D := le_max_left _ _
      _ = 1 * D := by rw [one_mul]
      _ ≤ max 1 ‖L‖ * D :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hD0
  have hspace : dist (L x) (L y) ≤ max 1 ‖L‖ * D := by
    calc
      dist (L x) (L y) = ‖L (x - y)‖ := by
        rw [dist_eq_norm, map_sub]
      _ ≤ ‖L‖ * ‖x - y‖ := L.le_opNorm (x - y)
      _ = ‖L‖ * dist x y := by rw [dist_eq_norm]
      _ ≤ max 1 ‖L‖ * D :=
        mul_le_mul (le_max_right _ _) (le_max_right _ _)
          (dist_nonneg) (by positivity)
  exact max_le htime hspace

theorem lipschitzWith_parabolicLinearMap
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    (L : V →L[Real] V) :
    LipschitzWith (max 1 ‖L‖₊) (parabolicLinearMap L) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simpa only [NNReal.coe_max, NNReal.coe_one, coe_nnnorm] using
    dist_parabolicLinearMap_le L p q

def parabolicLinearPreimage {V : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] (L : V →L[Real] V)
    (Q : Set (ParabolicPoint V)) : Set (ParabolicPoint V) :=
  parabolicLinearMap L ⁻¹' Q

@[simp]
theorem parabolicLinearPreimage_cylinder_univ
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    (L : V →L[Real] V) (J : Set Real) :
    parabolicLinearPreimage L (parabolicCylinder J Set.univ) =
      parabolicCylinder J Set.univ := by
  ext p
  simp [parabolicLinearPreimage, parabolicCylinder]

theorem parabolicHolder_linearMap
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [MetricSpace F] {alpha C : NNReal} {Q : Set (ParabolicPoint V)}
    {f : ParabolicPoint V → F} (L : V →L[Real] V)
    (hf : HolderWith C alpha (Q.restrict f)) :
    HolderWith (C * (max 1 ‖L‖₊) ^ (alpha : Real)) alpha
      ((parabolicLinearPreimage L Q).restrict
        (f ∘ parabolicLinearMap L)) := by
  let g : parabolicLinearPreimage L Q → Q := fun p =>
    ⟨parabolicLinearMap L p.1, p.2⟩
  have hg : LipschitzWith (max 1 ‖L‖₊) g :=
    ((lipschitzWith_parabolicLinearMap L).restrict
      (parabolicLinearPreimage L Q)).subtype_mk fun p => p.2
  have hcomp := hf.comp hg.holderWith
  simpa only [g, Function.comp_apply, Set.restrict_apply, mul_one] using hcomp

theorem parabolicSpatialJet_linearEquiv
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (L : V ≃L[Real] V) (u : Real → V → F) (j : Nat)
    (p : ParabolicPoint V) :
    parabolicSpatialJet j (fun t x => u t (L x)) p =
      (parabolicSpatialJet j u
        (parabolicLinearMap (L : V →L[Real] V) p)).compContinuousLinearMap
          (fun _ => (L : V →L[Real] V)) := by
  unfold parabolicSpatialJet
  simp only [parabolicLinearMap_time, parabolicLinearMap_space]
  have h := L.iteratedFDerivWithin_comp_right (u p.time)
    uniqueDiffOn_univ (mem_univ (L p.space)) j
  simpa only [preimage_univ, iteratedFDerivWithin_univ,
    Function.comp_apply] using h

theorem parabolicTimeDerivative_linearEquiv
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (L : V ≃L[Real] V) (u : Real → V → F) (p : ParabolicPoint V) :
    parabolicTimeDerivative (fun t x => u t (L x)) p =
      parabolicTimeDerivative u
        (parabolicLinearMap (L : V →L[Real] V) p) := by
  rfl

theorem lipschitzWith_compContinuousLinearMapL
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (j : Nat) (L : V →L[Real] V) :
    LipschitzWith (∏ _ : Fin j, ‖L‖₊)
      (ContinuousMultilinearMap.compContinuousLinearMapL
        (F := F) (fun _ : Fin j => L)) := by
  apply LipschitzWith.of_dist_le_mul
  intro B C
  rw [dist_eq_norm, ← map_sub]
  simpa only [dist_eq_norm, NNReal.coe_prod, coe_nnnorm, mul_comm,
    ContinuousMultilinearMap.compContinuousLinearMapL_apply] using
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (B - C) (fun _ : Fin j => L)

def parabolicC2HolderLinearEquivConst
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    (L : V ≃L[Real] V) (alpha C : NNReal) : NNReal :=
  let R := max 1 ‖(L.symm : V →L[Real] V)‖₊
  C + R * C + R ^ 2 * C + C +
    R ^ 2 * (C * R ^ (alpha : Real)) + C * R ^ (alpha : Real)

theorem eParabolicC2HolderGaugeOn_linearEquiv_le
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (L : V ≃L[Real] V) (alpha C : NNReal) (J : Set Real)
    (u : Real → V → F)
    (h : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder J Set.univ) (fun t x => u t (L x)) ≤ C) :
    eParabolicC2HolderGaugeOn alpha (parabolicCylinder J Set.univ) u ≤
      parabolicC2HolderLinearEquivConst L alpha C := by
  let Q : Set (ParabolicPoint V) := parabolicCylinder J Set.univ
  let v : Real → V → F := fun t x => u t (L x)
  let R : NNReal := max 1 ‖(L.symm : V →L[Real] V)‖₊
  let Cspatial : Nat → NNReal := fun j =>
    match j with
    | 0 => C
    | 1 => R * C
    | _ => R ^ 2 * C
  have h' : eParabolicC2HolderGaugeOn alpha Q v ≤ C := h
  have hR : ‖(L.symm : V →L[Real] V)‖₊ ≤ R := by
    exact le_max_right _ _
  have hspatial : ∀ j < 3, ∀ p ∈ Q,
      ‖parabolicSpatialJet j u p‖ ≤ Cspatial j := by
    intro j hj p hp
    let q := parabolicLinearMap (L.symm : V →L[Real] V) p
    have hq : q ∈ Q := by
      simpa only [q, Q, parabolicCylinder, parabolicLinearMap_time,
        parabolicLinearMap_space, mem_setOf_eq, mem_univ, and_true] using hp
    have heq : parabolicSpatialJet j u p =
        (parabolicSpatialJet j v q).compContinuousLinearMap
          (fun _ => (L.symm : V →L[Real] V)) := by
      have hlin := parabolicSpatialJet_linearEquiv L.symm v j p
      simpa only [v, q, ContinuousLinearEquiv.apply_symm_apply] using hlin
    rw [heq]
    have hnorm := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (parabolicSpatialJet j v q)
      (fun _ : Fin j => (L.symm : V →L[Real] V))
    have hadapt := parabolicSpatialJet_norm_le h' (Nat.le_of_lt_succ hj) hq
    interval_cases j
    · calc
        ‖(parabolicSpatialJet 0 v q).compContinuousLinearMap
            (fun _ => (L.symm : V →L[Real] V))‖ ≤
            ‖parabolicSpatialJet 0 v q‖ * 1 := by
          simpa only [Finset.prod_fin_eq_prod_range,
            Finset.prod_range_zero] using hnorm
        _ = ‖parabolicSpatialJet 0 v q‖ := mul_one _
        _ ≤ (Cspatial 0 : Real) := by
          simpa only [Cspatial] using hadapt
    · calc
        ‖(parabolicSpatialJet 1 v q).compContinuousLinearMap
            (fun _ => (L.symm : V →L[Real] V))‖ ≤
            ‖parabolicSpatialJet 1 v q‖ *
              ‖(L.symm : V →L[Real] V)‖ := by
          simpa only [Fin.prod_univ_one] using hnorm
        _ ≤ C * (R : Real) := by
          exact mul_le_mul hadapt (by exact_mod_cast hR)
            (norm_nonneg _) C.coe_nonneg
        _ = (Cspatial 1 : Real) := by
          simp only [Cspatial, NNReal.coe_mul]
          ring
    · calc
        ‖(parabolicSpatialJet 2 v q).compContinuousLinearMap
            (fun _ => (L.symm : V →L[Real] V))‖ ≤
            ‖parabolicSpatialJet 2 v q‖ *
              (‖(L.symm : V →L[Real] V)‖ *
                ‖(L.symm : V →L[Real] V)‖) := by
          simpa only [Fin.prod_univ_two] using hnorm
        _ ≤ C * ((R : Real) * R) := by
          apply mul_le_mul hadapt
          · exact mul_le_mul (by exact_mod_cast hR) (by exact_mod_cast hR)
              (norm_nonneg _) R.coe_nonneg
          · positivity
          · exact C.coe_nonneg
        _ = (Cspatial 2 : Real) := by
          simp only [Cspatial, NNReal.coe_mul, NNReal.coe_pow]
          ring
  have htime : ∀ p ∈ Q, ‖parabolicTimeDerivative u p‖ ≤ C := by
    intro p hp
    let q := parabolicLinearMap (L.symm : V →L[Real] V) p
    have hq : q ∈ Q := by
      simpa only [q, Q, parabolicCylinder, parabolicLinearMap_time,
        parabolicLinearMap_space, mem_setOf_eq, mem_univ, and_true] using hp
    have heq := parabolicTimeDerivative_linearEquiv L.symm v p
    have heq' : parabolicTimeDerivative u p =
        parabolicTimeDerivative v q := by
      simpa only [v, q, ContinuousLinearEquiv.apply_symm_apply] using heq
    rw [heq']
    exact parabolicTimeDerivative_norm_le h' hq
  have hspatialHolder : HolderWith
      (R ^ 2 * (C * R ^ (alpha : Real))) alpha
      (Q.restrict (parabolicSpatialJet 2 u)) := by
    have hadapt := parabolicSpatialJet_holderWith_restrict h'
    have hdomain : HolderWith (C * R ^ (alpha : Real)) alpha
        (Q.restrict (parabolicSpatialJet 2 v ∘
          parabolicLinearMap (L.symm : V →L[Real] V))) := by
      have hraw := parabolicHolder_linearMap
        (L.symm : V →L[Real] V) hadapt
      simpa only [R, Q, parabolicLinearPreimage_cylinder_univ] using hraw
    let P := ContinuousMultilinearMap.compContinuousLinearMapL
      (F := F) (fun _ : Fin 2 => (L.symm : V →L[Real] V))
    have hP0 := lipschitzWith_compContinuousLinearMapL
      (F := F) 2 (L.symm : V →L[Real] V)
    have hprod : (∏ _ : Fin 2, ‖(L.symm : V →L[Real] V)‖₊) ≤ R ^ 2 := by
      simpa only [Fin.prod_univ_two, pow_two] using
        mul_le_mul hR hR (zero_le _) (zero_le _)
    have hP : LipschitzWith (R ^ 2) P := hP0.weaken hprod
    have hcomp := hP.holderWith.comp hdomain
    have hcomp' : HolderWith
        (R ^ 2 * (C * R ^ (alpha : Real))) alpha
        (P ∘ Q.restrict (parabolicSpatialJet 2 v ∘
          parabolicLinearMap (L.symm : V →L[Real] V))) := by
      simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul] using hcomp
    convert hcomp' using 1
    funext p
    have hlin := parabolicSpatialJet_linearEquiv L.symm v 2 p.1
    simpa only [P, v, Function.comp_apply, Set.restrict_apply,
      ContinuousLinearEquiv.apply_symm_apply] using hlin
  have htimeHolder : HolderWith (C * R ^ (alpha : Real)) alpha
      (Q.restrict (parabolicTimeDerivative u)) := by
    have hadapt := parabolicTimeDerivative_holderWith_restrict h'
    have hraw := parabolicHolder_linearMap
      (L.symm : V →L[Real] V) hadapt
    have hraw' : HolderWith (C * R ^ (alpha : Real)) alpha
        (Q.restrict (parabolicTimeDerivative v ∘
          parabolicLinearMap (L.symm : V →L[Real] V))) := by
      simpa only [R, Q, parabolicLinearPreimage_cylinder_univ] using hraw
    convert hraw' using 1
    funext p
    have hlin := parabolicTimeDerivative_linearEquiv L.symm v p.1
    simpa only [v, Function.comp_apply, Set.restrict_apply,
      ContinuousLinearEquiv.apply_symm_apply] using hlin
  have hresult := eParabolicC2HolderGaugeOn_le Cspatial C
    (R ^ 2 * (C * R ^ (alpha : Real)))
    (C * R ^ (alpha : Real)) hspatial htime hspatialHolder htimeHolder
  unfold parabolicC2HolderLinearEquivConst
  simpa only [Q, R, Cspatial, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow,
    NNReal.coe_rpow] using hresult

end DifferentialGeometry.Analysis.Schauder
