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

end DifferentialGeometry.Analysis.Schauder
