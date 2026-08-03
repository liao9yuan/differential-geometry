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

end DifferentialGeometry.Analysis.Schauder
