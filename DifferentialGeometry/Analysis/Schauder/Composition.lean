import DifferentialGeometry.Analysis.Schauder.Holder

noncomputable section

open Set
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Schauder

variable {X Y F : Type*} [MetricSpace X] [MetricSpace Y]
  [NormedAddCommGroup F]

omit [MetricSpace X] [MetricSpace Y] in
theorem eSupNormOn_comp_le_of_mapsTo
    {s : Set X} {t : Set Y} (phi : X → Y) (f : Y → F)
    (hphi : MapsTo phi s t) :
    eSupNormOn s (f ∘ phi) ≤ eSupNormOn t f := by
  rw [eSupNormOn_le]
  intro x hx
  exact norm_le_eSupNormOn t f (phi x) (hphi hx)

theorem holderWith_restrict_comp_of_lipschitzWith
    {s : Set X} {t : Set Y} {L K alpha : NNReal}
    (phi : X → Y) (f : Y → F)
    (hphi : LipschitzWith L phi) (hst : MapsTo phi s t)
    (hf : HolderWith K alpha (t.restrict f)) :
    HolderWith (K * L ^ (alpha : Real)) alpha (s.restrict (f ∘ phi)) := by
  let phi' : s → t := fun x ↦ ⟨phi x, hst x.2⟩
  have hphi' : LipschitzWith L phi' := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact hphi.dist_le_mul x.1 y.1
  have hcomp := hf.comp hphi'.holderWith
  have heq : t.restrict f ∘ phi' = s.restrict (f ∘ phi) := by
    rfl
  rw [heq] at hcomp
  simpa only [mul_one] using hcomp

theorem eHolderSeminormOn_comp_le_of_lipschitzWith
    {s : Set X} {t : Set Y} {L K alpha : NNReal}
    (phi : X → Y) (f : Y → F)
    (hphi : LipschitzWith L phi) (hst : MapsTo phi s t)
    (hf : eHolderSeminormOn alpha t f ≤ K) :
    eHolderSeminormOn alpha s (f ∘ phi) ≤
      ((K * L ^ (alpha : Real) : NNReal) : ENNReal) := by
  exact HolderWith.eHolderNorm_le
    (holderWith_restrict_comp_of_lipschitzWith phi f hphi hst
      (holderWith_restrict_of_eHolderSeminormOn_le hf))

def parabolicMap (phi : X → Y) : ParabolicPoint X → ParabolicPoint Y :=
  fun p ↦ parabolicPoint p.time (phi p.space)

omit [MetricSpace X] [MetricSpace Y] in
@[simp]
theorem parabolicMap_apply (phi : X → Y) (t : Real) (x : X) :
    parabolicMap phi (parabolicPoint t x) = parabolicPoint t (phi x) := by
  rfl

omit [MetricSpace X] [MetricSpace Y] in
@[simp]
theorem parabolicMap_time (phi : X → Y) (p : ParabolicPoint X) :
    (parabolicMap phi p).time = p.time := by
  rfl

omit [MetricSpace X] [MetricSpace Y] in
@[simp]
theorem parabolicMap_space (phi : X → Y) (p : ParabolicPoint X) :
    (parabolicMap phi p).space = phi p.space := by
  rfl

omit [MetricSpace X] [MetricSpace Y] in
theorem parabolicMap_preimage_cylinder
    (phi : X → Y) (J : Set Real) (Omega : Set Y) :
    parabolicMap phi ⁻¹' parabolicCylinder J Omega =
      parabolicCylinder J (phi ⁻¹' Omega) := by
  ext p
  rfl

theorem lipschitzWith_parabolicMap
    {L : NNReal} (hL : 1 ≤ L) {phi : X → Y}
    (hphi : LipschitzWith L phi) :
    LipschitzWith L (parabolicMap phi) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [← parabolicPoint_time_space p, ← parabolicPoint_time_space q,
    parabolicMap_apply, parabolicMap_apply, dist_parabolicPoint,
    dist_parabolicPoint]
  apply max_le
  · calc
      |p.time - q.time| ^ (1 / 2 : Real) ≤
          max (|p.time - q.time| ^ (1 / 2 : Real)) (dist p.space q.space) :=
        le_max_left _ _
      _ = 1 * max (|p.time - q.time| ^ (1 / 2 : Real))
          (dist p.space q.space) := by rw [one_mul]
      _ ≤ L * max (|p.time - q.time| ^ (1 / 2 : Real))
          (dist p.space q.space) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hL)
          ((Real.rpow_nonneg (abs_nonneg _) _).trans
            (le_max_left _ _))
  · exact (hphi.dist_le_mul p.space q.space).trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) L.coe_nonneg)

theorem holderWith_restrict_comp_parabolicMap
    {Q : Set (ParabolicPoint X)} {R : Set (ParabolicPoint Y)}
    {L K alpha : NNReal} (hL : 1 ≤ L)
    (phi : X → Y) (f : ParabolicPoint Y → F)
    (hphi : LipschitzWith L phi) (hQR : MapsTo (parabolicMap phi) Q R)
    (hf : HolderWith K alpha (R.restrict f)) :
    HolderWith (K * L ^ (alpha : Real)) alpha
      (Q.restrict (f ∘ parabolicMap phi)) := by
  exact holderWith_restrict_comp_of_lipschitzWith
    (parabolicMap phi) f (lipschitzWith_parabolicMap hL hphi) hQR hf

theorem eHolderSeminormOn_comp_parabolicMap_le
    {Q : Set (ParabolicPoint X)} {R : Set (ParabolicPoint Y)}
    {L K alpha : NNReal} (hL : 1 ≤ L)
    (phi : X → Y) (f : ParabolicPoint Y → F)
    (hphi : LipschitzWith L phi) (hQR : MapsTo (parabolicMap phi) Q R)
    (hf : eHolderSeminormOn alpha R f ≤ K) :
    eHolderSeminormOn alpha Q (f ∘ parabolicMap phi) ≤
      ((K * L ^ (alpha : Real) : NNReal) : ENNReal) := by
  exact eHolderSeminormOn_comp_le_of_lipschitzWith
    (parabolicMap phi) f (lipschitzWith_parabolicMap hL hphi) hQR hf

end DifferentialGeometry.Analysis.Schauder

end
