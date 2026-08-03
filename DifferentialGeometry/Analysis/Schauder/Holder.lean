import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Topology.MetricSpace.Snowflaking

noncomputable section

open Set
open scoped ENNReal NNReal BigOperators Topology

namespace DifferentialGeometry.Analysis.Schauder

variable {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]

def eSupNormOn (s : Set X) (f : X → F) : ENNReal :=
  ⨆ x : s, ENNReal.ofReal ‖f x‖

omit [MetricSpace X] in
theorem norm_le_eSupNormOn (s : Set X) (f : X → F) (x : X) (hx : x ∈ s) :
    ENNReal.ofReal ‖f x‖ ≤ eSupNormOn s f :=
  le_iSup (fun y : s => ENNReal.ofReal ‖f y‖) ⟨x, hx⟩

omit [MetricSpace X] in
theorem eSupNormOn_le {s : Set X} {f : X → F} {C : ENNReal} :
    eSupNormOn s f ≤ C ↔ ∀ x ∈ s, ENNReal.ofReal ‖f x‖ ≤ C := by
  simp only [eSupNormOn, iSup_le_iff, Subtype.forall]

def eHolderSeminormOn (alpha : NNReal) (s : Set X) (f : X → F) : ENNReal :=
  eHolderNorm alpha (s.restrict f)

theorem holderWith_restrict_of_eHolderSeminormOn_le
    {alpha C : NNReal} {s : Set X} {f : X → F}
    (h : eHolderSeminormOn alpha s f ≤ C) :
    HolderWith C alpha (s.restrict f) := by
  let g : s → F := s.restrict f
  have he : eHolderNorm alpha g ≤ (C : ENNReal) := by
    simpa only [eHolderSeminormOn, g] using h
  have hmem : MemHolder alpha g :=
    eHolderNorm_lt_top.mp (lt_of_le_of_lt he ENNReal.coe_lt_top)
  have hbase : HolderWith (nnHolderNorm alpha g) alpha g :=
    MemHolder.holderWith hmem
  have hnn : nnHolderNorm alpha g ≤ C :=
    ENNReal.coe_le_coe.mp (coe_nnHolderNorm_le_eHolderNorm.trans he)
  simpa only [g] using hbase.mono hnn

section Spatial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedSpace Real F]

def eContDiffHolderGaugeOn (k : Nat) (alpha : NNReal)
    (s : Set V) (f : V → F) : ENNReal :=
  (∑ j ∈ Finset.range (k + 1), eSupNormOn s (iteratedFDeriv Real j f)) +
    eHolderSeminormOn alpha s (iteratedFDeriv Real k f)

def IsContDiffHolderOn (k : Nat) (alpha : NNReal)
    (s : Set V) (f : V → F) : Prop :=
  (∀ x ∈ s, ContDiffAt Real k f x) ∧
    MemHolder alpha (s.restrict (iteratedFDeriv Real k f))

theorem spatialJet_le_eContDiffHolderGaugeOn
    (k : Nat) (alpha : NNReal) (s : Set V) (f : V → F)
    {j : Nat} (hj : j ≤ k) (x : V) (hx : x ∈ s) :
    ENNReal.ofReal ‖iteratedFDeriv Real j f x‖ ≤
      eContDiffHolderGaugeOn k alpha s f := by
  have hterm : eSupNormOn s (iteratedFDeriv Real j f) ≤
      ∑ q ∈ Finset.range (k + 1), eSupNormOn s (iteratedFDeriv Real q f) :=
    Finset.single_le_sum
      (fun q _ => zero_le (eSupNormOn s (iteratedFDeriv Real q f)))
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
  exact (norm_le_eSupNormOn s (iteratedFDeriv Real j f) x hx).trans
    (hterm.trans (by
      unfold eContDiffHolderGaugeOn
      exact le_add_right le_rfl))

theorem holderSeminorm_le_eContDiffHolderGaugeOn
    (k : Nat) (alpha : NNReal) (s : Set V) (f : V → F) :
    eHolderSeminormOn alpha s (iteratedFDeriv Real k f) ≤
      eContDiffHolderGaugeOn k alpha s f := by
  unfold eContDiffHolderGaugeOn
  exact le_add_left le_rfl

theorem spatialJet_norm_le {k : Nat} {alpha C : NNReal}
    {s : Set V} {f : V → F}
    (h : eContDiffHolderGaugeOn k alpha s f ≤ C)
    {j : Nat} (hj : j ≤ k) {x : V} (hx : x ∈ s) :
    ‖iteratedFDeriv Real j f x‖ ≤ C := by
  rw [← ENNReal.ofReal_le_coe]
  exact (spatialJet_le_eContDiffHolderGaugeOn k alpha s f hj x hx).trans h

theorem topSpatialJet_holderWith_restrict {k : Nat} {alpha C : NNReal}
    {s : Set V} {f : V → F}
    (h : eContDiffHolderGaugeOn k alpha s f ≤ C) :
    HolderWith C alpha (s.restrict (iteratedFDeriv Real k f)) :=
  holderWith_restrict_of_eHolderSeminormOn_le
    ((holderSeminorm_le_eContDiffHolderGaugeOn k alpha s f).trans h)

end Spatial

abbrev ParabolicPoint (V : Type*) :=
  Metric.Snowflaking Real (1 / 2) (by norm_num) (by norm_num) × V

def parabolicPoint {V : Type*} (t : Real) (x : V) : ParabolicPoint V :=
  (Metric.Snowflaking.toSnowflaking t, x)

def ParabolicPoint.time {V : Type*} (p : ParabolicPoint V) : Real :=
  p.1.ofSnowflaking

def ParabolicPoint.space {V : Type*} (p : ParabolicPoint V) : V :=
  p.2

@[simp]
theorem parabolicPoint_time {V : Type*} (t : Real) (x : V) :
    (parabolicPoint t x).time = t := rfl

@[simp]
theorem parabolicPoint_space {V : Type*} (t : Real) (x : V) :
    (parabolicPoint t x).space = x := rfl

theorem dist_parabolicPoint {V : Type*} [PseudoMetricSpace V]
    (t s : Real) (x y : V) :
    dist (parabolicPoint t x) (parabolicPoint s y) =
      max (|t - s| ^ (1 / 2 : Real)) (dist x y) := by
  simp [parabolicPoint, Prod.dist_eq, Real.dist_eq]

def parabolicCylinder {V : Type*} (J : Set Real) (Omega : Set V) :
    Set (ParabolicPoint V) :=
  {p | p.time ∈ J ∧ p.space ∈ Omega}

theorem parabolicHolder_space_dist_le
    {V F : Type*} [PseudoMetricSpace V] [MetricSpace F]
    {alpha C : NNReal} {Q : Set (ParabolicPoint V)}
    {f : ParabolicPoint V → F}
    (h : HolderWith C alpha (Q.restrict f))
    {t : Real} {x y : V}
    (hx : parabolicPoint t x ∈ Q) (hy : parabolicPoint t y ∈ Q) :
    dist (f (parabolicPoint t x)) (f (parabolicPoint t y)) ≤
      C * dist x y ^ (alpha : Real) := by
  have hraw := h.dist_le
    (⟨parabolicPoint t x, hx⟩ : Q) (⟨parabolicPoint t y, hy⟩ : Q)
  change dist (f (parabolicPoint t x)) (f (parabolicPoint t y)) ≤
    C * dist (parabolicPoint t x) (parabolicPoint t y) ^ (alpha : Real) at hraw
  simpa [dist_parabolicPoint] using hraw

theorem parabolicHolder_time_dist_le
    {V F : Type*} [PseudoMetricSpace V] [MetricSpace F]
    {alpha C : NNReal} {Q : Set (ParabolicPoint V)}
    {f : ParabolicPoint V → F}
    (h : HolderWith C alpha (Q.restrict f))
    {t s : Real} {x : V}
    (ht : parabolicPoint t x ∈ Q) (hs : parabolicPoint s x ∈ Q) :
    dist (f (parabolicPoint t x)) (f (parabolicPoint s x)) ≤
      C * |t - s| ^ ((alpha : Real) / 2) := by
  have hraw := h.dist_le
    (⟨parabolicPoint t x, ht⟩ : Q) (⟨parabolicPoint s x, hs⟩ : Q)
  change dist (f (parabolicPoint t x)) (f (parabolicPoint s x)) ≤
    C * dist (parabolicPoint t x) (parabolicPoint s x) ^ (alpha : Real) at hraw
  rw [dist_parabolicPoint, dist_self, max_eq_left
    (Real.rpow_nonneg (abs_nonneg _) _)] at hraw
  rw [← Real.rpow_mul (abs_nonneg _) (1 / 2 : Real) (alpha : Real)] at hraw
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using hraw

section Parabolic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedSpace Real F]

def parabolicSpatialJet (j : Nat) (u : Real → V → F) :
    ParabolicPoint V → (V [×j]→L[Real] F) :=
  fun p => iteratedFDeriv Real j (u p.time) p.space

def parabolicTimeDerivative (u : Real → V → F) : ParabolicPoint V → F :=
  fun p => fderiv Real (fun t => u t p.space) p.time 1

def eParabolicC2HolderGaugeOn (alpha : NNReal)
    (Q : Set (ParabolicPoint V)) (u : Real → V → F) : ENNReal :=
  (∑ j ∈ Finset.range 3, eSupNormOn Q (parabolicSpatialJet j u)) +
    eSupNormOn Q (parabolicTimeDerivative u) +
    eHolderSeminormOn alpha Q (parabolicSpatialJet 2 u) +
    eHolderSeminormOn alpha Q (parabolicTimeDerivative u)

def IsParabolicC2HolderOn (alpha : NNReal)
    (Q : Set (ParabolicPoint V)) (u : Real → V → F) : Prop :=
  (∀ p ∈ Q, ContDiffAt Real 2 (u p.time) p.space) ∧
    (∀ p ∈ Q, DifferentiableAt Real (fun t => u t p.space) p.time) ∧
    MemHolder alpha (Q.restrict (parabolicSpatialJet 2 u)) ∧
    MemHolder alpha (Q.restrict (parabolicTimeDerivative u))

theorem parabolicSpatialJet_le
    (alpha : NNReal) (Q : Set (ParabolicPoint V)) (u : Real → V → F)
    {j : Nat} (hj : j < 3) (p : ParabolicPoint V) (hp : p ∈ Q) :
    ENNReal.ofReal ‖parabolicSpatialJet j u p‖ ≤
      eParabolicC2HolderGaugeOn alpha Q u := by
  have hterm : eSupNormOn Q (parabolicSpatialJet j u) ≤
      ∑ q ∈ Finset.range 3, eSupNormOn Q (parabolicSpatialJet q u) :=
    Finset.single_le_sum
      (fun q _ => zero_le (eSupNormOn Q (parabolicSpatialJet q u)))
      (Finset.mem_range.mpr hj)
  exact (norm_le_eSupNormOn Q (parabolicSpatialJet j u) p hp).trans
    (hterm.trans (by
      unfold eParabolicC2HolderGaugeOn
      exact (le_add_right le_rfl).trans
        ((le_add_right le_rfl).trans (le_add_right le_rfl))))

theorem parabolicTimeDerivative_le
    (alpha : NNReal) (Q : Set (ParabolicPoint V)) (u : Real → V → F)
    (p : ParabolicPoint V) (hp : p ∈ Q) :
    ENNReal.ofReal ‖parabolicTimeDerivative u p‖ ≤
      eParabolicC2HolderGaugeOn alpha Q u := by
  exact (norm_le_eSupNormOn Q (parabolicTimeDerivative u) p hp).trans (by
    unfold eParabolicC2HolderGaugeOn
    exact (le_add_left le_rfl).trans
      ((le_add_right le_rfl).trans (le_add_right le_rfl)))

theorem parabolicSpatialHolderSeminorm_le
    (alpha : NNReal) (Q : Set (ParabolicPoint V)) (u : Real → V → F) :
    eHolderSeminormOn alpha Q (parabolicSpatialJet 2 u) ≤
      eParabolicC2HolderGaugeOn alpha Q u := by
  unfold eParabolicC2HolderGaugeOn
  exact (le_add_left le_rfl).trans (le_add_right le_rfl)

theorem parabolicTimeHolderSeminorm_le
    (alpha : NNReal) (Q : Set (ParabolicPoint V)) (u : Real → V → F) :
    eHolderSeminormOn alpha Q (parabolicTimeDerivative u) ≤
      eParabolicC2HolderGaugeOn alpha Q u := by
  unfold eParabolicC2HolderGaugeOn
  exact le_add_left le_rfl

theorem parabolicSpatialJet_norm_le {alpha C : NNReal}
    {Q : Set (ParabolicPoint V)} {u : Real → V → F}
    (h : eParabolicC2HolderGaugeOn alpha Q u ≤ C)
    {j : Nat} (hj : j ≤ 2) {p : ParabolicPoint V} (hp : p ∈ Q) :
    ‖parabolicSpatialJet j u p‖ ≤ C := by
  rw [← ENNReal.ofReal_le_coe]
  exact (parabolicSpatialJet_le alpha Q u (by omega) p hp).trans h

theorem parabolicTimeDerivative_norm_le {alpha C : NNReal}
    {Q : Set (ParabolicPoint V)} {u : Real → V → F}
    (h : eParabolicC2HolderGaugeOn alpha Q u ≤ C)
    {p : ParabolicPoint V} (hp : p ∈ Q) :
    ‖parabolicTimeDerivative u p‖ ≤ C := by
  rw [← ENNReal.ofReal_le_coe]
  exact (parabolicTimeDerivative_le alpha Q u p hp).trans h

theorem parabolicSpatialJet_holderWith_restrict {alpha C : NNReal}
    {Q : Set (ParabolicPoint V)} {u : Real → V → F}
    (h : eParabolicC2HolderGaugeOn alpha Q u ≤ C) :
    HolderWith C alpha (Q.restrict (parabolicSpatialJet 2 u)) :=
  holderWith_restrict_of_eHolderSeminormOn_le
    ((parabolicSpatialHolderSeminorm_le alpha Q u).trans h)

theorem parabolicTimeDerivative_holderWith_restrict {alpha C : NNReal}
    {Q : Set (ParabolicPoint V)} {u : Real → V → F}
    (h : eParabolicC2HolderGaugeOn alpha Q u ≤ C) :
    HolderWith C alpha (Q.restrict (parabolicTimeDerivative u)) :=
  holderWith_restrict_of_eHolderSeminormOn_le
    ((parabolicTimeHolderSeminorm_le alpha Q u).trans h)

end Parabolic

end DifferentialGeometry.Analysis.Schauder
