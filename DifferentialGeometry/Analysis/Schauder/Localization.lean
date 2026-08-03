import DifferentialGeometry.Analysis.Schauder.Holder
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Set
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Schauder

variable {X V F : Type*} [MetricSpace X]
  [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

omit [MetricSpace X] [NormedSpace Real F]
    [NormedAddCommGroup V] [NormedSpace Real V] in
theorem eSupNormOn_mono {s t : Set X} (hst : s ⊆ t) (f : X → F) :
    eSupNormOn s f ≤ eSupNormOn t f := by
  apply iSup_le
  intro x
  exact le_iSup_of_le ⟨x, hst x.2⟩ le_rfl

omit [NormedSpace Real F] [NormedAddCommGroup V] [NormedSpace Real V] in
theorem eHolderSeminormOn_mono {s t : Set X} (hst : s ⊆ t)
    (alpha : NNReal) (f : X → F) :
    eHolderSeminormOn alpha s f ≤ eHolderSeminormOn alpha t f := by
  unfold eHolderSeminormOn eHolderNorm
  apply le_iInf
  intro C
  apply le_iInf
  intro hC
  exact HolderWith.eHolderNorm_le
    ((HolderWith.restrict_iff.mp hC).mono hst).holderWith

theorem eContDiffHolderGaugeOn_mono {s t : Set V} (hst : s ⊆ t)
    (k : Nat) (alpha : NNReal) (f : V → F) :
    eContDiffHolderGaugeOn k alpha s f ≤
      eContDiffHolderGaugeOn k alpha t f := by
  unfold eContDiffHolderGaugeOn
  gcongr with j
  · exact eSupNormOn_mono hst _
  · exact eHolderSeminormOn_mono hst alpha _

theorem eParabolicC2HolderGaugeOn_mono
    {Q R : Set (ParabolicPoint V)} (hQR : Q ⊆ R)
    (alpha : NNReal) (u : Real → V → F) :
    eParabolicC2HolderGaugeOn alpha Q u ≤
      eParabolicC2HolderGaugeOn alpha R u := by
  unfold eParabolicC2HolderGaugeOn
  gcongr with j
  · exact eSupNormOn_mono hQR _
  · exact eSupNormOn_mono hQR _
  · exact eHolderSeminormOn_mono hQR alpha _
  · exact eHolderSeminormOn_mono hQR alpha _

omit [NormedSpace Real V] [NormedSpace Real F] in
theorem holderWith_parabolicCylinder_Icc_of_time_support
    {a b S T : Real} (ha : 0 < a) (haT : a ≤ T) (hbT : b < T)
    (hTS : T ≤ S)
    {alpha K : NNReal} (f : ParabolicPoint V → F)
    (hsupport : ∀ p, p.time ∈ Set.Icc (0 : Real) S →
      p.time ∉ Set.Ioo a b → f p = 0)
    (hlocal : HolderWith K alpha
      ((parabolicCylinder (Set.Ioc (0 : Real) T) Set.univ).restrict f)) :
    HolderWith K alpha
      ((parabolicCylinder (Set.Icc (0 : Real) S) Set.univ).restrict f) := by
  let Q := parabolicCylinder (Set.Icc (0 : Real) S) (Set.univ : Set V)
  let U := parabolicCylinder (Set.Ioc (0 : Real) T) (Set.univ : Set V)
  let project : Q → U := fun p ↦
    ⟨parabolicPoint
      ((Set.projIcc a T haT p.1.time : Set.Icc a T) : Real) p.1.space,
      ⟨⟨ha.trans_le (Set.projIcc a T haT p.1.time).2.1,
        (Set.projIcc a T haT p.1.time).2.2⟩, Set.mem_univ p.1.space⟩⟩
  have hproject : LipschitzWith 1 project := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    change dist (project p).1 (project q).1 ≤ (1 : Real) * dist p.1 q.1
    rw [one_mul]
    dsimp only [project]
    change dist
      (parabolicPoint
        ((Set.projIcc a T haT p.1.time : Set.Icc a T) : Real) p.1.space)
      (parabolicPoint
        ((Set.projIcc a T haT q.1.time : Set.Icc a T) : Real) q.1.space) ≤
      dist p.1 q.1
    rw [dist_parabolicPoint, ← parabolicPoint_time_space p.1,
      ← parabolicPoint_time_space q.1, dist_parabolicPoint]
    apply max_le_max
    · exact Real.rpow_le_rpow
        (abs_nonneg _)
        (Set.abs_projIcc_sub_projIcc haT)
        (by norm_num)
    · exact le_rfl
  have hprojectValue : ∀ p : Q, f (project p).1 = f p.1 := by
    intro p
    have hprojectMem : (project p).1.time ∈ Set.Icc (0 : Real) S := by
      exact ⟨le_trans (le_of_lt ha)
          (Set.projIcc a T haT p.1.time).2.1,
        (Set.projIcc a T haT p.1.time).2.2.trans hTS⟩
    by_cases hp : p.1.time ∈ Set.Icc a T
    · have hproj := Set.projIcc_of_mem haT hp
      change f (parabolicPoint
        ((Set.projIcc a T haT p.1.time : Set.Icc a T) : Real) p.1.space) =
          f p.1
      rw [show ((Set.projIcc a T haT p.1.time : Set.Icc a T) : Real) =
        p.1.time from congrArg Subtype.val hproj, parabolicPoint_time_space]
    · by_cases hpa : p.1.time < a
      · have hproj := Set.projIcc_of_le_left haT hpa.le
        have hprojectTime : (project p).1.time = a := by
          change ((Set.projIcc a T haT p.1.time : Set.Icc a T) : Real) = a
          exact congrArg Subtype.val hproj
        rw [hsupport p.1 p.2.1 (fun hmem ↦ (not_lt_of_ge hpa.le) hmem.1),
          hsupport (project p).1 hprojectMem (fun hmem ↦
            (lt_irrefl a) (hprojectTime ▸ hmem.1))]
      · have hpT : T < p.1.time := by
          by_contra hnot
          exact hp ⟨le_of_not_gt hpa, le_of_not_gt hnot⟩
        have hproj := Set.projIcc_of_right_le haT hpT.le
        have hprojectTime : (project p).1.time = T := by
          change ((Set.projIcc a T haT p.1.time : Set.Icc a T) : Real) = T
          exact congrArg Subtype.val hproj
        rw [hsupport p.1 p.2.1 (fun hmem ↦
            (not_lt_of_ge (hbT.le.trans hpT.le)) hmem.2),
          hsupport (project p).1 hprojectMem (fun hmem ↦
            (not_lt_of_ge hbT.le) (hprojectTime ▸ hmem.2))]
  have hcomp := hlocal.comp hproject.holderWith
  have hfun :
      ((parabolicCylinder (Set.Ioc (0 : Real) T) Set.univ).restrict f) ∘
          project = Q.restrict f := by
    funext p
    exact hprojectValue p
  rw [hfun] at hcomp
  simpa only [Q, NNReal.one_rpow, mul_one] using hcomp

omit [NormedAddCommGroup V] [NormedSpace Real V] [NormedSpace Real F] in
theorem eSupNormOn_parabolicCylinder_Icc_le_Ioc_of_time_support
    {a b S T : Real} (ha : 0 < a) (haT : a ≤ T) (hbT : b < T)
    (hTS : T ≤ S)
    (f : ParabolicPoint V → F)
    (hsupport : ∀ p, p.time ∈ Set.Icc (0 : Real) S →
      p.time ∉ Set.Ioo a b → f p = 0) :
    eSupNormOn (parabolicCylinder (Set.Icc (0 : Real) S) Set.univ) f ≤
      eSupNormOn (parabolicCylinder (Set.Ioc (0 : Real) T) Set.univ) f := by
  let Q := parabolicCylinder (Set.Icc (0 : Real) S) (Set.univ : Set V)
  let U := parabolicCylinder (Set.Ioc (0 : Real) T) (Set.univ : Set V)
  let project : Q → U := fun p ↦
    ⟨parabolicPoint
      ((Set.projIcc a T haT p.1.time : Set.Icc a T) : Real) p.1.space,
      ⟨⟨ha.trans_le (Set.projIcc a T haT p.1.time).2.1,
        (Set.projIcc a T haT p.1.time).2.2⟩, Set.mem_univ p.1.space⟩⟩
  have hprojectValue : ∀ p : Q, f (project p).1 = f p.1 := by
    intro p
    have hprojectMem : (project p).1.time ∈ Set.Icc (0 : Real) S := by
      exact ⟨le_trans (le_of_lt ha)
          (Set.projIcc a T haT p.1.time).2.1,
        (Set.projIcc a T haT p.1.time).2.2.trans hTS⟩
    by_cases hp : p.1.time ∈ Set.Icc a T
    · have hproj := Set.projIcc_of_mem haT hp
      change f (parabolicPoint
        ((Set.projIcc a T haT p.1.time : Set.Icc a T) : Real) p.1.space) =
          f p.1
      rw [show ((Set.projIcc a T haT p.1.time : Set.Icc a T) : Real) =
        p.1.time from congrArg Subtype.val hproj, parabolicPoint_time_space]
    · by_cases hpa : p.1.time < a
      · have hproj := Set.projIcc_of_le_left haT hpa.le
        have hprojectTime : (project p).1.time = a := by
          change ((Set.projIcc a T haT p.1.time : Set.Icc a T) : Real) = a
          exact congrArg Subtype.val hproj
        rw [hsupport p.1 p.2.1 (fun hmem ↦ (not_lt_of_ge hpa.le) hmem.1),
          hsupport (project p).1 hprojectMem (fun hmem ↦
            (lt_irrefl a) (hprojectTime ▸ hmem.1))]
      · have hpT : T < p.1.time := by
          by_contra hnot
          exact hp ⟨le_of_not_gt hpa, le_of_not_gt hnot⟩
        have hproj := Set.projIcc_of_right_le haT hpT.le
        have hprojectTime : (project p).1.time = T := by
          change ((Set.projIcc a T haT p.1.time : Set.Icc a T) : Real) = T
          exact congrArg Subtype.val hproj
        rw [hsupport p.1 p.2.1 (fun hmem ↦
            (not_lt_of_ge (hbT.le.trans hpT.le)) hmem.2),
          hsupport (project p).1 hprojectMem (fun hmem ↦
            (not_lt_of_ge hbT.le) (hprojectTime ▸ hmem.2))]
  rw [eSupNormOn_le]
  intro p hp
  rw [← hprojectValue ⟨p, hp⟩]
  exact norm_le_eSupNormOn U f (project ⟨p, hp⟩).1 (project ⟨p, hp⟩).2

omit [NormedSpace Real V] [NormedSpace Real F] in
theorem eHolderSeminormOn_parabolicCylinder_Icc_le_Ioc_of_time_support
    {a b S T : Real} (ha : 0 < a) (haT : a ≤ T) (hbT : b < T)
    (hTS : T ≤ S)
    (alpha : NNReal) (f : ParabolicPoint V → F)
    (hsupport : ∀ p, p.time ∈ Set.Icc (0 : Real) S →
      p.time ∉ Set.Ioo a b → f p = 0) :
    eHolderSeminormOn alpha
        (parabolicCylinder (Set.Icc (0 : Real) S) Set.univ) f ≤
      eHolderSeminormOn alpha
        (parabolicCylinder (Set.Ioc (0 : Real) T) Set.univ) f := by
  unfold eHolderSeminormOn eHolderNorm
  apply le_iInf
  intro C
  apply le_iInf
  intro hC
  exact HolderWith.eHolderNorm_le
    (holderWith_parabolicCylinder_Icc_of_time_support
      ha haT hbT hTS f hsupport hC)

theorem eParabolicC2HolderGaugeOn_Icc_le_Ioc_of_time_support
    {a b S T : Real} (ha : 0 < a) (haT : a ≤ T) (hbT : b < T)
    (hTS : T ≤ S)
    (alpha : NNReal) (u : Real → V → F)
    (hspatialSupport : ∀ j < 3, ∀ p,
      p.time ∈ Set.Icc (0 : Real) S →
        p.time ∉ Set.Ioo a b → parabolicSpatialJet j u p = 0)
    (htimeSupport : ∀ p,
      p.time ∈ Set.Icc (0 : Real) S →
        p.time ∉ Set.Ioo a b → parabolicTimeDerivative u p = 0) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Set.Icc (0 : Real) S) Set.univ) u ≤
      eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Set.Ioc (0 : Real) T) Set.univ) u := by
  unfold eParabolicC2HolderGaugeOn
  gcongr with j hj
  · exact eSupNormOn_parabolicCylinder_Icc_le_Ioc_of_time_support
      ha haT hbT hTS _ (hspatialSupport j (Finset.mem_range.mp hj))
  · exact eSupNormOn_parabolicCylinder_Icc_le_Ioc_of_time_support
      ha haT hbT hTS _ htimeSupport
  · exact eHolderSeminormOn_parabolicCylinder_Icc_le_Ioc_of_time_support
      ha haT hbT hTS alpha _ (hspatialSupport 2 (by norm_num))
  · exact eHolderSeminormOn_parabolicCylinder_Icc_le_Ioc_of_time_support
      ha haT hbT hTS alpha _ htimeSupport

theorem eContDiffHolderGaugeOn_congr {s : Set V} {f g : V → F}
    {k : Nat} (hfg : ∀ j ≤ k,
      Set.EqOn (iteratedFDeriv Real j f) (iteratedFDeriv Real j g) s)
    (alpha : NNReal) :
    eContDiffHolderGaugeOn k alpha s f =
      eContDiffHolderGaugeOn k alpha s g := by
  unfold eContDiffHolderGaugeOn
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    exact eSupNormOn_congr
      (hfg j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
  · exact eHolderSeminormOn_congr (hfg k le_rfl) alpha

theorem eParabolicC2HolderGaugeOn_congr
    {Q : Set (ParabolicPoint V)} {u v : Real → V → F}
    (hspatial : ∀ j ≤ 2,
      Set.EqOn (parabolicSpatialJet j u) (parabolicSpatialJet j v) Q)
    (htime : Set.EqOn (parabolicTimeDerivative u)
      (parabolicTimeDerivative v) Q)
    (alpha : NNReal) :
    eParabolicC2HolderGaugeOn alpha Q u =
      eParabolicC2HolderGaugeOn alpha Q v := by
  have hsum :
      (∑ j ∈ Finset.range 3,
        eSupNormOn Q (parabolicSpatialJet j u)) =
      ∑ j ∈ Finset.range 3,
        eSupNormOn Q (parabolicSpatialJet j v) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact eSupNormOn_congr
      (hspatial j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
  have hsupTime : eSupNormOn Q (parabolicTimeDerivative u) =
      eSupNormOn Q (parabolicTimeDerivative v) :=
    eSupNormOn_congr htime
  have hholderSpatial :
      eHolderSeminormOn alpha Q (parabolicSpatialJet 2 u) =
        eHolderSeminormOn alpha Q (parabolicSpatialJet 2 v) :=
    eHolderSeminormOn_congr (hspatial 2 le_rfl) alpha
  have hholderTime :
      eHolderSeminormOn alpha Q (parabolicTimeDerivative u) =
        eHolderSeminormOn alpha Q (parabolicTimeDerivative v) :=
    eHolderSeminormOn_congr htime alpha
  unfold eParabolicC2HolderGaugeOn
  rw [hsum, hsupTime, hholderSpatial, hholderTime]

theorem eParabolicC2HolderGaugeOn_congr_of_eqOn_open
    {Q U : Set (ParabolicPoint V)} (hU : IsOpen U) (hQU : Q ⊆ U)
    {u v : Real → V → F}
    (huv : Set.EqOn (fun p ↦ u p.time p.space)
      (fun p ↦ v p.time p.space) U)
    (alpha : NNReal) :
    eParabolicC2HolderGaugeOn alpha Q u =
      eParabolicC2HolderGaugeOn alpha Q v := by
  apply eParabolicC2HolderGaugeOn_congr
  · intro j _hj p hp
    have hmap : ContinuousAt
        (fun x ↦ parabolicPoint p.time x) p.space := by
      unfold parabolicPoint
      exact (continuous_const.prodMk continuous_id).continuousAt
    have heq : u p.time =ᶠ[nhds p.space] v p.time := by
      filter_upwards [hmap (hU.mem_nhds (hQU hp))] with x hx
      exact huv hx
    unfold parabolicSpatialJet
    exact (Filter.EventuallyEq.iteratedFDeriv Real heq j).eq_of_nhds
  · intro p hp
    have hmap : ContinuousAt
        (fun t ↦ parabolicPoint t p.space) p.time := by
      unfold parabolicPoint
      exact (Metric.Snowflaking.continuous_toSnowflaking.prodMk
        continuous_const).continuousAt
    have heq : (fun t ↦ u t p.space) =ᶠ[nhds p.time]
        fun t ↦ v t p.space := by
      filter_upwards [hmap (hU.mem_nhds (hQU hp))] with t ht
      exact huv ht
    unfold parabolicTimeDerivative
    rw [heq.fderiv_eq]

theorem eContDiffHolderGaugeOn_congr_of_eqOn_open
    {s U : Set V} (hU : IsOpen U) (hsU : s ⊆ U)
    {f g : V → F} (hfg : Set.EqOn f g U)
    (k : Nat) (alpha : NNReal) :
    eContDiffHolderGaugeOn k alpha s f =
      eContDiffHolderGaugeOn k alpha s g := by
  apply eContDiffHolderGaugeOn_congr
  intro j hj x hx
  have heq : f =ᶠ[nhds x] g :=
    Filter.mem_of_superset (hU.mem_nhds (hsU hx)) hfg
  exact (Filter.EventuallyEq.iteratedFDeriv Real heq j).eq_of_nhds

def holderBallOscillationConst (R : Real) (alpha K : NNReal) : NNReal :=
  K * (Real.toNNReal R) ^ (alpha : Real)

omit [NormedSpace Real F] [NormedAddCommGroup V] [NormedSpace Real V] in
theorem norm_sub_le_holderBallOscillationConst_of_mem_ball
    {center x : X} {R : Real} (hR : 0 < R)
    {alpha K : NNReal} {f : X → F}
    (hf : HolderWith K alpha ((Metric.ball center R).restrict f))
    (hx : x ∈ Metric.ball center R) :
    ‖f center - f x‖ ≤ holderBallOscillationConst R alpha K := by
  have hcenter : center ∈ Metric.ball center R := by
    simpa only [Metric.mem_ball, dist_self] using hR
  have hraw := hf.dist_le
    (⟨center, hcenter⟩ : Metric.ball center R)
    (⟨x, hx⟩ : Metric.ball center R)
  have hdist : dist center x ≤ R := by
    simpa only [dist_comm] using (Metric.mem_ball.mp hx).le
  have hrpow : dist center x ^ (alpha : Real) ≤ R ^ (alpha : Real) :=
    Real.rpow_le_rpow (dist_nonneg) hdist alpha.coe_nonneg
  calc
    ‖f center - f x‖ = dist (f center) (f x) := (dist_eq_norm _ _).symm
    _ ≤ (K : Real) * dist center x ^ (alpha : Real) := by
      simpa only [Set.restrict_apply, Subtype.dist_eq] using hraw
    _ ≤ (K : Real) * R ^ (alpha : Real) :=
      mul_le_mul_of_nonneg_left hrpow K.coe_nonneg
    _ = holderBallOscillationConst R alpha K := by
      simp only [holderBallOscillationConst, NNReal.coe_mul, NNReal.coe_rpow,
        Real.coe_toNNReal R hR.le]

theorem holderWith_smul_of_norm_le
    {alpha C D M N : NNReal} {f : X → Real} {g : X → F}
    (hf : HolderWith C alpha f) (hg : HolderWith D alpha g)
    (hfnorm : ∀ x, ‖f x‖ ≤ M) (hgnorm : ∀ x, ‖g x‖ ≤ N) :
    HolderWith (M * D + N * C) alpha (f • g) := by
  intro x y
  rw [edist_dist, edist_dist]
  have hreal : dist (f x • g x) (f y • g y) ≤
      ((M * D + N * C : NNReal) : Real) *
        dist x y ^ (alpha : Real) := by
    rw [dist_eq_norm]
    calc
      ‖f x • g x - f y • g y‖ =
          ‖f x • (g x - g y) + (f x - f y) • g y‖ := by
        congr 1
        module
      _ ≤ ‖f x • (g x - g y)‖ +
          ‖(f x - f y) • g y‖ := norm_add_le _ _
      _ ≤ (M : Real) * ((D : Real) * dist x y ^ (alpha : Real)) +
          ((C : Real) * dist x y ^ (alpha : Real)) * (N : Real) := by
        rw [norm_smul, norm_smul]
        gcongr
        · simpa only [Real.norm_eq_abs] using hfnorm x
        · simpa only [dist_eq_norm] using hg.dist_le x y
        · simpa only [Real.dist_eq] using hf.dist_le x y
        · exact hgnorm y
      _ = ((M * D + N * C : NNReal) : Real) *
          dist x y ^ (alpha : Real) := by
        push_cast
        ring
  calc
    ENNReal.ofReal (dist (f x • g x) (f y • g y)) ≤
        ENNReal.ofReal (((M * D + N * C : NNReal) : Real) *
          dist x y ^ (alpha : Real)) := ENNReal.ofReal_le_ofReal hreal
    _ = ((M * D + N * C : NNReal) : ENNReal) *
        ENNReal.ofReal (dist x y ^ (alpha : Real)) := by
      rw [ENNReal.ofReal_mul (by positivity :
        (0 : Real) ≤ ((M * D + N * C : NNReal) : Real))]
      congr 1
      exact ENNReal.ofReal_coe_nnreal
    _ = ((M * D + N * C : NNReal) : ENNReal) *
        ENNReal.ofReal (dist x y) ^ (alpha : Real) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) alpha.coe_nonneg]

theorem holderWith_comp_continuousLinearMap_of_norm_le_one
    {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace Real A]
    [NormedAddCommGroup B] [NormedSpace Real B]
    {alpha K : NNReal} {f : X → A}
    (L : A →L[Real] B) (hL : ‖L‖ ≤ 1)
    (hf : HolderWith K alpha f) :
    HolderWith K alpha (fun x ↦ L (f x)) := by
  have hraw := L.lipschitz.holderWith.comp hf
  have hraw' : HolderWith (‖L‖₊ * K) alpha (fun x ↦ L (f x)) := by
    simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul, Function.comp_apply] using hraw
  have hnorm : ‖L‖₊ * K ≤ K := by
    apply mul_le_of_le_one_left (zero_le K)
    exact_mod_cast hL
  exact hraw'.mono hnorm

omit [NormedSpace Real F] in
theorem holderWith_finset_sum
    {I : Type*} {alpha : NNReal} {K : I → NNReal} {f : I → X → F}
    (s : Finset I) (h : ∀ i ∈ s, HolderWith (K i) alpha (f i)) :
    HolderWith (∑ i ∈ s, K i) alpha (fun x ↦ ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        (HolderWith.zero : HolderWith 0 alpha (0 : X → F))
  | @insert i s hi ih =>
      have hi' := h i (Finset.mem_insert_self i s)
      have hs' := ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj)
      simpa only [Finset.sum_insert hi, Pi.add_apply] using hi'.add hs'

theorem holderWith_of_hasFDerivAt_of_norm_le
    {A : Type*} [NormedAddCommGroup A] [NormedSpace Real A]
    {f : V → A} {df : V → V →L[Real] A}
    {alpha M N : NNReal}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hf : ∀ x, HasFDerivAt f (df x) x)
    (hfnorm : ∀ x, ‖f x‖ ≤ M)
    (hdfnorm : ∀ x, ‖df x‖ ≤ N) :
    HolderWith (max (2 * M) N) alpha f := by
  have hlip : LipschitzWith N f := by
    apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := Real)
    · exact fun x ↦ (hf x).differentiableAt
    · intro x
      rw [(hf x).fderiv]
      exact_mod_cast hdfnorm x
  have hzero : HolderWith (2 * M) 0 f :=
    holderWith_zero_of_norm_le hfnorm
  exact hzero.of_le_of_le hlip.holderWith halpha0 halpha1

theorem eHolderSeminormOn_smul_le
    {s : Set X} {alpha C D M N : NNReal}
    {f : X → Real} {g : X → F}
    (hf : HolderWith C alpha (s.restrict f))
    (hg : HolderWith D alpha (s.restrict g))
    (hfnorm : ∀ x ∈ s, ‖f x‖ ≤ M)
    (hgnorm : ∀ x ∈ s, ‖g x‖ ≤ N) :
    eHolderSeminormOn alpha s (f • g) ≤ M * D + N * C := by
  apply HolderWith.eHolderNorm_le
  have hproduct := holderWith_smul_of_norm_le hf hg
    (fun x ↦ hfnorm x x.2) (fun x ↦ hgnorm x x.2)
  simpa only [Pi.smul_apply] using hproduct

end DifferentialGeometry.Analysis.Schauder

end
