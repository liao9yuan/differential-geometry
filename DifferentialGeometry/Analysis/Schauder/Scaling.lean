import DifferentialGeometry.Analysis.Schauder.Holder

noncomputable section

open Set
open scoped NNReal

namespace DifferentialGeometry.Analysis.Schauder

def parabolicDilation {V : Type*} [SMul Real V]
    (r : NNReal) (p : ParabolicPoint V) : ParabolicPoint V :=
  parabolicPoint ((r : Real) ^ 2 * p.time) ((r : Real) • p.space)

def parabolicTranslation {V : Type*} [Add V]
    (p0 p : ParabolicPoint V) : ParabolicPoint V :=
  parabolicPoint (p0.time + p.time) (p0.space + p.space)

def parabolicDilationAt {V : Type*} [Add V] [SMul Real V]
    (r : NNReal) (p0 p : ParabolicPoint V) : ParabolicPoint V :=
  parabolicTranslation p0 (parabolicDilation r p)

@[simp]
theorem parabolicDilation_time {V : Type*} [SMul Real V]
    (r : NNReal) (p : ParabolicPoint V) :
    (parabolicDilation r p).time = (r : Real) ^ 2 * p.time := rfl

@[simp]
theorem parabolicDilation_space {V : Type*} [SMul Real V]
    (r : NNReal) (p : ParabolicPoint V) :
    (parabolicDilation r p).space = (r : Real) • p.space := rfl

@[simp]
theorem parabolicTranslation_time {V : Type*} [Add V]
    (p0 p : ParabolicPoint V) :
    (parabolicTranslation p0 p).time = p0.time + p.time := rfl

@[simp]
theorem parabolicTranslation_space {V : Type*} [Add V]
    (p0 p : ParabolicPoint V) :
    (parabolicTranslation p0 p).space = p0.space + p.space := rfl

@[simp]
theorem parabolicDilationAt_time {V : Type*} [Add V] [SMul Real V]
    (r : NNReal) (p0 p : ParabolicPoint V) :
    (parabolicDilationAt r p0 p).time =
      p0.time + (r : Real) ^ 2 * p.time := rfl

@[simp]
theorem parabolicDilationAt_space {V : Type*} [Add V] [SMul Real V]
    (r : NNReal) (p0 p : ParabolicPoint V) :
    (parabolicDilationAt r p0 p).space =
      p0.space + (r : Real) • p.space := rfl

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

theorem dist_parabolicTranslation {V : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] (p0 p q : ParabolicPoint V) :
    dist (parabolicTranslation p0 p) (parabolicTranslation p0 q) =
      dist p q := by
  rcases p0 with ⟨⟨t0⟩, x0⟩
  rcases p with ⟨⟨t⟩, x⟩
  rcases q with ⟨⟨s⟩, y⟩
  simp only [parabolicTranslation, dist_parabolicPoint]
  rw [add_sub_add_left_eq_sub, dist_add_left]
  rfl

theorem dist_parabolicDilationAt {V : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] (r : NNReal) (p0 p q : ParabolicPoint V) :
    dist (parabolicDilationAt r p0 p) (parabolicDilationAt r p0 q) =
      (r : Real) * dist p q := by
  change dist (parabolicTranslation p0 (parabolicDilation r p))
    (parabolicTranslation p0 (parabolicDilation r q)) = _
  rw [dist_parabolicTranslation,
    dist_parabolicDilation]

@[simp]
theorem parabolicDilationAt_origin {V : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] (r : NNReal) (p0 : ParabolicPoint V) :
    parabolicDilationAt r p0 (parabolicPoint 0 0) = p0 := by
  rw [← parabolicPoint_time_space p0]
  simp [parabolicDilationAt, parabolicTranslation, parabolicDilation]

def parabolicPreimage {V : Type*} [SMul Real V]
    (r : NNReal) (Q : Set (ParabolicPoint V)) : Set (ParabolicPoint V) :=
  parabolicDilation r ⁻¹' Q

def parabolicPreimageAt {V : Type*} [Add V] [SMul Real V]
    (r : NNReal) (p0 : ParabolicPoint V)
    (Q : Set (ParabolicPoint V)) : Set (ParabolicPoint V) :=
  parabolicDilationAt r p0 ⁻¹' Q

def parabolicRescale {V F : Type*} [SMul Real V]
    (r : NNReal) (u : Real → V → F) : Real → V → F :=
  fun t x ↦ u ((r : Real) ^ 2 * t) ((r : Real) • x)

def parabolicRescaleAt {V F : Type*} [Add V] [SMul Real V]
    (r : NNReal) (p0 : ParabolicPoint V) (u : Real → V → F) :
    Real → V → F :=
  fun t x ↦ u (p0.time + (r : Real) ^ 2 * t)
    (p0.space + (r : Real) • x)

def parabolicSourceRescaleAt
    {V F : Type*} [Add V] [SMul Real V] [SMul Real F]
    (r : NNReal) (p0 : ParabolicPoint V) (f : ParabolicPoint V → F) :
    ParabolicPoint V → F :=
  fun p ↦ (r : Real) ^ 2 • f (parabolicDilationAt r p0 p)

@[simp]
theorem parabolicRescale_apply {V F : Type*} [SMul Real V]
    (r : NNReal) (u : Real → V → F) (t : Real) (x : V) :
    parabolicRescale r u t x =
      u ((r : Real) ^ 2 * t) ((r : Real) • x) := rfl

@[simp]
theorem parabolicRescaleAt_apply {V F : Type*} [Add V] [SMul Real V]
    (r : NNReal) (p0 : ParabolicPoint V) (u : Real → V → F)
    (t : Real) (x : V) :
    parabolicRescaleAt r p0 u t x =
      u (p0.time + (r : Real) ^ 2 * t)
        (p0.space + (r : Real) • x) := rfl

@[simp]
theorem parabolicSourceRescaleAt_apply
    {V F : Type*} [Add V] [SMul Real V] [SMul Real F]
    (r : NNReal) (p0 : ParabolicPoint V) (f : ParabolicPoint V → F)
    (p : ParabolicPoint V) :
    parabolicSourceRescaleAt r p0 f p =
      (r : Real) ^ 2 • f (parabolicDilationAt r p0 p) := rfl

theorem parabolicDilation_mapsTo_preimage {V : Type*} [SMul Real V]
    (r : NNReal) (Q : Set (ParabolicPoint V)) :
    MapsTo (parabolicDilation r) (parabolicPreimage r Q) Q :=
  fun _ hp => hp

theorem parabolicDilationAt_mapsTo_preimage
    {V : Type*} [Add V] [SMul Real V]
    (r : NNReal) (p0 : ParabolicPoint V) (Q : Set (ParabolicPoint V)) :
    MapsTo (parabolicDilationAt r p0) (parabolicPreimageAt r p0 Q) Q :=
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

theorem parabolicHolder_dilationAt
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [MetricSpace F] {alpha C : NNReal} {Q : Set (ParabolicPoint V)}
    {f : ParabolicPoint V → F} (r : NNReal) (p0 : ParabolicPoint V)
    (hf : HolderWith C alpha (Q.restrict f)) :
    HolderWith (C * r ^ (alpha : Real)) alpha
      ((parabolicPreimageAt r p0 Q).restrict
        (f ∘ parabolicDilationAt r p0)) := by
  intro p q
  change edist (f (parabolicDilationAt r p0 p.1))
      (f (parabolicDilationAt r p0 q.1)) ≤ _
  have hpQ : parabolicDilationAt r p0 p.1 ∈ Q := p.2
  have hqQ : parabolicDilationAt r p0 q.1 ∈ Q := q.2
  have hdist := hf.edist_le
    (x := ⟨parabolicDilationAt r p0 p.1, hpQ⟩)
    (y := ⟨parabolicDilationAt r p0 q.1, hqQ⟩)
  change edist (f (parabolicDilationAt r p0 p.1))
      (f (parabolicDilationAt r p0 q.1)) ≤
    (C : ENNReal) * edist (parabolicDilationAt r p0 p.1)
      (parabolicDilationAt r p0 q.1) ^ (alpha : Real) at hdist
  rw [edist_dist, edist_dist, dist_parabolicDilationAt r] at hdist
  rw [edist_dist, edist_dist]
  change ENNReal.ofReal (dist (f (parabolicDilationAt r p0 p.1))
      (f (parabolicDilationAt r p0 q.1))) ≤
    (C * r ^ (alpha : Real) : NNReal) *
      ENNReal.ofReal (dist p.1 q.1) ^ (alpha : Real)
  simp only [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ alpha.coe_nonneg]
  calc
    ENNReal.ofReal (dist (f (parabolicDilationAt r p0 p.1))
      (f (parabolicDilationAt r p0 q.1))) ≤
        C * ENNReal.ofReal ((r : Real) * dist p.1 q.1) ^
          (alpha : Real) := hdist
    _ = (C * (r : ENNReal) ^ (alpha : Real)) *
        ENNReal.ofReal (dist p.1 q.1) ^ (alpha : Real) := by
      rw [ENNReal.ofReal_mul r.coe_nonneg, ENNReal.ofReal_coe_nnreal,
        ENNReal.mul_rpow_of_nonneg _ _ alpha.coe_nonneg]
      ring

theorem parabolicDilationAt_mapsTo_ball
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    (r : NNReal) (hr : 0 < r) (R : Real) (p0 : ParabolicPoint V) :
    MapsTo (parabolicDilationAt r p0)
      (Metric.ball (parabolicPoint 0 0) R)
      (Metric.ball p0 ((r : Real) * R)) := by
  intro p hp
  rw [Metric.mem_ball]
  have hcenter := parabolicDilationAt_origin r p0
  calc
    dist (parabolicDilationAt r p0 p) p0 =
        dist (parabolicDilationAt r p0 p)
          (parabolicDilationAt r p0 (parabolicPoint 0 0)) := by
      rw [hcenter]
    _ = (r : Real) * dist p (parabolicPoint 0 0) :=
      dist_parabolicDilationAt r p0 p (parabolicPoint 0 0)
    _ < (r : Real) * R :=
      mul_lt_mul_of_pos_left (Metric.mem_ball.mp hp) hr

theorem parabolicDilationAt_mapsTo_unitBall
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    (r : NNReal) (hr : 0 < r) (p0 : ParabolicPoint V) :
    MapsTo (parabolicDilationAt r p0)
      (Metric.ball (parabolicPoint 0 0) 1) (Metric.ball p0 r) := by
  intro p hp
  rw [Metric.mem_ball]
  have hcenter := parabolicDilationAt_origin r p0
  calc
    dist (parabolicDilationAt r p0 p) p0 =
        dist (parabolicDilationAt r p0 p)
          (parabolicDilationAt r p0 (parabolicPoint 0 0)) := by
      rw [hcenter]
    _ = (r : Real) * dist p (parabolicPoint 0 0) :=
      dist_parabolicDilationAt r p0 p (parabolicPoint 0 0)
    _ < (r : Real) * 1 :=
      mul_lt_mul_of_pos_left (Metric.mem_ball.mp hp) hr
    _ = (r : Real) := by ring

theorem parabolicHolder_dilationAt_ball
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [MetricSpace F] {alpha C : NNReal} (r : NNReal) (hr : 0 < r)
    (R : Real) (p0 : ParabolicPoint V) {f : ParabolicPoint V → F}
    (hf : HolderWith C alpha
      ((Metric.ball p0 ((r : Real) * R)).restrict f)) :
    HolderWith (C * r ^ (alpha : Real)) alpha
      ((Metric.ball (parabolicPoint 0 0) R).restrict
        (f ∘ parabolicDilationAt r p0)) := by
  have hadapt := parabolicHolder_dilationAt r p0 hf
  exact ((HolderWith.restrict_iff.mp hadapt).mono
    (parabolicDilationAt_mapsTo_ball r hr R p0)).holderWith

theorem parabolicHolder_dilationAt_unitBall
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [MetricSpace F] {alpha C : NNReal} (r : NNReal) (hr : 0 < r)
    (p0 : ParabolicPoint V) {f : ParabolicPoint V → F}
    (hf : HolderWith C alpha ((Metric.ball p0 r).restrict f)) :
    HolderWith (C * r ^ (alpha : Real)) alpha
      ((Metric.ball (parabolicPoint 0 0) 1).restrict
        (f ∘ parabolicDilationAt r p0)) := by
  have hadapt := parabolicHolder_dilationAt r p0 hf
  exact ((HolderWith.restrict_iff.mp hadapt).mono
    (parabolicDilationAt_mapsTo_unitBall r hr p0)).holderWith

theorem parabolicSourceRescaleAt_holderWith_unitBall
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    {alpha K : NNReal} (r : NNReal) (hr : 0 < r)
    (p0 : ParabolicPoint V) (f : ParabolicPoint V → F)
    (hf : HolderWith K alpha ((Metric.ball p0 r).restrict f)) :
    HolderWith (K * r ^ (alpha : Real) * r ^ 2) alpha
      ((Metric.ball (parabolicPoint 0 0) 1).restrict
        (parabolicSourceRescaleAt r p0 f)) := by
  have hadapt := parabolicHolder_dilationAt_unitBall r hr p0 hf
  have hscaled := hadapt.smul ((r : Real) ^ 2)
  have hrnorm : ‖(r : Real) ^ 2‖₊ = r ^ 2 := by
    ext
    simp only [coe_nnnorm, Real.norm_of_nonneg (sq_nonneg (r : Real)),
      NNReal.coe_pow]
  rw [hrnorm] at hscaled
  simpa only [parabolicSourceRescaleAt, Function.comp_apply,
    Set.restrict_apply, Pi.smul_apply] using hscaled

theorem norm_parabolicSourceRescaleAt_le_of_mem_unitBall
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (r : NNReal) (hr : 0 < r) (p0 : ParabolicPoint V)
    (f : ParabolicPoint V → F) (B : NNReal)
    (hf : ∀ p, p ∈ Metric.ball p0 r → ‖f p‖ ≤ B)
    (p : ParabolicPoint V)
    (hp : p ∈ Metric.ball (parabolicPoint 0 0) 1) :
    ‖parabolicSourceRescaleAt r p0 f p‖ ≤ r ^ 2 * B := by
  have hmap := parabolicDilationAt_mapsTo_unitBall r hr p0 hp
  rw [parabolicSourceRescaleAt_apply, norm_smul,
    Real.norm_of_nonneg (sq_nonneg (r : Real))]
  calc
    (r : Real) ^ 2 * ‖f (parabolicDilationAt r p0 p)‖ ≤
        (r : Real) ^ 2 * B :=
      mul_le_mul_of_nonneg_left (hf _ hmap) (sq_nonneg (r : Real))
    _ = (r ^ 2 * B : NNReal) := by
      simp only [NNReal.coe_mul, NNReal.coe_pow]

theorem parabolicSpatialJet_rescale
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (r : NNReal) (u : Real → V → F) (j : Nat)
    (p : ParabolicPoint V)
    (hspace : ContDiff Real j (u ((r : Real) ^ 2 * p.time))) :
    parabolicSpatialJet j (parabolicRescale r u) p =
      (r : Real) ^ j •
        parabolicSpatialJet j u (parabolicDilation r p) := by
  unfold parabolicSpatialJet parabolicRescale
  have h := iteratedFDeriv_comp_const_smul (r : Real) hspace
  exact congrFun h p.space

theorem parabolicTimeDerivative_rescale
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (r : NNReal) (u : Real → V → F) (p : ParabolicPoint V) :
    parabolicTimeDerivative (parabolicRescale r u) p =
      (r : Real) ^ 2 •
        parabolicTimeDerivative u (parabolicDilation r p) := by
  unfold parabolicTimeDerivative parabolicRescale
  have h := fderiv_comp_smul
    (f := fun t ↦ u t ((r : Real) • p.space))
    (x := p.time) ((r : Real) ^ 2)
  simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul, mul_one] using
    congrArg (fun L : Real →L[Real] F ↦ L 1) h

theorem parabolicSpatialJet_rescaleAt
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (r : NNReal) (p0 : ParabolicPoint V) (u : Real → V → F)
    (j : Nat) (p : ParabolicPoint V)
    (hspace : ContDiff Real j
      (u (p0.time + (r : Real) ^ 2 * p.time))) :
    parabolicSpatialJet j (parabolicRescaleAt r p0 u) p =
      (r : Real) ^ j •
        parabolicSpatialJet j u (parabolicDilationAt r p0 p) := by
  unfold parabolicSpatialJet parabolicRescaleAt
  have htranslated : ContDiff Real j
      (fun x ↦ u (p0.time + (r : Real) ^ 2 * p.time) (p0.space + x)) :=
    hspace.comp (contDiff_const.add contDiff_id)
  have h := iteratedFDeriv_comp_const_smul (r : Real) htranslated
  simpa only [iteratedFDeriv_comp_add_left] using congrFun h p.space

theorem parabolicTimeDerivative_rescaleAt
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (r : NNReal) (p0 : ParabolicPoint V) (u : Real → V → F)
    (p : ParabolicPoint V) :
    parabolicTimeDerivative (parabolicRescaleAt r p0 u) p =
      (r : Real) ^ 2 •
        parabolicTimeDerivative u (parabolicDilationAt r p0 p) := by
  unfold parabolicTimeDerivative parabolicRescaleAt
  let f : Real → F := fun t ↦
    u (p0.time + t) (p0.space + (r : Real) • p.space)
  have h := fderiv_comp_smul (f := f) (x := p.time) ((r : Real) ^ 2)
  have htranslate : fderiv Real f ((r : Real) ^ 2 * p.time) =
      fderiv Real
        (fun t ↦ u t (p0.space + (r : Real) • p.space))
        (p0.time + (r : Real) ^ 2 * p.time) := by
    simpa only [f] using fderiv_comp_add_left
      (f := fun t ↦ u t (p0.space + (r : Real) • p.space))
      (x := (r : Real) ^ 2 * p.time) p0.time
  change fderiv Real (fun t ↦ f ((r : Real) ^ 2 * t)) p.time =
    (r : Real) ^ 2 • fderiv Real f ((r : Real) ^ 2 * p.time) at h
  rw [htranslate] at h
  simpa only [f, ContinuousLinearMap.smul_apply, smul_eq_mul, mul_one] using
    congrArg (fun L : Real →L[Real] F ↦ L 1) h

def parabolicC2HolderRescaleConst
    (r alpha C : NNReal) : NNReal :=
  (∑ j ∈ Finset.range 3, r ^ j * C) + r ^ 2 * C +
    C * r ^ (alpha : Real) * r ^ 2 +
      C * r ^ (alpha : Real) * r ^ 2

theorem eParabolicC2HolderGaugeOn_rescale_le
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (r alpha C : NNReal) (Q : Set (ParabolicPoint V))
    (u : Real → V → F) (hspace : ∀ t, ContDiff Real 2 (u t))
    (h : eParabolicC2HolderGaugeOn alpha Q u ≤ C) :
    eParabolicC2HolderGaugeOn alpha (parabolicPreimage r Q)
      (parabolicRescale r u) ≤
        parabolicC2HolderRescaleConst r alpha C := by
  let Cspatial : Nat → NNReal := fun j ↦ r ^ j * C
  have hspatial : ∀ j < 3, ∀ p ∈ parabolicPreimage r Q,
      ‖parabolicSpatialJet j (parabolicRescale r u) p‖ ≤ Cspatial j := by
    intro j hj p hp
    rw [parabolicSpatialJet_rescale r u j p
      ((hspace _).of_le (by
        exact_mod_cast Nat.le_of_lt_succ hj))]
    calc
      ‖(r : Real) ^ j • parabolicSpatialJet j u (parabolicDilation r p)‖ =
          (r : Real) ^ j *
            ‖parabolicSpatialJet j u (parabolicDilation r p)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (pow_nonneg r.coe_nonneg j)]
      _ ≤ (r : Real) ^ j * C :=
        mul_le_mul_of_nonneg_left
          (parabolicSpatialJet_norm_le h (by omega) hp)
          (pow_nonneg r.coe_nonneg j)
      _ = (Cspatial j : Real) := by
        simp only [Cspatial, NNReal.coe_mul, NNReal.coe_pow]
  have htime : ∀ p ∈ parabolicPreimage r Q,
      ‖parabolicTimeDerivative (parabolicRescale r u) p‖ ≤
        ((r ^ 2 * C : NNReal) : Real) := by
    intro p hp
    rw [parabolicTimeDerivative_rescale r u p]
    calc
      ‖(r : Real) ^ 2 • parabolicTimeDerivative u (parabolicDilation r p)‖ =
          (r : Real) ^ 2 *
            ‖parabolicTimeDerivative u (parabolicDilation r p)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (sq_nonneg (r : Real))]
      _ ≤ (r : Real) ^ 2 * C :=
        mul_le_mul_of_nonneg_left
          (parabolicTimeDerivative_norm_le h hp) (sq_nonneg (r : Real))
      _ = (r ^ 2 * C : NNReal) := by
        simp only [NNReal.coe_mul, NNReal.coe_pow]
  have hspatialHolder : HolderWith
      (C * r ^ (alpha : Real) * r ^ 2) alpha
      ((parabolicPreimage r Q).restrict
        (parabolicSpatialJet 2 (parabolicRescale r u))) := by
    have hadapt := parabolicHolder_dilation r
      (parabolicSpatialJet_holderWith_restrict h)
    have hscaled := hadapt.smul ((r : Real) ^ 2)
    have hrnorm : ‖(r : Real) ^ 2‖₊ = r ^ 2 := by
      ext
      simp only [coe_nnnorm, Real.norm_of_nonneg (sq_nonneg (r : Real)),
        NNReal.coe_pow]
    convert hscaled using 1
    · rw [hrnorm]
    · funext p
      simp only [Pi.smul_apply, Function.comp_apply, Set.restrict_apply]
      exact (parabolicSpatialJet_rescale r u 2 p.1
        ((hspace _).of_le le_rfl))
  have htimeHolder : HolderWith
      (C * r ^ (alpha : Real) * r ^ 2) alpha
      ((parabolicPreimage r Q).restrict
        (parabolicTimeDerivative (parabolicRescale r u))) := by
    have hadapt := parabolicHolder_dilation r
      (parabolicTimeDerivative_holderWith_restrict h)
    have hscaled := hadapt.smul ((r : Real) ^ 2)
    have hrnorm : ‖(r : Real) ^ 2‖₊ = r ^ 2 := by
      ext
      simp only [coe_nnnorm, Real.norm_of_nonneg (sq_nonneg (r : Real)),
        NNReal.coe_pow]
    convert hscaled using 1
    · rw [hrnorm]
    · funext p
      simp only [Pi.smul_apply, Function.comp_apply, Set.restrict_apply]
      exact parabolicTimeDerivative_rescale r u p.1
  have hresult := eParabolicC2HolderGaugeOn_le Cspatial (r ^ 2 * C)
    (C * r ^ (alpha : Real) * r ^ 2)
    (C * r ^ (alpha : Real) * r ^ 2)
    hspatial htime hspatialHolder htimeHolder
  unfold parabolicC2HolderRescaleConst
  simpa only [Cspatial] using hresult

theorem eParabolicC2HolderGaugeOn_rescaleAt_le
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (r alpha C : NNReal) (p0 : ParabolicPoint V)
    (Q : Set (ParabolicPoint V))
    (u : Real → V → F) (hspace : ∀ t, ContDiff Real 2 (u t))
    (h : eParabolicC2HolderGaugeOn alpha Q u ≤ C) :
    eParabolicC2HolderGaugeOn alpha (parabolicPreimageAt r p0 Q)
      (parabolicRescaleAt r p0 u) ≤
        parabolicC2HolderRescaleConst r alpha C := by
  let Cspatial : Nat → NNReal := fun j ↦ r ^ j * C
  have hspatial : ∀ j < 3, ∀ p ∈ parabolicPreimageAt r p0 Q,
      ‖parabolicSpatialJet j (parabolicRescaleAt r p0 u) p‖ ≤
        Cspatial j := by
    intro j hj p hp
    rw [parabolicSpatialJet_rescaleAt r p0 u j p
      ((hspace _).of_le (by exact_mod_cast Nat.le_of_lt_succ hj))]
    calc
      ‖(r : Real) ^ j • parabolicSpatialJet j u
          (parabolicDilationAt r p0 p)‖ =
          (r : Real) ^ j *
            ‖parabolicSpatialJet j u (parabolicDilationAt r p0 p)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (pow_nonneg r.coe_nonneg j)]
      _ ≤ (r : Real) ^ j * C :=
        mul_le_mul_of_nonneg_left
          (parabolicSpatialJet_norm_le h (by omega) hp)
          (pow_nonneg r.coe_nonneg j)
      _ = (Cspatial j : Real) := by
        simp only [Cspatial, NNReal.coe_mul, NNReal.coe_pow]
  have htime : ∀ p ∈ parabolicPreimageAt r p0 Q,
      ‖parabolicTimeDerivative (parabolicRescaleAt r p0 u) p‖ ≤
        ((r ^ 2 * C : NNReal) : Real) := by
    intro p hp
    rw [parabolicTimeDerivative_rescaleAt r p0 u p]
    calc
      ‖(r : Real) ^ 2 • parabolicTimeDerivative u
          (parabolicDilationAt r p0 p)‖ =
          (r : Real) ^ 2 *
            ‖parabolicTimeDerivative u (parabolicDilationAt r p0 p)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (sq_nonneg (r : Real))]
      _ ≤ (r : Real) ^ 2 * C :=
        mul_le_mul_of_nonneg_left
          (parabolicTimeDerivative_norm_le h hp) (sq_nonneg (r : Real))
      _ = (r ^ 2 * C : NNReal) := by
        simp only [NNReal.coe_mul, NNReal.coe_pow]
  have hspatialHolder : HolderWith
      (C * r ^ (alpha : Real) * r ^ 2) alpha
      ((parabolicPreimageAt r p0 Q).restrict
        (parabolicSpatialJet 2 (parabolicRescaleAt r p0 u))) := by
    have hadapt := parabolicHolder_dilationAt r p0
      (parabolicSpatialJet_holderWith_restrict h)
    have hscaled := hadapt.smul ((r : Real) ^ 2)
    have hrnorm : ‖(r : Real) ^ 2‖₊ = r ^ 2 := by
      ext
      simp only [coe_nnnorm, Real.norm_of_nonneg (sq_nonneg (r : Real)),
        NNReal.coe_pow]
    convert hscaled using 1
    · rw [hrnorm]
    · funext p
      simp only [Pi.smul_apply, Function.comp_apply, Set.restrict_apply]
      exact parabolicSpatialJet_rescaleAt r p0 u 2 p.1
        ((hspace _).of_le le_rfl)
  have htimeHolder : HolderWith
      (C * r ^ (alpha : Real) * r ^ 2) alpha
      ((parabolicPreimageAt r p0 Q).restrict
        (parabolicTimeDerivative (parabolicRescaleAt r p0 u))) := by
    have hadapt := parabolicHolder_dilationAt r p0
      (parabolicTimeDerivative_holderWith_restrict h)
    have hscaled := hadapt.smul ((r : Real) ^ 2)
    have hrnorm : ‖(r : Real) ^ 2‖₊ = r ^ 2 := by
      ext
      simp only [coe_nnnorm, Real.norm_of_nonneg (sq_nonneg (r : Real)),
        NNReal.coe_pow]
    convert hscaled using 1
    · rw [hrnorm]
    · funext p
      simp only [Pi.smul_apply, Function.comp_apply, Set.restrict_apply]
      exact parabolicTimeDerivative_rescaleAt r p0 u p.1
  have hresult := eParabolicC2HolderGaugeOn_le Cspatial (r ^ 2 * C)
    (C * r ^ (alpha : Real) * r ^ 2)
    (C * r ^ (alpha : Real) * r ^ 2)
    hspatial htime hspatialHolder htimeHolder
  unfold parabolicC2HolderRescaleConst
  simpa only [Cspatial] using hresult

def parabolicLinearMap {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] [NormedAddCommGroup W] [NormedSpace Real W]
    (L : V →L[Real] W) (p : ParabolicPoint V) : ParabolicPoint W :=
  parabolicPoint p.time (L p.space)

@[simp]
theorem parabolicLinearMap_time {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] [NormedAddCommGroup W] [NormedSpace Real W]
    (L : V →L[Real] W) (p : ParabolicPoint V) :
    (parabolicLinearMap L p).time = p.time := rfl

@[simp]
theorem parabolicLinearMap_space {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] [NormedAddCommGroup W] [NormedSpace Real W]
    (L : V →L[Real] W) (p : ParabolicPoint V) :
    (parabolicLinearMap L p).space = L p.space := rfl

theorem dist_parabolicLinearMap_le {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] [NormedAddCommGroup W] [NormedSpace Real W]
    (L : V →L[Real] W) (p q : ParabolicPoint V) :
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
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup W] [NormedSpace Real W]
    (L : V →L[Real] W) :
    LipschitzWith (max 1 ‖L‖₊) (parabolicLinearMap L) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simpa only [NNReal.coe_max, NNReal.coe_one, coe_nnnorm] using
    dist_parabolicLinearMap_le L p q

def parabolicLinearPreimage {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] [NormedAddCommGroup W] [NormedSpace Real W]
    (L : V →L[Real] W) (Q : Set (ParabolicPoint W)) : Set (ParabolicPoint V) :=
  parabolicLinearMap L ⁻¹' Q

@[simp]
theorem parabolicLinearPreimage_cylinder_univ
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup W] [NormedSpace Real W]
    (L : V →L[Real] W) (J : Set Real) :
    parabolicLinearPreimage L (parabolicCylinder J Set.univ) =
      parabolicCylinder J Set.univ := by
  ext p
  simp [parabolicLinearPreimage, parabolicCylinder]

theorem parabolicHolder_linearMap
    {V W F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup W] [NormedSpace Real W]
    [MetricSpace F] {alpha C : NNReal} {Q : Set (ParabolicPoint V)}
    {f : ParabolicPoint V → F} (L : W →L[Real] V)
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
    {V W F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup W] [NormedSpace Real W]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (L : W ≃L[Real] V) (u : Real → V → F) (j : Nat)
    (p : ParabolicPoint W) :
    parabolicSpatialJet j (fun t x => u t (L x)) p =
      (parabolicSpatialJet j u
        (parabolicLinearMap (L : W →L[Real] V) p)).compContinuousLinearMap
          (fun _ => (L : W →L[Real] V)) := by
  unfold parabolicSpatialJet
  simp only [parabolicLinearMap_time, parabolicLinearMap_space]
  have h := L.iteratedFDerivWithin_comp_right (u p.time)
    uniqueDiffOn_univ (mem_univ (L p.space)) j
  simpa only [preimage_univ, iteratedFDerivWithin_univ,
    Function.comp_apply] using h

theorem parabolicTimeDerivative_linearEquiv
    {V W F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup W] [NormedSpace Real W]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (L : W ≃L[Real] V) (u : Real → V → F) (p : ParabolicPoint W) :
    parabolicTimeDerivative (fun t x => u t (L x)) p =
      parabolicTimeDerivative u
        (parabolicLinearMap (L : W →L[Real] V) p) := by
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

def contDiffHolderLinearEquivConst
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    (L : V ≃L[Real] V) (alpha C : NNReal) : NNReal :=
  let R := max 1 ‖(L.symm : V →L[Real] V)‖₊
  C + R * C + R ^ 2 * C + R ^ 2 * (C * R ^ (alpha : Real))

theorem eContDiffHolderGaugeOn_linearEquiv_le
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (L : V ≃L[Real] V) (alpha C : NNReal) (u : V → F)
    (h : eContDiffHolderGaugeOn 2 alpha Set.univ (fun x ↦ u (L x)) ≤ C) :
    eContDiffHolderGaugeOn 2 alpha Set.univ u ≤
      contDiffHolderLinearEquivConst L alpha C := by
  let v : V → F := fun x ↦ u (L x)
  let R : NNReal := max 1 ‖(L.symm : V →L[Real] V)‖₊
  let Cspatial : Nat → NNReal := fun j ↦
    match j with
    | 0 => C
    | 1 => R * C
    | _ => R ^ 2 * C
  have h' : eContDiffHolderGaugeOn 2 alpha Set.univ v ≤ C := h
  have hR : ‖(L.symm : V →L[Real] V)‖₊ ≤ R := le_max_right _ _
  have hspatial : ∀ j ≤ 2, ∀ x ∈ (Set.univ : Set V),
      ‖iteratedFDeriv Real j u x‖ ≤ Cspatial j := by
    intro j hj x hx
    let q := L.symm x
    have heq : iteratedFDeriv Real j u x =
        (iteratedFDeriv Real j v q).compContinuousLinearMap
          (fun _ ↦ (L.symm : V →L[Real] V)) := by
      have hlin := L.symm.iteratedFDerivWithin_comp_right v
        uniqueDiffOn_univ (mem_univ (L.symm x)) j
      have hfun : v ∘ L.symm = u := by
        funext y
        simp only [v, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
      rw [hfun] at hlin
      simpa only [v, q, preimage_univ, iteratedFDerivWithin_univ,
        Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using hlin
    rw [heq]
    have hnorm := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv Real j v q)
      (fun _ : Fin j ↦ (L.symm : V →L[Real] V))
    have hadapt := spatialJet_norm_le h' hj (Set.mem_univ q)
    interval_cases j
    · calc
        ‖(iteratedFDeriv Real 0 v q).compContinuousLinearMap
            (fun _ ↦ (L.symm : V →L[Real] V))‖ ≤
            ‖iteratedFDeriv Real 0 v q‖ * 1 := by
          simpa only [Finset.prod_fin_eq_prod_range,
            Finset.prod_range_zero] using hnorm
        _ = ‖iteratedFDeriv Real 0 v q‖ := mul_one _
        _ ≤ (Cspatial 0 : Real) := by simpa only [Cspatial] using hadapt
    · calc
        ‖(iteratedFDeriv Real 1 v q).compContinuousLinearMap
            (fun _ ↦ (L.symm : V →L[Real] V))‖ ≤
            ‖iteratedFDeriv Real 1 v q‖ *
              ‖(L.symm : V →L[Real] V)‖ := by
          simpa only [Fin.prod_univ_one] using hnorm
        _ ≤ C * (R : Real) := by
          exact mul_le_mul hadapt (by exact_mod_cast hR)
            (norm_nonneg _) C.coe_nonneg
        _ = (Cspatial 1 : Real) := by
          simp only [Cspatial, NNReal.coe_mul]
          ring
    · calc
        ‖(iteratedFDeriv Real 2 v q).compContinuousLinearMap
            (fun _ ↦ (L.symm : V →L[Real] V))‖ ≤
            ‖iteratedFDeriv Real 2 v q‖ *
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
  have hholder : HolderWith (R ^ 2 * (C * R ^ (alpha : Real))) alpha
      ((Set.univ : Set V).restrict (iteratedFDeriv Real 2 u)) := by
    have hadapt := topSpatialJet_holderWith_restrict h'
    have hadaptGlobal : HolderWith C alpha (iteratedFDeriv Real 2 v) :=
      holderOnWith_univ.mp (HolderWith.restrict_iff.mp hadapt)
    have hdomain : HolderWith (C * R ^ (alpha : Real)) alpha
        ((Set.univ : Set V).restrict
          (iteratedFDeriv Real 2 v ∘ L.symm)) := by
      have hraw := hadaptGlobal.comp L.symm.lipschitz.holderWith
      have hraw' : HolderWith
          (C * ‖(L.symm : V →L[Real] V)‖₊ ^ (alpha : Real)) alpha
          (iteratedFDeriv Real 2 v ∘ L.symm) := by
        simpa only [mul_one] using hraw
      have hweak : HolderWith (C * R ^ (alpha : Real)) alpha
          (iteratedFDeriv Real 2 v ∘ L.symm) :=
        hraw'.mono (by gcongr)
      have hrestrict := (hweak.holderOnWith (Set.univ : Set V)).holderWith
      simpa only [Function.comp_apply, Set.restrict_apply, mul_one] using hrestrict
    let P := ContinuousMultilinearMap.compContinuousLinearMapL
      (F := F) (fun _ : Fin 2 ↦ (L.symm : V →L[Real] V))
    have hP0 := lipschitzWith_compContinuousLinearMapL
      (F := F) 2 (L.symm : V →L[Real] V)
    have hprod : (∏ _ : Fin 2, ‖(L.symm : V →L[Real] V)‖₊) ≤ R ^ 2 := by
      simpa only [Fin.prod_univ_two, pow_two] using
        mul_le_mul hR hR (zero_le _) (zero_le _)
    have hP : LipschitzWith (R ^ 2) P := hP0.weaken hprod
    have hcomp := hP.holderWith.comp hdomain
    have hcomp' : HolderWith (R ^ 2 * (C * R ^ (alpha : Real))) alpha
        (P ∘ (Set.univ : Set V).restrict
          (iteratedFDeriv Real 2 v ∘ L.symm)) := by
      simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul] using hcomp
    convert hcomp' using 1
    funext x
    have hlin := L.symm.iteratedFDerivWithin_comp_right v
      uniqueDiffOn_univ (mem_univ (L.symm x.1)) 2
    have hfun : v ∘ L.symm = u := by
      funext y
      simp only [v, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    rw [hfun] at hlin
    simpa only [P, v, Function.comp_apply, Set.restrict_apply,
      preimage_univ, iteratedFDerivWithin_univ,
      ContinuousLinearEquiv.apply_symm_apply] using hlin
  have hresult := eContDiffHolderGaugeOn_le Cspatial
    (R ^ 2 * (C * R ^ (alpha : Real))) hspatial hholder
  unfold contDiffHolderLinearEquivConst
  simpa only [R, Cspatial, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow,
    NNReal.coe_rpow] using hresult

def parabolicC2HolderLinearEquivConst
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    (L : V ≃L[Real] V) (alpha C : NNReal) : NNReal :=
  let R := max 1 ‖(L.symm : V →L[Real] V)‖₊
  C + R * C + R ^ 2 * C + C +
    R ^ 2 * (C * R ^ (alpha : Real)) + C * R ^ (alpha : Real)

theorem parabolicC2HolderLinearEquivConst_add
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    (L : V ≃L[Real] V) (alpha C₁ C₂ : NNReal) :
    parabolicC2HolderLinearEquivConst L alpha (C₁ + C₂) =
      parabolicC2HolderLinearEquivConst L alpha C₁ +
        parabolicC2HolderLinearEquivConst L alpha C₂ := by
  unfold parabolicC2HolderLinearEquivConst
  ring

theorem parabolicC2HolderLinearEquivConst_nnreal_mul
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    (L : V ≃L[Real] V) (alpha c C : NNReal) :
    parabolicC2HolderLinearEquivConst L alpha (c * C) =
      c * parabolicC2HolderLinearEquivConst L alpha C := by
  unfold parabolicC2HolderLinearEquivConst
  ring

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
