import DifferentialGeometry.Geometry.Comparison.Volume.SegmentInterior

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold
open scoped Manifold ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space (TangentBundle I M)] in
/-- Positive parameters whose radial vectors lie in the interior
minimizing-segment domain. -/
def segIntRay
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (u : TangentSpace I x) : Set ℝ :=
  {t : ℝ | 0 < t ∧ t • u ∈ SegInt (I := I) g hEnorm x}

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space (TangentBundle I M)] in
/-- The positive parameters for which a nonzero radial vector lies in the
interior minimizing-segment domain form either a bounded open initial interval
or the whole positive ray. -/
theorem segIntRay_eq
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (u : TangentSpace I x) (hu : u ≠ 0) :
    (∃ b : ℝ, 0 < b ∧ segIntRay (I := I) g hEnorm x u = Ioo 0 b) ∨
      segIntRay (I := I) g hEnorm x u = Ioi 0 := by
  classical
  let A : Set ℝ := segIntRay (I := I) g hEnorm x u
  let L : ℝ := Real.sqrt (g.inner x u u)
  have hLpos : 0 < L := Real.sqrt_pos.mpr (g.pos x u hu)
  obtain ⟨ρ, hρpos, hsmall⟩ :=
    radial_riemannianEDist_eq_of_small' (I := I) g hEnorm x
  let δ : ℝ := ρ / (2 * L)
  have hδpos : 0 < δ := div_pos hρpos (mul_pos (by norm_num) hLpos)
  have hδlen : Real.sqrt (g.inner x (δ • u) (δ • u)) = δ * L := by
    simpa only [L] using
      sqrt_gInner_smul_self (I := I) g x hδpos.le u
  have hδL : δ * L = ρ / 2 := by
    dsimp only [δ]
    field_simp [hLpos.ne']
  have hδlt : Real.sqrt (g.inner x (δ • u) (δ • u)) < ρ := by
    rw [hδlen, hδL]
    linarith
  have hδD : δ • u ∈ SegDom (I := I) g hEnorm x := by
    rw [mem_segDom, hsmall hδlt,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  have hAne : A.Nonempty := by
    refine ⟨δ / 2, ?_, ?_⟩
    · exact div_pos hδpos (by norm_num)
    · rw [mem_segInt]
      refine ⟨2, by norm_num, ?_⟩
      convert hδD using 1
      rw [smul_smul]
      congr 1
      ring
  have hdown {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t ∈ A) :
      s ∈ A := by
    change 0 < t ∧ t • u ∈ SegInt (I := I) g hEnorm x at ht
    change 0 < s ∧ s • u ∈ SegInt (I := I) g hEnorm x
    refine ⟨hs, ?_⟩
    have htpos : 0 < t := ht.1
    have hratio0 : 0 ≤ s / t := div_nonneg hs.le htpos.le
    have hratio1 : s / t ≤ 1 := (div_le_one htpos).2 hst
    have hmem := segInt_smul (I := I) g hEnorm ht.2 hratio0 hratio1
    simpa only [smul_smul, div_mul_cancel₀ s htpos.ne'] using hmem
  have hextend {t : ℝ} (ht : t ∈ A) : ∃ s ∈ A, t < s := by
    change 0 < t ∧ t • u ∈ SegInt (I := I) g hEnorm x at ht
    obtain ⟨c, hc, hcD⟩ := (mem_segInt (I := I)).mp ht.2
    let q : ℝ := (1 + c) / 2
    have hq1 : 1 < q := by
      dsimp only [q]
      linarith
    have hqc : q < c := by
      dsimp only [q]
      linarith
    have hqpos : 0 < q := one_pos.trans hq1
    have hfactor : 1 < c / q := (one_lt_div hqpos).2 hqc
    have hmem : (q * t) • u ∈ SegInt (I := I) g hEnorm x := by
      rw [mem_segInt]
      refine ⟨c / q, hfactor, ?_⟩
      have hscalar : (c / q) * (q * t) = c * t := by
        field_simp [hqpos.ne']
      simpa only [smul_smul, hscalar] using hcD
    refine ⟨q * t, ⟨mul_pos hqpos ht.1, hmem⟩, ?_⟩
    nlinarith [mul_pos (sub_pos.mpr hq1) ht.1]
  by_cases hAbdd : BddAbove A
  · left
    obtain ⟨a, haA⟩ := hAne
    refine ⟨sSup A, ?_, ?_⟩
    · exact lt_of_lt_of_le haA.1 (le_csSup hAbdd haA)
    · change A = Ioo 0 (sSup A)
      ext t
      simp only [mem_Ioo]
      constructor
      · intro ht
        have htle : t ≤ sSup A := le_csSup hAbdd ht
        have htne : t ≠ sSup A := by
          intro heq
          obtain ⟨s, hsA, hts⟩ := hextend ht
          have hsle : s ≤ sSup A := le_csSup hAbdd hsA
          linarith
        exact ⟨ht.1, lt_of_le_of_ne htle htne⟩
      · intro ht
        obtain ⟨s, hsA, hts⟩ :=
          (lt_csSup_iff hAbdd ⟨a, haA⟩).mp ht.2
        exact hdown ht.1 hts.le hsA
  · right
    change A = Ioi 0
    ext t
    simp only [mem_Ioi]
    constructor
    · exact fun ht ↦ ht.1
    · intro ht
      obtain ⟨s, hsA, hts⟩ := (not_bddAbove_iff.mp hAbdd) t
      exact hdown ht hts.le hsA

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space (TangentBundle I M)] in
/-- Intersecting a nondegenerate interior minimizing ray with a positive metric
ball gives a bounded open initial interval. -/
theorem segIntRay_gball_eq
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (u : TangentSpace I x) (hu : 0 < g.inner x u u)
    {R : ℝ} (hR : 0 < R) :
    ∃ b : ℝ, 0 < b ∧
      b ≤ R / Real.sqrt (g.inner x u u) ∧
      {t : ℝ | 0 < t ∧
        t • u ∈ SegInt (I := I) g hEnorm x ∩ gBall (I := I) g x R} =
          Ioo 0 b := by
  have hu0 : u ≠ 0 := by
    intro hu0
    subst u
    simp at hu
  let L : ℝ := Real.sqrt (g.inner x u u)
  have hLpos : 0 < L := Real.sqrt_pos.mpr hu
  have hcut : 0 < R / L := div_pos hR hLpos
  have hball {t : ℝ} (ht : 0 < t) :
      t • u ∈ gBall (I := I) g x R ↔ t < R / L := by
    change Real.sqrt (g.inner x (t • u) (t • u)) < R ↔ t < R / L
    rw [sqrt_gInner_smul_self (I := I) g x ht.le u,
      show Real.sqrt (g.inner x u u) = L from rfl, lt_div_iff₀ hLpos]
  rcases segIntRay_eq (I := I) g hEnorm x u hu0 with
    ⟨b, hb, hseg⟩ | hseg
  · refine ⟨min b (R / L), lt_min hb hcut,
      min_le_right b (R / L), ?_⟩
    ext t
    simp only [mem_setOf_eq, mem_inter_iff, mem_Ioo]
    constructor
    · intro ht
      have htRay : t ∈ segIntRay (I := I) g hEnorm x u := ⟨ht.1, ht.2.1⟩
      rw [hseg] at htRay
      exact ⟨ht.1, lt_min htRay.2 ((hball ht.1).mp ht.2.2)⟩
    · intro ht
      have htb : t < b := ht.2.trans_le (min_le_left b (R / L))
      have htR : t < R / L := ht.2.trans_le (min_le_right b (R / L))
      have htRay : t ∈ segIntRay (I := I) g hEnorm x u := by
        rw [hseg]
        exact ⟨ht.1, htb⟩
      exact ⟨ht.1, htRay.2, (hball ht.1).mpr htR⟩
  · refine ⟨R / L, hcut, le_rfl, ?_⟩
    ext t
    simp only [mem_setOf_eq, mem_inter_iff, mem_Ioo]
    constructor
    · intro ht
      exact ⟨ht.1, (hball ht.1).mp ht.2.2⟩
    · intro ht
      have htRay : t ∈ segIntRay (I := I) g hEnorm x u := by
        rw [hseg]
        exact ht.1
      exact ⟨ht.1, htRay.2, (hball ht.1).mpr ht.2⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space (TangentBundle I M)] in
/-- Intersecting an interior minimizing ray with a positive metric ball gives
a bounded open initial interval. -/
theorem segIntRay_ball_eq
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (u : TangentSpace I x) (hu : g.inner x u u = 1)
    {R : ℝ} (hR : 0 < R) :
    ∃ b : ℝ, 0 < b ∧ b ≤ R ∧
      {t : ℝ | 0 < t ∧
        t • u ∈ SegInt (I := I) g hEnorm x ∩ gBall (I := I) g x R} =
          Ioo 0 b := by
  obtain ⟨b, hb, hbR, hset⟩ :=
    segIntRay_gball_eq (I := I) g hEnorm x u (by simpa only [hu] using one_pos) hR
  refine ⟨b, hb, ?_, hset⟩
  simpa only [hu, Real.sqrt_one, div_one] using hbR

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
