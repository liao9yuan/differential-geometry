import DifferentialGeometry.Analysis.Parabolic.Moser.Oscillation
import DifferentialGeometry.Analysis.Integration.Holder.Weighted
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def cutoffWeightedMeasure {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g) : Measure M :=
  (riemannianVolumeMeasure (I := I) (M := M) g).withDensity
    (fun x => ENNReal.ofReal (cutoff.toFun x ^ 2))

instance cutoffWeightedMeasure_isFiniteMeasure
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g) :
    IsFiniteMeasure (cutoffWeightedMeasure (I := I) (M := M) cutoff) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  haveI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  exact isFiniteMeasure_withDensity_ofReal
    ((cutoff.smooth.continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).hasFiniteIntegral

omit [CompactSpace M] in
theorem cutoffWeightedMeasure_mono
    {g : SmoothRiemannianMetric I M} {cutoff outer : SmoothScalar g}
    (hcutoff : ∀ x, cutoff.toFun x ^ 2 ≤ outer.toFun x ^ 2) :
    cutoffWeightedMeasure (I := I) (M := M) cutoff ≤
      cutoffWeightedMeasure (I := I) (M := M) outer := by
  unfold cutoffWeightedMeasure
  apply withDensity_mono
  filter_upwards with x
  exact ENNReal.ofReal_le_ofReal (hcutoff x)

def localizedSpacetimeMeasure {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g) (a b : ℝ) : Measure (ℝ × M) :=
  (volume.restrict (Ioc a b)).prod
    (cutoffWeightedMeasure (I := I) (M := M) cutoff)

def localizedSpacetimeRpowMoment {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g) (u : ℝ → M → ℝ)
    (p a b : ℝ) : ℝ :=
  ∫ z, u z.1 z.2 ^ p
    ∂localizedSpacetimeMeasure (I := I) (M := M) cutoff a b

def localizedSpacetimeRpowNorm {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g) (u : ℝ → M → ℝ)
    (p a b : ℝ) : ℝ :=
  localizedSpacetimeRpowMoment (I := I) (M := M) cutoff u p a b ^ (1 / p)

theorem localizedSpacetimeMeasure_mono
    {g : SmoothRiemannianMetric I M} {cutoff outer : SmoothScalar g}
    {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d)
    (hcutoff : ∀ x, cutoff.toFun x ^ 2 ≤ outer.toFun x ^ 2) :
    localizedSpacetimeMeasure (I := I) (M := M) cutoff a b ≤
      localizedSpacetimeMeasure (I := I) (M := M) outer c d := by
  unfold localizedSpacetimeMeasure
  exact DifferentialGeometry.Integral.Measure.prod_mono
    (Measure.restrict_mono_set volume (Set.Ioc_subset_Ioc hca hbd))
    (cutoffWeightedMeasure_mono (I := I) (M := M) hcutoff)

instance localizedSpacetimeMeasure_isFiniteMeasure
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g) (a b : ℝ) :
    IsFiniteMeasure
      (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b) := by
  unfold localizedSpacetimeMeasure
  infer_instance

theorem integrable_localizedSpacetimeMeasure_of_continuous
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (a b : ℝ) {f : ℝ × M → ℝ} (hf : Continuous f) :
    Integrable f
      (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b) := by
  let K : Set (ℝ × M) := Icc a b ×ˢ (Set.univ : Set M)
  have hK : IsCompact K :=
    isCompact_Icc.prod (isCompact_univ : IsCompact (Set.univ : Set M))
  have hfK : IntegrableOn f K
      ((volume : Measure ℝ).prod
        (cutoffWeightedMeasure (I := I) (M := M) cutoff)) :=
    hf.continuousOn.integrableOn_compact hK
  rw [localizedSpacetimeMeasure, Measure.restrict_prod_eq_prod_univ]
  apply hfK.mono_set
  intro z hz
  exact ⟨⟨hz.1.1.le, hz.1.2⟩, Set.mem_univ z.2⟩

theorem integrable_localizedSpacetimeRpow_of_continuous_pos
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : Continuous (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x) (p a b : ℝ) :
    Integrable (fun z : ℝ × M => u z.1 z.2 ^ p)
      (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b) := by
  apply integrable_localizedSpacetimeMeasure_of_continuous
  exact hu.rpow_const fun z => Or.inl (hpos z.1 z.2).ne'

omit [CompactSpace M] in
theorem localizedSpacetimeRpowMoment_nonneg
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ) (hu : ∀ t x, 0 ≤ u t x)
    (p a b : ℝ) :
    0 ≤ localizedSpacetimeRpowMoment (I := I) (M := M) cutoff u p a b := by
  exact integral_nonneg fun z => Real.rpow_nonneg (hu z.1 z.2) p

theorem localizedSpacetimeRpowMoment_mono
    {g : SmoothRiemannianMetric I M} {cutoff outer : SmoothScalar g}
    (u : ℝ → M → ℝ)
    (hu : Continuous (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d)
    (hcutoff : ∀ x, cutoff.toFun x ^ 2 ≤ outer.toFun x ^ 2) :
    localizedSpacetimeRpowMoment (I := I) (M := M) cutoff u p a b ≤
      localizedSpacetimeRpowMoment (I := I) (M := M) outer u p c d := by
  exact integral_mono_measure
    (localizedSpacetimeMeasure_mono (I := I) (M := M) hca hbd hcutoff)
    (ae_of_all _ fun z => Real.rpow_nonneg (hpos z.1 z.2).le p)
    (integrable_localizedSpacetimeRpow_of_continuous_pos
      (I := I) (M := M) outer u hu hpos p c d)

theorem localizedSpacetimeRpowNorm_mono_measure
    {g : SmoothRiemannianMetric I M} {cutoff outer : SmoothScalar g}
    (u : ℝ → M → ℝ)
    (hu : Continuous (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p a b c d : ℝ} (hp : 0 < p) (hca : c ≤ a) (hbd : b ≤ d)
    (hcutoff : ∀ x, cutoff.toFun x ^ 2 ≤ outer.toFun x ^ 2) :
    localizedSpacetimeRpowNorm (I := I) (M := M) cutoff u p a b ≤
      localizedSpacetimeRpowNorm (I := I) (M := M) outer u p c d := by
  unfold localizedSpacetimeRpowNorm
  exact Real.rpow_le_rpow
    (localizedSpacetimeRpowMoment_nonneg (I := I) (M := M)
      cutoff u (fun t x => (hpos t x).le) p a b)
    (localizedSpacetimeRpowMoment_mono (I := I) (M := M)
      u hu hpos hca hbd hcutoff)
    (div_pos one_pos hp).le

omit [CompactSpace M] in
theorem localizedSpacetimeRpowNorm_nonneg
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ) (hu : ∀ t x, 0 ≤ u t x)
    (p a b : ℝ) :
    0 ≤ localizedSpacetimeRpowNorm (I := I) (M := M) cutoff u p a b :=
  Real.rpow_nonneg
    (localizedSpacetimeRpowMoment_nonneg (I := I) (M := M)
      cutoff u hu p a b) _

omit [CompactSpace M] in
theorem localizedSpacetimeRpowNorm_pos
    {g : SmoothRiemannianMetric I M} {cutoff : SmoothScalar g}
    {u : ℝ → M → ℝ} {p a b : ℝ}
    (hmoment : 0 <
      localizedSpacetimeRpowMoment (I := I) (M := M) cutoff u p a b) :
    0 < localizedSpacetimeRpowNorm (I := I) (M := M) cutoff u p a b :=
  Real.rpow_pos_of_pos hmoment _

theorem localizedSpacetimeRpowNorm_mono
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : Continuous (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p q a b : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (hmass :
      (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b).real
        Set.univ ≤ 1) :
    localizedSpacetimeRpowNorm (I := I) (M := M) cutoff u p a b ≤
      localizedSpacetimeRpowNorm (I := I) (M := M) cutoff u q a b := by
  exact DifferentialGeometry.Integral.integral_rpow_root_mono_of_measure_le_one
    hp hpq (ae_of_all _ fun z => (hpos z.1 z.2).le)
      (integrable_localizedSpacetimeRpow_of_continuous_pos
        (I := I) (M := M) cutoff u hu hpos q a b) hmass

omit [CompactSpace M] in
theorem integral_cutoffWeightedMeasure
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g) (f : M → ℝ) :
    (∫ x, f x ∂cutoffWeightedMeasure (I := I) (M := M) cutoff) =
      ∫ x, cutoff.toFun x ^ 2 * f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  have hdensity : Measurable (fun x : M => ENNReal.ofReal (cutoff.toFun x ^ 2)) :=
    ENNReal.measurable_ofReal.comp (cutoff.smooth.continuous.pow 2).measurable
  rw [cutoffWeightedMeasure,
    integral_withDensity_eq_integral_toReal_smul hdensity (by simp)]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

omit [CompactSpace M] in
theorem cutoffWeightedMeasure_real_apply
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    {s : Set M} (hs : MeasurableSet s) :
    (cutoffWeightedMeasure (I := I) (M := M) cutoff).real s =
      ∫ x in s, cutoff.toFun x ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [← integral_indicator_one hs,
    integral_cutoffWeightedMeasure (I := I) (M := M)]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ s <;> simp [Set.indicator, hx]

theorem integral_localizedSpacetimeMeasure
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    {a b : ℝ} (hab : a ≤ b) (f : ℝ × M → ℝ)
    (hf : Integrable f
      (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b)) :
    (∫ z, f z ∂localizedSpacetimeMeasure (I := I) (M := M) cutoff a b) =
      ∫ t in a..b, ∫ x, cutoff.toFun x ^ 2 * f (t, x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [localizedSpacetimeMeasure, integral_prod f hf]
  simp_rw [integral_cutoffWeightedMeasure (I := I) (M := M)]
  exact (intervalIntegral.integral_of_le hab).symm

theorem localizedSpacetimeRpowMoment_eq_intervalIntegral
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ) {p a b : ℝ} (hab : a ≤ b)
    (hu : Integrable (fun z : ℝ × M => u z.1 z.2 ^ p)
      (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b)) :
    localizedSpacetimeRpowMoment (I := I) (M := M) cutoff u p a b =
      ∫ t in a..b, ∫ x, cutoff.toFun x ^ 2 * u t x ^ p
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  exact integral_localizedSpacetimeMeasure (I := I) (M := M)
    cutoff hab (fun z : ℝ × M => u z.1 z.2 ^ p) hu

theorem localizedSpacetimeRpowMoment_eq_intervalIntegral_of_continuous_pos
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : Continuous (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x) {p a b : ℝ} (hab : a ≤ b) :
    localizedSpacetimeRpowMoment (I := I) (M := M) cutoff u p a b =
      ∫ t in a..b, ∫ x, cutoff.toFun x ^ 2 * u t x ^ p
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  exact localizedSpacetimeRpowMoment_eq_intervalIntegral
    (I := I) (M := M) cutoff u hab
      (integrable_localizedSpacetimeRpow_of_continuous_pos
        (I := I) (M := M) cutoff u hu hpos p a b)

theorem localizedSpacetimeMeasure_real_superlevel
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    {a b level : ℝ} (hab : a ≤ b) (v : ℝ × M → ℝ)
    (hv : Continuous v) :
    (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b).real
        {z | level < v z} =
      ∫ t in a..b, ∫ x in {x : M | level < v (t, x)}, cutoff.toFun x ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  let S : Set (ℝ × M) := {z | level < v z}
  have hS : MeasurableSet S := (isOpen_lt continuous_const hv).measurableSet
  have hInt : Integrable (S.indicator (1 : (ℝ × M) → ℝ))
      (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b) :=
    (integrable_const (1 : ℝ)).indicator hS
  calc
    (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b).real
        {z | level < v z} =
        ∫ z, S.indicator (1 : (ℝ × M) → ℝ) z
          ∂localizedSpacetimeMeasure (I := I) (M := M) cutoff a b := by
      simpa only [S] using (integral_indicator_one hS).symm
    _ = ∫ t in a..b, ∫ x, cutoff.toFun x ^ 2 *
          S.indicator (1 : (ℝ × M) → ℝ) (t, x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      integral_localizedSpacetimeMeasure (I := I) (M := M) cutoff hab _ hInt
    _ = ∫ t in a..b, ∫ x in {x : M | level < v (t, x)}, cutoff.toFun x ^ 2
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      apply intervalIntegral.integral_congr
      intro t _
      let St : Set M := {x : M | level < v (t, x)}
      have hSt : MeasurableSet St :=
        (isOpen_lt continuous_const
          (hv.comp (continuous_const.prodMk continuous_id))).measurableSet
      change (∫ x, cutoff.toFun x ^ 2 *
          S.indicator (1 : (ℝ × M) → ℝ) (t, x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ∫ x in St, cutoff.toFun x ^ 2
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      rw [← integral_indicator hSt]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ St
      · have hxS : (t, x) ∈ S := by simpa only [S, St, mem_setOf_eq] using hx
        simp only [Set.indicator_of_mem hxS, Set.indicator_of_mem hx, Pi.one_apply, mul_one]
      · have hxS : (t, x) ∉ S := by simpa only [S, St, mem_setOf_eq] using hx
        simp only [Set.indicator_of_notMem hxS, Set.indicator_of_notMem hx, mul_zero]

theorem localizedSpacetimeMeasure_real_sublevel
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    {a b level : ℝ} (hab : a ≤ b) (v : ℝ × M → ℝ)
    (hv : Continuous v) :
    (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b).real
        {z | v z < level} =
      ∫ t in a..b, ∫ x in {x : M | v (t, x) < level}, cutoff.toFun x ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have h := localizedSpacetimeMeasure_real_superlevel
    (I := I) (M := M) cutoff hab (fun z => -v z) hv.neg
      (level := -level)
  simpa only [neg_lt_neg_iff] using h

end DifferentialGeometry.Analysis.Parabolic.Moser

end
