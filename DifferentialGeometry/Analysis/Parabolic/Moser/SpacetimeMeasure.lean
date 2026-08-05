import DifferentialGeometry.Analysis.Parabolic.Moser.Oscillation
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

instance localizedSpacetimeMeasure_isFiniteMeasure
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g) (a b : ℝ) :
    IsFiniteMeasure
      (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b) := by
  unfold localizedSpacetimeMeasure
  infer_instance

omit [CompactSpace M] in
theorem localizedSpacetimeRpowMoment_nonneg
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ) (hu : ∀ t x, 0 ≤ u t x)
    (p a b : ℝ) :
    0 ≤ localizedSpacetimeRpowMoment (I := I) (M := M) cutoff u p a b := by
  exact integral_nonneg fun z => Real.rpow_nonneg (hu z.1 z.2) p

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
