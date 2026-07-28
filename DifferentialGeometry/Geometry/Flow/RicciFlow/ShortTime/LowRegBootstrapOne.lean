import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleParabolicTraceEnergy
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionFieldLink

/-!
# First same-horizon low-regularity bootstrap

The order-one maximal-regularity solution has an `L²_t H3` companion field and
an `H¹_t H1` carrier.  The cross-scale Lions--Magenes construction therefore
produces an `H2` representative at every time of the original interval.  This
file records the exact links needed by the low-regularity Ricci--DeTurck lane:
the representative realizes the carrier everywhere, realizes the `H3` field
almost everywhere, and inherits an almost-everywhere `H2` ball bound at every
time without shrinking the horizon.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

/-- The affine maximal-regularity Duhamel solution, packaged with its top
spatial companion as a cross-scale field on the same time interval. -/
def duhamelCross (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    CrossScaleField (I := I) (M := M) g r s a T where
  hiL2 := maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ f
  lo := maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ f
  link := solField_toFun_ae (I := I) (M := M) hT hT1
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) u₀ f

omit [BoundarylessManifold I M] in
/-- The intermediate representative realizes the continuous lower carrier at
every time of the original interval. -/
theorem crossRepr_toFun
    (u : CrossScaleField (I := I) (M := M) g r s a T)
    (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 1 by linarith) (u.repr t) = u.lo.toFun t := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorHsInclusion_coeff_apply, u.repr_coeff hT ht]
  rfl

omit [BoundarylessManifold I M] in
/-- The intermediate representative is the intermediate inclusion of the top
companion field almost everywhere on the original interval. -/
theorem crossRepr_hi_ae
    (u : CrossScaleField (I := I) (M := M) g r s a T)
    (hT : 0 < T) :
    (fun t => u.repr t) =ᵐ[timeMeasure T]
      fun t => tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith) (u.hiL2 t) := by
  filter_upwards [u.ae_coeffFun_eq_hiL2,
    ae_restrict_mem (μ := volume) measurableSet_Icc] with t hcoeff ht
  refine tensorHs.ext ?_
  funext i
  rw [u.repr_coeff hT ht, tensorHsInclusion_coeff_apply]
  exact hcoeff i

omit [BoundarylessManifold I M] in
/-- The same-horizon Duhamel cross representative realizes the affine carrier
at every time. -/
theorem duhRepr_toFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 1 by linarith)
        ((duhamelCross (I := I) (M := M) g r s a hT hT1 u₀ f).repr t) =
      (maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ f).toFun t := by
  simpa only [duhamelCross] using
    crossRepr_toFun (I := I) (M := M)
      (duhamelCross (I := I) (M := M) g r s a hT hT1 u₀ f) hT ht

omit [BoundarylessManifold I M] in
/-- The same-horizon Duhamel cross representative realizes the intermediate
inclusion of the top Duhamel field almost everywhere. -/
theorem duhRepr_field_ae
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    (fun t => (duhamelCross (I := I) (M := M) g r s a hT hT1 u₀ f).repr t)
      =ᵐ[timeMeasure T]
        fun t => tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a + 1 ≤ a + 2 by linarith)
          (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ f t) := by
  simpa only [duhamelCross] using
    crossRepr_hi_ae (I := I) (M := M)
      (duhamelCross (I := I) (M := M) g r s a hT hT1 u₀ f) hT

omit [BoundarylessManifold I M] in
/-- The same-horizon Duhamel cross representative is strongly measurable at
the intermediate Sobolev order. -/
theorem duhRepr_meas
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    AEStronglyMeasurable
      (fun t => (duhamelCross (I := I) (M := M)
        g r s a hT hT1 u₀ f).repr t)
      (timeMeasure T) := by
  have hfield : AEStronglyMeasurable
      (fun t => tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          a hT hT1 u₀ f t))
      (timeMeasure T) :=
    (tensorHsInclusion (I := I) (M := M)
      (g := g) (r := r) (s := s)
      (show a + 1 ≤ a + 2 by linarith)).continuous.comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable
          (maxRegDuhamelSolField (I := I) (M := M)
            a hT hT1 u₀ f))
  exact hfield.congr
    (duhRepr_field_ae (I := I) (M := M)
      g r s a hT hT1 u₀ f).symm

omit [BoundarylessManifold I M] in
/-- An almost-everywhere intermediate-order ball bound for the top companion
holds for the cross-scale representative at every time.  The proof uses the
already established continuity of its squared norm, so it does not require a
later time shrink. -/
theorem crossRepr_ball
    (u : CrossScaleField (I := I) (M := M) g r s a T)
    (hT : 0 < T) {R : ℝ} (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂(timeMeasure T),
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith) (u.hiL2 t)‖ ≤ R) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ‖u.repr t‖ ≤ R := by
  have hrepr := crossRepr_hi_ae (I := I) (M := M) u hT
  have hzero :
      (fun t => max (‖u.repr t‖ ^ 2 - R ^ 2) 0) =ᵐ[timeMeasure T]
        (fun _ => (0 : ℝ)) := by
    filter_upwards [hrepr, hball] with t htrepr htball
    rw [htrepr]
    have hsq :
        ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show a + 1 ≤ a + 2 by linarith) (u.hiL2 t)‖ ^ 2 ≤ R ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hR).2 htball
    exact max_eq_right (sub_nonpos.mpr hsq)
  have hcont : ContinuousOn (fun t => max (‖u.repr t‖ ^ 2 - R ^ 2) 0)
      (Set.Icc (0 : ℝ) T) :=
    ((u.continuousOn_normSq_repr hT).sub continuousOn_const).sup continuousOn_const
  have hregular : Set.Icc (0 : ℝ) T ⊆
      closure (interior (Set.Icc (0 : ℝ) T)) := by
    rw [interior_Icc, closure_Ioo (ne_of_lt hT)]
  have heqOn : Set.EqOn (fun t => max (‖u.repr t‖ ^ 2 - R ^ 2) 0)
      (fun _ => (0 : ℝ)) (Set.Icc (0 : ℝ) T) :=
    MeasureTheory.Measure.eqOn_of_ae_eq hzero hcont continuousOn_const hregular
  intro t ht
  have hmax := heqOn ht
  have hsub : ‖u.repr t‖ ^ 2 - R ^ 2 ≤ 0 := by
    have hle := le_max_left (‖u.repr t‖ ^ 2 - R ^ 2) 0
    change max (‖u.repr t‖ ^ 2 - R ^ 2) 0 = 0 at hmax
    rw [hmax] at hle
    exact hle
  exact (sq_le_sq₀ (norm_nonneg _) hR).1 (sub_nonpos.mp hsub)

omit [BoundarylessManifold I M] in
/-- An almost-everywhere intermediate-order bound for a Duhamel top field
becomes an every-time bound for its same-horizon cross representative. -/
theorem duhRepr_ball
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    {T R : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂(timeMeasure T),
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          a hT hT1 u₀ f t)‖ ≤ R) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖(duhamelCross (I := I) (M := M)
        g r s a hT hT1 u₀ f).repr t‖ ≤ R :=
  crossRepr_ball (I := I) (M := M)
    (duhamelCross (I := I) (M := M)
      g r s a hT hT1 u₀ f) hT hR hball

omit [BoundarylessManifold I M] in
/-- A uniformly bounded Duhamel cross representative defines an honest
time-`L2` field at the intermediate Sobolev order. -/
theorem duhRepr_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    {R : ℝ} (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂(timeMeasure T),
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          a hT hT1 u₀ f t)‖ ≤ R) :
    MemLp
      (fun t => (duhamelCross (I := I) (M := M)
        g r s a hT hT1 u₀ f).repr t)
      2 (timeMeasure T) := by
  refine MemLp.of_bound
    (duhRepr_meas (I := I) (M := M)
      g r s a hT hT1 u₀ f) R ?_
  have hrepr := crossRepr_ball (I := I) (M := M)
    (duhamelCross (I := I) (M := M)
      g r s a hT hT1 u₀ f) hT hR hball
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht
  exact hrepr t ht

/-- The intermediate Duhamel representative as a time-`L2` field. -/
def duhReprL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    {R : ℝ} (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂(timeMeasure T),
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          a hT hT1 u₀ f t)‖ ≤ R) :
    timeL2 (tensorHs (I := I) (M := M) g r s (a + 1)) T :=
  (duhRepr_memLp (I := I) (M := M)
    g r s a hT hT1 u₀ f hR hball).toLp
      (fun t => (duhamelCross (I := I) (M := M)
        g r s a hT hT1 u₀ f).repr t)

omit [BoundarylessManifold I M] in
/-- The time-`L2` intermediate field is represented by the Duhamel cross
representative almost everywhere. -/
theorem duhReprL2_ae
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    {R : ℝ} (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂(timeMeasure T),
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          a hT hT1 u₀ f t)‖ ≤ R) :
    duhReprL2 (I := I) (M := M)
        g r s a hT hT1 u₀ f hR hball =ᵐ[timeMeasure T]
      fun t => (duhamelCross (I := I) (M := M)
        g r s a hT hT1 u₀ f).repr t :=
  (duhRepr_memLp (I := I) (M := M)
    g r s a hT hT1 u₀ f hR hball).coeFn_toLp

omit [BoundarylessManifold I M] in
/-- The intermediate time-`L2` field inherits the prescribed state-ball bound
almost everywhere. -/
theorem duhReprL2_ae_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    {R : ℝ} (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂(timeMeasure T),
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          a hT hT1 u₀ f t)‖ ≤ R) :
    ∀ᵐ t ∂(timeMeasure T),
      ‖duhReprL2 (I := I) (M := M)
        g r s a hT hT1 u₀ f hR hball t‖ ≤ R := by
  filter_upwards [
    duhReprL2_ae (I := I) (M := M)
      g r s a hT hT1 u₀ f hR hball,
    duhRepr_field_ae (I := I) (M := M)
      g r s a hT hT1 u₀ f,
    hball] with t hcoe hrepr ht
  rw [hcoe, hrepr]
  exact ht

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
