import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegLiftAffine

/-!
# The low-regularity forcing satisfies the low affine fixed-point equation

The coefficient families here split the refolded low-base action
`refoldBaseN` into its second- and first-order summands at the exact Sobolev
exponents consumed by `lowreg_lift_two`.  The radial maps stay inside the
families, so their self-application is definitionally the zero-based low
action and does not double-count the principal arm.

The first-order family is built from the complete refolded low action `FLo`
produced by `refold_time`, not from the dense extension `lowA1Lo`: only the
refolded route has an unconditional continuity and affine-growth certificate.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private abbrev loH1 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

private abbrev loH2 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev loH3 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (3 : ℝ)

private abbrev loH4 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (4 : ℝ)

private noncomputable abbrev incl32 (g : SmoothRiemannianMetric I M) :
    loH3 (I := I) (M := M) g →L[ℝ] loH2 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g)
    (r := 0) (s := 2) (by norm_num)

private def affState
    (g : SmoothRiemannianMetric I M) {T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) (t : ℝ) :
    loH3 (I := I) (M := M) g :=
  tensorHsCongr (I := I) (M := M) g 0 2
    (show (1 : ℝ) + 2 = 3 by norm_num)
    (maxRegDuhamelSolField (I := I) (M := M)
      (1 : ℝ) hT hT1 0 f t)

/-- The order-one Duhamel trajectory as a time-`L²` field at the lower-state
exponent `((1 : ℕ) : ℝ) + 2`.  This is the state in which the trajectory ball
hypothesis of `lowreg_hfLo_data` is phrased, so it has to be nameable by that
theorem's callers. -/
def stateField
    (g : SmoothRiemannianMetric I M) {T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) :
    timeL2
      (tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2)) T :=
  (tensorHsCongrL (I := I) (M := M) g 0 2
    (show (1 : ℝ) + 2 = ((1 : ℕ) : ℝ) + 2 by norm_num)).compLpL
      2 (timeMeasure T)
      (maxRegDuhamelSolField (I := I) (M := M)
        (1 : ℝ) hT hT1 0 f)

omit [BoundarylessManifold I M] in
private theorem stateField_ae
    (g : SmoothRiemannianMetric I M) {T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) :
    stateField (I := I) (M := M) g hT hT1 f =ᵐ[timeMeasure T]
      fun t => tensorHsCongr (I := I) (M := M) g 0 2
        (show (1 : ℝ) + 2 = ((1 : ℕ) : ℝ) + 2 by norm_num)
        (maxRegDuhamelSolField (I := I) (M := M)
          (1 : ℝ) hT hT1 0 f t) := by
  exact (tensorHsCongrL (I := I) (M := M) g 0 2
    (show (1 : ℝ) + 2 = ((1 : ℕ) : ℝ) + 2 by norm_num)).coeFn_compLpL
      (p := 2) (μ := timeMeasure T)
      (maxRegDuhamelSolField (I := I) (M := M)
        (1 : ℝ) hT hT1 0 f)

/-- The order-one Duhamel trajectory as a time-`L²` field at the literal
exponent `3`.  This is the state that `refold_time` is evaluated at, and its
time-`L²` norm is the size appearing in both first-order operator
certificates. -/
def duhH3
    (g : SmoothRiemannianMetric I M) {T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) :
    timeL2 (loH3 (I := I) (M := M) g) T :=
  (tensorHsCongrL (I := I) (M := M) g 0 2
    (show (1 : ℝ) + 2 = (3 : ℝ) by norm_num)).compLpL
      2 (timeMeasure T)
      (maxRegDuhamelSolField (I := I) (M := M)
        (1 : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2)) f)

omit [BoundarylessManifold I M] in
private theorem duhH3_ae
    (g : SmoothRiemannianMetric I M) {T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) :
    duhH3 (I := I) (M := M) g hT hT1 f =ᵐ[timeMeasure T]
      affState (I := I) (M := M) g hT hT1 f :=
  (tensorHsCongrL (I := I) (M := M) g 0 2
    (show (1 : ℝ) + 2 = (3 : ℝ) by norm_num)).coeFn_compLpL
      (p := 2) (μ := timeMeasure T)
      (maxRegDuhamelSolField (I := I) (M := M)
        (1 : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2)) f)

omit [BoundarylessManifold I M] in
/-- The time-`L²` lift of an exponent transport is norm preserving, because the
transport itself is a linear isometry.  (Canonical home: beside `tensorHsCongrL`
in `SobolevScale/ExponentCongr.lean`, once that file sees the time-`L²`
layer.) -/
theorem norm_congrLp (g : SmoothRiemannianMetric I M) {a b T : ℝ} (h : a = b)
    (u : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T) :
    ‖(tensorHsCongrL (I := I) (M := M) g 0 2 h).compLpL 2 (timeMeasure T) u‖ =
      ‖u‖ := by
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def]
  congr 1
  refine eLpNorm_congr_norm_ae ?_
  filter_upwards [(tensorHsCongrL (I := I) (M := M) g 0 2 h).coeFn_compLpL
    (p := 2) (μ := timeMeasure T) u] with t ht
  rw [ht, tensorHsCongrL_apply, norm_tensorHsCongr]

/-- **The core maximal-regularity size of the order-one Duhamel trajectory.**
With zero initial datum, the `L²_t H³` size of the trajectory is controlled by
the `L²_t H¹` size of its forcing with the `T`-benign constant `1 + T ≤ 2`.
This is the `duhH3` spelling of `norm_maxRegDuhamelSolField_zero_le`, and it is
what replaces a pointwise `L^∞_t H³` trajectory bound in the smallness chain of
the adjacent-scale lift. -/
theorem norm_duhH3_le
    (g : SmoothRiemannianMetric I M) {T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) :
    ‖duhH3 (I := I) (M := M) g hT hT1 f‖ ≤ (1 + T) * ‖f‖ :=
  le_trans
    (le_of_eq (norm_congrLp (I := I) (M := M) g _ _))
    (norm_maxRegDuhamelSolField_zero_le (I := I) (M := M) (g₀ := g) hT hT1 f)

omit [BoundarylessManifold I M] in
private theorem affState_aemeas
    (g : SmoothRiemannianMetric I M) {T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) :
    AEStronglyMeasurable
      (affState (I := I) (M := M) g hT hT1 f) (timeMeasure T) := by
  have hfield : AEStronglyMeasurable
      (fun t => maxRegDuhamelSolField (I := I) (M := M)
        (1 : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2)) f t)
      (timeMeasure T) :=
    Lp.aestronglyMeasurable _
  simpa only [affState, tensorHsCongrL_apply] using
    (tensorHsCongrL (I := I) (M := M) g 0 2
      (show (1 : ℝ) + 2 = 3 by norm_num)).continuous
      |>.comp_aestronglyMeasurable hfield

omit [BoundarylessManifold I M] in
private theorem hsCongr_trans
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {a b c : ℝ} (hab : a = b) (hbc : b = c) (hac : a = c)
    (u : tensorHs (I := I) (M := M) g r s a) :
    tensorHsCongr (I := I) (M := M) g r s hbc
        (tensorHsCongr (I := I) (M := M) g r s hab u) =
      tensorHsCongr (I := I) (M := M) g r s hac u := by
  cases hab
  cases hbc
  rfl

/-- The complete second-order low family along the order-one Duhamel field.
Its radial factor is part of the family, exactly as in `lowBaseA`. -/
def lowAffA2
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) :
    ℝ → tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2) →L[ℝ]
      loH1 (I := I) (M := M) g :=
  fun t =>
    (lowA2Lo (I := I) (M := M) g hρ hδ0 hδ_le hreal
        (incl32 (I := I) (M := M) g
          (affState (I := I) (M := M) g hT hT1 f t))).comp
      ((radialCLM (I := I) (M := M) g
          (show (0 : ℝ) ≤ 3 by norm_num) ρ
          (incl32 (I := I) (M := M) g
            (affState (I := I) (M := M) g hT hT1 f t))).comp
        (tensorHsCongrL (I := I) (M := M) g 0 2
          (show (1 : ℝ) + 2 = 3 by norm_num)))

/-- Radialization and exponent normalization do not enlarge the complete low
second-order coefficient norm. -/
theorem lowAffA2_le
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) (t : ℝ) :
    ‖lowAffA2 (I := I) (M := M) g hρ hδ0 hδ_le hreal hT hT1 f t‖ ≤
      ‖lowA2Lo (I := I) (M := M) g hρ hδ0 hδ_le hreal
        (incl32 (I := I) (M := M) g
          (affState (I := I) (M := M) g hT hT1 f t))‖ := by
  let A2 :=
    lowA2Lo (I := I) (M := M) g hρ hδ0 hδ_le hreal
      (incl32 (I := I) (M := M) g
        (affState (I := I) (M := M) g hT hT1 f t))
  let R3 :=
    radialCLM (I := I) (M := M) g
      (show (0 : ℝ) ≤ 3 by norm_num) ρ
      (incl32 (I := I) (M := M) g
        (affState (I := I) (M := M) g hT hT1 f t))
  let Q :=
    tensorHsCongrL (I := I) (M := M) g 0 2
      (show (1 : ℝ) + 2 = 3 by norm_num)
  have hR3 : ‖R3‖ ≤ 1 :=
    radialCLM_norm (I := I) (M := M) g (by norm_num) hρ _
  have hR3Q : ‖R3.comp Q‖ ≤ 1 := by
    exact (opNorm_comp_congr_le (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (1 : ℝ) + 2 = 3 by norm_num) R3).trans hR3
  change ‖A2.comp (R3.comp Q)‖ ≤ ‖A2‖
  calc
    ‖A2.comp (R3.comp Q)‖ ≤ ‖A2‖ * ‖R3.comp Q‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A2‖ * 1 :=
      mul_le_mul_of_nonneg_left hR3Q (norm_nonneg A2)
    _ = ‖A2‖ := mul_one _

/-- A continuous uniformly bounded completed second-order coefficient produces
the exact strongly measurable low time family and its `NNReal` pointwise
operator bound. -/
theorem lowAffA2_data
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcont : Continuous
      (lowA2Lo (I := I) (M := M) g hρ hδ0 hδ_le hreal))
    {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ v : loH2 (I := I) (M := M) g,
      ‖lowA2Lo (I := I) (M := M) g hρ hδ0 hδ_le hreal v‖ ≤ C)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) :
    ∃ C2 : NNReal, (C2 : ℝ) = C ∧
      AEStronglyMeasurable
          (lowAffA2 (I := I) (M := M)
            g hρ hδ0 hδ_le hreal hT hT1 f) (timeMeasure T) ∧
        (∀ᵐ t ∂timeMeasure T,
          ‖lowAffA2 (I := I) (M := M)
            g hρ hδ0 hδ_le hreal hT hT1 f t‖ ≤ (C2 : ℝ)) := by
  let u : ℝ → loH3 (I := I) (M := M) g :=
    affState (I := I) (M := M) g hT hT1 f
  have hfield : AEStronglyMeasurable
      (fun t => maxRegDuhamelSolField (I := I) (M := M)
        (1 : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2)) f t)
      (timeMeasure T) :=
    Lp.aestronglyMeasurable _
  have hu : AEStronglyMeasurable u (timeMeasure T) := by
    simpa only [u, affState, tensorHsCongrL_apply] using
      (tensorHsCongrL (I := I) (M := M) g 0 2
        (show (1 : ℝ) + 2 = 3 by norm_num)).continuous
        |>.comp_aestronglyMeasurable hfield
  have hju : AEStronglyMeasurable
      (fun t => incl32 (I := I) (M := M) g (u t)) (timeMeasure T) :=
    (incl32 (I := I) (M := M) g).continuous.comp_aestronglyMeasurable hu
  have hA2 : AEStronglyMeasurable
      (fun t => lowA2Lo (I := I) (M := M) g hρ hδ0 hδ_le hreal
        (incl32 (I := I) (M := M) g (u t))) (timeMeasure T) :=
    hcont.comp_aestronglyMeasurable hju
  have hR3 : AEStronglyMeasurable
      (fun t => radialCLM (I := I) (M := M) g
        (show (0 : ℝ) ≤ 3 by norm_num) ρ
          (incl32 (I := I) (M := M) g (u t))) (timeMeasure T) :=
    radialCLM_aemeas (I := I) (M := M) g (by norm_num) hju
  have hQ : AEStronglyMeasurable
      (fun _ : ℝ => tensorHsCongrL (I := I) (M := M) g 0 2
        (show (1 : ℝ) + 2 = 3 by norm_num)) (timeMeasure T) :=
    aestronglyMeasurable_const
  have hR3Q : AEStronglyMeasurable
      (fun t =>
        (radialCLM (I := I) (M := M) g
          (show (0 : ℝ) ≤ 3 by norm_num) ρ
            (incl32 (I := I) (M := M) g (u t))).comp
          (tensorHsCongrL (I := I) (M := M) g 0 2
            (show (1 : ℝ) + 2 = 3 by norm_num))) (timeMeasure T) :=
    (ContinuousLinearMap.compL ℝ
      (tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2))
      (loH3 (I := I) (M := M) g)
      (loH3 (I := I) (M := M) g)).continuous₂
        |>.comp_aestronglyMeasurable₂ hR3 hQ
  have hmeas : AEStronglyMeasurable
      (lowAffA2 (I := I) (M := M)
        g hρ hδ0 hδ_le hreal hT hT1 f) (timeMeasure T) := by
    simpa only [lowAffA2, u] using
      (ContinuousLinearMap.compL ℝ
        (tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2))
        (loH3 (I := I) (M := M) g)
        (loH1 (I := I) (M := M) g)).continuous₂
          |>.comp_aestronglyMeasurable₂ hA2 hR3Q
  let C2 : NNReal := ⟨C, hC⟩
  have hbound : ∀ᵐ t ∂timeMeasure T,
      ‖lowAffA2 (I := I) (M := M)
        g hρ hδ0 hδ_le hreal hT hT1 f t‖ ≤ (C2 : ℝ) := by
    refine Filter.Eventually.of_forall fun t => ?_
    exact (lowAffA2_le (I := I) (M := M)
      g hρ hδ0 hδ_le hreal hT hT1 f t).trans
        (hbd (incl32 (I := I) (M := M) g (u t)))
  exact ⟨C2, rfl, hmeas, hbound⟩

/-- The complete second-order high family along the order-one Duhamel field.
It is the `H⁴ → H²` sibling of `lowAffA2`, normalized to the arithmetic domain
exponent `(2 : ℝ) + 2` that the adjacent-scale lift consumes at `aHi = 2`, and
it carries the same radial factor selected by the same `H²` state. -/
def lowAffA2Hi
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) :
    ℝ → tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2) →L[ℝ]
      loH2 (I := I) (M := M) g :=
  fun t =>
    (lowA2Hi (I := I) (M := M) g hρ hδ0 hδ_le hreal
        (incl32 (I := I) (M := M) g
          (affState (I := I) (M := M) g hT hT1 f t))).comp
      ((radialCLM (I := I) (M := M) g
          (show (0 : ℝ) ≤ 4 by norm_num) ρ
          (incl32 (I := I) (M := M) g
            (affState (I := I) (M := M) g hT hT1 f t))).comp
        (tensorHsCongrL (I := I) (M := M) g 0 2
          (show (2 : ℝ) + 2 = 4 by norm_num)))

/-- Radialization and exponent normalization do not enlarge the complete high
second-order coefficient norm. -/
theorem lowAffA2Hi_le
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) (t : ℝ) :
    ‖lowAffA2Hi (I := I) (M := M) g hρ hδ0 hδ_le hreal hT hT1 f t‖ ≤
      ‖lowA2Hi (I := I) (M := M) g hρ hδ0 hδ_le hreal
        (incl32 (I := I) (M := M) g
          (affState (I := I) (M := M) g hT hT1 f t))‖ := by
  let A2 :=
    lowA2Hi (I := I) (M := M) g hρ hδ0 hδ_le hreal
      (incl32 (I := I) (M := M) g
        (affState (I := I) (M := M) g hT hT1 f t))
  let R4 :=
    radialCLM (I := I) (M := M) g
      (show (0 : ℝ) ≤ 4 by norm_num) ρ
      (incl32 (I := I) (M := M) g
        (affState (I := I) (M := M) g hT hT1 f t))
  let Q :=
    tensorHsCongrL (I := I) (M := M) g 0 2
      (show (2 : ℝ) + 2 = 4 by norm_num)
  have hR4 : ‖R4‖ ≤ 1 :=
    radialCLM_norm (I := I) (M := M) g (by norm_num) hρ _
  have hR4Q : ‖R4.comp Q‖ ≤ 1 := by
    exact (opNorm_comp_congr_le (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) + 2 = 4 by norm_num) R4).trans hR4
  change ‖A2.comp (R4.comp Q)‖ ≤ ‖A2‖
  calc
    ‖A2.comp (R4.comp Q)‖ ≤ ‖A2‖ * ‖R4.comp Q‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A2‖ * 1 :=
      mul_le_mul_of_nonneg_left hR4Q (norm_nonneg A2)
    _ = ‖A2‖ := mul_one _

/-- A continuous uniformly bounded completed high second-order coefficient
produces the exact strongly measurable high time family and its `NNReal`
pointwise operator bound. -/
theorem lowAffA2Hi_data
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcont : Continuous
      (lowA2Hi (I := I) (M := M) g hρ hδ0 hδ_le hreal))
    {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ v : loH2 (I := I) (M := M) g,
      ‖lowA2Hi (I := I) (M := M) g hρ hδ0 hδ_le hreal v‖ ≤ C)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) :
    ∃ C2 : NNReal, (C2 : ℝ) = C ∧
      AEStronglyMeasurable
          (lowAffA2Hi (I := I) (M := M)
            g hρ hδ0 hδ_le hreal hT hT1 f) (timeMeasure T) ∧
        (∀ᵐ t ∂timeMeasure T,
          ‖lowAffA2Hi (I := I) (M := M)
            g hρ hδ0 hδ_le hreal hT hT1 f t‖ ≤ (C2 : ℝ)) := by
  have hu := affState_aemeas (I := I) (M := M) g hT hT1 f
  have hju : AEStronglyMeasurable
      (fun t => incl32 (I := I) (M := M) g
        (affState (I := I) (M := M) g hT hT1 f t)) (timeMeasure T) :=
    (incl32 (I := I) (M := M) g).continuous.comp_aestronglyMeasurable hu
  have hA2 : AEStronglyMeasurable
      (fun t => lowA2Hi (I := I) (M := M) g hρ hδ0 hδ_le hreal
        (incl32 (I := I) (M := M) g
          (affState (I := I) (M := M) g hT hT1 f t))) (timeMeasure T) :=
    hcont.comp_aestronglyMeasurable hju
  have hR4 : AEStronglyMeasurable
      (fun t => radialCLM (I := I) (M := M) g
        (show (0 : ℝ) ≤ 4 by norm_num) ρ
          (incl32 (I := I) (M := M) g
            (affState (I := I) (M := M) g hT hT1 f t))) (timeMeasure T) :=
    radialCLM_aemeas (I := I) (M := M) g (by norm_num) hju
  have hQ : AEStronglyMeasurable
      (fun _ : ℝ => tensorHsCongrL (I := I) (M := M) g 0 2
        (show (2 : ℝ) + 2 = 4 by norm_num)) (timeMeasure T) :=
    aestronglyMeasurable_const
  have hR4Q : AEStronglyMeasurable
      (fun t =>
        (radialCLM (I := I) (M := M) g
          (show (0 : ℝ) ≤ 4 by norm_num) ρ
            (incl32 (I := I) (M := M) g
              (affState (I := I) (M := M) g hT hT1 f t))).comp
          (tensorHsCongrL (I := I) (M := M) g 0 2
            (show (2 : ℝ) + 2 = 4 by norm_num))) (timeMeasure T) :=
    (ContinuousLinearMap.compL ℝ
      (tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2))
      (loH4 (I := I) (M := M) g)
      (loH4 (I := I) (M := M) g)).continuous₂
        |>.comp_aestronglyMeasurable₂ hR4 hQ
  have hmeas : AEStronglyMeasurable
      (lowAffA2Hi (I := I) (M := M)
        g hρ hδ0 hδ_le hreal hT hT1 f) (timeMeasure T) := by
    simpa only [lowAffA2Hi] using
      (ContinuousLinearMap.compL ℝ
        (tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2))
        (loH4 (I := I) (M := M) g)
        (loH2 (I := I) (M := M) g)).continuous₂
          |>.comp_aestronglyMeasurable₂ hA2 hR4Q
  refine ⟨⟨C, hC⟩, rfl, hmeas, Filter.Eventually.of_forall fun t => ?_⟩
  exact (lowAffA2Hi_le (I := I) (M := M)
    g hρ hδ0 hδ_le hreal hT hT1 f t).trans (hbd _)

/-- The two second-order families form the canonical Sobolev-inclusion square
at every time: this is the `hA2compat` input of the adjacent-scale lift at
`aLo = 1`, `aHi = 2`.  Its only genuine inputs are the completed `H²`-state
square of `lowA2Hi` / `lowA2Lo` and the fact that the frozen radial passenger
commutes with the scale inclusions. -/
theorem lowAffA2_compat
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hsq : ∀ v : loH2 (I := I) (M := M) g,
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp
          (lowA2Hi (I := I) (M := M) g hρ hδ0 hδ_le hreal v) =
        (lowA2Lo (I := I) (M := M) g hρ hδ0 hδ_le hreal v).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ 4 by norm_num)))
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) (t : ℝ) :
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp
        (lowAffA2Hi (I := I) (M := M)
          g hρ hδ0 hδ_le hreal hT hT1 f t) =
      (lowAffA2 (I := I) (M := M)
          g hρ hδ0 hδ_le hreal hT hT1 f t).comp
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) + 2 ≤ (2 : ℝ) + 2 by norm_num)) := by
  refine ContinuousLinearMap.ext fun x => ?_
  have hpt := DFunLike.congr_fun
    (hsq (incl32 (I := I) (M := M) g
      (affState (I := I) (M := M) g hT hT1 f t)))
    ((radialCLM (I := I) (M := M) g
        (show (0 : ℝ) ≤ 4 by norm_num) ρ
        (incl32 (I := I) (M := M) g
          (affState (I := I) (M := M) g hT hT1 f t)))
      (tensorHsCongr (I := I) (M := M) g 0 2
        (show (2 : ℝ) + 2 = 4 by norm_num) x))
  have hrad := DFunLike.congr_fun
    (radialCLM_incl (I := I) (M := M) g
      (show (0 : ℝ) ≤ 3 by norm_num) (show (0 : ℝ) ≤ 4 by norm_num)
      (show (3 : ℝ) ≤ 4 by norm_num) ρ
      (incl32 (I := I) (M := M) g
        (affState (I := I) (M := M) g hT hT1 f t)))
    (tensorHsCongr (I := I) (M := M) g 0 2
      (show (2 : ℝ) + 2 = 4 by norm_num) x)
  have hincl := tensorHsCongr_incl (I := I) (M := M) (g := g) (r := 0) (s := 2)
    (show (1 : ℝ) + 2 = 3 by norm_num)
    (show (2 : ℝ) + 2 = 4 by norm_num)
    (show (1 : ℝ) + 2 ≤ (2 : ℝ) + 2 by norm_num)
    (show (3 : ℝ) ≤ 4 by norm_num) x
  simp only [ContinuousLinearMap.comp_apply] at hpt hrad
  rw [hrad] at hpt
  simp only [lowAffA2Hi, lowAffA2, ContinuousLinearMap.comp_apply,
    tensorHsCongrL_apply, hincl]
  exact hpt

/-- The first-order low family along the order-one Duhamel field, built from
the complete refolded low action `FLo`.  It acts on the canonical intermediate
`H2` representative and contains the same radial factor as the first-order
summand of `refoldBaseN`. -/
def refoldAffA1
    (g : SmoothRiemannianMetric I M) (ρ : ℝ)
    (FLo : loH3 (I := I) (M := M) g →
      (loH2 (I := I) (M := M) g →L[ℝ] loH1 (I := I) (M := M) g))
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) :
    ℝ → tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 1) →L[ℝ]
      loH1 (I := I) (M := M) g :=
  fun t =>
    (FLo (affState (I := I) (M := M) g hT hT1 f t)).comp
      ((radialCLM (I := I) (M := M) g
          (show (0 : ℝ) ≤ 2 by norm_num) ρ
          (incl32 (I := I) (M := M) g
            (affState (I := I) (M := M) g hT hT1 f t))).comp
        (tensorHsCongrL (I := I) (M := M) g 0 2
          (show (1 : ℝ) + 1 = 2 by norm_num)))

/-- Radialization and exponent normalization do not enlarge the refolded low
first-order coefficient norm. -/
theorem refoldAffA1_le
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (FLo : loH3 (I := I) (M := M) g →
      (loH2 (I := I) (M := M) g →L[ℝ] loH1 (I := I) (M := M) g))
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) (t : ℝ) :
    ‖refoldAffA1 (I := I) (M := M) g ρ FLo hT hT1 f t‖ ≤
      ‖FLo (affState (I := I) (M := M) g hT hT1 f t)‖ := by
  let A1 := FLo (affState (I := I) (M := M) g hT hT1 f t)
  let R2 :=
    radialCLM (I := I) (M := M) g
      (show (0 : ℝ) ≤ 2 by norm_num) ρ
      (incl32 (I := I) (M := M) g
        (affState (I := I) (M := M) g hT hT1 f t))
  let Q :=
    tensorHsCongrL (I := I) (M := M) g 0 2
      (show (1 : ℝ) + 1 = 2 by norm_num)
  have hR2 : ‖R2‖ ≤ 1 :=
    radialCLM_norm (I := I) (M := M) g (by norm_num) hρ _
  have hR2Q : ‖R2.comp Q‖ ≤ 1 := by
    exact (opNorm_comp_congr_le (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (1 : ℝ) + 1 = 2 by norm_num) R2).trans hR2
  change ‖A1.comp (R2.comp Q)‖ ≤ ‖A1‖
  calc
    ‖A1.comp (R2.comp Q)‖ ≤ ‖A1‖ * ‖R2.comp Q‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A1‖ * 1 :=
      mul_le_mul_of_nonneg_left hR2Q (norm_nonneg A1)
    _ = ‖A1‖ := mul_one _

/-- The refolded first-order family along a continuous action is strongly
measurable in time. -/
theorem refoldAffA1_aemeas
    (g : SmoothRiemannianMetric I M) (ρ : ℝ)
    (FLo : loH3 (I := I) (M := M) g →
      (loH2 (I := I) (M := M) g →L[ℝ] loH1 (I := I) (M := M) g))
    (hFLo : Continuous FLo)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) :
    AEStronglyMeasurable
      (refoldAffA1 (I := I) (M := M) g ρ FLo hT hT1 f) (timeMeasure T) := by
  have hu := affState_aemeas (I := I) (M := M) g hT hT1 f
  have hju : AEStronglyMeasurable
      (fun t => incl32 (I := I) (M := M) g
        (affState (I := I) (M := M) g hT hT1 f t)) (timeMeasure T) :=
    (incl32 (I := I) (M := M) g).continuous.comp_aestronglyMeasurable hu
  have hA1 : AEStronglyMeasurable
      (fun t => FLo (affState (I := I) (M := M) g hT hT1 f t))
      (timeMeasure T) :=
    hFLo.comp_aestronglyMeasurable hu
  have hR2 : AEStronglyMeasurable
      (fun t => radialCLM (I := I) (M := M) g
        (show (0 : ℝ) ≤ 2 by norm_num) ρ
          (incl32 (I := I) (M := M) g
            (affState (I := I) (M := M) g hT hT1 f t))) (timeMeasure T) :=
    radialCLM_aemeas (I := I) (M := M) g (by norm_num) hju
  have hQ : AEStronglyMeasurable
      (fun _ : ℝ => tensorHsCongrL (I := I) (M := M) g 0 2
        (show (1 : ℝ) + 1 = 2 by norm_num)) (timeMeasure T) :=
    aestronglyMeasurable_const
  have hR2Q : AEStronglyMeasurable
      (fun t =>
        (radialCLM (I := I) (M := M) g
          (show (0 : ℝ) ≤ 2 by norm_num) ρ
            (incl32 (I := I) (M := M) g
              (affState (I := I) (M := M) g hT hT1 f t))).comp
          (tensorHsCongrL (I := I) (M := M) g 0 2
            (show (1 : ℝ) + 1 = 2 by norm_num))) (timeMeasure T) :=
    (ContinuousLinearMap.compL ℝ
      (tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 1))
      (loH2 (I := I) (M := M) g)
      (loH2 (I := I) (M := M) g)).continuous₂
        |>.comp_aestronglyMeasurable₂ hR2 hQ
  simpa only [refoldAffA1] using
    (ContinuousLinearMap.compL ℝ
      (tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 1))
      (loH2 (I := I) (M := M) g)
      (loH1 (I := I) (M := M) g)).continuous₂
        |>.comp_aestronglyMeasurable₂ hA1 hR2Q

/-- The time-`L²` certificate of the refolded low first-order family: the affine
state bound of `refold_time` gives membership together with the Minkowski norm
estimate in the size of the `H³` Duhamel trajectory. -/
theorem refoldAffA1_memLp
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (FLo : loH3 (I := I) (M := M) g →
      (loH2 (I := I) (M := M) g →L[ℝ] loH1 (I := I) (M := M) g))
    (hFLo : Continuous FLo)
    {Z L : ℝ} (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (hFbd : ∀ x : loH3 (I := I) (M := M) g, ‖FLo x‖ ≤ Z + L * ‖x‖)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) :
    ∃ hmem : MemLp
        (refoldAffA1 (I := I) (M := M) g ρ FLo hT hT1 f) 2 (timeMeasure T),
      ‖hmem.toLp (refoldAffA1 (I := I) (M := M) g ρ FLo hT hT1 f)‖ ≤
        L * ‖duhH3 (I := I) (M := M) g hT hT1 f‖ + Real.sqrt T * Z := by
  refine memLp_clm_affine (duhH3 (I := I) (M := M) g hT hT1 f) _
    (refoldAffA1_aemeas (I := I) (M := M) g ρ FLo hFLo hT hT1 f) hL hZ ?_
  filter_upwards [duhH3_ae (I := I) (M := M) g hT hT1 f] with t hd
  rw [hd]
  exact (refoldAffA1_le (I := I) (M := M) g hρ FLo hT hT1 f t).trans (hFbd _)

/-- The first-order high family along the order-one Duhamel field, built from
the complete refolded high action `FHi` produced by `refold_time`.  It is the
`H³ → H²` sibling of `refoldAffA1`, normalized to the arithmetic domain
exponent `(2 : ℝ) + 1` that the adjacent-scale lift consumes at `aHi = 2`, and
it carries the same radial factor. -/
def refoldAffA1Hi
    (g : SmoothRiemannianMetric I M) (ρ : ℝ)
    (FHi : loH3 (I := I) (M := M) g →
      (loH3 (I := I) (M := M) g →L[ℝ] loH2 (I := I) (M := M) g))
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) :
    ℝ → tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 1) →L[ℝ]
      loH2 (I := I) (M := M) g :=
  fun t =>
    (FHi (affState (I := I) (M := M) g hT hT1 f t)).comp
      ((radialCLM (I := I) (M := M) g
          (show (0 : ℝ) ≤ 3 by norm_num) ρ
          (incl32 (I := I) (M := M) g
            (affState (I := I) (M := M) g hT hT1 f t))).comp
        (tensorHsCongrL (I := I) (M := M) g 0 2
          (show (2 : ℝ) + 1 = 3 by norm_num)))

/-- Radialization and exponent normalization do not enlarge the refolded high
first-order coefficient norm. -/
theorem refoldAffA1Hi_le
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (FHi : loH3 (I := I) (M := M) g →
      (loH3 (I := I) (M := M) g →L[ℝ] loH2 (I := I) (M := M) g))
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) (t : ℝ) :
    ‖refoldAffA1Hi (I := I) (M := M) g ρ FHi hT hT1 f t‖ ≤
      ‖FHi (affState (I := I) (M := M) g hT hT1 f t)‖ := by
  let A1 := FHi (affState (I := I) (M := M) g hT hT1 f t)
  let R3 :=
    radialCLM (I := I) (M := M) g
      (show (0 : ℝ) ≤ 3 by norm_num) ρ
      (incl32 (I := I) (M := M) g
        (affState (I := I) (M := M) g hT hT1 f t))
  let Q :=
    tensorHsCongrL (I := I) (M := M) g 0 2
      (show (2 : ℝ) + 1 = 3 by norm_num)
  have hR3 : ‖R3‖ ≤ 1 :=
    radialCLM_norm (I := I) (M := M) g (by norm_num) hρ _
  have hR3Q : ‖R3.comp Q‖ ≤ 1 := by
    exact (opNorm_comp_congr_le (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) + 1 = 3 by norm_num) R3).trans hR3
  change ‖A1.comp (R3.comp Q)‖ ≤ ‖A1‖
  calc
    ‖A1.comp (R3.comp Q)‖ ≤ ‖A1‖ * ‖R3.comp Q‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A1‖ * 1 :=
      mul_le_mul_of_nonneg_left hR3Q (norm_nonneg A1)
    _ = ‖A1‖ := mul_one _

/-- The refolded high first-order family along a continuous action is strongly
measurable in time. -/
theorem refoldAffA1Hi_aemeas
    (g : SmoothRiemannianMetric I M) (ρ : ℝ)
    (FHi : loH3 (I := I) (M := M) g →
      (loH3 (I := I) (M := M) g →L[ℝ] loH2 (I := I) (M := M) g))
    (hFHi : Continuous FHi)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) :
    AEStronglyMeasurable
      (refoldAffA1Hi (I := I) (M := M) g ρ FHi hT hT1 f) (timeMeasure T) := by
  have hu := affState_aemeas (I := I) (M := M) g hT hT1 f
  have hju : AEStronglyMeasurable
      (fun t => incl32 (I := I) (M := M) g
        (affState (I := I) (M := M) g hT hT1 f t)) (timeMeasure T) :=
    (incl32 (I := I) (M := M) g).continuous.comp_aestronglyMeasurable hu
  have hA1 : AEStronglyMeasurable
      (fun t => FHi (affState (I := I) (M := M) g hT hT1 f t))
      (timeMeasure T) :=
    hFHi.comp_aestronglyMeasurable hu
  have hR3 : AEStronglyMeasurable
      (fun t => radialCLM (I := I) (M := M) g
        (show (0 : ℝ) ≤ 3 by norm_num) ρ
          (incl32 (I := I) (M := M) g
            (affState (I := I) (M := M) g hT hT1 f t))) (timeMeasure T) :=
    radialCLM_aemeas (I := I) (M := M) g (by norm_num) hju
  have hQ : AEStronglyMeasurable
      (fun _ : ℝ => tensorHsCongrL (I := I) (M := M) g 0 2
        (show (2 : ℝ) + 1 = 3 by norm_num)) (timeMeasure T) :=
    aestronglyMeasurable_const
  have hR3Q : AEStronglyMeasurable
      (fun t =>
        (radialCLM (I := I) (M := M) g
          (show (0 : ℝ) ≤ 3 by norm_num) ρ
            (incl32 (I := I) (M := M) g
              (affState (I := I) (M := M) g hT hT1 f t))).comp
          (tensorHsCongrL (I := I) (M := M) g 0 2
            (show (2 : ℝ) + 1 = 3 by norm_num))) (timeMeasure T) :=
    (ContinuousLinearMap.compL ℝ
      (tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 1))
      (loH3 (I := I) (M := M) g)
      (loH3 (I := I) (M := M) g)).continuous₂
        |>.comp_aestronglyMeasurable₂ hR3 hQ
  simpa only [refoldAffA1Hi] using
    (ContinuousLinearMap.compL ℝ
      (tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 1))
      (loH3 (I := I) (M := M) g)
      (loH2 (I := I) (M := M) g)).continuous₂
        |>.comp_aestronglyMeasurable₂ hA1 hR3Q

/-- The time-`L²` certificate of the refolded high first-order family: the
`H³`-side sibling of `refoldAffA1_memLp`, with the same Minkowski bound in the
size of the `H³` Duhamel trajectory and no trajectory hypothesis. -/
theorem refoldAffA1Hi_memLp
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (FHi : loH3 (I := I) (M := M) g →
      (loH3 (I := I) (M := M) g →L[ℝ] loH2 (I := I) (M := M) g))
    (hFHi : Continuous FHi)
    {Z L : ℝ} (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (hFbd : ∀ x : loH3 (I := I) (M := M) g, ‖FHi x‖ ≤ Z + L * ‖x‖)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) :
    ∃ hmem : MemLp
        (refoldAffA1Hi (I := I) (M := M) g ρ FHi hT hT1 f) 2 (timeMeasure T),
      ‖hmem.toLp (refoldAffA1Hi (I := I) (M := M) g ρ FHi hT hT1 f)‖ ≤
        L * ‖duhH3 (I := I) (M := M) g hT hT1 f‖ + Real.sqrt T * Z := by
  refine memLp_clm_affine (duhH3 (I := I) (M := M) g hT hT1 f) _
    (refoldAffA1Hi_aemeas (I := I) (M := M) g ρ FHi hFHi hT hT1 f) hL hZ ?_
  filter_upwards [duhH3_ae (I := I) (M := M) g hT hT1 f] with t hd
  rw [hd]
  exact (refoldAffA1Hi_le (I := I) (M := M) g hρ FHi hT hT1 f t).trans (hFbd _)

/-- The two refolded first-order families form the canonical Sobolev-inclusion
square at almost every time: this is the `hA1compat` input of the
adjacent-scale lift at `aLo = 1`, `aHi = 2`.  Its only input is the
trajectory-free square of the affine packet (`refold_aff`), transported through
the frozen radial passenger and the two exponent normalizations. -/
theorem refoldAffA1_compat
    (g : SmoothRiemannianMetric I M) (ρ : ℝ)
    (FHi : loH3 (I := I) (M := M) g →
      (loH3 (I := I) (M := M) g →L[ℝ] loH2 (I := I) (M := M) g))
    (FLo : loH3 (I := I) (M := M) g →
      (loH2 (I := I) (M := M) g →L[ℝ] loH1 (I := I) (M := M) g))
    (hFComm : ∀ x : loH3 (I := I) (M := M) g,
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp (FHi x) =
        (FLo x).comp (incl32 (I := I) (M := M) g))
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) :
    ∀ᵐ t ∂timeMeasure T,
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp
          (refoldAffA1Hi (I := I) (M := M) g ρ FHi hT hT1 f t) =
        (refoldAffA1 (I := I) (M := M) g ρ FLo hT hT1 f t).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (1 : ℝ) + 1 ≤ (2 : ℝ) + 1 by norm_num)) := by
  have hsq : ∀ t : ℝ,
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp
          ((FHi (duhH3 (I := I) (M := M) g hT hT1 f t)).comp
            (radialCLM (I := I) (M := M) g
              (show (0 : ℝ) ≤ 3 by norm_num) ρ
              (incl32 (I := I) (M := M) g
                (duhH3 (I := I) (M := M) g hT hT1 f t)))) =
        ((FLo (duhH3 (I := I) (M := M) g hT hT1 f t)).comp
            (radialCLM (I := I) (M := M) g
              (show (0 : ℝ) ≤ 2 by norm_num) ρ
              (incl32 (I := I) (M := M) g
                (duhH3 (I := I) (M := M) g hT hT1 f t)))).comp
          (incl32 (I := I) (M := M) g) := by
    intro t
    refine ContinuousLinearMap.ext fun x => ?_
    have hcoef := DFunLike.congr_fun
      (hFComm (duhH3 (I := I) (M := M) g hT hT1 f t))
      (radialCLM (I := I) (M := M) g
        (show (0 : ℝ) ≤ 3 by norm_num) ρ
        (incl32 (I := I) (M := M) g
          (duhH3 (I := I) (M := M) g hT hT1 f t)) x)
    have hrad := DFunLike.congr_fun
      (radialCLM_incl (I := I) (M := M) g
        (show (0 : ℝ) ≤ 2 by norm_num) (show (0 : ℝ) ≤ 3 by norm_num)
        (show (2 : ℝ) ≤ 3 by norm_num) ρ
        (incl32 (I := I) (M := M) g
          (duhH3 (I := I) (M := M) g hT hT1 f t))) x
    simp only [ContinuousLinearMap.comp_apply] at hcoef hrad ⊢
    rw [hcoef, hrad]
  filter_upwards [duhH3_ae (I := I) (M := M) g hT hT1 f] with t hd
  refine ContinuousLinearMap.ext fun x => ?_
  have hpt := DFunLike.congr_fun (hsq t)
    (tensorHsCongrL (I := I) (M := M) g 0 2
      (show (2 : ℝ) + 1 = 3 by norm_num) x)
  rw [hd] at hpt
  simp only [ContinuousLinearMap.comp_apply] at hpt
  have hincl := tensorHsCongr_incl (I := I) (M := M) (g := g) (r := 0) (s := 2)
    (show (1 : ℝ) + 1 = 2 by norm_num)
    (show (2 : ℝ) + 1 = 3 by norm_num)
    (show (1 : ℝ) + 1 ≤ (2 : ℝ) + 1 by norm_num)
    (show (2 : ℝ) ≤ 3 by norm_num) x
  simp only [refoldAffA1Hi, refoldAffA1, ContinuousLinearMap.comp_apply,
    tensorHsCongrL_apply, hincl]
  exact hpt

private theorem refoldAff_self
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (FLo : loH3 (I := I) (M := M) g →
      (loH2 (I := I) (M := M) g →L[ℝ] loH1 (I := I) (M := M) g))
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) (t : ℝ)
    (v : tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 1))
    (hv : tensorHsCongr (I := I) (M := M) g 0 2
        (show (1 : ℝ) + 1 = 2 by norm_num) v =
      incl32 (I := I) (M := M) g
        (affState (I := I) (M := M) g hT hT1 f t)) :
    lowBaseForce (I := I) (M := M) g +
        (lowAffA2 (I := I) (M := M) g hρ.le hδ0 hδ_le hreal hT hT1 f t
            (maxRegDuhamelSolField (I := I) (M := M)
              (1 : ℝ) hT hT1 0 f t) +
          refoldAffA1 (I := I) (M := M) g ρ FLo hT hT1 f t v) =
      refoldBaseN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal FLo
        (affState (I := I) (M := M) g hT hT1 f t) := by
  have h3 : radialCLM (I := I) (M := M) g
        (show (0 : ℝ) ≤ 3 by norm_num) ρ
        (incl32 (I := I) (M := M) g
          (affState (I := I) (M := M) g hT hT1 f t))
        (tensorHsCongr (I := I) (M := M) g 0 2
          (show (1 : ℝ) + 2 = 3 by norm_num)
          (maxRegDuhamelSolField (I := I) (M := M)
            (1 : ℝ) hT hT1 0 f t)) =
      lowRadialH3 (I := I) (M := M) g ρ
        (affState (I := I) (M := M) g hT hT1 f t) :=
    radialCLM_h3 (I := I) (M := M) g hρ
      (affState (I := I) (M := M) g hT hT1 f t)
  have h2 : radialCLM (I := I) (M := M) g
        (show (0 : ℝ) ≤ 2 by norm_num) ρ
        (incl32 (I := I) (M := M) g
          (affState (I := I) (M := M) g hT hT1 f t))
        (incl32 (I := I) (M := M) g
          (affState (I := I) (M := M) g hT hT1 f t)) =
      lowRadialHs (I := I) (M := M) g ρ
        (incl32 (I := I) (M := M) g
          (affState (I := I) (M := M) g hT hT1 f t)) :=
    radialCLM_h2 (I := I) (M := M) g hρ.le
      (incl32 (I := I) (M := M) g
        (affState (I := I) (M := M) g hT hT1 f t))
  simp only [lowAffA2, refoldAffA1, refoldBaseN,
    ContinuousLinearMap.comp_apply, tensorHsCongrL_apply]
  rw [hv, h3, h2]
  abel

/-- The genuine low-regularity forcing satisfies the exact low affine
fixed-point equation consumed by `lowreg_lift_two`.  The first-order family is
built from the complete refolded low action `FLo`, whose continuity and
smooth-core formula are the state-level outputs of `refold_time`; the
coefficient measurability and time-integrability packets are the independent
operator-family inputs of `lowreg_lift_two`. -/
theorem lowreg_hfLo
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {R ρ δ T : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (hRρ : R ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hNcont : Continuous (lowRegN (I := I) (M := M) g g hR hδ hreal))
    (hcore : Continuous (coreN (I := I) (M := M) g g hδ hreal))
    (hA2cont : Continuous
      (lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'))
    (hA2core : ∀ S : SmoothCcTensor g 0 2,
      lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
        (refoldCore (I := I) (M := M) g
          hρ.le hδ0 hδ_le hreal' S).a2Lo (I := I) (M := M))
    (FLo : loH3 (I := I) (M := M) g →
      (loH2 (I := I) (M := M) g →L[ℝ] loH1 (I := I) (M := M) g))
    (hFLo : Continuous FLo)
    (hFcore : ∀ S : SmoothCcTensor g 0 2,
      FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
        (c0CoreData (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal' S).a1Lo (I := I) (M := M) +
          (oneCore (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal' S).a1Lo (I := I) (M := M))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T)
    (hball : ∀ᵐ t ∂timeMeasure T,
      stateField (I := I) (M := M) g hT hT1 f t ∈
        lowerState (I := I) (M := M) g 1 R)
    (hforce : f =ᵐ[timeMeasure T] fun t =>
      tensorHsCongr (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
        (lowRegN (I := I) (M := M) g g hR hδ hreal
          (aeSetLift
            (zero_mem_lowerState (I := I) (M := M) g 1 hR.le)
            (stateField (I := I) (M := M) g hT hT1 f) t)))
    (hA2 : AEStronglyMeasurable
      (lowAffA2 (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
        hT hT1 f) (timeMeasure T))
    (C2 : NNReal)
    (hC2 : ∀ᵐ t ∂timeMeasure T,
      ‖lowAffA2 (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
        hT hT1 f t‖ ≤ (C2 : ℝ))
    (hA1 : MemLp
      (refoldAffA1 (I := I) (M := M) g ρ FLo hT hT1 f) 2 (timeMeasure T)) :
    f =
      nonautL2Map (I := I) (M := M) hT hT1
          (tensorResolventL2_isCompactOperator
            (I := I) (M := M) g 0 2)
          (lowAffA2 (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
            hT hT1 f) hA2 C2 hC2
          (refoldAffA1 (I := I) (M := M) g ρ FLo hT hT1 f) hA1 f +
        liftForceLo (I := I) (M := M) g g T := by
  let field :=
    maxRegDuhamelSolField (I := I) (M := M)
      (1 : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2)) f
  let state := stateField (I := I) (M := M) g hT hT1 f
  let A2 :=
    lowAffA2 (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' hT hT1 f
  let A1 := refoldAffA1 (I := I) (M := M) g ρ FLo hT hT1 f
  have hlift := aeSetLift_coe_ae
    (zero_mem_lowerState (I := I) (M := M) g 1 hR.le) state hball
  have hstateCoe := stateField_ae (I := I) (M := M) g hT hT1 f
  have htop := timeOp_apply_ae A2 hA2 C2 hC2 field
  have hfirst := timeOpL2_apply_ae A1 hA1
    (fun t => (zeroDuhamelCross (I := I) (M := M)
      hT hT1
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
      f).repr t)
    (zeroRepr_meas (I := I) (M := M) hT hT1
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) f)
    (zeroReprNN (I := I) (M := M) hT f)
    (zeroRepr_ae_le (I := I) (M := M) hT hT1
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) f)
  have hduh := duhamel_incl (I := I) (M := M) hT hT1
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
    (0 : tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2)) f
  have hzero := zeroRepr_ae (I := I) (M := M) hT hT1
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) f
  rw [← hduh] at hzero
  have hincl :=
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)).coeFn_compLpL
        (p := 2) (μ := timeMeasure T) field
  have hrepr :
      (fun t => (zeroDuhamelCross (I := I) (M := M)
          hT hT1
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          f).repr t) =ᵐ[timeMeasure T]
        fun t => tensorHsInclusion (I := I) (M := M)
          (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith) (field t) := by
    filter_upwards [hzero, hincl] with t hz hi
    exact hz.trans hi
  have hconst :
      liftForceLo (I := I) (M := M) g g T =ᵐ[timeMeasure T]
        fun _ => lowBaseForce (I := I) (M := M) g := by
    rw [liftForceLo_lowBase (I := I) (M := M)]
    exact timeConstL2_coeFn T (lowBaseForce (I := I) (M := M) g)
  refine Lp.ext ?_
  filter_upwards [hforce, hlift, hstateCoe, htop, hfirst, hrepr, hconst,
    Lp.coeFn_add
      (nonautL2Map (I := I) (M := M) hT hT1
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        A2 hA2 C2 hC2 A1 hA1 f)
      (liftForceLo (I := I) (M := M) g g T),
    Lp.coeFn_add
      (timeOp A2 hA2 C2 hC2 field)
      (a1L2Term (I := I) (M := M) hT hT1
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        A1 hA1 f)] with t hft hlt hst h2 h1 hr hc houter hinner
  have hstate := lowreg_N_affine (I := I) (M := M) hDim g
    hR hρ hRρ hδ0 hδ_le hδ hreal hreal' hNcont hcore hA2cont
    hA2core FLo hFLo hFcore
    (aeSetLift
      (zero_mem_lowerState (I := I) (M := M) g 1 hR.le) state t)
  have hstate' :
      tensorHsCongr (I := I) (M := M) g 0 2
          (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
          (lowRegN (I := I) (M := M) g g hR hδ hreal
            (aeSetLift
              (zero_mem_lowerState (I := I) (M := M) g 1 hR.le) state t)) =
        refoldBaseN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FLo
          (affState (I := I) (M := M) g hT hT1 f t) := by
    rw [hstate]
    congr 1
    rw [hlt, hst]
    simpa only [affState, field] using
      hsCongr_trans (I := I) (M := M) g 0 2
        (show (1 : ℝ) + 2 = ((1 : ℕ) : ℝ) + 2 by norm_num)
        (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
        (show (1 : ℝ) + 2 = (3 : ℝ) by norm_num) (field t)
  have hv :
      tensorHsCongr (I := I) (M := M) g 0 2
          (show (1 : ℝ) + 1 = 2 by norm_num)
          ((zeroDuhamelCross (I := I) (M := M)
            hT hT1
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            f).repr t) =
        incl32 (I := I) (M := M) g
          (affState (I := I) (M := M) g hT hT1 f t) := by
    rw [hr]
    simpa only [affState, field] using
      tensorHsCongr_incl (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 = 2 by norm_num)
        (show (1 : ℝ) + 2 = 3 by norm_num)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (show (2 : ℝ) ≤ 3 by norm_num) (field t)
  have hself := refoldAff_self (I := I) (M := M) g
    hρ hδ0 hδ_le hreal' FLo hT hT1 f t
    ((zeroDuhamelCross (I := I) (M := M)
      hT hT1
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
      f).repr t) hv
  change (timeOp A2 hA2 C2 hC2 field) t = A2 t (field t) at h2
  change
    (a1L2Term (I := I) (M := M) hT hT1
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
      A1 hA1 f) t =
        A1 t ((zeroDuhamelCross (I := I) (M := M)
          hT hT1
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          f).repr t) at h1
  change (f : timeL2 (loH1 (I := I) (M := M) g) T) t =
    (nonautL2Map (I := I) (M := M) hT hT1
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
      A2 hA2 C2 hC2 A1 hA1 f +
        liftForceLo (I := I) (M := M) g g T) t
  rw [houter, Pi.add_apply]
  change (f : timeL2 (loH1 (I := I) (M := M) g) T) t =
    (timeOp A2 hA2 C2 hC2 field +
      a1L2Term (I := I) (M := M) hT hT1
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        A1 hA1 f) t +
      (liftForceLo (I := I) (M := M) g g T) t
  rw [hinner, Pi.add_apply, h2, h1, hc]
  rw [hft, hstate', ← hself]
  abel

/-- The complete affine packet on one radius, on both adjacent scales, along a
given trajectory.

It *consumes* the trajectory-free affine packet of `refold_aff` — the two
refolded first-order actions `FHi`, `FLo` with their continuity, the low
smooth-core formula, the common affine growth constants `Z, L` and the
Sobolev-inclusion square — and produces the low second-order family with its
`NNReal` pointwise bound, the two first-order `MemLp` witnesses with their
time-`L²` Minkowski bounds `≤ L‖duhH3 f‖ + √T·Z`, the a.e. Sobolev-inclusion
square of the two first-order families, and the exact low fixed-point equality.
Taking the packet instead of producing it is what lets a caller cap its state
radius against `L` before any trajectory exists.

The only trajectory hypotheses are the lower-state ball and the Nemytskii
forcing identity: the first-order sizes are certified in `L²_t` through
`memLp_clm_affine`, never pointwise in time. -/
theorem lowreg_hfLo_data
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {R ρ δ T B2 Z L : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hRρ : R ≤ ρ)
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hNcont : Continuous (lowRegN (I := I) (M := M) g g hR hδ hreal))
    (hcore : Continuous (coreN (I := I) (M := M) g g hδ hreal))
    (hA2cont : Continuous
      (lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'))
    (hA2core : ∀ S : SmoothCcTensor g 0 2,
      lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
        (refoldCore (I := I) (M := M) g
          hρ.le hδ0 hδ_le hreal' S).a2Lo (I := I) (M := M))
    (hB2 : 0 ≤ B2)
    (hA2bd : ∀ v : loH2 (I := I) (M := M) g,
      ‖lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v‖ ≤ B2)
    (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (FHi : loH3 (I := I) (M := M) g →
      (loH3 (I := I) (M := M) g →L[ℝ] loH2 (I := I) (M := M) g))
    (FLo : loH3 (I := I) (M := M) g →
      (loH2 (I := I) (M := M) g →L[ℝ] loH1 (I := I) (M := M) g))
    (hFHi : Continuous FHi) (hFLo : Continuous FLo)
    (hFLoCore : ∀ S : SmoothCcTensor g 0 2,
      FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
        (c0CoreData (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal' S).a1Lo (I := I) (M := M) +
          (oneCore (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal' S).a1Lo (I := I) (M := M))
    (hFHiBd : ∀ x : loH3 (I := I) (M := M) g, ‖FHi x‖ ≤ Z + L * ‖x‖)
    (hFLoBd : ∀ x : loH3 (I := I) (M := M) g, ‖FLo x‖ ≤ Z + L * ‖x‖)
    (hFComm : ∀ x : loH3 (I := I) (M := M) g,
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp (FHi x) =
        (FLo x).comp (incl32 (I := I) (M := M) g))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T)
    (hball : ∀ᵐ t ∂timeMeasure T,
      stateField (I := I) (M := M) g hT hT1 f t ∈
        lowerState (I := I) (M := M) g 1 R)
    (hforce : f =ᵐ[timeMeasure T] fun t =>
      tensorHsCongr (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
        (lowRegN (I := I) (M := M) g g hR hδ hreal
          (aeSetLift
            (zero_mem_lowerState (I := I) (M := M) g 1 hR.le)
            (stateField (I := I) (M := M) g hT hT1 f) t))) :
    ∃ (C2 : NNReal)
      (hA2 : AEStronglyMeasurable
        (lowAffA2 (I := I) (M := M) g
          hρ.le hδ0 hδ_le hreal' hT hT1 f) (timeMeasure T))
      (hC2 : ∀ᵐ t ∂timeMeasure T,
        ‖lowAffA2 (I := I) (M := M) g
          hρ.le hδ0 hδ_le hreal' hT hT1 f t‖ ≤ (C2 : ℝ))
      (hA1 : MemLp
        (refoldAffA1 (I := I) (M := M) g ρ FLo hT hT1 f) 2
          (timeMeasure T))
      (hA1Hi : MemLp
        (refoldAffA1Hi (I := I) (M := M) g ρ FHi hT hT1 f) 2
          (timeMeasure T)),
      (C2 : ℝ) = B2 ∧
      ‖hA1.toLp (refoldAffA1 (I := I) (M := M) g ρ FLo hT hT1 f)‖ ≤
          L * ‖duhH3 (I := I) (M := M) g hT hT1 f‖ + Real.sqrt T * Z ∧
        ‖hA1Hi.toLp
            (refoldAffA1Hi (I := I) (M := M) g ρ FHi hT hT1 f)‖ ≤
          L * ‖duhH3 (I := I) (M := M) g hT hT1 f‖ + Real.sqrt T * Z ∧
        (∀ᵐ t ∂timeMeasure T,
          (tensorHsInclusion (I := I) (M := M)
              (g := g) (r := 0) (s := 2)
              (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp
              (refoldAffA1Hi (I := I) (M := M) g ρ FHi hT hT1 f t) =
            (refoldAffA1 (I := I) (M := M) g ρ FLo hT hT1 f t).comp
              (tensorHsInclusion (I := I) (M := M)
                (g := g) (r := 0) (s := 2)
                (show (1 : ℝ) + 1 ≤ (2 : ℝ) + 1 by norm_num))) ∧
        f =
          nonautL2Map (I := I) (M := M) hT hT1
              (tensorResolventL2_isCompactOperator
                (I := I) (M := M) g 0 2)
              (lowAffA2 (I := I) (M := M) g
                hρ.le hδ0 hδ_le hreal' hT hT1 f) hA2 C2 hC2
              (refoldAffA1 (I := I) (M := M) g ρ FLo hT hT1 f) hA1 f +
            liftForceLo (I := I) (M := M) g g T := by
  obtain ⟨C2, hC2eq, hA2, hC2⟩ :=
    lowAffA2_data (I := I) (M := M) g
      hρ.le hδ0 hδ_le hreal' hA2cont hB2 hA2bd hT hT1 f
  obtain ⟨hA1, hA1norm⟩ :=
    refoldAffA1_memLp (I := I) (M := M) g hρ.le FLo hFLo hZ hL hFLoBd hT hT1 f
  obtain ⟨hA1Hi, hA1HiNorm⟩ :=
    refoldAffA1Hi_memLp (I := I) (M := M) g hρ.le FHi hFHi hZ hL hFHiBd
      hT hT1 f
  have hsq :=
    refoldAffA1_compat (I := I) (M := M) g ρ FHi FLo hFComm hT hT1 f
  have heq := lowreg_hfLo (I := I) (M := M) hDim g
    hR hρ hRρ hδ0 hδ_le hδ hreal hreal'
    hNcont hcore hA2cont hA2core FLo hFLo hFLoCore
    hT hT1 f hball hforce hA2 C2 hC2 hA1
  exact ⟨C2, hA2, hC2, hA1, hA1Hi, hC2eq, hA1norm, hA1HiNorm, hsq, heq⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
