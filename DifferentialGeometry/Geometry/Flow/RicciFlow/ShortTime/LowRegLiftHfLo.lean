import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegA1LoPair

/-!
# The low-regularity forcing satisfies the low affine fixed-point equation

The coefficient families here split `lowBaseA` into its second- and
first-order summands at the exact Sobolev exponents consumed by
`lowreg_lift_two`.  The radial maps stay inside the families, so their
self-application is definitionally the zero-based low action and does not
double-count the principal arm.
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

private def stateField
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

/-- The first-order low family along the order-one Duhamel field.  It acts on
the canonical intermediate `H2` representative and contains the same radial
factor as the first-order summand of `lowBaseA`. -/
def lowAffA1
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) :
    ℝ → tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 1) →L[ℝ]
      loH1 (I := I) (M := M) g :=
  fun t =>
    (lowA1Lo (I := I) (M := M) g hρ hδ0 hδ_le hreal
        (affState (I := I) (M := M) g hT hT1 f t)).comp
      ((radialCLM (I := I) (M := M) g
          (show (0 : ℝ) ≤ 2 by norm_num) ρ
          (incl32 (I := I) (M := M) g
            (affState (I := I) (M := M) g hT hT1 f t))).comp
        (tensorHsCongrL (I := I) (M := M) g 0 2
          (show (1 : ℝ) + 1 = 2 by norm_num)))

/-- Radialization and exponent normalization do not enlarge the low
first-order coefficient norm. -/
theorem lowAffA1_le
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) (t : ℝ) :
    ‖lowAffA1 (I := I) (M := M) g hρ hδ0 hδ_le hreal hT hT1 f t‖ ≤
      ‖lowA1Lo (I := I) (M := M) g hρ hδ0 hδ_le hreal
        (affState (I := I) (M := M) g hT hT1 f t)‖ := by
  let A1 :=
    lowA1Lo (I := I) (M := M) g hρ hδ0 hδ_le hreal
      (affState (I := I) (M := M) g hT hT1 f t)
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

/-- Along an a.e. bounded `H3` Duhamel trajectory, the exact first-order
family is strongly measurable, square-integrable in time, and uniformly
bounded in operator norm.  The bound is ball-local; no false global affine
growth estimate is assumed. -/
theorem lowAffA1_data
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hpair : LowA1CorePair (I := I) (M := M)
      g hρ hδ0 hδ_le hreal)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T)
    {R : ℝ} (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖maxRegDuhamelSolField (I := I) (M := M)
        (1 : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2)) f t‖ ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      AEStronglyMeasurable
          (lowAffA1 (I := I) (M := M)
            g hρ hδ0 hδ_le hreal hT hT1 f) (timeMeasure T) ∧
        MemLp
          (lowAffA1 (I := I) (M := M)
            g hρ hδ0 hδ_le hreal hT hT1 f) 2 (timeMeasure T) ∧
        (∀ᵐ t ∂timeMeasure T,
          ‖lowAffA1 (I := I) (M := M)
            g hρ hδ0 hδ_le hreal hT hT1 f t‖ ≤ C) := by
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
  have hA1 : AEStronglyMeasurable
      (fun t => lowA1Lo (I := I) (M := M) g hρ hδ0 hδ_le hreal (u t))
      (timeMeasure T) :=
    (lowA1Lo_cont (I := I) (M := M) hpair).comp_aestronglyMeasurable hu
  have hR2 : AEStronglyMeasurable
      (fun t => radialCLM (I := I) (M := M) g
        (show (0 : ℝ) ≤ 2 by norm_num) ρ
          (incl32 (I := I) (M := M) g (u t))) (timeMeasure T) :=
    radialCLM_aemeas (I := I) (M := M) g (by norm_num) hju
  have hQ : AEStronglyMeasurable
      (fun _ : ℝ => tensorHsCongrL (I := I) (M := M) g 0 2
        (show (1 : ℝ) + 1 = 2 by norm_num)) (timeMeasure T) :=
    aestronglyMeasurable_const
  have hR2Q : AEStronglyMeasurable
      (fun t =>
        (radialCLM (I := I) (M := M) g
          (show (0 : ℝ) ≤ 2 by norm_num) ρ
            (incl32 (I := I) (M := M) g (u t))).comp
          (tensorHsCongrL (I := I) (M := M) g 0 2
            (show (1 : ℝ) + 1 = 2 by norm_num))) (timeMeasure T) :=
    (ContinuousLinearMap.compL ℝ
      (tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 1))
      (loH2 (I := I) (M := M) g)
      (loH2 (I := I) (M := M) g)).continuous₂
        |>.comp_aestronglyMeasurable₂ hR2 hQ
  have hmeas : AEStronglyMeasurable
      (lowAffA1 (I := I) (M := M)
        g hρ hδ0 hδ_le hreal hT hT1 f) (timeMeasure T) := by
    simpa only [lowAffA1, u] using
      (ContinuousLinearMap.compL ℝ
        (tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 1))
        (loH2 (I := I) (M := M) g)
        (loH1 (I := I) (M := M) g)).continuous₂
          |>.comp_aestronglyMeasurable₂ hA1 hR2Q
  have huball : ∀ᵐ t ∂timeMeasure T, ‖u t‖ ≤ R := by
    filter_upwards [hball] with t ht
    simpa only [u, affState, norm_tensorHsCongr] using ht
  obtain ⟨C, hC, hCstate⟩ :=
    lowA1Lo_ball (I := I) (M := M) g hρ hδ0 hδ_le hreal hpair hR
  have hbd : ∀ᵐ t ∂timeMeasure T,
      ‖lowAffA1 (I := I) (M := M)
        g hρ hδ0 hδ_le hreal hT hT1 f t‖ ≤ C := by
    filter_upwards [huball] with t ht
    exact (lowAffA1_le (I := I) (M := M)
      g hρ hδ0 hδ_le hreal hT hT1 f t).trans (hCstate (u t) ht)
  have hmem : MemLp
      (lowAffA1 (I := I) (M := M)
        g hρ hδ0 hδ_le hreal hT hT1 f) 2 (timeMeasure T) :=
    MemLp.of_bound
      (f := lowAffA1 (I := I) (M := M)
        g hρ hδ0 hδ_le hreal hT hT1 f)
      (p := 2) (μ := timeMeasure T) hmeas C hbd
  exact ⟨C, hC, hmeas, hmem, hbd⟩

private theorem lowAff_self
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (loH1 (I := I) (M := M) g) T) (t : ℝ)
    (v : tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 1))
    (hv : tensorHsCongr (I := I) (M := M) g 0 2
        (show (1 : ℝ) + 1 = 2 by norm_num) v =
      incl32 (I := I) (M := M) g
        (affState (I := I) (M := M) g hT hT1 f t)) :
    lowAffA2 (I := I) (M := M) g hρ hδ0 hδ_le hreal hT hT1 f t
          (maxRegDuhamelSolField (I := I) (M := M)
            (1 : ℝ) hT hT1 0 f t) +
        lowAffA1 (I := I) (M := M) g hρ hδ0 hδ_le hreal hT hT1 f t v =
      lowBaseA (I := I) (M := M) g hρ hδ0 hδ_le hreal
        (affState (I := I) (M := M) g hT hT1 f t)
        (affState (I := I) (M := M) g hT hT1 f t) := by
  simp only [lowAffA2, lowAffA1, lowBaseA,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    tensorHsCongrL_apply]
  rw [hv]
  rfl

/-- On a sufficiently small radial cutoff, the genuine low-regularity forcing
satisfies the exact low affine fixed-point equation consumed by
`lowreg_lift_two`.  The coefficient measurability and time-integrability
packets are the independent operator-family inputs of that theorem; no
first-order core-pair hypothesis remains. -/
theorem lowreg_hfLo
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ {R ρ δ T : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (_ : ρ ≤ ρ₀)
        (_ : R ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδ : δ < 1)
        (hreal : ∀ S : SmoothCcTensor g 0 2,
          ‖smoothCcToTensorHs (I := I) (M := M) g
              (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ)
        (hreal' : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ)
        (_ : Continuous (lowRegN (I := I) (M := M) g g hR hδ hreal))
        (_ : Continuous (coreN (I := I) (M := M) g g hδ hreal))
        (_ : Continuous
          (lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'))
        (_ : ∀ S : SmoothCcTensor g 0 2,
          lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
              (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
            (lowCoreData (I := I) (M := M) g
              hρ.le hδ0 hδ_le hreal' S).a2Lo (I := I) (M := M))
        (hT : 0 < T) (hT1 : T ≤ 1)
        (f : timeL2 (loH1 (I := I) (M := M) g) T)
        (_ : ∀ᵐ t ∂timeMeasure T,
          stateField (I := I) (M := M) g hT hT1 f t ∈
            lowerState (I := I) (M := M) g 1 R)
        (_ : f =ᵐ[timeMeasure T] fun t =>
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
          (lowAffA1 (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
            hT hT1 f) 2 (timeMeasure T)),
        f =
          nonautL2Map (I := I) (M := M) hT hT1
              (tensorResolventL2_isCompactOperator
                (I := I) (M := M) g 0 2)
              (lowAffA2 (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
                hT hT1 f) hA2 C2 hC2
              (lowAffA1 (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
                hT hT1 f) hA1 f +
            liftForceLo (I := I) (M := M) g g T := by
  obtain ⟨ρ₀, hρ₀, hpair⟩ :=
    lowA1Core_pair (I := I) (M := M) hDim g
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro R ρ δ T hR hρ hρ_le hRρ hδ0 hδ_le hδ hreal hreal'
    hNcont hcore hA2cont hA2core hT hT1 f hball hforce hA2 C2 hC2 hA1
  let field :=
    maxRegDuhamelSolField (I := I) (M := M)
      (1 : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2)) f
  let state := stateField (I := I) (M := M) g hT hT1 f
  let A2 :=
    lowAffA2 (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' hT hT1 f
  let A1 :=
    lowAffA1 (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' hT hT1 f
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
    hA2core (hpair hρ hρ_le hδ0 hδ_le hreal')
    (aeSetLift
      (zero_mem_lowerState (I := I) (M := M) g 1 hR.le) state t)
  have hstate' :
      tensorHsCongr (I := I) (M := M) g 0 2
          (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
          (lowRegN (I := I) (M := M) g g hR hδ hreal
            (aeSetLift
              (zero_mem_lowerState (I := I) (M := M) g 1 hR.le) state t)) =
        lowBaseN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
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
  have hself := lowAff_self (I := I) (M := M) g
    hρ.le hδ0 hδ_le hreal' hT hT1 f t
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
  rw [hft, hstate',
    lowBaseN_frozen (I := I) (M := M) g hρ hδ0 hδ_le hreal'
      (affState (I := I) (M := M) g hT hT1 f t)]
  rw [← hself]
  abel

/-- The complete low affine packet on one radius: the second-order family,
its `NNReal` pointwise bound, the first-order `MemLp` witness and uniform
`M`-bound, and the exact fixed-point equality.  The only trajectory hypothesis
beyond the lower-state ball is the honest a.e. `H3` bound used by the
first-order coefficient. -/
theorem lowreg_hfLo_data
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ {R ρ δ T B2 B3 : ℝ}
        (hR : 0 < R) (hρ : 0 < ρ) (_ : ρ ≤ ρ₀)
        (_ : R ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδ : δ < 1)
        (hreal : ∀ S : SmoothCcTensor g 0 2,
          ‖smoothCcToTensorHs (I := I) (M := M) g
              (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ)
        (hreal' : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ)
        (_ : Continuous
          (lowRegN (I := I) (M := M) g g hR hδ hreal))
        (_ : Continuous (coreN (I := I) (M := M) g g hδ hreal))
        (_ : Continuous
          (lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'))
        (_ : ∀ S : SmoothCcTensor g 0 2,
          lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
              (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
            (lowCoreData (I := I) (M := M) g
              hρ.le hδ0 hδ_le hreal' S).a2Lo (I := I) (M := M))
        (_ : 0 ≤ B2)
        (_ : ∀ v : loH2 (I := I) (M := M) g,
          ‖lowA2Lo (I := I) (M := M) g
            hρ.le hδ0 hδ_le hreal' v‖ ≤ B2)
        (hT : 0 < T) (hT1 : T ≤ 1)
        (f : timeL2 (loH1 (I := I) (M := M) g) T)
        (_ : ∀ᵐ t ∂timeMeasure T,
          stateField (I := I) (M := M) g hT hT1 f t ∈
            lowerState (I := I) (M := M) g 1 R)
        (_ : f =ᵐ[timeMeasure T] fun t =>
          tensorHsCongr (I := I) (M := M) g 0 2
            (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
            (lowRegN (I := I) (M := M) g g hR hδ hreal
              (aeSetLift
                (zero_mem_lowerState (I := I) (M := M) g 1 hR.le)
                (stateField (I := I) (M := M) g hT hT1 f) t)))
        (_ : 0 ≤ B3)
        (_ : ∀ᵐ t ∂timeMeasure T,
          ‖maxRegDuhamelSolField (I := I) (M := M)
            (1 : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2)) f t‖ ≤ B3),
        ∃ (C2 : NNReal)
          (hA2 : AEStronglyMeasurable
            (lowAffA2 (I := I) (M := M) g
              hρ.le hδ0 hδ_le hreal' hT hT1 f) (timeMeasure T))
          (hC2 : ∀ᵐ t ∂timeMeasure T,
            ‖lowAffA2 (I := I) (M := M) g
              hρ.le hδ0 hδ_le hreal' hT hT1 f t‖ ≤ (C2 : ℝ))
          (hA1 : MemLp
            (lowAffA1 (I := I) (M := M) g
              hρ.le hδ0 hδ_le hreal' hT hT1 f) 2 (timeMeasure T)),
          ∃ B1 : ℝ, 0 ≤ B1 ∧
            (∀ᵐ t ∂timeMeasure T,
              ‖lowAffA1 (I := I) (M := M) g
                hρ.le hδ0 hδ_le hreal' hT hT1 f t‖ ≤ B1) ∧
            f =
              nonautL2Map (I := I) (M := M) hT hT1
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) g 0 2)
                  (lowAffA2 (I := I) (M := M) g
                    hρ.le hδ0 hδ_le hreal' hT hT1 f) hA2 C2 hC2
                  (lowAffA1 (I := I) (M := M) g
                    hρ.le hδ0 hδ_le hreal' hT hT1 f) hA1 f +
                liftForceLo (I := I) (M := M) g g T := by
  obtain ⟨ρH, hρH, hH⟩ := lowreg_hfLo (I := I) (M := M) hDim g
  obtain ⟨ρP, hρP, hP⟩ := lowA1Core_pair (I := I) (M := M) hDim g
  refine ⟨min ρH ρP, lt_min hρH hρP, ?_⟩
  intro R ρ δ T B2 B3 hR hρ hρ_le hRρ hδ0 hδ_le hδ
    hreal hreal' hNcont hcore hA2cont hA2core hB2 hA2bd
    hT hT1 f hball hforce hB3 hball3
  have hρH' : ρ ≤ ρH := hρ_le.trans (min_le_left _ _)
  have hρP' : ρ ≤ ρP := hρ_le.trans (min_le_right _ _)
  have hpair : LowA1CorePair (I := I) (M := M)
      g hρ.le hδ0 hδ_le hreal' :=
    hP hρ hρP' hδ0 hδ_le hreal'
  obtain ⟨C2, -, hA2, hC2⟩ :=
    lowAffA2_data (I := I) (M := M) g
      hρ.le hδ0 hδ_le hreal' hA2cont hB2 hA2bd hT hT1 f
  obtain ⟨B1, hB1, -, hA1, hA1bd⟩ :=
    lowAffA1_data (I := I) (M := M) g
      hρ.le hδ0 hδ_le hreal' hpair hT hT1 f hB3 hball3
  have heq := hH hR hρ hρH' hRρ hδ0 hδ_le hδ hreal hreal'
    hNcont hcore hA2cont hA2core hT hT1 f hball hforce hA2 C2 hC2 hA1
  exact ⟨C2, hA2, hC2, hA1, B1, hB1, hA1bd, heq⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
