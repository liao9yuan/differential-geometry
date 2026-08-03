import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseTimeA2
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseTimeA1
import DifferentialGeometry.Analysis.DenseExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgA1Pair
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgH2

/-!
# Fixed-background low-base radial core

This module evaluates the canonical low-base action at the existing spectral
radial state while retaining an independent fixed DeTurck background.
-/

noncomputable section

open Bundle Manifold MeasureTheory
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev metricH3 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (3 : ℝ)

omit [BoundarylessManifold I M] in
private theorem zero_fibre_bound
    (g : SmoothRiemannianMetric I M) {δ : ℝ} (hδ : 0 ≤ δ) :
    gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ := by
  intro x u v
  refine
    (gFibreOpBound_ccTensorBilinSymm_zero
      (I := I) (M := M) g x u v).trans ?_
  simp only [zero_mul]
  exact mul_nonneg
    (mul_nonneg hδ (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

/-- The canonical radial low-base bundle with an independent fixed DeTurck
background. -/
noncomputable def lowCoreDataBg
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) : LowBaseActionData g :=
  lowBaseData (I := I) (M := M) g gB
    (lowRadial (I := I) (M := M) g ρ T)
    (lt_of_le_of_lt hδ_le (by norm_num))
    (hreal _ (lowRadial_norm (I := I) (M := M) g hρ T))
    (zero_fibre_bound (I := I) (M := M) g hδ0)

/-- The fixed-background radial bundle gives the exact zero-based smooth
Ricci--DeTurck remainder split. -/
theorem lowCoreBg_split
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    let S := lowRadial (I := I) (M := M) g ρ T
    let A := lowCoreDataBg (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T
    deTurckSmoothRemainder (I := I) g gB S
          (lt_of_le_of_lt hδ_le (by norm_num))
          (hreal S (lowRadial_norm (I := I) (M := M) g hρ T)) -
        deTurckSmoothRemainder (I := I) g gB
          (0 : SmoothCcTensor g 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num))
          (zero_fibre_bound (I := I) (M := M) g hδ0) =
      A.a2 (I := I) (M := M) S + A.a1 (I := I) (M := M) S := by
  obtain ⟨_, _, hsplit⟩ := lowData_split (I := I) (M := M) g gB
  let S := lowRadial (I := I) (M := M) g ρ T
  have hs := hsplit S
    (lowRadial_symm (I := I) (M := M) g ρ T)
    hδ_le hδ0
    (hreal S (lowRadial_norm (I := I) (M := M) g hρ T))
    (zero_fibre_bound (I := I) (M := M) g hδ0)
  simpa only [S, lowCoreDataBg] using hs.1

private abbrev lowA2LoBgOp (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
    tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

private noncomputable def lowBgRep
    (g : SmoothRiemannianMetric I M)
    (x : LowBaseTimeInternal.LowCore (I := I) (M := M) g) :
    SmoothCcTensor g 0 2 :=
  Classical.choose x.property

private theorem lowBgRep_spec
    (g : SmoothRiemannianMetric I M)
    (x : LowBaseTimeInternal.LowCore (I := I) (M := M) g) :
    ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)
        (lowBgRep (I := I) (M := M) g x) =
      (x : metricH2 (I := I) (M := M) g) :=
  Classical.choose_spec x.property

private noncomputable def lowBgCore
    {Y : Type*} (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (proj : LowBaseActionData g → Y) :
    LowBaseTimeInternal.LowCore (I := I) (M := M) g → Y :=
  fun x => proj (lowCoreDataBg (I := I) (M := M)
    g gB hρ hδ0 hδ_le hreal (lowBgRep (I := I) (M := M) g x))

private theorem lowBgCore_value
    {Y : Type*} (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (proj : LowBaseActionData g → Y) (T : SmoothCcTensor g 0 2) :
    lowBgCore (I := I) (M := M) g gB hρ hδ0 hδ_le hreal proj
        ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩ =
      proj (lowCoreDataBg (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T) := by
  have hrep : lowBgRep (I := I) (M := M) g
      ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩ = T := by
    apply ccToHs_injective (I := I) (M := M) g 2 (2 : ℝ)
    simpa only [ccToHsLin_apply] using
      lowBgRep_spec (I := I) (M := M) g
        ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩
  simp only [lowBgCore, hrep]

private noncomputable def highBgRep
    (g : SmoothRiemannianMetric I M)
    (x : LowBaseTimeInternal.HighCore (I := I) (M := M) g) :
    SmoothCcTensor g 0 2 :=
  Classical.choose x.property

private theorem highBgRep_spec
    (g : SmoothRiemannianMetric I M)
    (x : LowBaseTimeInternal.HighCore (I := I) (M := M) g) :
    ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)
        (highBgRep (I := I) (M := M) g x) =
      (x : metricH3 (I := I) (M := M) g) :=
  Classical.choose_spec x.property

private noncomputable def highBgCore
    {Y : Type*} (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (proj : LowBaseActionData g → Y) :
    LowBaseTimeInternal.HighCore (I := I) (M := M) g → Y :=
  fun x => proj (lowCoreDataBg (I := I) (M := M)
    g gB hρ hδ0 hδ_le hreal (highBgRep (I := I) (M := M) g x))

private theorem highBgCore_value
    {Y : Type*} (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (proj : LowBaseActionData g → Y) (T : SmoothCcTensor g 0 2) :
    highBgCore (I := I) (M := M) g gB hρ hδ0 hδ_le hreal proj
        ⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩ =
      proj (lowCoreDataBg (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T) := by
  have hrep : highBgRep (I := I) (M := M) g
      ⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩ = T := by
    apply ccToHs_injective (I := I) (M := M) g 2 (3 : ℝ)
    simpa only [ccToHsLin_apply] using
      highBgRep_spec (I := I) (M := M) g
        ⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩
  simp only [highBgCore, hrep]

/-- Ball-local smooth-core pair predicate for the arbitrary-background low
first-order action. -/
def BgA1CorePair
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) : Prop :=
  ∀ r : ℝ, ∃ K : ℝ, ∀ T U : SmoothCcTensor g 0 2,
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ r →
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r →
      ‖(lowCoreDataBg (I := I) (M := M)
            g gB hρ hδ0 hδ_le hreal T).a1Lo (I := I) (M := M) -
          (lowCoreDataBg (I := I) (M := M)
            g gB hρ hδ0 hδ_le hreal U).a1Lo (I := I) (M := M)‖ ≤
        K * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
          ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖

/-- Ball-local smooth-core pair predicate for the high first-order action. -/
def BgA1HiCorePair
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) : Prop :=
  ∀ r : ℝ, ∃ K : ℝ, ∀ T U : SmoothCcTensor g 0 2,
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ r →
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r →
      ‖(lowCoreDataBg (I := I) (M := M)
            g gB hρ hδ0 hδ_le hreal T).a1Hi (I := I) (M := M) -
          (lowCoreDataBg (I := I) (M := M)
            g gB hρ hδ0 hδ_le hreal U).a1Hi (I := I) (M := M)‖ ≤
        K * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
          ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖

/-- The radial high first-order coefficient as an `H3 → H2` operator-valued
map on the completed `H3` state space. -/
noncomputable def lowA1HiBg
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    metricH3 (I := I) (M := M) g →
      LowBaseTimeInternal.A1HiOp (I := I) (M := M) g :=
  Dense.extend
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (highBgCore (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
      fun A => A.a1Hi (I := I) (M := M))

/-- The arbitrary-background radial first-order coefficient as an `H2 → H1`
operator-valued map on the completed `H3` state space. -/
noncomputable def lowA1LoBg
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    metricH3 (I := I) (M := M) g →
      LowBaseTimeInternal.A1LoOp (I := I) (M := M) g :=
  Dense.extend
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (highBgCore (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
      fun A => A.a1Lo (I := I) (M := M))

private theorem inclCc32_bg
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
        (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T) =
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorHsInclusion_coeff_apply, ccTensorToHs_coeff,
    ccTensorToHs_coeff]

private theorem ccToHsSub_bg
    (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (T U : SmoothCcTensor g 0 2) :
    ccTensorToHs (I := I) (M := M) g 2 σ (T - U) =
      ccTensorToHs (I := I) (M := M) g 2 σ T -
        ccTensorToHs (I := I) (M := M) g 2 σ U := by
  simpa only [ccToHsLin_apply] using
    map_sub (ccToHsLin (I := I) (M := M) g 2 σ) T U

private theorem sqrt_scale
    (q d : ℝ) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    Real.sqrt (q * d ^ 2) = Real.sqrt q * d := by
  rw [Real.sqrt_mul hq, Real.sqrt_sq hd]

/-- One positive spectral cutoff radius makes the arbitrary-background radial
low first-order action locally Lipschitz on every bounded H3 core ball. -/
theorem radialA1Bg_pair
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (_ : ρ ≤ ρ₀)
        (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hreal : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ),
        BgA1CorePair (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal := by
  obtain ⟨ρ₀, Bs, Z0, Z1, O0, O1, Ca, hρ₀, hBs, hZ0, hZ1,
      hO0, hO1, hCa, hpair⟩ :=
    a1Lo_bg_pair (I := I) (M := M) hDim g gB
  obtain ⟨C₂, hC₂, hjet₂⟩ := jet2_le_hs (I := I) (M := M) g
  obtain ⟨C₃, hC₃, hjet₃⟩ := jet3_le_hs (I := I) (M := M) g
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ δ hρ hρρ₀ hδ0 hδ_le hreal
  dsimp only [BgA1CorePair]
  intro r
  let R₂ : ℝ := C₂ * ρ
  let A₃ : ℝ := C₃ * r
  let L : ℝ := 1 + (1 / ρ) * r
  let P : ℝ := 1 + A₃ + A₃ ^ 2
  let E0 : ℝ :=
    2 *
      (Bs R₂ * (P ^ 4 * (C₂ ^ 2 + 1)) +
        (Z0 R₂ A₃ * C₂ + Z1 A₃) ^ 2)
  let E1 : ℝ := O0 * C₃ * L + O1 + O1 * A₃
  let K : ℝ := Ca * (Real.sqrt E0 + E1)
  refine ⟨K, ?_⟩
  intro T U hTr hUr
  have hr : 0 ≤ r := (norm_nonneg _).trans hTr
  have hρ0 : 0 ≤ ρ := hρ.le
  have hR₂ : 0 ≤ R₂ := mul_nonneg hC₂ hρ0
  have hA₃ : 0 ≤ A₃ := mul_nonneg hC₃ hr
  have hρinv : 0 ≤ (1 / ρ : ℝ) := (one_div_pos.mpr hρ).le
  have hL : 0 ≤ L := by
    simp only [L]
    positivity
  let D : ℝ :=
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
      ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖
  let D₂ : ℝ := C₂ * D
  let D₃ : ℝ := C₃ * L * D
  have hD : 0 ≤ D := norm_nonneg _
  have hD₂ : 0 ≤ D₂ := mul_nonneg hC₂ hD
  have hD₃ : 0 ≤ D₃ := mul_nonneg (mul_nonneg hC₃ hL) hD
  let T₀ : SmoothCcTensor g 0 2 :=
    lowRadial (I := I) (M := M) g ρ T
  let U₀ : SmoothCcTensor g 0 2 :=
    lowRadial (I := I) (M := M) g ρ U
  have hT₀ρ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T₀‖ ≤ ρ :=
    lowRadial_norm (I := I) (M := M) g hρ0 T
  have hU₀ρ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U₀‖ ≤ ρ :=
    lowRadial_norm (I := I) (M := M) g hρ0 U
  have hTδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g T₀) δ :=
    hreal T₀ hT₀ρ
  have hUδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g U₀) δ :=
    hreal U₀ hU₀ρ
  have hZδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2)) δ :=
    zero_fibre_bound (I := I) (M := M) g hδ0
  have hT₂ :
      lowJetSq (I := I) (M := M) g 2 T₀ ≤ R₂ ^ 2 := by
    refine (hjet₂ T₀).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC₂ (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hT₀ρ hC₂) 2
  have hU₂ :
      lowJetSq (I := I) (M := M) g 2 U₀ ≤ R₂ ^ 2 := by
    refine (hjet₂ U₀).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC₂ (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hU₀ρ hC₂) 2
  have hT₀top :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T₀‖ ≤ r := by
    have hrad := lowRadialH3_le (I := I) (M := M) g hρ
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T)
    rw [lowRadialH3_core (I := I) (M := M) g hρ T] at hrad
    simp only [ccToHsLin_apply] at hrad
    exact hrad.trans hTr
  have hU₀top :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U₀‖ ≤ r := by
    have hrad := lowRadialH3_le (I := I) (M := M) g hρ
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U)
    rw [lowRadialH3_core (I := I) (M := M) g hρ U] at hrad
    simp only [ccToHsLin_apply] at hrad
    exact hrad.trans hUr
  have hT₃ :
      lowJetSq (I := I) (M := M) g 3 T₀ ≤ A₃ ^ 2 := by
    refine (hjet₃ T₀).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC₃ (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hT₀top hC₃) 2
  have hU₃ :
      lowJetSq (I := I) (M := M) g 3 U₀ ≤ A₃ ^ 2 := by
    refine (hjet₃ U₀).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC₃ (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hU₀top hC₃) 2
  have hincl :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ D := by
    have h := tensorHsInclusion_norm_le (I := I) (M := M)
      (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
      (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T -
        ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U)
    rw [map_sub, inclCc32_bg (I := I) (M := M) g T,
      inclCc32_bg (I := I) (M := M) g U] at h
    simpa only [D, ccToHsLin_apply] using h
  have hrad₂ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T₀ - U₀)‖ ≤ D := by
    rw [ccToHsSub_bg]
    exact (lowRadial_lip (I := I) (M := M) g hρ0 T U).trans hincl
  have hTU₂ :
      lowJetSq (I := I) (M := M) g 2 (T₀ - U₀) ≤ D₂ ^ 2 := by
    refine (hjet₂ (T₀ - U₀)).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC₂ (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hrad₂ hC₂) 2
  have hmax :
      max
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r :=
    max_le hTr hUr
  have hprod :
      max
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤
        r * D :=
    mul_le_mul hmax hincl (norm_nonneg _) hr
  have hrad₃ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (T₀ - U₀)‖ ≤
        L * D := by
    rw [ccToHsSub_bg]
    refine (lowRadial_h3_sub (I := I) (M := M) g hρ T U).trans ?_
    have hscaled := mul_le_mul_of_nonneg_left hprod hρinv
    have hscaled' :
        (1 / ρ) *
              max
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
                ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤
          (1 / ρ) * (r * D) := by
      calc
        (1 / ρ) *
              max
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
                ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ =
            (1 / ρ) *
              (max
                  ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                  ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
                ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
                  ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖) := by ring
        _ ≤ (1 / ρ) * (r * D) := hscaled
    calc
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ +
            (1 / ρ) *
              max
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
                ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤
          D + (1 / ρ) * (r * D) := by
        change D + _ ≤ D + _
        exact add_le_add_right hscaled' D
      _ = L * D := by
        simp only [L]
        ring
  have hTU₃ :
      lowJetSq (I := I) (M := M) g 3 (T₀ - U₀) ≤ D₃ ^ 2 := by
    refine (hjet₃ (T₀ - U₀)).trans ?_
    simpa only [D₃, mul_assoc] using pow_le_pow_left₀
      (mul_nonneg hC₃ (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hrad₃ hC₃) 2
  have hout := hpair T₀ U₀
    (lowRadial_symm (I := I) (M := M) g ρ T)
    (lowRadial_symm (I := I) (M := M) g ρ U)
    hδ_le hδ0 hTδ hUδ hZδ
    R₂ A₃ D₂ D₃ D hR₂ hA₃ hD₂ hD₃ hD
    hT₂ hU₂ hT₃ hU₃ hTU₂ hTU₃
    (hT₀ρ.trans hρρ₀) (hU₀ρ.trans hρρ₀) hrad₂
  dsimp only at hout
  have hcore :
      ‖(lowCoreDataBg (I := I) (M := M)
            g gB hρ.le hδ0 hδ_le hreal T).a1Lo (I := I) (M := M) -
          (lowCoreDataBg (I := I) (M := M)
            g gB hρ.le hδ0 hδ_le hreal U).a1Lo (I := I) (M := M)‖ ≤
        Ca *
          (Real.sqrt
              (2 *
                (Bs R₂ * (P ^ 4 * (D₂ ^ 2 + D ^ 2)) +
                  (Z0 R₂ A₃ * D₂ + Z1 A₃ * D) ^ 2)) +
            (O0 * D₃ + O1 * D + O1 * A₃ * D)) := by
    simpa only [lowCoreDataBg, T₀, U₀, P, A₃] using hout
  have hfirst :
      0 ≤ Bs R₂ * (P ^ 4 * (C₂ ^ 2 + 1)) :=
    mul_nonneg (hBs R₂ hR₂)
      (mul_nonneg (by positivity) (by nlinarith [sq_nonneg C₂]))
  have hE0 : 0 ≤ E0 := by
    dsimp only [E0]
    exact mul_nonneg (by norm_num)
      (add_nonneg hfirst (sq_nonneg _))
  have hquad :
      2 *
          (Bs R₂ * (P ^ 4 * (D₂ ^ 2 + D ^ 2)) +
            (Z0 R₂ A₃ * D₂ + Z1 A₃ * D) ^ 2) =
        E0 * D ^ 2 := by
    simp only [D₂, E0]
    ring
  have hsqrt :
      Real.sqrt
          (2 *
            (Bs R₂ * (P ^ 4 * (D₂ ^ 2 + D ^ 2)) +
              (Z0 R₂ A₃ * D₂ + Z1 A₃ * D) ^ 2)) =
        Real.sqrt E0 * D := by
    rw [hquad]
    exact sqrt_scale E0 D hE0 hD
  have hlin :
      O0 * D₃ + O1 * D + O1 * A₃ * D = E1 * D := by
    simp only [D₃, E1]
    ring
  calc
    ‖(lowCoreDataBg (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal T).a1Lo (I := I) (M := M) -
        (lowCoreDataBg (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal U).a1Lo (I := I) (M := M)‖ ≤
        Ca *
          (Real.sqrt
              (2 *
                (Bs R₂ * (P ^ 4 * (D₂ ^ 2 + D ^ 2)) +
                  (Z0 R₂ A₃ * D₂ + Z1 A₃ * D) ^ 2)) +
            (O0 * D₃ + O1 * D + O1 * A₃ * D)) := hcore
    _ = K * D := by
      rw [hsqrt, hlin]
      simp only [K]
      ring
    _ = K * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
        ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
      simp only [D]

/-- One positive spectral cutoff radius makes the same-background radial high
first-order action locally Lipschitz on every bounded H3 core ball. -/
theorem radialA1Hi_self
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (_ : ρ ≤ ρ₀)
        (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hreal : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ),
        BgA1HiCorePair (I := I) (M := M)
          g g hρ.le hδ0 hδ_le hreal := by
  obtain ⟨ρ₀, B, O0, O1, Ca, hρ₀, hB, hO0, hO1, hCa, hpair⟩ :=
    a1Hi_self_pair (I := I) (M := M) hDim g
  obtain ⟨C₂, hC₂, hjet₂⟩ := jet2_le_hs (I := I) (M := M) g
  obtain ⟨C₃, hC₃, hjet₃⟩ := jet3_le_hs (I := I) (M := M) g
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ δ hρ hρρ₀ hδ0 hδ_le hreal
  dsimp only [BgA1HiCorePair]
  intro r
  let R₂ : ℝ := C₂ * ρ
  let A₃ : ℝ := C₃ * r
  let L : ℝ := 1 + (1 / ρ) * r
  let F0 : ℝ := B R₂ * (1 + A₃ ^ 2) * (C₃ * L + C₂ + 1)
  let F1 : ℝ := O0 * C₃ * L + O1 + O1 * A₃
  let E0 : ℝ := F0 ^ 2 + F1 ^ 2
  let K : ℝ := Ca * Real.sqrt E0
  refine ⟨K, ?_⟩
  intro T U hTr hUr
  have hr : 0 ≤ r := (norm_nonneg _).trans hTr
  have hρ0 : 0 ≤ ρ := hρ.le
  have hR₂ : 0 ≤ R₂ := mul_nonneg hC₂ hρ0
  have hA₃ : 0 ≤ A₃ := mul_nonneg hC₃ hr
  have hρinv : 0 ≤ (1 / ρ : ℝ) := (one_div_pos.mpr hρ).le
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  let D : ℝ :=
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
      ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖
  let D₂ : ℝ := C₂ * D
  let D₃ : ℝ := C₃ * L * D
  have hD : 0 ≤ D := norm_nonneg _
  have hD₂ : 0 ≤ D₂ := mul_nonneg hC₂ hD
  have hD₃ : 0 ≤ D₃ := mul_nonneg (mul_nonneg hC₃ hL) hD
  let T₀ : SmoothCcTensor g 0 2 :=
    lowRadial (I := I) (M := M) g ρ T
  let U₀ : SmoothCcTensor g 0 2 :=
    lowRadial (I := I) (M := M) g ρ U
  have hT₀ρ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T₀‖ ≤ ρ :=
    lowRadial_norm (I := I) (M := M) g hρ0 T
  have hU₀ρ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U₀‖ ≤ ρ :=
    lowRadial_norm (I := I) (M := M) g hρ0 U
  have hTδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g T₀) δ :=
    hreal T₀ hT₀ρ
  have hUδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g U₀) δ :=
    hreal U₀ hU₀ρ
  have hZδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2)) δ :=
    zero_fibre_bound (I := I) (M := M) g hδ0
  have hT₂ :
      lowJetSq (I := I) (M := M) g 2 T₀ ≤ R₂ ^ 2 := by
    refine (hjet₂ T₀).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC₂ (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hT₀ρ hC₂) 2
  have hU₂ :
      lowJetSq (I := I) (M := M) g 2 U₀ ≤ R₂ ^ 2 := by
    refine (hjet₂ U₀).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC₂ (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hU₀ρ hC₂) 2
  have hT₀top :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T₀‖ ≤ r := by
    have hrad := lowRadialH3_le (I := I) (M := M) g hρ
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T)
    rw [lowRadialH3_core (I := I) (M := M) g hρ T] at hrad
    simp only [ccToHsLin_apply] at hrad
    exact hrad.trans hTr
  have hU₀top :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U₀‖ ≤ r := by
    have hrad := lowRadialH3_le (I := I) (M := M) g hρ
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U)
    rw [lowRadialH3_core (I := I) (M := M) g hρ U] at hrad
    simp only [ccToHsLin_apply] at hrad
    exact hrad.trans hUr
  have hT₃ :
      lowJetSq (I := I) (M := M) g 3 T₀ ≤ A₃ ^ 2 := by
    refine (hjet₃ T₀).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC₃ (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hT₀top hC₃) 2
  have hU₃ :
      lowJetSq (I := I) (M := M) g 3 U₀ ≤ A₃ ^ 2 := by
    refine (hjet₃ U₀).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC₃ (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hU₀top hC₃) 2
  have hincl :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ D := by
    have h := tensorHsInclusion_norm_le (I := I) (M := M)
      (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
      (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T -
        ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U)
    rw [map_sub, inclCc32_bg (I := I) (M := M) g T,
      inclCc32_bg (I := I) (M := M) g U] at h
    simpa only [D, ccToHsLin_apply] using h
  have hrad₂ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T₀ - U₀)‖ ≤ D := by
    rw [ccToHsSub_bg]
    exact (lowRadial_lip (I := I) (M := M) g hρ0 T U).trans hincl
  have hTU₂ :
      lowJetSq (I := I) (M := M) g 2 (T₀ - U₀) ≤ D₂ ^ 2 := by
    refine (hjet₂ (T₀ - U₀)).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC₂ (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hrad₂ hC₂) 2
  have hmax :
      max
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r :=
    max_le hTr hUr
  have hprod :
      max
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤
        r * D :=
    mul_le_mul hmax hincl (norm_nonneg _) hr
  have hrad₃ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (T₀ - U₀)‖ ≤
        L * D := by
    rw [ccToHsSub_bg]
    refine (lowRadial_h3_sub (I := I) (M := M) g hρ T U).trans ?_
    have hscaled := mul_le_mul_of_nonneg_left hprod hρinv
    have hscaled' :
        (1 / ρ) *
              max
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
                ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤
          (1 / ρ) * (r * D) := by
      calc
        (1 / ρ) *
              max
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
                ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ =
            (1 / ρ) *
              (max
                  ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                  ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
                ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
                  ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖) := by ring
        _ ≤ (1 / ρ) * (r * D) := hscaled
    calc
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ +
            (1 / ρ) *
              max
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
                ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤
          D + (1 / ρ) * (r * D) := by
        change D + _ ≤ D + _
        exact add_le_add_right hscaled' D
      _ = L * D := by
        simp only [L]
        ring
  have hTU₃ :
      lowJetSq (I := I) (M := M) g 3 (T₀ - U₀) ≤ D₃ ^ 2 := by
    refine (hjet₃ (T₀ - U₀)).trans ?_
    simpa only [D₃, mul_assoc] using pow_le_pow_left₀
      (mul_nonneg hC₃ (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hrad₃ hC₃) 2
  have hout := hpair T₀ U₀
    (lowRadial_symm (I := I) (M := M) g ρ T)
    (lowRadial_symm (I := I) (M := M) g ρ U)
    hδ_le hδ0 hTδ hUδ hZδ
    R₂ A₃ D₂ D₃ D hR₂ hA₃ hD₂ hD₃ hD
    hT₂ hU₂ hT₃ hU₃ hTU₂ hTU₃
    (hT₀ρ.trans hρρ₀) (hU₀ρ.trans hρρ₀) hrad₂
  dsimp only at hout
  have hcore :
      ‖(lowCoreDataBg (I := I) (M := M)
            g g hρ.le hδ0 hδ_le hreal T).a1Hi (I := I) (M := M) -
          (lowCoreDataBg (I := I) (M := M)
            g g hρ.le hδ0 hδ_le hreal U).a1Hi (I := I) (M := M)‖ ≤
        Ca * Real.sqrt
          ((B R₂ * (1 + A₃ ^ 2) * (D₃ + D₂ + D)) ^ 2 +
            (O0 * D₃ + O1 * D + O1 * A₃ * D) ^ 2) := by
    simpa only [lowCoreDataBg, T₀, U₀] using hout
  have hE0 : 0 ≤ E0 := by
    dsimp only [E0]
    exact add_nonneg (sq_nonneg F0) (sq_nonneg F1)
  have hquad :
      (B R₂ * (1 + A₃ ^ 2) * (D₃ + D₂ + D)) ^ 2 +
          (O0 * D₃ + O1 * D + O1 * A₃ * D) ^ 2 =
        E0 * D ^ 2 := by
    simp only [D₂, D₃, E0, F0, F1]
    ring
  have hsqrt :
      Real.sqrt
          ((B R₂ * (1 + A₃ ^ 2) * (D₃ + D₂ + D)) ^ 2 +
            (O0 * D₃ + O1 * D + O1 * A₃ * D) ^ 2) =
        Real.sqrt E0 * D := by
    rw [hquad]
    exact sqrt_scale E0 D hE0 hD
  calc
    ‖(lowCoreDataBg (I := I) (M := M)
          g g hρ.le hδ0 hδ_le hreal T).a1Hi (I := I) (M := M) -
        (lowCoreDataBg (I := I) (M := M)
          g g hρ.le hδ0 hδ_le hreal U).a1Hi (I := I) (M := M)‖ ≤
        Ca * Real.sqrt
          ((B R₂ * (1 + A₃ ^ 2) * (D₃ + D₂ + D)) ^ 2 +
            (O0 * D₃ + O1 * D + O1 * A₃ * D) ^ 2) := hcore
    _ = K * D := by
      rw [hsqrt]
      simp only [K]
      ring
    _ = K * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
        ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
      simp only [D]

set_option synthInstance.maxHeartbeats 1000000 in
/-- The completed arbitrary-background low first-order map takes its canonical
value on every smooth H3 core state. -/
theorem lowA1LoBg_core
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} {hρ : 0 ≤ ρ} {hδ0 : 0 ≤ δ} {hδ_le : δ ≤ 1 / 3}
    {hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ}
    (hpair : BgA1CorePair (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal)
    (T : SmoothCcTensor g 0 2) :
    lowA1LoBg (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
        (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T) =
      (lowCoreDataBg (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).a1Lo (I := I) (M := M) :=
  DifferentialGeometry.Analysis.extend_pair_apply
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (highBgCore (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
      fun A => A.a1Lo (I := I) (M := M))
    (fun U => (lowCoreDataBg (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal U).a1Lo (I := I) (M := M))
    (highBgCore_value (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal
        (fun A => A.a1Lo (I := I) (M := M)))
    (by simpa only [BgA1CorePair] using hpair) T

set_option synthInstance.maxHeartbeats 1000000 in
/-- The completed arbitrary-background radial low first-order coefficient is
continuous on the H3 state space. -/
theorem lowA1LoBg_cont
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} {hρ : 0 ≤ ρ} {hδ0 : 0 ≤ δ} {hδ_le : δ ≤ 1 / 3}
    {hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ}
    (hpair : BgA1CorePair (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal) :
    Continuous (lowA1LoBg (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal) :=
  DifferentialGeometry.Analysis.cont_extend_pair
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (highBgCore (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
      fun A => A.a1Lo (I := I) (M := M))
    (fun U => (lowCoreDataBg (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal U).a1Lo (I := I) (M := M))
    (highBgCore_value (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal
        (fun A => A.a1Lo (I := I) (M := M)))
    (by simpa only [BgA1CorePair] using hpair)

/-- Continuous arbitrary-background A1 coefficients preserve a.e. strong
measurability of time-dependent H3 states. -/
theorem lowA1LoBg_aesm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} {hρ : 0 ≤ ρ} {hδ0 : 0 ≤ δ} {hδ_le : δ ≤ 1 / 3}
    {hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ}
    (hpair : BgA1CorePair (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal)
    (u : Ω → metricH3 (I := I) (M := M) g)
    (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable
      (fun t => lowA1LoBg (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal (u t)) μ :=
  (lowA1LoBg_cont (I := I) (M := M) g gB hpair).comp_aestronglyMeasurable hu

set_option synthInstance.maxHeartbeats 1000000 in
/-- The completed high first-order map takes its canonical value on every
smooth H3 core state. -/
theorem lowA1HiBg_core
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} {hρ : 0 ≤ ρ} {hδ0 : 0 ≤ δ} {hδ_le : δ ≤ 1 / 3}
    {hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ}
    (hpair : BgA1HiCorePair (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal)
    (T : SmoothCcTensor g 0 2) :
    lowA1HiBg (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
        (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T) =
      (lowCoreDataBg (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).a1Hi (I := I) (M := M) :=
  DifferentialGeometry.Analysis.extend_pair_apply
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (highBgCore (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
      fun A => A.a1Hi (I := I) (M := M))
    (fun U => (lowCoreDataBg (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal U).a1Hi (I := I) (M := M))
    (highBgCore_value (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal
        (fun A => A.a1Hi (I := I) (M := M)))
    (by simpa only [BgA1HiCorePair] using hpair) T

set_option synthInstance.maxHeartbeats 1000000 in
/-- The completed radial high first-order coefficient is continuous on the H3
state space. -/
theorem lowA1HiBg_cont
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} {hρ : 0 ≤ ρ} {hδ0 : 0 ≤ δ} {hδ_le : δ ≤ 1 / 3}
    {hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ}
    (hpair : BgA1HiCorePair (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal) :
    Continuous (lowA1HiBg (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal) :=
  DifferentialGeometry.Analysis.cont_extend_pair
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (highBgCore (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
      fun A => A.a1Hi (I := I) (M := M))
    (fun U => (lowCoreDataBg (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal U).a1Hi (I := I) (M := M))
    (highBgCore_value (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal
        (fun A => A.a1Hi (I := I) (M := M)))
    (by simpa only [BgA1HiCorePair] using hpair)

/-- Continuous high A1 coefficients preserve a.e. strong measurability of
time-dependent H3 states. -/
theorem lowA1HiBg_aesm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} {hρ : 0 ≤ ρ} {hδ0 : 0 ≤ δ} {hδ_le : δ ≤ 1 / 3}
    {hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ}
    (hpair : BgA1HiCorePair (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal)
    (u : Ω → metricH3 (I := I) (M := M) g)
    (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable
      (fun t => lowA1HiBg (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal (u t)) μ :=
  (lowA1HiBg_cont (I := I) (M := M) g gB hpair).comp_aestronglyMeasurable hu

/-- On the same DeTurck background, the completed high and low first-order
actions are the two adjacent-scale realizations of one smooth-core formula. -/
theorem lowA1Bg_comm
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hHi : BgA1HiCorePair (I := I) (M := M)
      g g hρ.le hδ0 hδ_le hreal)
    (hLo : BgA1CorePair (I := I) (M := M)
      g g hρ.le hδ0 hδ_le hreal)
    (v : metricH3 (I := I) (M := M) g) :
    (tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
        (lowA1HiBg (I := I) (M := M)
          g g hρ.le hδ0 hδ_le hreal v) =
      (lowA1LoBg (I := I) (M := M)
          g g hρ.le hδ0 hδ_le hreal v).comp
        (tensorHsInclusion (I := I) (M := M) (g := g)
          (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num)) := by
  obtain ⟨_, _, _, _, hcoreComm⟩ :=
    radialA1_pair (I := I) (M := M) hDim g hρ hδ0 hδ_le hreal
  let J12 :=
    tensorHsInclusion (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)
  let J23 :=
    tensorHsInclusion (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num)
  let AHi := lowA1HiBg (I := I) (M := M)
    g g hρ.le hδ0 hδ_le hreal
  let ALo := lowA1LoBg (I := I) (M := M)
    g g hρ.le hδ0 hδ_le hreal
  have hleft : Continuous (fun w => J12.comp (AHi w)) :=
    (ContinuousLinearMap.compL ℝ
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ))
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
      (tensorHs (I := I) (M := M) g 0 2 (1 : ℝ))).continuous₂.comp
        (continuous_const.prodMk
          (lowA1HiBg_cont (I := I) (M := M) g g hHi))
  have hright : Continuous (fun w => (ALo w).comp J23) :=
    (ContinuousLinearMap.compL ℝ
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ))
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
      (tensorHs (I := I) (M := M) g 0 2 (1 : ℝ))).continuous₂.comp
        ((lowA1LoBg_cont (I := I) (M := M) g g hLo).prodMk
          continuous_const)
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  refine hdense.induction_on v (isClosed_eq hleft hright) ?_
  intro T
  rw [lowA1HiBg_core (I := I) (M := M) g g hHi T,
    lowA1LoBg_core (I := I) (M := M) g g hLo T]
  simpa only [lowCoreDataBg, lowCoreData] using (hcoreComm T).2.2

/-- The fixed-background radial second-order coefficient as an `H4 → H2`
operator-valued map on the completed `H2` state space. -/
noncomputable def lowA2HiBg
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    metricH2 (I := I) (M := M) g → lowA2HiOp (I := I) (M := M) g :=
  Dense.extend
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (lowBgCore (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
      fun A => A.a2Hi (I := I) (M := M))

/-- The same fixed-background radial second-order coefficient as an
`H3 → H1` operator-valued map on the completed `H2` state space. -/
noncomputable def lowA2LoBg
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    metricH2 (I := I) (M := M) g → lowA2LoBgOp (I := I) (M := M) g :=
  Dense.extend
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (lowBgCore (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
      fun A => A.a2Lo (I := I) (M := M))

private theorem lowBgCore_pair
    {Y : Type*} [NormedAddCommGroup Y]
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ C : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (proj : LowBaseActionData g → Y)
    (hpair : ∀ T U : SmoothCcTensor g 0 2,
      ‖proj (lowCoreDataBg (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal T) -
        proj (lowCoreDataBg (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal U)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖)
    (x y : LowBaseTimeInternal.LowCore (I := I) (M := M) g) :
    ‖lowBgCore (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal proj x -
        lowBgCore (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal proj y‖ ≤
      C * ‖(x : metricH2 (I := I) (M := M) g) -
        (y : metricH2 (I := I) (M := M) g)‖ := by
  obtain ⟨T, hT⟩ := x.property
  obtain ⟨U, hU⟩ := y.property
  have hx : x =
      ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩ := by
    apply Subtype.ext
    exact hT.symm
  have hy : y =
      ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) U, ⟨U, rfl⟩⟩ := by
    apply Subtype.ext
    exact hU.symm
  rw [hx, hy, lowBgCore_value, lowBgCore_value, ← map_sub]
  simpa only [ccToHsLin_apply] using hpair T U

private theorem lowBg_ext_lip
    {Y : Type*} [NormedAddCommGroup Y] [CompleteSpace Y]
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ C : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (proj : LowBaseActionData g → Y) (hC : 0 ≤ C)
    (hpair : ∀ T U : SmoothCcTensor g 0 2,
      ‖proj (lowCoreDataBg (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal T) -
        proj (lowCoreDataBg (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal U)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖) :
    LipschitzWith ⟨C, hC⟩
      (Dense.extend
        (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
        (lowBgCore (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal proj)) := by
  refine DifferentialGeometry.Analysis.Parabolic.QuasiLinear.dense_lipschitz
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)) _ ?_
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_mk, dist_eq_norm, Subtype.dist_eq] using
    lowBgCore_pair (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal proj hpair x y

private theorem lowBg_ext_core
    {Y : Type*} [NormedAddCommGroup Y] [CompleteSpace Y]
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ C : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (proj : LowBaseActionData g → Y) (hC : 0 ≤ C)
    (hpair : ∀ T U : SmoothCcTensor g 0 2,
      ‖proj (lowCoreDataBg (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal T) -
        proj (lowCoreDataBg (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal U)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖)
    (T : SmoothCcTensor g 0 2) :
    Dense.extend
        (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
        (lowBgCore (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal proj)
        (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) =
      proj (lowCoreDataBg (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T) := by
  let D : Set (metricH2 (I := I) (M := M) g) :=
    Set.range (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ))
  let F : D → Y := lowBgCore (I := I) (M := M)
    g gB hρ hδ0 hδ_le hreal proj
  have hF : LipschitzWith ⟨C, hC⟩ F := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [NNReal.coe_mk, dist_eq_norm, Subtype.dist_eq, F] using
      lowBgCore_pair (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal proj hpair x y
  let x : D :=
    ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩
  have hext :=
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)).extend_eq
      hF.continuous x
  change Dense.extend
      (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
      F (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) = _
  calc
    Dense.extend
        (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
        F (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) = F x := hext
    _ = _ := lowBgCore_value (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal proj T

/-- Below one realized spectral `H2` cutoff, the fixed-background total
second-order coefficient gives compatible Lipschitz `H4 → H2` and `H3 → H1`
operator maps on the completed `H2` state space. -/
theorem radialA2Bg_lip
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M)
    {ρ₀ δ : ℝ} (hρ₀ : 0 < ρ₀) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ₀ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    ∃ (ρ : ℝ) (C : NNReal) (_hρ : 0 < ρ) (hρ_le : ρ ≤ ρ₀),
      ∀ {r : ℝ} (hr0 : 0 ≤ r) (hr_le : r ≤ ρ),
        let hreal' : ∀ S : SmoothCcTensor g 0 2,
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ r →
              gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g S) δ :=
          fun S hS => hreal S (hS.trans (hr_le.trans hρ_le))
        LipschitzWith C
            (lowA2HiBg (I := I) (M := M)
              g gB hr0 hδ0 hδ_le hreal') ∧
          LipschitzWith C
            (lowA2LoBg (I := I) (M := M)
              g gB hr0 hδ0 hδ_le hreal') ∧
          (∀ T : SmoothCcTensor g 0 2,
            lowA2HiBg (I := I) (M := M)
                g gB hr0 hδ0 hδ_le hreal'
                (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) =
              (lowCoreDataBg (I := I) (M := M)
                g gB hr0 hδ0 hδ_le hreal' T).a2Hi (I := I) (M := M)) ∧
          (∀ T : SmoothCcTensor g 0 2,
            lowA2LoBg (I := I) (M := M)
                g gB hr0 hδ0 hδ_le hreal'
                (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) =
              (lowCoreDataBg (I := I) (M := M)
                g gB hr0 hδ0 hδ_le hreal' T).a2Lo (I := I) (M := M)) ∧
          ∀ v : metricH2 (I := I) (M := M) g,
            (tensorHsInclusion (I := I) (M := M) (g := g)
                (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
                (lowA2HiBg (I := I) (M := M)
                  g gB hr0 hδ0 hδ_le hreal' v) =
              (lowA2LoBg (I := I) (M := M)
                  g gB hr0 hδ0 hδ_le hreal' v).comp
                (tensorHsInclusion (I := I) (M := M) (g := g)
                  (r := 0) (s := 2)
                  (show (3 : ℝ) ≤ 4 by norm_num)) := by
  obtain ⟨ρp, C, hρp, hC, hpair⟩ :=
    a2_pair_lip (I := I) (M := M) hDim g gB
  let ρ : ℝ := min ρ₀ ρp
  have hρ : 0 < ρ := lt_min hρ₀ hρp
  have hρ_le : ρ ≤ ρ₀ := min_le_left _ _
  have hρp_le : ρ ≤ ρp := min_le_right _ _
  refine ⟨ρ, ⟨C, hC⟩, hρ, hρ_le, ?_⟩
  intro r hr0 hr_le
  dsimp only
  let hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ r →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ :=
    fun S hS => hreal S (hS.trans (hr_le.trans hρ_le))
  have hδlt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hZδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2)) δ :=
    zero_fibre_bound (I := I) (M := M) g hδ0
  have hBoth : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreDataBg (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal' T).a2Hi (I := I) (M := M) -
        (lowCoreDataBg (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal' U).a2Hi (I := I) (M := M)‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (T - U)‖ ∧
      ‖(lowCoreDataBg (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal' T).a2Lo (I := I) (M := M) -
        (lowCoreDataBg (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal' U).a2Lo (I := I) (M := M)‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (T - U)‖ := by
    intro T U
    let S := lowRadial (I := I) (M := M) g r T
    let V := lowRadial (I := I) (M := M) g r U
    have hSρ :
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ r :=
      lowRadial_norm (I := I) (M := M) g hr0 T
    have hVρ :
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) V‖ ≤ r :=
      lowRadial_norm (I := I) (M := M) g hr0 U
    have hSδ :
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ := hreal' S hSρ
    have hVδ :
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g V) δ := hreal' V hVρ
    obtain ⟨hHi, hLo⟩ :=
      hpair S V hδlt hSδ hVδ hZδ
        (hSρ.trans (hr_le.trans hρp_le))
        (hVρ.trans (hr_le.trans hρp_le))
    have hSV :
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V)‖ ≤
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ := by
      have hrad := lowRadial_lip (I := I) (M := M) g hr0 T U
      have hmapSV :
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V) =
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S -
              ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) V := by
        simpa only [ccToHsLin_apply] using
          map_sub (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) S V
      have hmapTU :
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U) =
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
              ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U := by
        simpa only [ccToHsLin_apply] using
          map_sub (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) T U
      rw [hmapSV, hmapTU]
      simpa only [S, V] using hrad
    have hbound :
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V)‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ :=
      mul_le_mul_of_nonneg_left hSV hC
    refine ⟨?_, ?_⟩
    · have hHi' :
          ‖(lowCoreDataBg (I := I) (M := M)
              g gB hr0 hδ0 hδ_le hreal' T).a2Hi (I := I) (M := M) -
            (lowCoreDataBg (I := I) (M := M)
              g gB hr0 hδ0 hδ_le hreal' U).a2Hi (I := I) (M := M)‖ ≤
            C * ‖ccTensorToHs (I := I) (M := M)
              g 2 (2 : ℝ) (S - V)‖ := by
        simpa only [lowCoreDataBg, S, V] using hHi
      exact hHi'.trans hbound
    · have hLo' :
          ‖(lowCoreDataBg (I := I) (M := M)
              g gB hr0 hδ0 hδ_le hreal' T).a2Lo (I := I) (M := M) -
            (lowCoreDataBg (I := I) (M := M)
              g gB hr0 hδ0 hδ_le hreal' U).a2Lo (I := I) (M := M)‖ ≤
            C * ‖ccTensorToHs (I := I) (M := M)
              g 2 (2 : ℝ) (S - V)‖ := by
        simpa only [lowCoreDataBg, S, V] using hLo
      exact hLo'.trans hbound
  have hHiPair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreDataBg (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal' T).a2Hi (I := I) (M := M) -
        (lowCoreDataBg (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal' U).a2Hi (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M)
          g 2 (2 : ℝ) (T - U)‖ := fun T U => (hBoth T U).1
  have hLoPair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreDataBg (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal' T).a2Lo (I := I) (M := M) -
        (lowCoreDataBg (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal' U).a2Lo (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M)
          g 2 (2 : ℝ) (T - U)‖ := fun T U => (hBoth T U).2
  have hHiLip : LipschitzWith ⟨C, hC⟩
      (lowA2HiBg (I := I) (M := M)
        g gB hr0 hδ0 hδ_le hreal') := by
    simpa only [lowA2HiBg] using
      lowBg_ext_lip (I := I) (M := M)
        g gB hr0 hδ0 hδ_le hreal'
          (fun A => A.a2Hi (I := I) (M := M)) hC hHiPair
  have hLoLip : LipschitzWith ⟨C, hC⟩
      (lowA2LoBg (I := I) (M := M)
        g gB hr0 hδ0 hδ_le hreal') := by
    simpa only [lowA2LoBg] using
      lowBg_ext_lip (I := I) (M := M)
        g gB hr0 hδ0 hδ_le hreal'
          (fun A => A.a2Lo (I := I) (M := M)) hC hLoPair
  have hHiCore : ∀ T : SmoothCcTensor g 0 2,
      lowA2HiBg (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal'
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) =
        (lowCoreDataBg (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal' T).a2Hi (I := I) (M := M) := by
    intro T
    simpa only [lowA2HiBg] using
      lowBg_ext_core (I := I) (M := M)
        g gB hr0 hδ0 hδ_le hreal'
          (fun A => A.a2Hi (I := I) (M := M)) hC hHiPair T
  have hLoCore : ∀ T : SmoothCcTensor g 0 2,
      lowA2LoBg (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal'
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) =
        (lowCoreDataBg (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal' T).a2Lo (I := I) (M := M) := by
    intro T
    simpa only [lowA2LoBg] using
      lowBg_ext_core (I := I) (M := M)
        g gB hr0 hδ0 hδ_le hreal'
          (fun A => A.a2Lo (I := I) (M := M)) hC hLoPair T
  refine ⟨hHiLip, hLoLip, hHiCore, hLoCore, ?_⟩
  let J12 :=
    tensorHsInclusion (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)
  let J34 :=
    tensorHsInclusion (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num)
  let AHi := lowA2HiBg (I := I) (M := M)
    g gB hr0 hδ0 hδ_le hreal'
  let ALo := lowA2LoBg (I := I) (M := M)
    g gB hr0 hδ0 hδ_le hreal'
  have hleft : Continuous (fun v => J12.comp (AHi v)) :=
    (ContinuousLinearMap.compL ℝ
      (tensorHs (I := I) (M := M) g 0 2 (4 : ℝ))
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
      (tensorHs (I := I) (M := M) g 0 2 (1 : ℝ))).continuous₂.comp
        (continuous_const.prodMk hHiLip.continuous)
  have hright : Continuous (fun v => (ALo v).comp J34) :=
    (ContinuousLinearMap.compL ℝ
      (tensorHs (I := I) (M := M) g 0 2 (4 : ℝ))
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ))
      (tensorHs (I := I) (M := M) g 0 2 (1 : ℝ))).continuous₂.comp
        (hLoLip.continuous.prodMk continuous_const)
  intro v
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  refine hdense.induction_on v (isClosed_eq hleft hright) ?_
  intro T
  rw [hHiCore T, hLoCore T]
  exact a2_comm (I := I) (M := M) hDim g
    (lowCoreDataBg (I := I) (M := M)
      g gB hr0 hδ0 hδ_le hreal' T)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
