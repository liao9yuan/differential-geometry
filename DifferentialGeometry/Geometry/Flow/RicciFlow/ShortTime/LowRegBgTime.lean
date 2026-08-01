import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseTimeA2
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgH2

/-!
# Fixed-background low-base radial core

This module evaluates the canonical low-base action at the existing spectral
radial state while retaining an independent fixed DeTurck background.
-/

noncomputable section

open Bundle Manifold
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
