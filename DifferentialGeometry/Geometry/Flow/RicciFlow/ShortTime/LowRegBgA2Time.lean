import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgTime

/-!
# Time packets for the same-background complete second-order action

This module turns the complete low-base `C₂` coefficient into the compatible
measurable `H4 → H2` and `H3 → H1` families used by the adjacent-scale lift.
The coefficient already includes the full principal deviation after subtraction
of the fixed rough Laplacian; no separate principal arm is added here.
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

private abbrev metricH4 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (4 : ℝ)

private abbrev metricH3 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (3 : ℝ)

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev metricH1 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

private abbrev a2HiOp (g : SmoothRiemannianMetric I M) :=
  metricH4 (I := I) (M := M) g →L[ℝ] metricH2 (I := I) (M := M) g

private abbrev a2LoOp (g : SmoothRiemannianMetric I M) :=
  metricH3 (I := I) (M := M) g →L[ℝ] metricH1 (I := I) (M := M) g

private noncomputable abbrev incl32
    (g : SmoothRiemannianMetric I M) :
    metricH3 (I := I) (M := M) g →L[ℝ]
      metricH2 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g)
    (r := 0) (s := 2) (by norm_num)

private noncomputable abbrev incl12
    (g : SmoothRiemannianMetric I M) :
    metricH2 (I := I) (M := M) g →L[ℝ]
      metricH1 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g)
    (r := 0) (s := 2) (by norm_num)

private noncomputable abbrev incl34
    (g : SmoothRiemannianMetric I M) :
    metricH4 (I := I) (M := M) g →L[ℝ]
      metricH3 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g)
    (r := 0) (s := 2) (by norm_num)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
private theorem a2HiBg_total_le
    (g : SmoothRiemannianMetric I M) {ρ δ c : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcont : Continuous
      (lowA2HiBg (I := I) (M := M) g g hρ hδ0 hδ_le hreal))
    (hcore : ∀ S : SmoothCcTensor g 0 2,
      lowA2HiBg (I := I) (M := M) g g hρ hδ0 hδ_le hreal
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
        (lowCoreDataBg (I := I) (M := M)
          g g hρ hδ0 hδ_le hreal S).a2Hi (I := I) (M := M))
    (hbd : ∀ S : SmoothCcTensor g 0 2,
      ‖(lowCoreDataBg (I := I) (M := M)
          g g hρ hδ0 hδ_le hreal S).a2Hi (I := I) (M := M)‖ ≤ c)
    (v : metricH2 (I := I) (M := M) g) :
    ‖show a2HiOp (I := I) (M := M) g from
      lowA2HiBg (I := I) (M := M) g g hρ hδ0 hδ_le hreal v‖ ≤ c := by
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by norm_num)
  have hclosed : IsClosed {w : metricH2 (I := I) (M := M) g |
      ‖show a2HiOp (I := I) (M := M) g from
        lowA2HiBg (I := I) (M := M)
          g g hρ hδ0 hδ_le hreal w‖ ≤ c} :=
    isClosed_le
      (Continuous.comp
        (continuous_norm (E := a2HiOp (I := I) (M := M) g)) hcont)
      continuous_const
  refine hdense.induction_on v hclosed ?_
  intro S
  have h := hbd S
  rw [← hcore S] at h
  exact h

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
private theorem a2LoBg_total_le
    (g : SmoothRiemannianMetric I M) {ρ δ c : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcont : Continuous
      (lowA2LoBg (I := I) (M := M) g g hρ hδ0 hδ_le hreal))
    (hcore : ∀ S : SmoothCcTensor g 0 2,
      lowA2LoBg (I := I) (M := M) g g hρ hδ0 hδ_le hreal
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
        (lowCoreDataBg (I := I) (M := M)
          g g hρ hδ0 hδ_le hreal S).a2Lo (I := I) (M := M))
    (hbd : ∀ S : SmoothCcTensor g 0 2,
      ‖(lowCoreDataBg (I := I) (M := M)
          g g hρ hδ0 hδ_le hreal S).a2Lo (I := I) (M := M)‖ ≤ c)
    (v : metricH2 (I := I) (M := M) g) :
    ‖show a2LoOp (I := I) (M := M) g from
      lowA2LoBg (I := I) (M := M) g g hρ hδ0 hδ_le hreal v‖ ≤ c := by
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by norm_num)
  have hclosed : IsClosed {w : metricH2 (I := I) (M := M) g |
      ‖show a2LoOp (I := I) (M := M) g from
        lowA2LoBg (I := I) (M := M)
          g g hρ hδ0 hδ_le hreal w‖ ≤ c} :=
    isClosed_le
      (Continuous.comp
        (continuous_norm (E := a2LoOp (I := I) (M := M) g)) hcont)
      continuous_const
  refine hdense.induction_on v hclosed ?_
  intro S
  have h := hbd S
  rw [← hcore S] at h
  exact h

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- On every sufficiently small same-background cutoff, the complete radial
second-order coefficient gives continuous compatible completed maps whose
operator norms are linear in the chosen cutoff radius. -/
theorem lowA2Bg_small
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {ρ₀ δ : ℝ}
    (hρ₀ : 0 < ρ₀) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ₀ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    ∃ (ρ C : ℝ) (_hρ : 0 < ρ) (hρ_le : ρ ≤ ρ₀), 0 ≤ C ∧
      ∀ {r : ℝ} (hr0 : 0 ≤ r) (hr_le : r ≤ ρ),
        let hreal' : ∀ S : SmoothCcTensor g 0 2,
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ r →
              gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g S) δ :=
          fun S hS => hreal S (hS.trans (hr_le.trans hρ_le))
        Continuous (lowA2HiBg (I := I) (M := M)
            g g hr0 hδ0 hδ_le hreal') ∧
          Continuous (lowA2LoBg (I := I) (M := M)
            g g hr0 hδ0 hδ_le hreal') ∧
          (∀ v : metricH2 (I := I) (M := M) g,
            ‖show a2HiOp (I := I) (M := M) g from
              lowA2HiBg (I := I) (M := M)
                g g hr0 hδ0 hδ_le hreal' v‖ ≤ C * r) ∧
          (∀ v : metricH2 (I := I) (M := M) g,
            ‖show a2LoOp (I := I) (M := M) g from
              lowA2LoBg (I := I) (M := M)
                g g hr0 hδ0 hδ_le hreal' v‖ ≤ C * r) ∧
          ∀ v : metricH2 (I := I) (M := M) g,
            (incl12 (I := I) (M := M) g).comp
                (lowA2HiBg (I := I) (M := M)
                  g g hr0 hδ0 hδ_le hreal' v) =
              (lowA2LoBg (I := I) (M := M)
                  g g hr0 hδ0 hδ_le hreal' v).comp
                (incl34 (I := I) (M := M) g) := by
  obtain ⟨ρL, CL, hρL, hρL_le, hlipdata⟩ :=
    radialA2Bg_lip (I := I) (M := M)
      hDim g g hρ₀ hδ0 hδ_le hreal
  obtain ⟨ρ₂, C₂, hρ₂, hC₂, hc₂⟩ :=
    c2_h2_small (I := I) (M := M) hDim g
  obtain ⟨Cₐ, hCₐ, hpair⟩ :=
    a2_pair (I := I) (M := M) hDim g
  let ρ : ℝ := min ρL ρ₂
  let C : ℝ := Cₐ * C₂
  have hρ : 0 < ρ := lt_min hρL hρ₂
  have hρ_le : ρ ≤ ρ₀ := (min_le_left _ _).trans hρL_le
  have hC : 0 ≤ C := mul_nonneg hCₐ hC₂
  refine ⟨ρ, C, hρ, hρ_le, hC, ?_⟩
  intro r hr0 hr_le
  dsimp only
  let hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ r →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ :=
    fun S hS => hreal S (hS.trans (hr_le.trans hρ_le))
  have hrL : r ≤ ρL := hr_le.trans (min_le_left _ _)
  have hr₂ : r ≤ ρ₂ := hr_le.trans (min_le_right _ _)
  obtain ⟨hlipHi, hlipLo, hcoreHi, hcoreLo, hsq⟩ :=
    hlipdata (r := r) hr0 hrL
  have hzeroHs :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ ρ₀ := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul, norm_zero]
    exact hρ₀.le
  have hZδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2)) δ :=
    hreal _ hzeroHs
  have hcoreBd : ∀ T : SmoothCcTensor g 0 2,
      ‖(lowCoreDataBg (I := I) (M := M)
          g g hr0 hδ0 hδ_le hreal' T).a2Hi (I := I) (M := M)‖ ≤ C * r ∧
        ‖(lowCoreDataBg (I := I) (M := M)
          g g hr0 hδ0 hδ_le hreal' T).a2Lo (I := I) (M := M)‖ ≤ C * r := by
    intro T
    let S : SmoothCcTensor g 0 2 :=
      lowRadial (I := I) (M := M) g r T
    have hSr :
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ r :=
      lowRadial_norm (I := I) (M := M) g hr0 T
    have hSδ :
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ :=
      hreal S (hSr.trans (hr_le.trans hρ_le))
    let A : LowBaseActionData g :=
      lowCoreDataBg (I := I) (M := M)
        g g hr0 hδ0 hδ_le hreal' T
    obtain ⟨hpoint, hjet⟩ :=
      hc₂ S
        (lowRadial_symm (I := I) (M := M) g r T)
        hδ_le hδ0 hSδ hZδ hr0 hr₂ hSr
    have hB : 0 ≤ C₂ * r := mul_nonneg hC₂ hr0
    obtain ⟨hHi, hLo, -, -, -⟩ :=
      hpair A (C₂ * r) hB (by
        simpa only [A, lowCoreDataBg, lowCoreData, S] using hpoint) (by
        simpa only [A, lowCoreDataBg, lowCoreData, S] using hjet)
    refine ⟨hHi.trans_eq ?_, hLo.trans_eq ?_⟩
    · simp only [C]
      ring
    · simp only [C]
      ring
  refine ⟨hlipHi.continuous, hlipLo.continuous, ?_, ?_, hsq⟩
  · intro v
    exact a2HiBg_total_le (I := I) (M := M)
      g hr0 hδ0 hδ_le hreal' hlipHi.continuous hcoreHi
        (fun T => (hcoreBd T).1) v
  · intro v
    exact a2LoBg_total_le (I := I) (M := M)
      g hr0 hδ0 hδ_le hreal' hlipLo.continuous hcoreLo
        (fun T => (hcoreBd T).2) v

/-- The high complete second-order family freezes the radial passenger at the
same H2 state at which its coefficient is evaluated. -/
noncomputable def hiAffA2Bg
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (u : ℝ → metricH3 (I := I) (M := M) g) :
    ℝ → a2HiOp (I := I) (M := M) g :=
  fun t =>
    (lowA2HiBg (I := I) (M := M)
      g g hρ hδ0 hδ_le hreal (incl32 (I := I) (M := M) g (u t))).comp
        (radialCLM (I := I) (M := M) g (by norm_num) ρ
          (incl32 (I := I) (M := M) g (u t)))

/-- The matching low complete second-order family uses the same frozen radial
scalar on the H3 passenger scale. -/
noncomputable def loAffA2Bg
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (u : ℝ → metricH3 (I := I) (M := M) g) :
    ℝ → a2LoOp (I := I) (M := M) g :=
  fun t =>
    (lowA2LoBg (I := I) (M := M)
      g g hρ hδ0 hδ_le hreal (incl32 (I := I) (M := M) g (u t))).comp
        (radialCLM (I := I) (M := M) g (by norm_num) ρ
          (incl32 (I := I) (M := M) g (u t)))

/-- Freezing the radial H4 passenger does not enlarge the high second-order
coefficient norm. -/
theorem hiAffA2Bg_le
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (u : ℝ → metricH3 (I := I) (M := M) g) (t : ℝ) :
    ‖hiAffA2Bg (I := I) (M := M) g hρ hδ0 hδ_le hreal u t‖ ≤
      ‖lowA2HiBg (I := I) (M := M)
        g g hρ hδ0 hδ_le hreal (incl32 (I := I) (M := M) g (u t))‖ := by
  let A2 := lowA2HiBg (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal (incl32 (I := I) (M := M) g (u t))
  let R4 := radialCLM (I := I) (M := M) g
    (show (0 : ℝ) ≤ 4 by norm_num) ρ
      (incl32 (I := I) (M := M) g (u t))
  have hR4 : ‖R4‖ ≤ 1 :=
    radialCLM_norm (I := I) (M := M) g (by norm_num) hρ _
  change ‖A2.comp R4‖ ≤ ‖A2‖
  calc
    ‖A2.comp R4‖ ≤ ‖A2‖ * ‖R4‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A2‖ * 1 := mul_le_mul_of_nonneg_left hR4 (norm_nonneg A2)
    _ = ‖A2‖ := mul_one _

/-- Freezing the radial H3 passenger does not enlarge the low second-order
coefficient norm. -/
theorem loAffA2Bg_le
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (u : ℝ → metricH3 (I := I) (M := M) g) (t : ℝ) :
    ‖loAffA2Bg (I := I) (M := M) g hρ hδ0 hδ_le hreal u t‖ ≤
      ‖lowA2LoBg (I := I) (M := M)
        g g hρ hδ0 hδ_le hreal (incl32 (I := I) (M := M) g (u t))‖ := by
  let A2 := lowA2LoBg (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal (incl32 (I := I) (M := M) g (u t))
  let R3 := radialCLM (I := I) (M := M) g
    (show (0 : ℝ) ≤ 3 by norm_num) ρ
      (incl32 (I := I) (M := M) g (u t))
  have hR3 : ‖R3‖ ≤ 1 :=
    radialCLM_norm (I := I) (M := M) g (by norm_num) hρ _
  change ‖A2.comp R3‖ ≤ ‖A2‖
  calc
    ‖A2.comp R3‖ ≤ ‖A2‖ * ‖R3‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A2‖ * 1 := mul_le_mul_of_nonneg_left hR3 (norm_nonneg A2)
    _ = ‖A2‖ := mul_one _

/-- The high and low radialized complete second-order families commute with
the adjacent Sobolev inclusions at every time. -/
theorem affA2Bg_comm
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcoef : ∀ v : metricH2 (I := I) (M := M) g,
      (incl12 (I := I) (M := M) g).comp
          (lowA2HiBg (I := I) (M := M)
            g g hρ hδ0 hδ_le hreal v) =
        (lowA2LoBg (I := I) (M := M)
            g g hρ hδ0 hδ_le hreal v).comp
          (incl34 (I := I) (M := M) g))
    (u : ℝ → metricH3 (I := I) (M := M) g) (t : ℝ) :
    (incl12 (I := I) (M := M) g).comp
        (hiAffA2Bg (I := I) (M := M)
          g hρ hδ0 hδ_le hreal u t) =
      (loAffA2Bg (I := I) (M := M)
          g hρ hδ0 hδ_le hreal u t).comp
        (incl34 (I := I) (M := M) g) := by
  let J12 := incl12 (I := I) (M := M) g
  let J34 := incl34 (I := I) (M := M) g
  let v := incl32 (I := I) (M := M) g (u t)
  let AHi := lowA2HiBg (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal v
  let ALo := lowA2LoBg (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal v
  let R4 := radialCLM (I := I) (M := M) g
    (show (0 : ℝ) ≤ 4 by norm_num) ρ v
  let R3 := radialCLM (I := I) (M := M) g
    (show (0 : ℝ) ≤ 3 by norm_num) ρ v
  have hcoef' : J12.comp AHi = ALo.comp J34 := hcoef v
  have hrad : J34.comp R4 = R3.comp J34 :=
    radialCLM_incl (I := I) (M := M) g
      (show (0 : ℝ) ≤ 3 by norm_num) (show (0 : ℝ) ≤ 4 by norm_num)
      (show (3 : ℝ) ≤ 4 by norm_num) ρ v
  apply ContinuousLinearMap.ext
  intro x
  simp only [hiAffA2Bg, loAffA2Bg, ContinuousLinearMap.comp_apply]
  rw [show J12 (AHi (R4 x)) = ALo (J34 (R4 x)) by
      exact DFunLike.congr_fun hcoef' (R4 x)]
  rw [show J34 (R4 x) = R3 (J34 x) by
      exact DFunLike.congr_fun hrad x]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- A measurable H3 trajectory gives measurable uniformly bounded compatible
high and low complete second-order families after radializing the passengers. -/
theorem affA2Bg_data
    (g : SmoothRiemannianMetric I M) {ρ δ c : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcontHi : Continuous
      (lowA2HiBg (I := I) (M := M) g g hρ hδ0 hδ_le hreal))
    (hcontLo : Continuous
      (lowA2LoBg (I := I) (M := M) g g hρ hδ0 hδ_le hreal))
    (hsmallHi : ∀ v : metricH2 (I := I) (M := M) g,
      ‖show a2HiOp (I := I) (M := M) g from
        lowA2HiBg (I := I) (M := M)
          g g hρ hδ0 hδ_le hreal v‖ ≤ c)
    (hsmallLo : ∀ v : metricH2 (I := I) (M := M) g,
      ‖show a2LoOp (I := I) (M := M) g from
        lowA2LoBg (I := I) (M := M)
          g g hρ hδ0 hδ_le hreal v‖ ≤ c)
    {T : ℝ} (u : ℝ → metricH3 (I := I) (M := M) g)
    (hu : AEStronglyMeasurable u (timeMeasure T)) :
    AEStronglyMeasurable
        (hiAffA2Bg (I := I) (M := M)
          g hρ hδ0 hδ_le hreal u) (timeMeasure T) ∧
      (∀ᵐ t ∂timeMeasure T,
        ‖hiAffA2Bg (I := I) (M := M)
          g hρ hδ0 hδ_le hreal u t‖ ≤ c) ∧
      AEStronglyMeasurable
        (loAffA2Bg (I := I) (M := M)
          g hρ hδ0 hδ_le hreal u) (timeMeasure T) ∧
      (∀ᵐ t ∂timeMeasure T,
        ‖loAffA2Bg (I := I) (M := M)
          g hρ hδ0 hδ_le hreal u t‖ ≤ c) := by
  have hju : AEStronglyMeasurable
      (fun t => incl32 (I := I) (M := M) g (u t)) (timeMeasure T) :=
    (incl32 (I := I) (M := M) g).continuous.comp_aestronglyMeasurable hu
  have hAHi : AEStronglyMeasurable
      (fun t => lowA2HiBg (I := I) (M := M)
        g g hρ hδ0 hδ_le hreal
          (incl32 (I := I) (M := M) g (u t))) (timeMeasure T) :=
    hcontHi.comp_aestronglyMeasurable hju
  have hALo : AEStronglyMeasurable
      (fun t => lowA2LoBg (I := I) (M := M)
        g g hρ hδ0 hδ_le hreal
          (incl32 (I := I) (M := M) g (u t))) (timeMeasure T) :=
    hcontLo.comp_aestronglyMeasurable hju
  have hR4 : AEStronglyMeasurable
      (fun t => radialCLM (I := I) (M := M) g
        (show (0 : ℝ) ≤ 4 by norm_num) ρ
          (incl32 (I := I) (M := M) g (u t))) (timeMeasure T) :=
    radialCLM_aemeas (I := I) (M := M) g (by norm_num) hju
  have hR3 : AEStronglyMeasurable
      (fun t => radialCLM (I := I) (M := M) g
        (show (0 : ℝ) ≤ 3 by norm_num) ρ
          (incl32 (I := I) (M := M) g (u t))) (timeMeasure T) :=
    radialCLM_aemeas (I := I) (M := M) g (by norm_num) hju
  have hmeasHi : AEStronglyMeasurable
      (hiAffA2Bg (I := I) (M := M)
        g hρ hδ0 hδ_le hreal u) (timeMeasure T) := by
    simpa only [hiAffA2Bg] using
      (ContinuousLinearMap.compL ℝ
        (metricH4 (I := I) (M := M) g)
        (metricH4 (I := I) (M := M) g)
        (metricH2 (I := I) (M := M) g)).continuous₂
          |>.comp_aestronglyMeasurable₂ hAHi hR4
  have hmeasLo : AEStronglyMeasurable
      (loAffA2Bg (I := I) (M := M)
        g hρ hδ0 hδ_le hreal u) (timeMeasure T) := by
    simpa only [loAffA2Bg] using
      (ContinuousLinearMap.compL ℝ
        (metricH3 (I := I) (M := M) g)
        (metricH3 (I := I) (M := M) g)
        (metricH1 (I := I) (M := M) g)).continuous₂
          |>.comp_aestronglyMeasurable₂ hALo hR3
  refine ⟨hmeasHi, Filter.Eventually.of_forall fun t => ?_, hmeasLo,
    Filter.Eventually.of_forall fun t => ?_⟩
  · exact (hiAffA2Bg_le (I := I) (M := M)
      g hρ hδ0 hδ_le hreal u t).trans
        (hsmallHi (incl32 (I := I) (M := M) g (u t)))
  · exact (loAffA2Bg_le (I := I) (M := M)
      g hρ hδ0 hδ_le hreal u t).trans
        (hsmallLo (incl32 (I := I) (M := M) g (u t)))

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
