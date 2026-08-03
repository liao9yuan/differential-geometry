import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgA1Time
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegRhsOne
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.NonautonomousL2Cross

/-!
# The affine packet of the fixed-background order-one arm

This module isolates the path-integrated `C1 · ∇W` arm of the low-base action.
Unlike the complete first-order coefficient, this arm has an affine high-jet
bound on every fixed `H2` state ball.  The packet `c1_bg_pack` is stated before
any time horizon or trajectory, so that a consumer can cap a radius against the
growth constant `L` and only then build a trajectory.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private abbrev metricH3 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (3 : ℝ)

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev metricH1 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

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

private theorem incl32_core
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    incl32 (I := I) (M := M) g
        (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T) =
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T := by
  refine tensorHs.ext ?_
  funext i
  simp only [incl32, tensorHsInclusion_coeff_apply, ccTensorToHs_coeff]

/-- The isolated order-one arm, represented in the common action bundle. -/
private noncomputable def c1Part
    {g : SmoothRiemannianMetric I M} (A : LowBaseActionData g) :
    LowBaseActionData g where
  C0 := 0
  C1 := A.C1
  C2 := 0

private noncomputable def zeroData
    (g : SmoothRiemannianMetric I M) : LowBaseActionData g where
  C0 := 0
  C1 := 0
  C2 := 0

private theorem zeroData_a1
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    (zeroData (I := I) (M := M) g).a1 (I := I) (M := M) W = 0 := by
  simp only [zeroData, LowBaseActionData.a1, ← appCcRS_zero_eq_appCc,
    appCcRS_zero_left, zero_add]

private theorem iter_zero
    (g : SmoothRiemannianMetric I M) (r s j : ℕ) :
    iteratedCovGrad (I := I) g r s j
        (0 : SmoothCcTensor g r s) = 0 := by
  have h := iteratedCovGrad_smul (I := I) (M := M) g r s j
    (0 : ℝ) (0 : SmoothCcTensor g r s)
  simpa only [zero_smul] using h

private theorem lowJet_zero
    (g : SmoothRiemannianMetric I M) (r s m : ℕ) :
    lowJetSq (I := I) (M := M) g m
        (0 : SmoothCcTensor g r s) = 0 := by
  simp only [lowJetSq, iter_zero (I := I) (M := M), norm_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero]

private theorem zeroData_pair
    (g : SmoothRiemannianMetric I M) :
    ‖(zeroData (I := I) (M := M) g).a1Hi (I := I) (M := M)‖ = 0 ∧
      ‖(zeroData (I := I) (M := M) g).a1Lo (I := I) (M := M)‖ = 0 := by
  obtain ⟨C, _, hpair⟩ := a1_pair (I := I) (M := M) g
  have hHi : ∀ W : SmoothCcTensor g 0 2,
      lowJetSq (I := I) (M := M) g 2
          ((zeroData (I := I) (M := M) g).a1 (I := I) (M := M) W) ≤
        (0 : ℝ) * lowJetSq (I := I) (M := M) g 3 W := by
    intro W
    rw [zeroData_a1 (I := I) (M := M),
      lowJet_zero (I := I) (M := M)]
    simp only [zero_mul]
    exact le_rfl
  have hLo : ∀ W : SmoothCcTensor g 0 2,
      lowJetSq (I := I) (M := M) g 1
          ((zeroData (I := I) (M := M) g).a1 (I := I) (M := M) W) ≤
        (0 : ℝ) * lowJetSq (I := I) (M := M) g 2 W := by
    intro W
    rw [zeroData_a1 (I := I) (M := M),
      lowJet_zero (I := I) (M := M)]
    simp only [zero_mul]
    exact le_rfl
  obtain ⟨hHiNorm, hLoNorm, _⟩ := hpair
    (zeroData (I := I) (M := M) g) 0 le_rfl hHi hLo
  constructor
  · exact le_antisymm (by simpa only [Real.sqrt_zero, mul_zero] using hHiNorm)
      (norm_nonneg
        ((zeroData (I := I) (M := M) g).a1Hi (I := I) (M := M)))
  · exact le_antisymm (by simpa only [Real.sqrt_zero, mul_zero] using hLoNorm)
      (norm_nonneg
        ((zeroData (I := I) (M := M) g).a1Lo (I := I) (M := M)))

omit [BoundarylessManifold I M] in
private theorem zero_fb
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

/-- On a fixed spectral `H2` ball, the path-integrated order-one coefficient
has an `H2` jet bound affine in the independent `H3` size. -/
theorem c1_bg_aff
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδlt : δ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ A →
        lowJetSq (I := I) (M := M) g 2
            (lowBaseData (I := I) (M := M) g gB T
              hδlt hδT hδZ).C1 ≤
          (B0 R + B1 R * A) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hpath⟩ :=
    rhs1_path_tame (I := I) (M := M) hDim g gB hδ0 hδlt
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro T hδT hδZ R A hR hA hT2 hT3
  have hZ2 :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ R := by
    rw [show ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2) = 0 by
      simpa only [ccToHsLin_apply] using
        map_zero (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ))]
    simpa only [norm_zero] using hR
  have hZ3 :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ A := by
    rw [show ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
        (0 : SmoothCcTensor g 0 2) = 0 by
      simpa only [ccToHsLin_apply] using
        map_zero (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ))]
    simpa only [norm_zero] using hA
  have hraw := hpath T (0 : SmoothCcTensor g 0 2)
    hδT hδZ R A hR hA hT2 hZ2 hT3 hZ3
  rw [LowBaseInternal.c1_eq (I := I) (M := M)
    g gB T hδlt hδT hδZ]
  simpa only [lowJetSq, Nat.reduceAdd] using hraw

private theorem c1_core_pair
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧
      ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (_ : ρ ≤ ρ0)
        (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hreal : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ)
        (r : ℝ),
      ∃ K : ℝ, 0 ≤ K ∧ ∀ T U : SmoothCcTensor g 0 2,
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ r →
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r →
        let AT := c1Part (I := I) (M := M)
          (lowCoreDataBg (I := I) (M := M)
            g gB hρ.le hδ0 hδ_le hreal T)
        let AU := c1Part (I := I) (M := M)
          (lowCoreDataBg (I := I) (M := M)
            g gB hρ.le hδ0 hδ_le hreal U)
        ‖AT.a1Hi (I := I) (M := M) - AU.a1Hi (I := I) (M := M)‖ ≤
            K * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
              ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ∧
          ‖AT.a1Lo (I := I) (M := M) - AU.a1Lo (I := I) (M := M)‖ ≤
            K * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
              ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
  obtain ⟨ρ0, B0, B1, hρ0, hB0, hB1, hcoeff⟩ :=
    c1_bg_pair_h2 (I := I) (M := M) hDim g gB
  obtain ⟨Ca, hCa, hact⟩ := a1_diff (I := I) (M := M) hDim g
  obtain ⟨C3, hC3, hjet3⟩ := jet3_le_hs (I := I) (M := M) g
  refine ⟨ρ0, hρ0, ?_⟩
  intro ρ δ hρ hρρ0 hδ0 hδ_le hreal r
  let r0 : ℝ := max r 0
  let L : ℝ := 1 + (1 / ρ) * r0
  let K0 : ℝ := B0 * C3 * L + B1 + B1 * (C3 * r0)
  let K : ℝ := Ca * K0
  have hr0 : 0 ≤ r0 := le_max_right r 0
  have hL : 0 ≤ L := by
    simp only [L]
    positivity
  have hK0 : 0 ≤ K0 := by
    simp only [K0]
    positivity
  refine ⟨K, mul_nonneg hCa hK0, ?_⟩
  intro T U hTr hUr
  let D : ℝ :=
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
      ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖
  let S : SmoothCcTensor g 0 2 :=
    lowRadial (I := I) (M := M) g ρ T
  let V : SmoothCcTensor g 0 2 :=
    lowRadial (I := I) (M := M) g ρ U
  have hD : 0 ≤ D := norm_nonneg _
  have hTr0 :
      ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ r0 :=
    hTr.trans (le_max_left r 0)
  have hUr0 :
      ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r0 :=
    hUr.trans (le_max_left r 0)
  have hSρ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ :=
    lowRadial_norm (I := I) (M := M) g hρ.le T
  have hVρ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) V‖ ≤ ρ :=
    lowRadial_norm (I := I) (M := M) g hρ.le U
  have hSδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g S) δ := hreal S hSρ
  have hVδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g V) δ := hreal V hVρ
  have hZδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2)) δ :=
    zero_fb (I := I) (M := M) g hδ0
  have hStop :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) S‖ ≤ r0 := by
    have hrad := lowRadialH3_le (I := I) (M := M) g hρ
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T)
    rw [lowRadialH3_core (I := I) (M := M) g hρ T] at hrad
    simpa only [S, ccToHsLin_apply] using hrad.trans hTr0
  have hincl :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ D := by
    have h := tensorHsInclusion_norm_le (I := I) (M := M)
      (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
      (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T -
        ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U)
    rw [map_sub, incl32_core (I := I) (M := M) g T,
      incl32_core (I := I) (M := M) g U] at h
    simpa only [D, ccToHsLin_apply] using h
  have hSV2 :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V)‖ ≤ D := by
    rw [show ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V) =
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) V by
      simpa only [ccToHsLin_apply] using
        map_sub (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) S V]
    exact (lowRadial_lip (I := I) (M := M) g hρ.le T U).trans hincl
  have hmax :
      max
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r0 := by
    simpa only [ccToHsLin_apply] using max_le hTr0 hUr0
  have hprod :
      max
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤
        r0 * D :=
    mul_le_mul hmax hincl (norm_nonneg _) hr0
  have hSV3 :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) S -
          ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) V‖ ≤
        L * D := by
    refine (lowRadial_h3_sub (I := I) (M := M) g hρ T U).trans ?_
    have hρinv : 0 ≤ (1 / ρ : ℝ) := (one_div_pos.mpr hρ).le
    have hscaled := mul_le_mul_of_nonneg_left hprod hρinv
    have hscaled' :
        (1 / ρ) *
              max
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
                ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤
          (1 / ρ) * (r0 * D) := by
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
                  ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖) := by
              ring
        _ ≤ (1 / ρ) * (r0 * D) := hscaled
    have hD3eq :
        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T -
            ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ = D := by
      simp only [D, ccToHsLin_apply]
    calc
      _ = D +
            (1 / ρ) *
              max
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
                ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
          rw [hD3eq]
      _ ≤ D + (1 / ρ) * (r0 * D) := by
          linarith only [hscaled']
      _ = L * D := by
          simp only [L]
          ring
  let A : ℝ := C3 * r0
  let D3 : ℝ := C3 * L * D
  have hA : 0 ≤ A := mul_nonneg hC3 hr0
  have hD3 : 0 ≤ D3 := mul_nonneg (mul_nonneg hC3 hL) hD
  have hS3 : lowJetSq (I := I) (M := M) g 3 S ≤ A ^ 2 := by
    refine (hjet3 S).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC3 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hStop hC3) 2
  have hSV3j : lowJetSq (I := I) (M := M) g 3 (S - V) ≤ D3 ^ 2 := by
    have hnorm :
        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (S - V)‖ ≤
          L * D := by
      rw [show ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (S - V) =
          ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) S -
            ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) V by
        simpa only [ccToHsLin_apply] using
          map_sub (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) S V]
      exact hSV3
    refine (hjet3 (S - V)).trans ?_
    simpa only [D3, mul_assoc] using pow_le_pow_left₀
      (mul_nonneg hC3 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hnorm hC3) 2
  have hraw := hcoeff S V
    (lowRadial_symm (I := I) (M := M) g ρ T)
    (lowRadial_symm (I := I) (M := M) g ρ U)
    hδ_le hδ0 hSδ hVδ hZδ
    (hSρ.trans hρρ0) (hVρ.trans hρρ0)
    A D3 hA hD3 hS3 hSV3j
  have hR :
      B0 * D3 +
          B1 * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V)‖ +
          B1 * A *
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V)‖ ≤
        K0 * D := by
    calc
      B0 * D3 +
            B1 * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V)‖ +
            B1 * A *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V)‖ ≤
          B0 * D3 + B1 * D + B1 * A * D := by
        gcongr
      _ = K0 * D := by
        simp only [D3, A, K0]
        ring
  have hR0 : 0 ≤
      B0 * D3 +
        B1 * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V)‖ +
        B1 * A *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V)‖ := by
    positivity
  have hcoeffBound :
      lowJetSq (I := I) (M := M) g 2
          ((lowBaseData (I := I) (M := M) g gB S
              (lt_of_le_of_lt hδ_le (by norm_num)) hSδ hZδ).C1 -
            (lowBaseData (I := I) (M := M) g gB V
              (lt_of_le_of_lt hδ_le (by norm_num)) hVδ hZδ).C1) ≤
        (K0 * D) ^ 2 :=
    hraw.trans (pow_le_pow_left₀ hR0 hR 2)
  let AT : LowBaseActionData g := c1Part (I := I) (M := M)
    (lowCoreDataBg (I := I) (M := M)
      g gB hρ.le hδ0 hδ_le hreal T)
  let AU : LowBaseActionData g := c1Part (I := I) (M := M)
    (lowCoreDataBg (I := I) (M := M)
      g gB hρ.le hδ0 hδ_le hreal U)
  have hcoeffAct :
      lowJetSq (I := I) (M := M) g 2 (AT.C0 - AU.C0) +
          lowJetSq (I := I) (M := M) g 2 (AT.C1 - AU.C1) ≤
        (K0 * D) ^ 2 := by
    simpa only [AT, AU, c1Part, lowCoreDataBg, S, V, sub_self,
      lowJet_zero (I := I) (M := M), zero_add] using hcoeffBound
  have hop := hact AT AU (K0 * D) (mul_nonneg hK0 hD) hcoeffAct
  change
    ‖AT.a1Hi (I := I) (M := M) - AU.a1Hi (I := I) (M := M)‖ ≤ K * D ∧
      ‖AT.a1Lo (I := I) (M := M) - AU.a1Lo (I := I) (M := M)‖ ≤ K * D
  constructor
  · calc
      ‖AT.a1Hi (I := I) (M := M) - AU.a1Hi (I := I) (M := M)‖ ≤
          Ca * (K0 * D) := hop.1
      _ = K * D := by simp only [K]; ring
  · calc
      ‖AT.a1Lo (I := I) (M := M) - AU.a1Lo (I := I) (M := M)‖ ≤
          Ca * (K0 * D) := hop.2
      _ = K * D := by simp only [K]; ring

private theorem c1_core_affine
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 < ρ)
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    ∃ Z L : ℝ, 0 ≤ Z ∧ 0 ≤ L ∧
      ∀ T : SmoothCcTensor g 0 2,
        let A := c1Part (I := I) (M := M)
          (lowCoreDataBg (I := I) (M := M)
            g gB hρ.le hδ0 hδ_le hreal T)
        ‖A.a1Hi (I := I) (M := M)‖ ≤
            Z + L * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ∧
          ‖A.a1Lo (I := I) (M := M)‖ ≤
            Z + L * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
  obtain ⟨B0, B1, hB0, hB1, hcoeff⟩ :=
    c1_bg_aff (I := I) (M := M) hDim g gB hδ0
      (lt_of_le_of_lt hδ_le (by norm_num))
  obtain ⟨Ca, hCa, hact⟩ := a1_diff (I := I) (M := M) hDim g
  let Z : ℝ := Ca * B0 ρ
  let L : ℝ := Ca * B1 ρ
  have hZ : 0 ≤ Z := mul_nonneg hCa (hB0 ρ hρ.le)
  have hL : 0 ≤ L := mul_nonneg hCa (hB1 ρ hρ.le)
  refine ⟨Z, L, hZ, hL, ?_⟩
  intro T
  let S : SmoothCcTensor g 0 2 :=
    lowRadial (I := I) (M := M) g ρ T
  let A : LowBaseActionData g := c1Part (I := I) (M := M)
    (lowCoreDataBg (I := I) (M := M)
      g gB hρ.le hδ0 hδ_le hreal T)
  let R : ℝ := B0 ρ + B1 ρ *
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖
  have hSρ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ :=
    lowRadial_norm (I := I) (M := M) g hρ.le T
  have hSδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g S) δ := hreal S hSρ
  have hZδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2)) δ :=
    zero_fb (I := I) (M := M) g hδ0
  have hS3 :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) S‖ ≤
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
    have hrad := lowRadialH3_le (I := I) (M := M) g hρ
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T)
    rw [lowRadialH3_core (I := I) (M := M) g hρ T] at hrad
    simpa only [S, ccToHsLin_apply] using hrad
  have hR : 0 ≤ R := by
    simp only [R]
    exact add_nonneg (hB0 ρ hρ.le)
      (mul_nonneg (hB1 ρ hρ.le) (norm_nonneg _))
  have hcoeffRaw :
      lowJetSq (I := I) (M := M) g 2
          (lowBaseData (I := I) (M := M) g gB S
            (lt_of_le_of_lt hδ_le (by norm_num)) hSδ hZδ).C1 ≤ R ^ 2 := by
    exact hcoeff S hSδ hZδ ρ
      ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖
      hρ.le (norm_nonneg _) hSρ hS3
  have hcoeffAct :
      lowJetSq (I := I) (M := M) g 2
          (A.C0 - (zeroData (I := I) (M := M) g).C0) +
        lowJetSq (I := I) (M := M) g 2
          (A.C1 - (zeroData (I := I) (M := M) g).C1) ≤ R ^ 2 := by
    simpa only [A, c1Part, zeroData, lowCoreDataBg, S, sub_zero,
      lowJet_zero (I := I) (M := M), zero_add] using hcoeffRaw
  have hop := hact A (zeroData (I := I) (M := M) g) R hR hcoeffAct
  have hz := zeroData_pair (I := I) (M := M) g
  have hzHi :
      (zeroData (I := I) (M := M) g).a1Hi (I := I) (M := M) = 0 :=
    (ContinuousLinearMap.opNorm_zero_iff
      ((zeroData (I := I) (M := M) g).a1Hi (I := I) (M := M))).mp hz.1
  have hzLo :
      (zeroData (I := I) (M := M) g).a1Lo (I := I) (M := M) = 0 :=
    (ContinuousLinearMap.opNorm_zero_iff
      ((zeroData (I := I) (M := M) g).a1Lo (I := I) (M := M))).mp hz.2
  change
    ‖A.a1Hi (I := I) (M := M)‖ ≤
        Z + L * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ∧
      ‖A.a1Lo (I := I) (M := M)‖ ≤
        Z + L * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖
  constructor
  · calc
      ‖A.a1Hi (I := I) (M := M)‖ ≤ Ca * R := by
        simpa only [hzHi, sub_zero] using hop.1
      _ = Z + L * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
        simp only [R, Z, L]
        ring
  · calc
      ‖A.a1Lo (I := I) (M := M)‖ ≤ Ca * R := by
        simpa only [hzLo, sub_zero] using hop.2
      _ = Z + L * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
        simp only [R, Z, L]
        ring

private theorem a1_comm_any
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowBaseActionData g) :
    (incl12 (I := I) (M := M) g).comp
        (A.a1Hi (I := I) (M := M)) =
      (A.a1Lo (I := I) (M := M)).comp
        (incl32 (I := I) (M := M) g) := by
  obtain ⟨_, _, hpair⟩ := a1_pair (I := I) (M := M) g
  obtain ⟨Ch, hCh, hhigh⟩ :=
    a1_h3_h2 (I := I) (M := M) hDim g
  obtain ⟨Cl, hCl, hlow⟩ :=
    a1_h2_h1 (I := I) (M := M) hDim g
  let J : ℝ :=
    lowJetSq (I := I) (M := M) g 2 A.C0 +
      lowJetSq (I := I) (M := M) g 2 A.C1
  let B : ℝ := Real.sqrt J
  let Ca : ℝ := Ch + Cl
  let Q : ℝ := (Ca * B) ^ 2
  have hJ : 0 ≤ J := add_nonneg
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = J := by
    simpa only [B] using Real.sq_sqrt hJ
  have hCa : 0 ≤ Ca := add_nonneg hCh hCl
  have hQ : 0 ≤ Q := sq_nonneg _
  have hHi : ∀ W : SmoothCcTensor g 0 2,
      lowJetSq (I := I) (M := M) g 2
          (A.a1 (I := I) (M := M) W) ≤
        Q * lowJetSq (I := I) (M := M) g 3 W := by
    intro W
    let S : ℝ := Real.sqrt (lowJetSq (I := I) (M := M) g 3 W)
    have hW : 0 ≤ lowJetSq (I := I) (M := M) g 3 W :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hS : 0 ≤ S := Real.sqrt_nonneg _
    have hSsq : S ^ 2 = lowJetSq (I := I) (M := M) g 3 W := by
      simpa only [S] using Real.sq_sqrt hW
    calc
      lowJetSq (I := I) (M := M) g 2
          (A.a1 (I := I) (M := M) W) ≤ (Ch * B * S) ^ 2 :=
        hhigh A W B S hB hS (by rw [hBsq])
          (by rw [hSsq])
      _ ≤ (Ca * B * S) ^ 2 := by
        exact pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hCh hB) hS)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right hCl) hB) hS) 2
      _ = Q * lowJetSq (I := I) (M := M) g 3 W := by
        rw [show (Ca * B * S) ^ 2 = (Ca * B) ^ 2 * S ^ 2 by ring,
          hSsq]
  have hLo : ∀ W : SmoothCcTensor g 0 2,
      lowJetSq (I := I) (M := M) g 1
          (A.a1 (I := I) (M := M) W) ≤
        Q * lowJetSq (I := I) (M := M) g 2 W := by
    intro W
    let S : ℝ := Real.sqrt (lowJetSq (I := I) (M := M) g 2 W)
    have hW : 0 ≤ lowJetSq (I := I) (M := M) g 2 W :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hS : 0 ≤ S := Real.sqrt_nonneg _
    have hSsq : S ^ 2 = lowJetSq (I := I) (M := M) g 2 W := by
      simpa only [S] using Real.sq_sqrt hW
    calc
      lowJetSq (I := I) (M := M) g 1
          (A.a1 (I := I) (M := M) W) ≤ (Cl * B * S) ^ 2 :=
        hlow A W B S hB hS (by rw [hBsq])
          (by rw [hSsq])
      _ ≤ (Ca * B * S) ^ 2 := by
        exact pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hCl hB) hS)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_left hCh) hB) hS) 2
      _ = Q * lowJetSq (I := I) (M := M) g 2 W := by
        rw [show (Ca * B * S) ^ 2 = (Ca * B) ^ 2 * S ^ 2 by ring,
          hSsq]
  obtain ⟨_, _, _, _, hcomm⟩ := hpair A Q hQ hHi hLo
  simpa only [incl12, incl32] using hcomm

private theorem c1_ext_pair
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧
      ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (_ : ρ ≤ ρ0)
        (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hreal : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ),
      ∃ Z L : ℝ, 0 ≤ Z ∧ 0 ≤ L ∧
        ∃ FHi : metricH3 (I := I) (M := M) g →
              (metricH3 (I := I) (M := M) g →L[ℝ]
                metricH2 (I := I) (M := M) g),
          ∃ FLo : metricH3 (I := I) (M := M) g →
              (metricH2 (I := I) (M := M) g →L[ℝ]
                metricH1 (I := I) (M := M) g),
            Continuous FHi ∧ Continuous FLo ∧
            (∀ T : SmoothCcTensor g 0 2,
              FHi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T) =
                (c1Part (I := I) (M := M)
                  (lowCoreDataBg (I := I) (M := M)
                    g gB hρ.le hδ0 hδ_le hreal T)).a1Hi
                      (I := I) (M := M)) ∧
            (∀ T : SmoothCcTensor g 0 2,
              FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T) =
                (c1Part (I := I) (M := M)
                  (lowCoreDataBg (I := I) (M := M)
                    g gB hρ.le hδ0 hδ_le hreal T)).a1Lo
                      (I := I) (M := M)) ∧
            (∀ x : metricH3 (I := I) (M := M) g,
              ‖FHi x‖ ≤ Z + L * ‖x‖) ∧
            (∀ x : metricH3 (I := I) (M := M) g,
              ‖FLo x‖ ≤ Z + L * ‖x‖) ∧
            (∀ x : metricH3 (I := I) (M := M) g,
              (incl12 (I := I) (M := M) g).comp (FHi x) =
                (FLo x).comp (incl32 (I := I) (M := M) g)) := by
  obtain ⟨ρ0, hρ0, hpair⟩ := c1_core_pair (I := I) (M := M) hDim g gB
  refine ⟨ρ0, hρ0, ?_⟩
  intro ρ δ hρ hρρ0 hδ0 hδ_le hreal
  obtain ⟨Z, L, hZ, hL, hbd⟩ :=
    c1_core_affine (I := I) (M := M) hDim g gB hρ hδ0 hδ_le hreal
  let fHi : SmoothCcTensor g 0 2 →
      (metricH3 (I := I) (M := M) g →L[ℝ]
        metricH2 (I := I) (M := M) g) := fun T =>
    (c1Part (I := I) (M := M)
      (lowCoreDataBg (I := I) (M := M)
        g gB hρ.le hδ0 hδ_le hreal T)).a1Hi (I := I) (M := M)
  let fLo : SmoothCcTensor g 0 2 →
      (metricH2 (I := I) (M := M) g →L[ℝ]
        metricH1 (I := I) (M := M) g) := fun T =>
    (c1Part (I := I) (M := M)
      (lowCoreDataBg (I := I) (M := M)
        g gB hρ.le hδ0 hδ_le hreal T)).a1Lo (I := I) (M := M)
  have hpairHi : ∀ r : ℝ, ∃ K : ℝ,
      ∀ T U : SmoothCcTensor g 0 2,
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ r →
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r →
        ‖fHi T - fHi U‖ ≤ K *
          ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
            ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
    intro r
    obtain ⟨K, _, hK⟩ := hpair hρ hρρ0 hδ0 hδ_le hreal r
    refine ⟨K, ?_⟩
    intro T U hT hU
    simpa only [fHi] using (hK T U hT hU).1
  have hpairLo : ∀ r : ℝ, ∃ K : ℝ,
      ∀ T U : SmoothCcTensor g 0 2,
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ r →
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r →
        ‖fLo T - fLo U‖ ≤ K *
          ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
            ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
    intro r
    obtain ⟨K, _, hK⟩ := hpair hρ hρρ0 hδ0 hδ_le hreal r
    refine ⟨K, ?_⟩
    intro T U hT hU
    simpa only [fLo] using (hK T U hT hU).2
  have hbdHi : ∀ T : SmoothCcTensor g 0 2,
      ‖fHi T‖ ≤ Z + L *
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
    intro T
    simpa only [fHi] using (hbd T).1
  have hbdLo : ∀ T : SmoothCcTensor g 0 2,
      ‖fLo T‖ ≤ Z + L *
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
    intro T
    simpa only [fLo] using (hbd T).2
  have hΦ : Continuous (fun x : ℝ => Z + L * x) := by
    fun_prop
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  obtain ⟨FHi, hFHi, hFHiCore, hFHiBd⟩ :=
    DifferentialGeometry.Analysis.exists_extend_le
      (j := ccToHsLin (I := I) (M := M) g 2 (3 : ℝ))
      hdense fHi hΦ hpairHi hbdHi
  obtain ⟨FLo, hFLo, hFLoCore, hFLoBd⟩ :=
    DifferentialGeometry.Analysis.exists_extend_le
      (j := ccToHsLin (I := I) (M := M) g 2 (3 : ℝ))
      hdense fLo hΦ hpairLo hbdLo
  have hleft : Continuous (fun x : metricH3 (I := I) (M := M) g =>
      (incl12 (I := I) (M := M) g).comp (FHi x)) :=
    (ContinuousLinearMap.compL ℝ
      (metricH3 (I := I) (M := M) g)
      (metricH2 (I := I) (M := M) g)
      (metricH1 (I := I) (M := M) g)).continuous₂.comp
        (continuous_const.prodMk hFHi)
  have hright : Continuous (fun x : metricH3 (I := I) (M := M) g =>
      (FLo x).comp (incl32 (I := I) (M := M) g)) :=
    (ContinuousLinearMap.compL ℝ
      (metricH3 (I := I) (M := M) g)
      (metricH2 (I := I) (M := M) g)
      (metricH1 (I := I) (M := M) g)).continuous₂.comp
        (hFLo.prodMk continuous_const)
  have hcomm : ∀ x : metricH3 (I := I) (M := M) g,
      (incl12 (I := I) (M := M) g).comp (FHi x) =
        (FLo x).comp (incl32 (I := I) (M := M) g) := by
    intro x
    refine hdense.induction_on x (isClosed_eq hleft hright) ?_
    intro T
    rw [hFHiCore T, hFLoCore T]
    exact a1_comm_any (I := I) (M := M) hDim g _
  exact ⟨Z, L, hZ, hL, FHi, FLo, hFHi, hFLo,
    hFHiCore, hFLoCore, hFHiBd, hFLoBd, hcomm⟩

/-- **The trajectory-free affine packet of the fixed-background order-one
arm.**  On every coefficient radius `ρ ≤ ρ₀` the path-integrated order-one
coefficient supplies a pair of completed action maps on the two adjacent
Sobolev scales, continuous, realizing the order-one core action on smooth data,
with a common affine growth certificate `‖F x‖ ≤ Z + L‖x‖` and the
Sobolev-inclusion square.  No time horizon and no trajectory occur here: `Z`
and `L` depend only on `ρ, δ` and the realization bound, so a consumer may cap
a radius against `L` before any trajectory exists. -/
theorem c1_bg_pack
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧
      ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (_ : ρ ≤ ρ0)
        (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hreal : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ),
      ∃ Z L : ℝ, 0 ≤ Z ∧ 0 ≤ L ∧
        ∃ FHi : metricH3 (I := I) (M := M) g →
              (metricH3 (I := I) (M := M) g →L[ℝ]
                metricH2 (I := I) (M := M) g),
          ∃ FLo : metricH3 (I := I) (M := M) g →
              (metricH2 (I := I) (M := M) g →L[ℝ]
                metricH1 (I := I) (M := M) g),
            Continuous FHi ∧ Continuous FLo ∧
            (∀ S : SmoothCcTensor g 0 2,
              FHi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
                ({ C0 := 0
                   C1 := (lowCoreDataBg (I := I) (M := M)
                     g gB hρ.le hδ0 hδ_le hreal S).C1
                   C2 := 0 } : LowBaseActionData g).a1Hi
                     (I := I) (M := M)) ∧
            (∀ S : SmoothCcTensor g 0 2,
              FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
                ({ C0 := 0
                   C1 := (lowCoreDataBg (I := I) (M := M)
                     g gB hρ.le hδ0 hδ_le hreal S).C1
                   C2 := 0 } : LowBaseActionData g).a1Lo
                      (I := I) (M := M)) ∧
            (∀ x : metricH3 (I := I) (M := M) g,
              ‖FHi x‖ ≤ Z + L * ‖x‖) ∧
            (∀ x : metricH3 (I := I) (M := M) g,
              ‖FLo x‖ ≤ Z + L * ‖x‖) ∧
            (∀ x : metricH3 (I := I) (M := M) g,
              (incl12 (I := I) (M := M) g).comp (FHi x) =
                (FLo x).comp (incl32 (I := I) (M := M) g)) := by
  obtain ⟨ρ0, hρ0, hpacket⟩ := c1_ext_pair (I := I) (M := M) hDim g gB
  refine ⟨ρ0, hρ0, ?_⟩
  intro ρ δ hρ hρρ0 hδ0 hδ_le hreal
  obtain ⟨Z, L, hZ, hL, FHi, FLo, hFHi, hFLo,
      hFHiCore, hFLoCore, hFHiBd, hFLoBd, hFComm⟩ :=
    hpacket hρ hρρ0 hδ0 hδ_le hreal
  refine ⟨Z, L, hZ, hL, FHi, FLo, hFHi, hFLo, ?_, ?_,
    hFHiBd, hFLoBd, hFComm⟩
  · intro S
    simpa only [c1Part] using hFHiCore S
  · intro S
    simpa only [c1Part] using hFLoCore S

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
