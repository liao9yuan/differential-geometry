import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgC0Assemble
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseTime

/-!
# Smooth-core control for the refolded order-zero arm

This public endpoint bundles the internal coefficient construction into the
radial same-background low-regularity action split.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

open LowRegBgC0Core

/-- The radial same-background order-zero refold, bundled as one first-order
smooth-core action on the two adjacent Sobolev scales. -/
noncomputable def c0CoreData
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) : LowBaseActionData g :=
  let S := lowRadial (I := I) (M := M) g ρ T
  c0Data (I := I) (M := M) g S
    (lowRadial_symm (I := I) (M := M) g ρ T)
    (lt_of_le_of_lt hδ_le (by norm_num))
    (hreal S (lowRadial_norm (I := I) (M := M) g hρ T))
    (zero_fb_c0 (I := I) (M := M) g hδ0)

/-- On a smooth core state, the radial order-zero coefficient self-action is
exactly the first-order action represented by `c0CoreData`. -/
theorem c0Core_self
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    let S := lowRadial (I := I) (M := M) g ρ T
    appCc (I := I) (M := M) g 2 2
        (lowBaseData (I := I) (M := M) g g S
          (lt_of_le_of_lt hδ_le (by norm_num))
          (hreal S (lowRadial_norm (I := I) (M := M) g hρ T))
          (zero_fb_c0 (I := I) (M := M) g hδ0)).C0 S =
      (c0CoreData (I := I) (M := M)
        g hρ hδ0 hδ_le hreal T).a1 (I := I) (M := M) S := by
  dsimp only
  simpa only [c0CoreData] using
    c0Data_self (I := I) (M := M) g
      (lowRadial (I := I) (M := M) g ρ T)
      (lowRadial_symm (I := I) (M := M) g ρ T)
      (lt_of_le_of_lt hδ_le (by norm_num))
      (hreal _ (lowRadial_norm (I := I) (M := M) g hρ T))
      (zero_fb_c0 (I := I) (M := M) g hδ0)

set_option maxHeartbeats 2400000 in
set_option linter.unusedVariables false in
/-- On every bounded spectral `H3` core ball, the two completed realizations
of the radial order-zero refold are jointly Lipschitz in the state. -/
theorem c0CorePair
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
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
        let AT := c0CoreData (I := I) (M := M)
          g hρ.le hδ0 hδ_le hreal T
        let AU := c0CoreData (I := I) (M := M)
          g hρ.le hδ0 hδ_le hreal U
        ‖AT.a1Hi (I := I) (M := M) - AU.a1Hi (I := I) (M := M)‖ ≤
            K * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
              ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ∧
          ‖AT.a1Lo (I := I) (M := M) - AU.a1Lo (I := I) (M := M)‖ ≤
            K * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
              ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
  obtain ⟨ρ0, B0, Ca, B1, hρ0, hB0, hCa, hB1, hpair⟩ :=
    c0DataPairH2 (I := I) (M := M) hDim g
  obtain ⟨C2, hC2, hjet2⟩ := jet2_le_hs (I := I) (M := M) g
  obtain ⟨C3, hC3, hjet3⟩ := jet3_le_hs (I := I) (M := M) g
  refine ⟨ρ0, hρ0, ?_⟩
  intro ρ δ hρ hρρ0 hδ0 hδ_le hreal r
  let r0 : ℝ := max r 0
  let R2 : ℝ := C2 * ρ
  let A3 : ℝ := C3 * r0
  let L : ℝ := 1 + (1 / ρ) * r0
  let F0 : ℝ := B0 * (1 + R2) * (C2 + 1)
  let F1 : ℝ := B1 R2 * (1 + A3) *
    (C3 * L + C2 + A3 * C2 + 1)
  let E0 : ℝ := F0 ^ 2 + F1 ^ 2
  let K : ℝ := Ca * Real.sqrt E0
  have hr0 : 0 ≤ r0 := le_max_right r 0
  have hR2 : 0 ≤ R2 := mul_nonneg hC2 hρ.le
  have hA3 : 0 ≤ A3 := mul_nonneg hC3 hr0
  have hL : 0 ≤ L := by
    simp only [L]
    positivity
  have hF0 : 0 ≤ F0 :=
    mul_nonneg (mul_nonneg hB0 (add_nonneg (by norm_num) hR2))
      (add_nonneg hC2 (by norm_num))
  have hF1 : 0 ≤ F1 :=
    mul_nonneg (mul_nonneg (hB1 R2 hR2) (add_nonneg (by norm_num) hA3))
      (add_nonneg
        (add_nonneg (add_nonneg (mul_nonneg hC3 hL) hC2)
          (mul_nonneg hA3 hC2)) (by norm_num))
  have hE0 : 0 ≤ E0 := add_nonneg (sq_nonneg F0) (sq_nonneg F1)
  refine ⟨K, mul_nonneg hCa (Real.sqrt_nonneg _), ?_⟩
  intro T U hTr hUr
  let D : ℝ :=
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
      ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖
  let D2 : ℝ := C2 * D
  let D3 : ℝ := C3 * L * D
  let S : SmoothCcTensor g 0 2 := lowRadial (I := I) (M := M) g ρ T
  let V : SmoothCcTensor g 0 2 := lowRadial (I := I) (M := M) g ρ U
  have hD : 0 ≤ D := norm_nonneg _
  have hD2 : 0 ≤ D2 := mul_nonneg hC2 hD
  have hD3 : 0 ≤ D3 := mul_nonneg (mul_nonneg hC3 hL) hD
  have hTr0 : ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ r0 :=
    hTr.trans (le_max_left r 0)
  have hUr0 : ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r0 :=
    hUr.trans (le_max_left r 0)
  have hSρ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ :=
    lowRadial_norm (I := I) (M := M) g hρ.le T
  have hVρ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) V‖ ≤ ρ :=
    lowRadial_norm (I := I) (M := M) g hρ.le U
  have hSδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g S) δ := hreal S hSρ
  have hVδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g V) δ := hreal V hVρ
  have hZδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ :=
    zero_fb_c0 (I := I) (M := M) g hδ0
  have hS2 : lowJetSq (I := I) (M := M) g 2 S ≤ R2 ^ 2 := by
    refine (hjet2 S).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC2 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hSρ hC2) 2
  have hV2 : lowJetSq (I := I) (M := M) g 2 V ≤ R2 ^ 2 := by
    refine (hjet2 V).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC2 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hVρ hC2) 2
  have hStop : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) S‖ ≤ r0 := by
    have hrad := lowRadialH3_le (I := I) (M := M) g hρ
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T)
    rw [lowRadialH3_core (I := I) (M := M) g hρ T] at hrad
    simpa only [S, ccToHsLin_apply] using hrad.trans hTr0
  have hVtop : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) V‖ ≤ r0 := by
    have hrad := lowRadialH3_le (I := I) (M := M) g hρ
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U)
    rw [lowRadialH3_core (I := I) (M := M) g hρ U] at hrad
    simpa only [V, ccToHsLin_apply] using hrad.trans hUr0
  have hS3 : lowJetSq (I := I) (M := M) g 3 S ≤ A3 ^ 2 := by
    refine (hjet3 S).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC3 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hStop hC3) 2
  have hV3 : lowJetSq (I := I) (M := M) g 3 V ≤ A3 ^ 2 := by
    refine (hjet3 V).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC3 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hVtop hC3) 2
  have hincl :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ D := by
    have h := tensorHsInclusion_norm_le (I := I) (M := M)
      (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ 3 by norm_num)
      (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T -
        ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U)
    rw [map_sub, incl32_c0 (I := I) (M := M) g T,
      incl32_c0 (I := I) (M := M) g U] at h
    simpa only [D, ccToHsLin_apply] using h
  have hSV2 : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V)‖ ≤ D := by
    rw [show ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V) =
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) V by
      simpa only [ccToHsLin_apply] using
        map_sub (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) S V]
    exact (lowRadial_lip (I := I) (M := M) g hρ.le T U).trans hincl
  have hSV2j : lowJetSq (I := I) (M := M) g 2 (S - V) ≤ D2 ^ 2 := by
    refine (hjet2 (S - V)).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC2 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hSV2 hC2) 2
  have hmax :
      max ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r0 := by
    simpa only [ccToHsLin_apply] using max_le hTr0 hUr0
  have hprod :
      max ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ r0 * D :=
    mul_le_mul hmax hincl (norm_nonneg _) hr0
  have hSV3 : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (S - V)‖ ≤
      L * D := by
    rw [show ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (S - V) =
        ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) S -
          ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) V by
      simpa only [ccToHsLin_apply] using
        map_sub (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) S V]
    refine (lowRadial_h3_sub (I := I) (M := M) g hρ T U).trans ?_
    have hscaled := mul_le_mul_of_nonneg_left hprod
      ((one_div_pos.mpr hρ).le)
    have hscaled' :
        (1 / ρ) *
            max ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
              ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤
          (1 / ρ) * (r0 * D) := by
      calc
        _ = (1 / ρ) *
            (max ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
                ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖) := by ring
        _ ≤ (1 / ρ) * (r0 * D) := hscaled
    calc
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ +
          (1 / ρ) *
            max ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
              ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤
        D + (1 / ρ) * (r0 * D) := by
          change D + _ ≤ D + _
          exact add_le_add_right hscaled' D
      _ = L * D := by
        simp only [L]
        ring
  have hSV3j : lowJetSq (I := I) (M := M) g 3 (S - V) ≤ D3 ^ 2 := by
    refine (hjet3 (S - V)).trans ?_
    simpa only [D3, mul_assoc] using pow_le_pow_left₀
      (mul_nonneg hC3 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hSV3 hC3) 2
  have hout := hpair S V
    (lowRadial_symm (I := I) (M := M) g ρ T)
    (lowRadial_symm (I := I) (M := M) g ρ U)
    hδ_le hδ0 hSδ hVδ hZδ
    (hSρ.trans hρρ0) (hVρ.trans hρρ0)
    R2 A3 D2 D3 D hR2 hA3 hD2 hD3 hD
    hS2 hV2 hS3 hV3 hSV2j hSV3j hSV2
  let AT : LowBaseActionData g := c0CoreData (I := I) (M := M)
    g hρ.le hδ0 hδ_le hreal T
  let AU : LowBaseActionData g := c0CoreData (I := I) (M := M)
    g hρ.le hδ0 hδ_le hreal U
  have hraw :
      ‖AT.a1Hi (I := I) (M := M) - AU.a1Hi (I := I) (M := M)‖ ≤
          Ca * Real.sqrt
            ((B0 * (1 + R2) * (D2 + D)) ^ 2 +
              (B1 R2 * (1 + A3) *
                (D3 + D2 + A3 * D2 + D)) ^ 2) ∧
        ‖AT.a1Lo (I := I) (M := M) - AU.a1Lo (I := I) (M := M)‖ ≤
          Ca * Real.sqrt
            ((B0 * (1 + R2) * (D2 + D)) ^ 2 +
              (B1 R2 * (1 + A3) *
                (D3 + D2 + A3 * D2 + D)) ^ 2) := by
    simpa only [AT, AU, c0CoreData, S, V] using hout
  have hq0 : B0 * (1 + R2) * (D2 + D) = F0 * D := by
    simp only [D2, F0]
    ring
  have hq1 : B1 R2 * (1 + A3) *
      (D3 + D2 + A3 * D2 + D) = F1 * D := by
    simp only [D3, D2, F1]
    ring
  have hquad : (F0 * D) ^ 2 + (F1 * D) ^ 2 = E0 * D ^ 2 := by
    simp only [E0]
    ring
  have hsqrt : Real.sqrt ((F0 * D) ^ 2 + (F1 * D) ^ 2) =
      Real.sqrt E0 * D := by
    rw [hquad]
    exact sqrt_scale_c0 E0 D hE0 hD
  constructor
  · calc
      ‖AT.a1Hi (I := I) (M := M) - AU.a1Hi (I := I) (M := M)‖ ≤
          Ca * Real.sqrt
            ((B0 * (1 + R2) * (D2 + D)) ^ 2 +
              (B1 R2 * (1 + A3) *
                (D3 + D2 + A3 * D2 + D)) ^ 2) := hraw.1
      _ = K * D := by
        rw [hq0, hq1, hsqrt]
        simp only [K]
        ring
  · calc
      ‖AT.a1Lo (I := I) (M := M) - AU.a1Lo (I := I) (M := M)‖ ≤
          Ca * Real.sqrt
            ((B0 * (1 + R2) * (D2 + D)) ^ 2 +
              (B1 R2 * (1 + A3) *
                (D3 + D2 + A3 * D2 + D)) ^ 2) := hraw.2
      _ = K * D := by
        rw [hq0, hq1, hsqrt]
        simp only [K]
        ring

set_option maxHeartbeats 800000 in
set_option linter.unusedVariables false in
/-- The radial order-zero refold has a two-jet coefficient bound affine in the
independent `H3` state size on each fixed `H2` ball. -/
theorem c0Coeff_aff
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B0 B1 : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
      let F := c0Data (I := I) (M := M) g T hT
        (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ
      lowJetSq (I := I) (M := M) g 2 F.C0 +
          lowJetSq (I := I) (M := M) g 2 F.C1 ≤
        (B0 R + B1 R * A) ^ 2 := by
  obtain ⟨ρ0, Bz, hρ0, hBz, hzero⟩ :=
    refoldC0_h2 (I := I) (M := M) hDim g
  obtain ⟨ρ1, Bo, hρ1, hBo, hone⟩ :=
    lowOneAInt_h2 (I := I) (M := M) hDim g
  let ρ : ℝ := min ρ0 ρ1
  let B0 : ℝ → ℝ := fun R => Bz R + Bo R
  let B1 : ℝ → ℝ := Bo
  have hρ : 0 < ρ := lt_min hρ0 hρ1
  refine ⟨ρ, B0, B1, hρ,
    fun R hR => add_nonneg (hBz R hR) (hBo R hR), hBo, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hTn
  dsimp only
  have hz := hzero T hT hδ_le hδ0 hδT hδZ R hR hT2
    (hTn.trans (min_le_left _ _))
  have ho := hone T hT hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
    (hTn.trans (min_le_right _ _))
  have hz0 : 0 ≤ Bz R := hBz R hR
  have ho0 : 0 ≤ Bo R * (1 + A) :=
    mul_nonneg (hBo R hR) (add_nonneg (by norm_num) hA)
  have hsum := sqAdd2 hz0 ho0
  calc
    lowJetSq (I := I) (M := M) g 2
          (c0Data (I := I) (M := M) g T hT
            (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ).C0 +
        lowJetSq (I := I) (M := M) g 2
          (c0Data (I := I) (M := M) g T hT
            (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ).C1 ≤
      Bz R ^ 2 + (Bo R * (1 + A)) ^ 2 := by
        simpa only [c0Data, refoldData] using add_le_add hz ho
    _ ≤ (Bz R + Bo R * (1 + A)) ^ 2 := hsum
    _ = (B0 R + B1 R * A) ^ 2 := by
      simp only [B0, B1]
      ring

private theorem refold_a1
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
      (lowBaseData (I := I) (M := M)
        g g T hδ_lt hδ hδZ).a1 (I := I) (M := M) T =
      (refoldData (I := I) (M := M)
        g T hT hδ_lt hδ hδZ).a1 (I := I) (M := M) T := by
  rw [LowBaseActionData.a1, LowBaseActionData.a1]
  rw [LowBaseInternal.c0_eq (I := I) (M := M)
    g g T hδ_lt hδ hδZ]
  rw [LowBaseInternal.c1_eq (I := I) (M := M)
    g g T hδ_lt hδ hδZ]
  simp only [refoldData, appCc_add_left]
  rw [self_aff_int (I := I) (M := M) g T hT hδ_lt hδ hδZ]
  abel

private theorem refold_eq
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    let hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
    let A := refoldData (I := I) (M := M)
      g T hT hδ_lt hδ hδZ
    deTurckSmoothRemainder (I := I) g g T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g g
          (0 : SmoothCcTensor g 0 2) hδ_lt hδZ =
      A.a2 (I := I) (M := M) T + A.a1 (I := I) (M := M) T := by
  obtain ⟨_, _, hsplit⟩ := lowData_split (I := I) (M := M) g g
  have hold := (hsplit T hT hδ_le hδ0 hδ hδZ).1
  dsimp only
  rw [hold]
  rw [refold_a1 (I := I) (M := M) g T hT
    (lt_of_le_of_lt hδ_le (by norm_num)) hδ hδZ]
  rfl

/-- In dimension three, the zero-based same-background remainder admits the
refolded smooth-core action split with a fibre-small second-order coefficient
and one common pair of low-regularity first-order estimates. -/
theorem refold_low_split
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ κ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ 0 ≤ κ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
      let F := refoldData (I := I) (M := M) g T hT
        (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ
      deTurckSmoothRemainder (I := I) g g T
            (lt_of_le_of_lt hδ_le (by norm_num)) hδT -
          deTurckSmoothRemainder (I := I) g g
            (0 : SmoothCcTensor g 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num)) hδZ =
        F.a2 (I := I) (M := M) T + F.a1 (I := I) (M := M) T ∧
      (∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 4 2 x
            (F.C2.toSection x) ≤
          (κ * (δ / (1 - δ) ^ 2)) ^ 2) ∧
      (∀ W : SmoothCcTensor g 0 2,
        lowJetSq (I := I) (M := M) g 2
            (F.a1 (I := I) (M := M) W) ≤
          (B R * (1 + A ^ 2) ^ 3) ^ 2 *
            lowJetSq (I := I) (M := M) g 3 W) ∧
      ∀ W : SmoothCcTensor g 0 2,
        lowJetSq (I := I) (M := M) g 1
            (F.a1 (I := I) (M := M) W) ≤
          (B R * (1 + A ^ 2) ^ 3) ^ 2 *
            lowJetSq (I := I) (M := M) g 2 W := by
  obtain ⟨ρ, B, hρ, hB, hact⟩ :=
    refoldA1_hl (I := I) (M := M) hDim g
  obtain ⟨κ, hκ, hsplit⟩ := lowData_split (I := I) (M := M) g g
  refine ⟨ρ, κ, B, hρ, hκ, hB, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hTn
  dsimp only
  let F := refoldData (I := I) (M := M) g T hT
    (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ
  have heq := refold_eq (I := I) (M := M) g T hT
    hδ_le hδ0 hδT hδZ
  have hsmall := (hsplit T hT hδ_le hδ0 hδT hδZ).2
  have ha := hact T hT hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3 hTn
  refine ⟨?_, ?_, ha.1, ha.2⟩
  · simpa only [F] using heq
  · simpa only [F, refoldData] using hsmall

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
