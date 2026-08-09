import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegSmoothBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifNZeroBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.ExponentCongr

/-!
# Fixed-background low affine identity

This module assembles the completed low-order action while keeping the DeTurck
background independent of the frozen spectral metric.  It is the
arbitrary-background replacement for the state identity in `LowRegLiftAffine`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

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

private abbrev metricH1 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev metricH3 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (3 : ℝ)

private noncomputable abbrev incl21Bg (g : SmoothRiemannianMetric I M) :
    metricH2 (I := I) (M := M) g →L[ℝ] metricH1 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
    (by norm_num)

private noncomputable abbrev incl32Bg (g : SmoothRiemannianMetric I M) :
    metricH3 (I := I) (M := M) g →L[ℝ] metricH2 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
    (by norm_num)

private theorem ccHs_eq
    (g : SmoothRiemannianMetric I M) (σ : ℝ) (S : SmoothCcTensor g 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g σ S =
      ccTensorToHs (I := I) (M := M) g 2 σ S :=
  tensorHs.ext (funext fun _ => rfl)

private theorem congr_cc
    (g : SmoothRiemannianMetric I M) {a b : ℝ} (hab : a = b)
    (S : SmoothCcTensor g 0 2) :
    tensorHsCongr (I := I) (M := M) g 0 2 hab
        (smoothCcToTensorHs (I := I) (M := M) g a S) =
      smoothCcToTensorHs (I := I) (M := M) g b S := by
  cases hab
  rfl

private theorem incl_cc
    (g : SmoothRiemannianMetric I M) {τ σ : ℝ} (hτσ : τ ≤ σ)
    (S : SmoothCcTensor g 0 2) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2) hτσ
        (ccTensorToHs (I := I) (M := M) g 2 σ S) =
      ccTensorToHs (I := I) (M := M) g 2 τ S := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorHsInclusion_coeff_apply, ccTensorToHs_coeff, ccTensorToHs_coeff]

private theorem norm_cc
    (g : SmoothRiemannianMetric I M) {a b : ℝ} (hab : a = b)
    (S : SmoothCcTensor g 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g a S‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g b S‖ := by
  cases hab
  rfl

private theorem smoothN_eq
    (g gB : SmoothRiemannianMetric I M) (a : ℕ)
    (T : SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ) :
    deTurckSmoothN (I := I) (M := M) g gB a T hδ_lt hδ =
      smoothCcToTensorHs (I := I) (M := M) g (a : ℝ)
        (deTurckSmoothRemainder (I := I) g gB T hδ_lt hδ) :=
  rfl

private theorem smoothRem_congr
    (g gB : SmoothRiemannianMetric I M)
    {S U : SmoothCcTensor g 0 2} (h : S = U) {δ : ℝ} (hδ_lt : δ < 1)
    (hS : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g S) δ)
    (hU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ) :
    deTurckSmoothRemainder (I := I) g gB S hδ_lt hS =
      deTurckSmoothRemainder (I := I) g gB U hδ_lt hU := by
  subst h
  rfl

/-- The zero-state Ricci--DeTurck forcing at the low scale, with an independent
fixed DeTurck background. -/
noncomputable def lowBaseForceBg
    (g gB : SmoothRiemannianMetric I M) : metricH1 (I := I) (M := M) g :=
  incl21Bg (I := I) (M := M) g
    (baseForceH2 (I := I) (M := M) g gB)

/-- The fixed-background low forcing is the direct spectral embedding of the
zero-state smooth remainder. -/
theorem lowBaseForceBg_core
    (g gB : SmoothRiemannianMetric I M) :
    lowBaseForceBg (I := I) (M := M) g gB =
      ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
        (deTurckSmoothRemainder (I := I) g gB
          (0 : SmoothCcTensor g 0 2) (by norm_num)
          (gFibreOpBound_ccTensorBilinSymm_zero (I := I) (M := M) g)) := by
  apply tensorHs.ext
  funext i
  simp only [lowBaseForceBg, incl21Bg, baseForceH2,
    tensorHsInclusion_coeff_apply, ccTensorToHs_coeff]

/-- The completed low affine forcing with an independent fixed DeTurck
background. -/
noncomputable def lowBaseNBg
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (u : metricH3 (I := I) (M := M) g) :
    metricH1 (I := I) (M := M) g :=
  lowBaseForceBg (I := I) (M := M) g gB +
    lowA2LoBg (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
      (incl32Bg (I := I) (M := M) g u)
      (lowRadialH3 (I := I) (M := M) g ρ u) +
    lowA1LoBg (I := I) (M := M) g gB hρ hδ0 hδ_le hreal u
      (lowRadialHs (I := I) (M := M) g ρ
        (incl32Bg (I := I) (M := M) g u))

/-- The fixed-background completed low affine forcing is continuous whenever
its two operator-valued coefficient maps are continuous. -/
theorem lowBaseNBg_cont
    (g gB : SmoothRiemannianMetric I M) {ρ δ : ℝ} (hρ : 0 < ρ)
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hA2 : Continuous
      (lowA2LoBg (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal))
    (hA1 : Continuous
      (lowA1LoBg (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal)) :
    Continuous
      (lowBaseNBg (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal) := by
  have hincl : Continuous fun u : metricH3 (I := I) (M := M) g =>
      incl32Bg (I := I) (M := M) g u :=
    (incl32Bg (I := I) (M := M) g).continuous
  have h2 : Continuous fun u : metricH3 (I := I) (M := M) g =>
      lowA2LoBg (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal
        (incl32Bg (I := I) (M := M) g u)
        (lowRadialH3 (I := I) (M := M) g ρ u) :=
    isBoundedBilinearMap_apply.continuous.comp
      ((hA2.comp hincl).prodMk (lowRadialH3_cont (I := I) (M := M) g hρ))
  have h1 : Continuous fun u : metricH3 (I := I) (M := M) g =>
      lowA1LoBg (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal u
        (lowRadialHs (I := I) (M := M) g ρ
          (incl32Bg (I := I) (M := M) g u)) :=
    isBoundedBilinearMap_apply.continuous.comp
      (hA1.prodMk
        ((lowRadialHs_cont (I := I) (M := M) g hρ.le).comp hincl))
  exact (continuous_const.add h2).add h1

/-- The completed lower Ricci--DeTurck nonlinearity is the fixed-background
affine action on every state of the lower `H3` ball. -/
theorem lowreg_N_bg_affine
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) {R ρ δ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hRρ : R ≤ ρ)
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hNcont : Continuous
      (lowRegN (I := I) (M := M) g gB hR hδ hreal))
    (hcore : Continuous (coreN (I := I) (M := M) g gB hδ hreal))
    (hA2cont : Continuous
      (lowA2LoBg (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal'))
    (hA2core : ∀ S : SmoothCcTensor g 0 2,
      lowA2LoBg (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal'
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
        (lowCoreDataBg (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal' S).a2Lo (I := I) (M := M))
    (hA1pair : BgA1CorePair (I := I) (M := M)
      g gB hρ.le hδ0 hδ_le hreal')
    (w : lowerState (I := I) (M := M) g 1 R) :
    tensorHsCongr (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
        (lowRegN (I := I) (M := M) g gB hR hδ hreal w) =
      lowBaseNBg (I := I) (M := M)
        g gB hρ.le hδ0 hδ_le hreal'
        (tensorHsCongr (I := I) (M := M) g 0 2
          (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num) w.1) := by
  classical
  have hzeroNorm : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
      (0 : SmoothCcTensor g 0 2)‖ ≤ ρ := by
    rw [show ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2) = 0 by
      simpa only [ccToHsLin_apply] using
        map_zero (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ))]
    simpa only [norm_zero] using hρ.le
  have hΦcont : Continuous fun v : lowerState (I := I) (M := M) g 1 R =>
      tensorHsCongr (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
        (lowRegN (I := I) (M := M) g gB hR hδ hreal v) :=
    (tensorHsCongr (I := I) (M := M) g 0 2
      (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)).continuous.comp hNcont
  have hΨcont : Continuous fun v : lowerState (I := I) (M := M) g 1 R =>
      lowBaseNBg (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal'
        (tensorHsCongr (I := I) (M := M) g 0 2
          (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num) v.1) :=
    (lowBaseNBg_cont (I := I) (M := M) g gB hρ hδ0 hδ_le hreal'
        hA2cont (lowA1LoBg_cont (I := I) (M := M) g gB hA1pair)).comp
      ((tensorHsCongr (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)).continuous.comp
          continuous_subtype_val)
  have hclosed : IsClosed {v : lowerState (I := I) (M := M) g 1 R |
      tensorHsCongr (I := I) (M := M) g 0 2
          (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
          (lowRegN (I := I) (M := M) g gB hR hδ hreal v) =
        lowBaseNBg (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal'
          (tensorHsCongr (I := I) (M := M) g 0 2
            (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num) v.1)} :=
    isClosed_eq hΦcont hΨcont
  have hsub : smoothCore (I := I) (M := M) g R ⊆
      {v : lowerState (I := I) (M := M) g 1 R |
        tensorHsCongr (I := I) (M := M) g 0 2
            (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
            (lowRegN (I := I) (M := M) g gB hR hδ hreal v) =
          lowBaseNBg (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal'
            (tensorHsCongr (I := I) (M := M) g 0 2
              (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num) v.1)} := by
    intro v hv
    obtain ⟨S, hS⟩ := hv
    have hball : ‖tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
        (smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 2) S)‖ ≤ R := by
      rw [hS]
      exact v.2
    have hnorm : ‖smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) S‖ ≤ R := by
      rwa [tensorHsInclusion_smoothCcToTensorHs] at hball
    have hnorm2 : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ R := by
      rw [← ccHs_eq,
        ← norm_cc (I := I) (M := M) g
          (show ((1 : ℕ) : ℝ) + 1 = (2 : ℝ) by norm_num) S]
      exact hnorm
    have hsymm2 : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (symmS (I := I) (M := M) g S)‖ ≤ ρ := by
      refine le_trans ?_ (le_trans hnorm2 hRρ)
      rw [← ccHs_eq, ← ccHs_eq]
      exact norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g (2 : ℝ) S
    have hrad : lowRadial (I := I) (M := M) g ρ S =
        symmS (I := I) (M := M) g S :=
      lowRadial_eq_self (I := I) (M := M) g S hsymm2
    have hveq : v = ⟨smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 2) S, hball⟩ := Subtype.ext hS.symm
    set A := lowCoreDataBg (I := I) (M := M)
      g gB hρ.le hδ0 hδ_le hreal' S with hA
    set S' := lowRadial (I := I) (M := M) g ρ S with hS'
    have hLHS : tensorHsCongr (I := I) (M := M) g 0 2
          (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
          (lowRegN (I := I) (M := M) g gB hR hδ hreal v) =
        ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
          (deTurckSmoothRemainder (I := I) g gB
            (symmS (I := I) (M := M) g S) hδ
            (hreal _ (symm_h2_of_state (I := I) (M := M) g S hball))) := by
      rw [hveq,
        lowRegN_on_smooth (I := I) (M := M) g gB hR hδ hreal hcore S hball,
        smoothN_eq, congr_cc, ccHs_eq]
    have hu : tensorHsCongr (I := I) (M := M) g 0 2
          (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
          (v.1 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2)) =
        ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S := by
      rw [hveq, congr_cc, ccToHsLin_apply, ccHs_eq]
    have hsplit :
        deTurckSmoothRemainder (I := I) g gB S' hδ
              (hreal' _ (lowRadial_norm (I := I) (M := M) g hρ.le S)) -
            deTurckSmoothRemainder (I := I) g gB
              (0 : SmoothCcTensor g 0 2) hδ (hreal' _ hzeroNorm) =
          A.a2 (I := I) (M := M) S' + A.a1 (I := I) (M := M) S' := by
      simpa only [A, S'] using
        lowCoreBg_split (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal' S
    have e1 : incl32Bg (I := I) (M := M) g
          (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
        ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S := by
      rw [ccToHsLin_apply, ccToHsLin_apply]
      exact incl_cc (I := I) (M := M) g _ S
    have e6 : A.a2Lo (I := I) (M := M)
          (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S') =
        ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
          (A.a2 (I := I) (M := M) S') := by
      rw [ccToHsLin_apply]
      exact a2Lo_core (I := I) (M := M) hDim g A S'
    have e7 : A.a1Lo (I := I) (M := M)
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S') =
        ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
          (A.a1 (I := I) (M := M) S') := by
      rw [ccToHsLin_apply]
      exact a1Lo_core_any (I := I) (M := M) hDim g A S'
    have hRHS : lowBaseNBg (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal'
          (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
        ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
          (deTurckSmoothRemainder (I := I) g gB
            (symmS (I := I) (M := M) g S) hδ
            (hreal _ (symm_h2_of_state (I := I) (M := M) g S hball))) := by
      rw [show lowBaseNBg (I := I) (M := M)
            g gB hρ.le hδ0 hδ_le hreal'
            (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
          lowBaseForceBg (I := I) (M := M) g gB +
            lowA2LoBg (I := I) (M := M)
              g gB hρ.le hδ0 hδ_le hreal'
              (incl32Bg (I := I) (M := M) g
                (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S))
              (lowRadialH3 (I := I) (M := M) g ρ
                (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S)) +
            lowA1LoBg (I := I) (M := M)
              g gB hρ.le hδ0 hδ_le hreal'
              (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S)
              (lowRadialHs (I := I) (M := M) g ρ
                (incl32Bg (I := I) (M := M) g
                  (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S))) from rfl,
        e1,
        lowRadialH3_core (I := I) (M := M) g hρ S,
        lowRadialHs_core (I := I) (M := M) g hρ.le S,
        hA2core S, lowA1LoBg_core (I := I) (M := M) g gB hA1pair S,
        ← hA, ← hS', e6, e7,
        lowBaseForceBg_core (I := I) (M := M) g gB,
        ← ccTensorToHs_add, ← ccTensorToHs_add]
      refine congrArg (ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)) ?_
      have hz0 := deTurckRem_zero (I := I) (M := M) g gB
        (show (0 : ℝ) < 1 by norm_num)
        (gFibreOpBound_ccTensorBilinSymm_zero (I := I) (M := M) g)
      have hz1 := deTurckRem_zero (I := I) (M := M) g gB hδ
        (hreal' (0 : SmoothCcTensor g 0 2) hzeroNorm)
      have hrem : deTurckSmoothRemainder (I := I) g gB S' hδ
            (hreal' _ (lowRadial_norm (I := I) (M := M) g hρ.le S)) =
          deTurckSmoothRemainder (I := I) g gB
            (symmS (I := I) (M := M) g S) hδ
            (hreal _ (symm_h2_of_state (I := I) (M := M) g S hball)) :=
        smoothRem_congr (I := I) (M := M) g gB hrad hδ _ _
      rw [← hrem, add_assoc, ← hsplit, hz0, ← hz1]
      abel
    rw [Set.mem_setOf_eq, hLHS, hu, hRHS]
  have hclos : closure (smoothCore (I := I) (M := M) g R) ⊆
      {v : lowerState (I := I) (M := M) g 1 R |
        tensorHsCongr (I := I) (M := M) g 0 2
            (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
            (lowRegN (I := I) (M := M) g gB hR hδ hreal v) =
          lowBaseNBg (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal'
            (tensorHsCongr (I := I) (M := M) g 0 2
              (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num) v.1)} :=
    hclosed.closure_subset_iff.mpr hsub
  have hw : w ∈ closure (smoothCore (I := I) (M := M) g R) := by
    rw [(smoothCore_dense (I := I) (M := M) g hR).closure_eq]
    trivial
  exact hclos hw

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
