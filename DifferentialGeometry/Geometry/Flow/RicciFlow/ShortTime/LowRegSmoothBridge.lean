import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegDenseSolve

/-!
# Low-regularity smooth forcing bridge

The dense lower-regularity nonlinearity agrees with the genuine smooth
Ricci--DeTurck nonlinearity on its smooth core.  Consequently, whenever a
smooth representative family is pinned to the maximal-regularity solution on
the original time interval, the forcing identity transfers on that same
interval; no post-solution time shrink is used here.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- Symmetrizing a smooth `H3` state representative preserves its lower
`H2` state-ball bound. -/
theorem symm_h2_of_state
    (g₀ : SmoothRiemannianMetric I M) {R : ℝ}
    (S : SmoothCcTensor g₀ 0 2)
    (hS : ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
      (smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 2) S)‖ ≤ R) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀
      (((1 : ℕ) : ℝ) + 1)
      (symmS (I := I) (M := M) g₀ S)‖ ≤ R := by
  calc
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1)
        (symmS (I := I) (M := M) g₀ S)‖ ≤
        ‖smoothCcToTensorHs (I := I) (M := M) g₀
          (((1 : ℕ) : ℝ) + 1) S‖ :=
      norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) S
    _ = ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
        (smoothCcToTensorHs (I := I) (M := M) g₀
          (((1 : ℕ) : ℝ) + 2) S)‖ := by
      rw [tensorHsInclusion_smoothCcToTensorHs]
    _ ≤ R := hS

/-- A continuous genuine core nonlinearity is recovered exactly by its dense
extension at every point of the smooth core.  `lowreg_partial_sol` exports the
required core continuity for its concrete `Nfun`. -/
theorem lowRegN_on_core
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal))
    (x : smoothCore (I := I) (M := M) g₀ R) :
    lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal x.1 =
      coreN (I := I) (M := M) g₀ g_bg hδ hreal x := by
  simpa only [lowRegN] using
    (smoothCore_dense (I := I) (M := M) g₀ hR).extend_eq hcore x

/-- On a directly supplied smooth state representative, `lowRegN` is the
order-one spectral embedding of the genuine smooth Ricci--DeTurck remainder. -/
theorem lowRegN_on_smooth
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ P : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) P‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal))
    (S : SmoothCcTensor g₀ 0 2)
    (hS : ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
      (smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 2) S)‖ ≤ R) :
    lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal
        ⟨smoothCcToTensorHs (I := I) (M := M) g₀
          (((1 : ℕ) : ℝ) + 2) S, hS⟩ =
      deTurckSmoothN (I := I) (M := M) g₀ g_bg 1
        (symmS (I := I) (M := M) g₀ S) hδ
        (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ S hS)) := by
  let u : lowerState (I := I) (M := M) g₀ 1 R :=
    ⟨smoothCcToTensorHs (I := I) (M := M) g₀
      (((1 : ℕ) : ℝ) + 2) S, hS⟩
  let x : smoothCore (I := I) (M := M) g₀ R := ⟨u, ⟨S, rfl⟩⟩
  have hrep : coreRep g₀ x = S := by
    apply smoothHs_inj (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
    rw [coreRep_spec]
  have hx := lowRegN_on_core (I := I) (M := M) g₀ g_bg hR hδ hreal hcore x
  have hN :
      coreN (I := I) (M := M) g₀ g_bg hδ hreal x =
        deTurckSmoothN (I := I) (M := M) g₀ g_bg 1
          (symmS (I := I) (M := M) g₀ S) hδ
          (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ S hS)) := by
    unfold coreN
    apply smoothN_wd (I := I) (M := M) g₀ g_bg 1
    rw [hrep]
  simpa only [u, x] using hx.trans hN

/-- **The static seed mass of the low-regularity Ricci--DeTurck forcing.**

`𝒩(0)` — the value of the dense-extension nonlinearity `lowRegN` at the zero
state — is, by `lowRegN_on_smooth` at the zero smooth representative, the
order-one spectral embedding of the genuine smooth remainder
`deTurckSmoothRemainder g₀ g_bg (symmS g₀ 0)`.  Hence every FINITE
`(1 + λᵢ)^n`-weighted mode mass of `𝒩(0)` is bounded by a constant squared that
depends only on the data `(g₀, g_bg, δ)` — in particular not on the mode set,
so not on a Galerkin level `N`.  This is the shape the rung Grönwall consumes
for its additive seed term.

It is the `a = 1` analogue of `deTurckGalerkinForcing_seed_mass`, whose
`2·finrank + 10 ≤ a` supercriticality gate blocks direct reuse at the low base;
here the identification of `𝒩(0)` with a smooth remainder comes from the dense
extension instead, so no gate is needed.  The finite-mass step is the existing
finite-set Bessel truncation `cc_partial_le_norm`; no new spectral input is
used. -/
theorem lowRegSeedMass
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ P : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) P‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal)) :
    ∃ Cseed : ℕ → ℝ, (∀ n, 0 ≤ Cseed n) ∧
      ∀ (n : ℕ) (F : Finset
          (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2)),
        ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            ((lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal
              ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩).coeff i) ^ 2 ≤
          Cseed n ^ 2 := by
  classical
  have hzero_embed :
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) =
        smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
          (0 : SmoothCcTensor g₀ 0 2) := by
    refine tensorHs.ext ?_
    funext i
    rw [tensorHs.zero_coeff, smoothCcToTensorHs_coeff,
      show SmoothCcTensor.toL2 (0 : SmoothCcTensor g₀ 0 2) = 0 from map_zero _,
      tensorL2Coeff_eq_inner, inner_zero_right]
  have hS : ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
      (smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
        (0 : SmoothCcTensor g₀ 0 2))‖ ≤ R := by
    rw [← hzero_embed]
    simpa only [map_zero, norm_zero] using hR.le
  have hsub : (⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩ :
        lowerState (I := I) (M := M) g₀ 1 R) =
      ⟨smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
        (0 : SmoothCcTensor g₀ 0 2), hS⟩ := Subtype.ext hzero_embed
  have hN := lowRegN_on_smooth (I := I) (M := M) g₀ g_bg hR hδ hreal hcore
    (0 : SmoothCcTensor g₀ 0 2) hS
  refine ⟨fun n => ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ)
      (deTurckSmoothRemainder (I := I) g₀ g_bg
        (symmS (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2)) hδ
        (hreal _ (symm_h2_of_state (I := I) (M := M) g₀
          (0 : SmoothCcTensor g₀ 0 2) hS)))‖,
    fun n => norm_nonneg _, ?_⟩
  intro n F
  have hcoeff : ∀ i, (lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩).coeff i =
      (ccTensorToHs (I := I) (M := M) g₀ 2 (n : ℝ)
        (deTurckSmoothRemainder (I := I) g₀ g_bg
          (symmS (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2)) hδ
          (hreal _ (symm_h2_of_state (I := I) (M := M) g₀
            (0 : SmoothCcTensor g₀ 0 2) hS)))).coeff i := by
    intro i
    rw [hsub, hN, deTurckSmoothN_coeff, ccTensorToHs_coeff]
  have hbridge : ccTensorToHs (I := I) (M := M) g₀ 2 (n : ℝ)
        (deTurckSmoothRemainder (I := I) g₀ g_bg
          (symmS (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2)) hδ
          (hreal _ (symm_h2_of_state (I := I) (M := M) g₀
            (0 : SmoothCcTensor g₀ 0 2) hS))) =
      smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ)
        (deTurckSmoothRemainder (I := I) g₀ g_bg
          (symmS (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2)) hδ
          (hreal _ (symm_h2_of_state (I := I) (M := M) g₀
            (0 : SmoothCcTensor g₀ 0 2) hS))) :=
    tensorHs.ext (funext (fun _ => rfl))
  calc ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
        ((lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal
          ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩).coeff i) ^ 2
      = ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
          ((ccTensorToHs (I := I) (M := M) g₀ 2 (n : ℝ)
            (deTurckSmoothRemainder (I := I) g₀ g_bg
              (symmS (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2)) hδ
              (hreal _ (symm_h2_of_state (I := I) (M := M) g₀
                (0 : SmoothCcTensor g₀ 0 2) hS)))).coeff i) ^ 2 :=
        Finset.sum_congr rfl (fun i _ => by rw [hcoeff i])
    _ ≤ ‖ccTensorToHs (I := I) (M := M) g₀ 2 (n : ℝ)
          (deTurckSmoothRemainder (I := I) g₀ g_bg
            (symmS (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2)) hδ
            (hreal _ (symm_h2_of_state (I := I) (M := M) g₀
              (0 : SmoothCcTensor g₀ 0 2) hS)))‖ ^ 2 :=
        cc_partial_le_norm (I := I) (M := M) g₀ 2 (n : ℝ) _ F
    _ = ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ)
          (deTurckSmoothRemainder (I := I) g₀ g_bg
            (symmS (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2)) hδ
            (hreal _ (symm_h2_of_state (I := I) (M := M) g₀
              (0 : SmoothCcTensor g₀ 0 2) hS)))‖ ^ 2 := by rw [hbridge]

/-- If a smooth representative family is pinned to the lower-regularity
maximal-regularity field, its forcing is the genuine smooth Ricci--DeTurck
forcing almost everywhere on the original time interval `T`. -/
theorem lowReg_force_smooth
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ T : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ P : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) P‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal))
    (field : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2
      (((1 : ℕ) : ℝ) + 2)) T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2
      ((1 : ℕ) : ℝ)) T)
    (hstate : ∀ᵐ t ∂(timeMeasure T),
      field t ∈ lowerState (I := I) (M := M) g₀ 1 R)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le) field t)))
    (F : ℝ → SmoothCcTensor g₀ 0 2)
    (hpin : ∀ᵐ t ∂(timeMeasure T),
      smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 2) (F t) = field t)
    (hball : ∀ t : ℝ,
      ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
        (smoothCcToTensorHs (I := I) (M := M) g₀
          (((1 : ℕ) : ℝ) + 2) (F t))‖ ≤ R) :
    gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSmoothN (I := I) (M := M) g₀ g_bg 1
        (symmS (I := I) (M := M) g₀ (F t)) hδ
        (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ (F t) (hball t)))) := by
  filter_upwards [hforce, hstate, hpin] with t htforce htstate htpin
  let uF : lowerState (I := I) (M := M) g₀ 1 R :=
    ⟨smoothCcToTensorHs (I := I) (M := M) g₀
      (((1 : ℕ) : ℝ) + 2) (F t), hball t⟩
  have hlift : aeSetLift
      (zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le) field t = uF := by
    apply Subtype.ext
    simp only [aeSetLift, dif_pos htstate, uF]
    exact htpin.symm
  rw [htforce, hlift]
  simpa only [uF] using
    lowRegN_on_smooth (I := I) (M := M) g₀ g_bg hR hδ hreal hcore (F t) (hball t)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
