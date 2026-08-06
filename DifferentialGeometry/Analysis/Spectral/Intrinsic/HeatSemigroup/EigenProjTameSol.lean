import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.EigenProjPartialSol
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.TameForcingFixedPoint

/-!
# The spectrally truncated TAME nonlinearity solves on the same horizon

`EigenProjPartialSol.lean` identifies the Galerkin limit for `partial_sol_const`,
whose nonlinearity is **globally Lipschitz** on the state ball.  At the critical
low regularity that hypothesis is unavailable and provably so: the state set
`lowerState g₀ a R` bounds only the `H^{a+1}` norm, while the third arm of the
Ricci--DeTurck tame estimate carries the ambient `H^{a+2}` norm of its
endpoints.  The campaign's solver is therefore `partial_sol_tame`, and this file
is the tame counterpart of the whole identification layer.

Nothing about the argument changes.  The spectral truncation has norm at most
one, so `Π_N ∘ Nfun` inherits continuity, the static bound and the *three-arm*
estimate with the same constants `A, B, C, D`; the projected system is the same
solve on the same closed-form horizon in the same forcing ball of radius `R/4`;
and subtracting the two fixed-point equations inside the one contraction
`Λ = A·R·(1+T) + B·2√T + 2·C·(R/4)·√(1+T)·(1+T) ≤ 1/2` identifies the projected
forcing with the unprojected one at rate `‖(Π_N - 1) f_*‖`.

## Main results

* `projN_cont`, `projN_tame` — continuity and the three-arm estimate are
  inherited verbatim, with the same constants.
* `proj_partial_sol_tame` — the projected tame forcing fixed point, on the
  identical horizon `T₀`.
* `projN_nemytskiiTame` — truncating before or after the tame Nemytskii
  operator agrees.
* `projFixTame_dist_le`, `projFixTame_le_two` — the fixed-point stability bound
  `‖f_N - f_*‖ ≤ (1 - Λ)⁻¹ ‖Π_N f_* - f_*‖`, and its absolute-constant form.

The limit steps (`projFix_tendsto`, `projField_tendsto`) and the
`V_N`-valuedness lemmas (`projForce_fixed`, `projField_fixed`) of
`EigenProjPartialSol.lean` carry no Lipschitz hypothesis and are reused
unchanged.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
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

/-! ## The truncated nonlinearity keeps every tame slot -/

/-- The truncated nonlinearity is continuous whenever `Nfun` is. -/
theorem projN_cont (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (N : ℕ)
    {Nfun : lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hcont : Continuous Nfun) :
    Continuous (projNfun (I := I) (M := M) g₀ a N Nfun) := by
  have h := (spatialProj_lip (I := I) (M := M) g₀ (a : ℝ) N).continuous.comp hcont
  simpa [projNfun, Function.comp_def] using h

/-- The truncated nonlinearity keeps the three-arm tame estimate of `Nfun`,
with the same constants `A, B, C`. -/
theorem projN_tame (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (N : ℕ)
    {A B C : ℝ≥0}
    {Nfun : lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hsingle : ∀ u u' : lowerState (I := I) (M := M) g₀ a R,
      ‖Nfun u - Nfun u'‖ ≤
        (A : ℝ) * R *
            ‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) - (u' : _)‖ +
          (B : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖ +
          (C : ℝ) *
              (‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ +
                ‖(u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖) :
    ∀ u u' : lowerState (I := I) (M := M) g₀ a R,
      ‖projNfun (I := I) (M := M) g₀ a N Nfun u -
          projNfun (I := I) (M := M) g₀ a N Nfun u'‖ ≤
        (A : ℝ) * R *
            ‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) - (u' : _)‖ +
          (B : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖ +
          (C : ℝ) *
              (‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ +
                ‖(u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖ := by
  intro u u'
  calc ‖projNfun (I := I) (M := M) g₀ a N Nfun u -
        projNfun (I := I) (M := M) g₀ a N Nfun u'‖
      = ‖spatialEigenProj (I := I) (M := M) g₀ (a : ℝ) N (Nfun u - Nfun u')‖ := by
        simp only [projNfun, map_sub]
    _ ≤ ‖Nfun u - Nfun u'‖ :=
        norm_spatialEigenProj_apply_le (I := I) (M := M) g₀ (a : ℝ) N _
    _ ≤ _ := hsingle u u'

/-- **The projected tame forcing fixed point, on the identical horizon.**  The
spectrally truncated nonlinearity `Π_N ∘ Nfun` inherits all the hypotheses of
`partial_sol_tame` with the same constants, so the projected system is solved on
the *same* closed-form horizon `T₀`, in the same forcing ball of radius `R/4`,
with every constant free of the truncation level `N`. -/
theorem proj_partial_sol_tame
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 < R) (N : ℕ)
    (Nfun : lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (hcont : Continuous Nfun)
    (A B C : ℝ≥0) (D : ℝ) (hD : 0 ≤ D)
    (hzero : ‖Nfun ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ a hR.le⟩‖ ≤ D)
    (hsmallA : (A : ℝ) * R ≤ 1 / 16)
    (hsmallC : (C : ℝ) * R ≤ 1 / 16)
    (hsingle : ∀ u u' : lowerState (I := I) (M := M) g₀ a R,
      ‖Nfun u - Nfun u'‖ ≤
        (A : ℝ) * R *
            ‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) - (u' : _)‖ +
          (B : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖ +
          (C : ℝ) *
              (‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ +
                ‖(u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖) :
    ∃ T₀ : ℝ,
      T₀ = min 1 (min (1 / (64 * ((B : ℝ) + 1) ^ 2))
        (((R / 4) / (2 * (D + 1))) ^ 2)) ∧
      0 < T₀ ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTT₀ : T ≤ T₀) (hT1 : T ≤ 1),
      ∃ (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T),
        let field := maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce
        u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce ∧
          (∀ᵐ t ∂(timeMeasure T),
            field t ∈ lowerState (I := I) (M := M) g₀ a R) ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => projNfun (I := I) (M := M) g₀ a N Nfun (aeSetLift
              (zero_mem_lowerState (I := I) (M := M) g₀ a hR.le) field t)) ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) (a : ℝ) field + gforce ∧
          ‖gforce‖ ≤ R / 4 :=
  partial_sol_tame (I := I) (M := M) g₀ a hR
    (projNfun (I := I) (M := M) g₀ a N Nfun)
    (projN_cont (I := I) (M := M) g₀ a N hcont) A B C D hD
    (projN_zero (I := I) (M := M) g₀ a hR.le N hzero) hsmallA hsmallC
    (projN_tame (I := I) (M := M) g₀ a N hsingle)

/-! ## The truncation passes through the tame Nemytskii operator -/

/-- **Truncating before or after the tame Nemytskii operator agrees.**  The
spectral projector acts pointwise in time, so the time-`L²` field of the
truncated nonlinearity is the truncation of the time-`L²` field of `Nfun`. -/
theorem projN_nemytskiiTame (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (N : ℕ) {A B C : ℝ≥0} {T : ℝ}
    {Nfun : lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hcont : Continuous Nfun)
    (hsingle : ∀ u u' : lowerState (I := I) (M := M) g₀ a R,
      ‖Nfun u - Nfun u'‖ ≤
        (A : ℝ) * R *
            ‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) - (u' : _)‖ +
          (B : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖ +
          (C : ℝ) *
              (‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ +
                ‖(u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖)
    (f : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T)
    (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ lowerState (I := I) (M := M) g₀ a R) :
    nemytskiiTame (I := I) (M := M) g₀ a hR
        (projN_cont (I := I) (M := M) g₀ a N hcont)
        (projN_tame (I := I) (M := M) g₀ a N hsingle) f hf =
      timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
        (nemytskiiTame (I := I) (M := M) g₀ a hR hcont hsingle f hf) := by
  refine MeasureTheory.Lp.ext ?_
  have hL := nemytskiiTame_coeFn (I := I) (M := M) g₀ a hR
    (projN_cont (I := I) (M := M) g₀ a N hcont)
    (projN_tame (I := I) (M := M) g₀ a N hsingle) f hf
  have hN := nemytskiiTame_coeFn (I := I) (M := M) g₀ a hR hcont hsingle f hf
  have hP : ⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
        (nemytskiiTame (I := I) (M := M) g₀ a hR hcont hsingle f hf))
      =ᵐ[timeMeasure T] fun t => spatialEigenProj (I := I) (M := M) g₀ (a : ℝ) N
        ((nemytskiiTame (I := I) (M := M) g₀ a hR hcont hsingle f hf) t) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  filter_upwards [hL, hP, hN] with t h1 h2 h3
  rw [h1, h2, h3, projNfun]

/-! ## Fixed-point stability -/

/-- The tame contraction factor of `partial_sol_tame`'s forcing map is at most
`1/2` on the forcing ball of radius `R/4`: its three arms are bounded by `1/8`,
`1/4` and `1/8` respectively, by the top-arm smallness `A·R ≤ 1/16`, the horizon
cap `T ≤ 1/(64(B+1)²)` and the tame-arm smallness `C·R ≤ 1/16`. -/
private lemma lamHalfTame {A B C : ℝ≥0} {R T : ℝ} (hR : 0 ≤ R)
    (hsmallA : (A : ℝ) * R ≤ 1 / 16) (hsmallC : (C : ℝ) * R ≤ 1 / 16)
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1)
    (hTlo : T ≤ 1 / (64 * ((B : ℝ) + 1) ^ 2)) :
    (A : ℝ) * R * (1 + T) + (B : ℝ) * (2 * Real.sqrt T) +
        2 * (C : ℝ) * (R / 4) * Real.sqrt (1 + T) * (1 + T) ≤ 1 / 2 := by
  have h1T : (1 : ℝ) + T ≤ 2 := by linarith
  have hsqrt1T : Real.sqrt (1 + T) ≤ 2 := by
    have hsq : Real.sqrt (1 + T) ≤ 1 + T := by
      calc
        Real.sqrt (1 + T) ≤ Real.sqrt ((1 + T) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1 + T)])
        _ = 1 + T := Real.sqrt_sq (by linarith)
    linarith
  have harm1 : (A : ℝ) * R * (1 + T) ≤ 1 / 8 := by
    have hARnn : 0 ≤ (A : ℝ) * R := mul_nonneg A.coe_nonneg hR
    calc
      (A : ℝ) * R * (1 + T) ≤ (A : ℝ) * R * 2 :=
        mul_le_mul_of_nonneg_left h1T hARnn
      _ ≤ (1 / 16 : ℝ) * 2 := mul_le_mul_of_nonneg_right hsmallA (by positivity)
      _ = 1 / 8 := by norm_num
  have hsqrtT : Real.sqrt T ≤ 1 / (8 * ((B : ℝ) + 1)) := by
    rw [show (1 : ℝ) / (8 * ((B : ℝ) + 1)) =
      Real.sqrt ((1 / (8 * ((B : ℝ) + 1))) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt (le_trans hTlo ?_)
    rw [div_pow, one_pow, mul_pow]
    norm_num
  have harm2 : (B : ℝ) * (2 * Real.sqrt T) ≤ 1 / 4 := by
    calc
      (B : ℝ) * (2 * Real.sqrt T) = 2 * (B : ℝ) * Real.sqrt T := by ring
      _ ≤ 2 * (B : ℝ) * (1 / (8 * ((B : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hsqrtT (by positivity)
      _ = (B : ℝ) / ((B : ℝ) + 1) * (1 / 4) := by
        field_simp
        ring
      _ ≤ 1 / 4 := by
        have hfrac : (B : ℝ) / ((B : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith [B.coe_nonneg]
        nlinarith [hfrac,
          div_nonneg B.coe_nonneg (by positivity : (0 : ℝ) ≤ (B : ℝ) + 1)]
  have harm3 :
      2 * (C : ℝ) * (R / 4) * Real.sqrt (1 + T) * (1 + T) ≤ 1 / 8 := by
    calc
      2 * (C : ℝ) * (R / 4) * Real.sqrt (1 + T) * (1 + T) ≤
          2 * (C : ℝ) * (R / 4) * 2 * 2 := by
        gcongr
      _ = 2 * ((C : ℝ) * R) := by ring
      _ ≤ 2 * (1 / 16 : ℝ) := mul_le_mul_of_nonneg_left hsmallC (by positivity)
      _ = 1 / 8 := by norm_num
  linarith

/-- **Fixed-point stability of the spectral truncation, tame case.**  Let `f_*`
solve the unprojected tame forcing fixed-point equation and `f_N` the projected
one, both in the `R/4` forcing ball on the same horizon.  Subtracting the two
equations and using that the projected map is the same `Λ`-contraction gives

  `‖f_N - f_*‖ ≤ (1 - Λ)⁻¹ ‖Π_N f_* - f_*‖`,
  `Λ = A·R·(1+T) + B·2√T + 2·C·(R/4)·√(1+T)·(1+T)`.

The right-hand side is the truncation defect of the *unprojected* fixed point
alone, so it tends to zero — this is the identification of the Galerkin limit at
critical regularity, in place of a compactness-plus-uniqueness argument. -/
theorem projFixTame_dist_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 < R) (N : ℕ)
    {A B C : ℝ≥0}
    {Nfun : lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hcont : Continuous Nfun)
    (hsingle : ∀ u u' : lowerState (I := I) (M := M) g₀ a R,
      ‖Nfun u - Nfun u'‖ ≤
        (A : ℝ) * R *
            ‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) - (u' : _)‖ +
          (B : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖ +
          (C : ℝ) *
              (‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ +
                ‖(u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖)
    (hsmallA : (A : ℝ) * R ≤ 1 / 16) (hsmallC : (C : ℝ) * R ≤ 1 / 16)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTlo : T ≤ 1 / (64 * ((B : ℝ) + 1) ^ 2))
    (fstar fN : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hsB : ‖fstar‖ ≤ R / 4) (hNB : ‖fN‖ ≤ R / 4)
    (hsE : ⇑fstar =ᵐ[timeMeasure T] fun t =>
      Nfun (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ a hR.le)
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) fstar) t))
    (hNE : ⇑fN =ᵐ[timeMeasure T] fun t =>
      projNfun (I := I) (M := M) g₀ a N Nfun
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ a hR.le)
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) fN) t)) :
    ‖fN - fstar‖ ≤
      (1 - ((A : ℝ) * R * (1 + T) + (B : ℝ) * (2 * Real.sqrt T) +
          2 * (C : ℝ) * (R / 4) * Real.sqrt (1 + T) * (1 + T)))⁻¹ *
        ‖timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N fstar - fstar‖ := by
  have h2R : 2 * (R / 4) ≤ R := by linarith
  have hSs := field_mem_lower (I := I) (M := M) g₀ a hT hT1 h2R fstar hsB
  have hSN := field_mem_lower (I := I) (M := M) g₀ a hT hT1 h2R fN hNB
  -- the unprojected fixed-point equation, as an identity of `L²` fields
  have hstarFix :
      nemytskiiTame (I := I) (M := M) g₀ a hR.le hcont hsingle
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) fstar) hSs =
        fstar :=
    MeasureTheory.Lp.ext
      ((nemytskiiTame_coeFn (I := I) (M := M) g₀ a hR.le hcont hsingle _ hSs).trans
        hsE.symm)
  -- the projected fixed-point equation
  have hNfix :
      nemytskiiTame (I := I) (M := M) g₀ a hR.le
          (projN_cont (I := I) (M := M) g₀ a N hcont)
          (projN_tame (I := I) (M := M) g₀ a N hsingle)
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) fN) hSN =
        fN :=
    MeasureTheory.Lp.ext
      ((nemytskiiTame_coeFn (I := I) (M := M) g₀ a hR.le
        (projN_cont (I := I) (M := M) g₀ a N hcont)
        (projN_tame (I := I) (M := M) g₀ a N hsingle) _ hSN).trans hNE.symm)
  -- the projected map at the unprojected fixed point is `Π_N f_*`
  have hbridge :
      nemytskiiTame (I := I) (M := M) g₀ a hR.le
          (projN_cont (I := I) (M := M) g₀ a N hcont)
          (projN_tame (I := I) (M := M) g₀ a N hsingle)
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) fstar) hSs =
        timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N fstar := by
    rw [projN_nemytskiiTame (I := I) (M := M) g₀ a hR.le N hcont hsingle _ hSs,
      hstarFix]
  have hcontr := tameMap_dist_le (I := I) (M := M) g₀ a hR.le
    (projN_cont (I := I) (M := M) g₀ a N hcont)
    (projN_tame (I := I) (M := M) g₀ a N hsingle) hT hT1 fN fstar hNB hsB hSN hSs
  rw [hNfix, hbridge] at hcontr
  have hΛ := lamHalfTame (A := A) (B := B) (C := C) (R := R) (T := T) hR.le
    hsmallA hsmallC hT.le hT1 hTlo
  have hΛ0 : (0 : ℝ) ≤ (A : ℝ) * R * (1 + T) + (B : ℝ) * (2 * Real.sqrt T) +
      2 * (C : ℝ) * (R / 4) * Real.sqrt (1 + T) * (1 + T) := by
    have hs := Real.sqrt_nonneg T
    have hs1 := Real.sqrt_nonneg (1 + T)
    have h1 : (0 : ℝ) ≤ (A : ℝ) * R * (1 + T) := by
      have hAR : (0 : ℝ) ≤ (A : ℝ) * R := mul_nonneg A.coe_nonneg hR.le
      nlinarith [hT.le]
    have h2 : (0 : ℝ) ≤ (B : ℝ) * (2 * Real.sqrt T) := by positivity
    have h3 : (0 : ℝ) ≤ 2 * (C : ℝ) * (R / 4) * Real.sqrt (1 + T) * (1 + T) := by
      have hCR : (0 : ℝ) ≤ 2 * (C : ℝ) * (R / 4) := by positivity
      have h1T : (0 : ℝ) ≤ 1 + T := by linarith [hT.le]
      exact mul_nonneg (mul_nonneg hCR hs1) h1T
    linarith
  have htri : ‖fN - fstar‖ ≤
      ‖fN - timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N fstar‖ +
        ‖timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N fstar - fstar‖ := by
    calc ‖fN - fstar‖
        = ‖(fN - timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N fstar) +
            (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N fstar - fstar)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
  have hpos : (0 : ℝ) <
      1 - ((A : ℝ) * R * (1 + T) + (B : ℝ) * (2 * Real.sqrt T) +
        2 * (C : ℝ) * (R / 4) * Real.sqrt (1 + T) * (1 + T)) := by linarith
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  nlinarith [htri, hcontr, norm_nonneg (fN - fstar)]

/-- **The tame stability modulus is an absolute constant.**  `partial_sol_tame`'s
own hypotheses force `Λ ≤ 1/2`, so the factor `(1 - Λ)⁻¹` of
`projFixTame_dist_le` is at most `2`, independently of `N`, `T`, `R` and the
nonlinear constants.  Together with `projFix_tendsto` (with `K = 2`) this is the
Galerkin identification at critical regularity. -/
theorem projFixTame_le_two
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 < R) (N : ℕ)
    {A B C : ℝ≥0}
    {Nfun : lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hcont : Continuous Nfun)
    (hsingle : ∀ u u' : lowerState (I := I) (M := M) g₀ a R,
      ‖Nfun u - Nfun u'‖ ≤
        (A : ℝ) * R *
            ‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) - (u' : _)‖ +
          (B : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖ +
          (C : ℝ) *
              (‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ +
                ‖(u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖)
    (hsmallA : (A : ℝ) * R ≤ 1 / 16) (hsmallC : (C : ℝ) * R ≤ 1 / 16)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTlo : T ≤ 1 / (64 * ((B : ℝ) + 1) ^ 2))
    (fstar fN : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hsB : ‖fstar‖ ≤ R / 4) (hNB : ‖fN‖ ≤ R / 4)
    (hsE : ⇑fstar =ᵐ[timeMeasure T] fun t =>
      Nfun (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ a hR.le)
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) fstar) t))
    (hNE : ⇑fN =ᵐ[timeMeasure T] fun t =>
      projNfun (I := I) (M := M) g₀ a N Nfun
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ a hR.le)
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) fN) t)) :
    ‖fN - fstar‖ ≤
      2 * ‖timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N fstar - fstar‖ := by
  refine (projFixTame_dist_le (I := I) (M := M) g₀ a hR N hcont hsingle hsmallA
    hsmallC hT hT1 hTlo fstar fN hsB hNB hsE hNE).trans ?_
  have hΛ := lamHalfTame (A := A) (B := B) (C := C) (R := R) (T := T) hR.le
    hsmallA hsmallC hT.le hT1 hTlo
  have hpos : (0 : ℝ) <
      1 - ((A : ℝ) * R * (1 + T) + (B : ℝ) * (2 * Real.sqrt T) +
        2 * (C : ℝ) * (R / 4) * Real.sqrt (1 + T) * (1 + T)) := by linarith
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [inv_le_comm₀ hpos (by norm_num)]
  linarith

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
