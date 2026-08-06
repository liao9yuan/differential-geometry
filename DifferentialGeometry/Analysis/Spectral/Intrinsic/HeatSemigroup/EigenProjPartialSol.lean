import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.EigenProjDuhamel
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PartialForcingFixedPoint

/-!
# The spectrally truncated nonlinearity solves on the same horizon

`partial_sol_const` solves `∂_t u = Δ_∇ u + N(u)`, `u(0) = 0`, for a
nonlinearity `Nfun` defined only on the lower-order state ball, from four
quantitative slots: a Lipschitz bound `hLip`, the two-arm difference bound
`hsingle` with constants `C₁, C₂`, the static bound `hzero` with constant `D`,
and the state-radius smallness `hsmall`.  Its horizon is the closed formula
`T₀ = min 1 (min (1/(64(C₂+1)²)) ((R/4)/(2(D+1)))²)`.

Since the spectral truncation has norm at most one, `Π_N ∘ Nfun` satisfies the
same four slots with the *same* constants `L, C₁, C₂, D`.  The projected
(Galerkin) system is therefore not a new solve: it is the same solve with the
same closed-form horizon and the same forcing radius `R/4`, and every constant
is independent of the truncation level `N`.

Both systems are fixed points of maps that differ only by `Π_N`, inside one
contraction with one modulus `Λ = C₁R(1+T) + C₂·2√T ≤ 1/2`.  Subtracting the
two fixed-point equations therefore identifies the projected forcing with the
unprojected one at rate `‖(Π_N - 1) f_*‖`, which tends to zero.  No
compactness, no weak-* extraction and no uniqueness theorem is involved.

## Main results

* `projNfun` — the truncated nonlinearity `u ↦ Π_N (Nfun u)`.
* `projN_lip`, `projN_zero`, `projN_single` — the three quantitative slots are
  inherited verbatim.
* `proj_partial_sol` — the projected forcing fixed point, on the identical
  horizon `T₀`.
* `projN_nemytskii` — truncating before or after the Nemytskii operator agrees.
* `forceMap_dist_le` — the contraction estimate `partial_sol_const` runs
  internally but does not export.
* `projFix_dist_le`, `projFix_le_two` — the fixed-point stability bound
  `‖f_N - f_*‖ ≤ (1 - Λ)⁻¹ ‖Π_N f_* - f_*‖`, and its absolute-constant form.
* `projFix_tendsto`, `projField_tendsto` — the projected forcing converges to
  the unprojected one, and so does its Duhamel field.
* `projForce_fixed`, `projField_fixed` — a truncated forcing and its Duhamel
  field are `V_N`-valued.
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

/-- **The spectrally truncated nonlinearity** `Π_N ∘ Nfun`, on the same
lower-order state ball as `Nfun`. -/
def projNfun (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (N : ℕ)
    (Nfun : lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) :
    lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
  fun u => spatialEigenProj (I := I) (M := M) g₀ (a : ℝ) N (Nfun u)

/-- The truncated nonlinearity keeps the Lipschitz constant of `Nfun`. -/
theorem projN_lip (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (N : ℕ)
    {L : ℝ≥0}
    {Nfun : lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun) :
    LipschitzWith L (projNfun (I := I) (M := M) g₀ a N Nfun) := by
  have h := (spatialProj_lip (I := I) (M := M) g₀ (a : ℝ) N).comp hLip
  simpa [projNfun, Function.comp_def] using h

/-- The truncated nonlinearity keeps the static bound of `Nfun`. -/
theorem projN_zero (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R D : ℝ}
    (hR : 0 ≤ R) (N : ℕ)
    {Nfun : lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hzero : ‖Nfun ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ a hR⟩‖ ≤ D) :
    ‖projNfun (I := I) (M := M) g₀ a N Nfun
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ a hR⟩‖ ≤ D :=
  le_trans (norm_spatialEigenProj_apply_le (I := I) (M := M) g₀ (a : ℝ) N _)
    hzero

/-- The truncated nonlinearity keeps the two-arm difference bound of `Nfun`,
with the same constants `C₁, C₂`. -/
theorem projN_single (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (N : ℕ)
    {C₁ C₂ : ℝ≥0}
    {Nfun : lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hsingle : ∀ u u' : lowerState (I := I) (M := M) g₀ a R,
      ‖Nfun u - Nfun u'‖ ≤
        (C₁ : ℝ) *
            max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u : _)‖
                ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u' : _)‖ *
              ‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) - (u' : _)‖ +
          (C₂ : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖) :
    ∀ u u' : lowerState (I := I) (M := M) g₀ a R,
      ‖projNfun (I := I) (M := M) g₀ a N Nfun u -
          projNfun (I := I) (M := M) g₀ a N Nfun u'‖ ≤
        (C₁ : ℝ) *
            max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u : _)‖
                ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u' : _)‖ *
              ‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) - (u' : _)‖ +
          (C₂ : ℝ) *
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

/-- **The projected forcing fixed point, on the identical horizon.**  The
spectrally truncated nonlinearity `Π_N ∘ Nfun` inherits all four hypotheses of
`partial_sol_const` with the same constants, so the projected system is solved
on the *same* closed-form horizon `T₀`, in the same forcing ball of radius
`R/4`, with every constant free of the truncation level `N`. -/
theorem proj_partial_sol
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 < R) (N : ℕ)
    {L : ℝ≥0}
    (Nfun : lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (hLip : LipschitzWith L Nfun)
    (C₁ C₂ : ℝ≥0) (D : ℝ) (hD : 0 ≤ D)
    (hzero : ‖Nfun ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ a hR.le⟩‖ ≤ D)
    (hsmall : (C₁ : ℝ) * R ≤ 1 / 8)
    (hsingle : ∀ u u' : lowerState (I := I) (M := M) g₀ a R,
      ‖Nfun u - Nfun u'‖ ≤
        (C₁ : ℝ) *
            max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u : _)‖
                ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u' : _)‖ *
              ‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) - (u' : _)‖ +
          (C₂ : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖) :
    ∃ T₀ : ℝ,
      T₀ = min 1 (min (1 / (64 * ((C₂ : ℝ) + 1) ^ 2))
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
  partial_sol_const (I := I) (M := M) g₀ a hR
    (projNfun (I := I) (M := M) g₀ a N Nfun)
    (projN_lip (I := I) (M := M) g₀ a N hLip) C₁ C₂ D hD
    (projN_zero (I := I) (M := M) g₀ a hR.le N hzero) hsmall
    (projN_single (I := I) (M := M) g₀ a N hsingle)

/-! ## The truncation passes through the Nemytskii operator -/

/-- **Truncating before or after the Nemytskii operator agrees.**  The spectral
projector acts pointwise in time, so the time-`L²` field of the truncated
nonlinearity is the truncation of the time-`L²` field of `Nfun`. -/
theorem projN_nemytskii (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (N : ℕ) {L : ℝ≥0} {T : ℝ}
    {Nfun : lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun)
    (f : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T)
    (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ lowerState (I := I) (M := M) g₀ a R) :
    nemytskiiOn (zero_mem_lowerState (I := I) (M := M) g₀ a hR)
        (projN_lip (I := I) (M := M) g₀ a N hLip) f hf =
      timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
        (nemytskiiOn (zero_mem_lowerState (I := I) (M := M) g₀ a hR) hLip f hf) := by
  refine MeasureTheory.Lp.ext ?_
  have hL := nemytskiiOn_coeFn (zero_mem_lowerState (I := I) (M := M) g₀ a hR)
    (projN_lip (I := I) (M := M) g₀ a N hLip) f hf
  have hN := nemytskiiOn_coeFn (zero_mem_lowerState (I := I) (M := M) g₀ a hR)
    hLip f hf
  have hP : ⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
        (nemytskiiOn (zero_mem_lowerState (I := I) (M := M) g₀ a hR) hLip f hf))
      =ᵐ[timeMeasure T] fun t => spatialEigenProj (I := I) (M := M) g₀ (a : ℝ) N
        ((nemytskiiOn (zero_mem_lowerState (I := I) (M := M) g₀ a hR)
          hLip f hf) t) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  filter_upwards [hL, hP, hN] with t h1 h2 h3
  rw [h1, h2, h3, projNfun]

/-! ## The contraction `partial_sol_const` does not export -/

/-- The contraction factor of `partial_sol_const`'s forcing map is at most
`1/2`: its two arms are bounded by `1/4` each, by the state smallness
`C₁R ≤ 1/8` and by the horizon cap `T ≤ 1/(64(C₂+1)²)` respectively. -/
private lemma lamHalf {C₁ C₂ : ℝ≥0} {R T : ℝ} (hR : 0 ≤ R)
    (hsmall : (C₁ : ℝ) * R ≤ 1 / 8) (hT1 : T ≤ 1)
    (hTlo : T ≤ 1 / (64 * ((C₂ : ℝ) + 1) ^ 2)) :
    (C₁ : ℝ) * R * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T) ≤ 1 / 2 := by
  have harm1 : (C₁ : ℝ) * R * (1 + T) ≤ 1 / 4 := by
    have hCRnn : 0 ≤ (C₁ : ℝ) * R := mul_nonneg C₁.coe_nonneg hR
    calc
      (C₁ : ℝ) * R * (1 + T) ≤ (C₁ : ℝ) * R * 2 :=
        mul_le_mul_of_nonneg_left (by linarith) hCRnn
      _ ≤ (1 / 8 : ℝ) * 2 := mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = 1 / 4 := by norm_num
  have hsqrtT : Real.sqrt T ≤ 1 / (8 * ((C₂ : ℝ) + 1)) := by
    rw [show (1 : ℝ) / (8 * ((C₂ : ℝ) + 1)) =
      Real.sqrt ((1 / (8 * ((C₂ : ℝ) + 1))) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt (le_trans hTlo ?_)
    rw [div_pow, one_pow, mul_pow]
    norm_num
  have harm2 : (C₂ : ℝ) * (2 * Real.sqrt T) ≤ 1 / 4 := by
    calc
      (C₂ : ℝ) * (2 * Real.sqrt T) = 2 * (C₂ : ℝ) * Real.sqrt T := by ring
      _ ≤ 2 * (C₂ : ℝ) * (1 / (8 * ((C₂ : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hsqrtT (by positivity)
      _ = (C₂ : ℝ) / ((C₂ : ℝ) + 1) * (1 / 4) := by field_simp; ring
      _ ≤ 1 / 4 := by
        have hfrac : (C₂ : ℝ) / ((C₂ : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith [C₂.coe_nonneg]
        nlinarith [hfrac,
          div_nonneg C₂.coe_nonneg (by positivity : (0 : ℝ) ≤ (C₂ : ℝ) + 1)]
  linarith

/-- **The forcing map is a `Λ`-contraction on the state ball**, with
`Λ = C₁R(1+T) + C₂·2√T`.  This is the estimate `partial_sol_const` runs
internally on its retracted map; the factor is a local `set` there and is not
exported, so it is restated here in the unretracted form the two fixed points
need — both of them lie in the ball where the retraction is the identity. -/
theorem forceMap_dist_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {L C₁ C₂ : ℝ≥0}
    {Nfun : lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun)
    (hsingle : ∀ u u' : lowerState (I := I) (M := M) g₀ a R,
      ‖Nfun u - Nfun u'‖ ≤
        (C₁ : ℝ) *
            max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u : _)‖
                ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u' : _)‖ *
              ‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) - (u' : _)‖ +
          (C₂ : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (F F' : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hF : ∀ᵐ t ∂(timeMeasure T),
      maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F t ∈
        lowerState (I := I) (M := M) g₀ a R)
    (hF' : ∀ᵐ t ∂(timeMeasure T),
      maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F' t ∈
        lowerState (I := I) (M := M) g₀ a R) :
    ‖nemytskiiOn (zero_mem_lowerState (I := I) (M := M) g₀ a hR) hLip
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F) hF -
        nemytskiiOn (zero_mem_lowerState (I := I) (M := M) g₀ a hR) hLip
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F') hF'‖ ≤
      ((C₁ : ℝ) * R * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)) * ‖F - F'‖ := by
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  have hfield_dist :
      ‖maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F -
          maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F'‖ ≤
        (1 + T) * ‖F - F'‖ :=
    maxRegDuhamelSolField_dist_le (I := I) (M := M) (h_compact := h_compact)
      (a := (a : ℝ)) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F F'
  have hincl_dist :
      ‖timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F -
            maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F')‖ ≤
        2 * Real.sqrt T * ‖F - F'‖ := by
    rw [map_sub,
      timeL2Inclusion_maxRegDuhamelSolField (I := I) (M := M) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F,
      timeL2Inclusion_maxRegDuhamelSolField (I := I) (M := M) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F']
    exact maxRegDuhamelSolFieldHa1_dist_le (I := I) (M := M)
      (h_compact := h_compact) (a := (a : ℝ)) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F F'
  calc
    ‖nemytskiiOn (zero_mem_lowerState (I := I) (M := M) g₀ a hR) hLip
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F) hF -
        nemytskiiOn (zero_mem_lowerState (I := I) (M := M) g₀ a hR) hLip
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F') hF'‖ ≤
        (C₁ : ℝ) * R *
            ‖maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
                (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F -
              maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
                (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F'‖ +
          (C₂ : ℝ) *
            ‖timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)
              (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
                  (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F -
                maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
                  (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F')‖ :=
      nemytskiiOn_mixed (I := I) (M := M) g₀ a hR hLip hsingle _ _ hF hF'
    _ ≤ (C₁ : ℝ) * R * ((1 + T) * ‖F - F'‖) +
          (C₂ : ℝ) * (2 * Real.sqrt T * ‖F - F'‖) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hfield_dist
            (mul_nonneg C₁.coe_nonneg hR))
          (mul_le_mul_of_nonneg_left hincl_dist C₂.coe_nonneg)
    _ = ((C₁ : ℝ) * R * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)) * ‖F - F'‖ := by
        ring

/-! ## Fixed-point stability -/

/-- **Fixed-point stability of the spectral truncation.**  Let `f_*` solve the
unprojected forcing fixed-point equation and `f_N` the projected one, both in
the `R/4` forcing ball on the same horizon.  Subtracting the two equations and
using that the projected map is the same `Λ`-contraction gives

  `‖f_N - f_*‖ ≤ (1 - Λ)⁻¹ ‖Π_N f_* - f_*‖`,   `Λ = C₁R(1+T) + C₂·2√T`.

The right-hand side is the truncation defect of the *unprojected* fixed point
alone, so it tends to zero — this is the identification of the Galerkin limit,
in place of a compactness-plus-uniqueness argument. -/
theorem projFix_dist_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 < R) (N : ℕ)
    {L C₁ C₂ : ℝ≥0}
    {Nfun : lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun)
    (hsingle : ∀ u u' : lowerState (I := I) (M := M) g₀ a R,
      ‖Nfun u - Nfun u'‖ ≤
        (C₁ : ℝ) *
            max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u : _)‖
                ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u' : _)‖ *
              ‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) - (u' : _)‖ +
          (C₂ : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖)
    (hsmall : (C₁ : ℝ) * R ≤ 1 / 8)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTlo : T ≤ 1 / (64 * ((C₂ : ℝ) + 1) ^ 2))
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
      (1 - ((C₁ : ℝ) * R * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)))⁻¹ *
        ‖timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N fstar - fstar‖ := by
  have h2R : 2 * (R / 4) ≤ R := by linarith
  have hSs := field_mem_lower (I := I) (M := M) g₀ a hT hT1 h2R fstar hsB
  have hSN := field_mem_lower (I := I) (M := M) g₀ a hT hT1 h2R fN hNB
  -- the unprojected fixed-point equation, as an identity of `L²` fields
  have hstarFix :
      nemytskiiOn (zero_mem_lowerState (I := I) (M := M) g₀ a hR.le) hLip
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) fstar) hSs =
        fstar :=
    MeasureTheory.Lp.ext
      ((nemytskiiOn_coeFn (zero_mem_lowerState (I := I) (M := M) g₀ a hR.le)
        hLip _ hSs).trans hsE.symm)
  -- the projected fixed-point equation
  have hNfix :
      nemytskiiOn (zero_mem_lowerState (I := I) (M := M) g₀ a hR.le)
          (projN_lip (I := I) (M := M) g₀ a N hLip)
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) fN) hSN =
        fN :=
    MeasureTheory.Lp.ext
      ((nemytskiiOn_coeFn (zero_mem_lowerState (I := I) (M := M) g₀ a hR.le)
        (projN_lip (I := I) (M := M) g₀ a N hLip) _ hSN).trans hNE.symm)
  -- the projected map at the unprojected fixed point is `Π_N f_*`
  have hbridge :
      nemytskiiOn (zero_mem_lowerState (I := I) (M := M) g₀ a hR.le)
          (projN_lip (I := I) (M := M) g₀ a N hLip)
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) fstar) hSs =
        timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N fstar := by
    rw [projN_nemytskii (I := I) (M := M) g₀ a hR.le N hLip _ hSs, hstarFix]
  have hcontr := forceMap_dist_le (I := I) (M := M) g₀ a hR.le
    (projN_lip (I := I) (M := M) g₀ a N hLip)
    (projN_single (I := I) (M := M) g₀ a N hsingle) hT hT1 fN fstar hSN hSs
  rw [hNfix, hbridge] at hcontr
  have hΛ := lamHalf (C₁ := C₁) (C₂ := C₂) (R := R) (T := T) hR.le hsmall hT1 hTlo
  have hΛ0 : (0 : ℝ) ≤ (C₁ : ℝ) * R * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T) := by
    have := Real.sqrt_nonneg T
    have h1 : (0 : ℝ) ≤ (C₁ : ℝ) * R * (1 + T) := by
      have : (0 : ℝ) ≤ (C₁ : ℝ) * R := mul_nonneg C₁.coe_nonneg hR.le
      nlinarith [hT.le]
    have h2 : (0 : ℝ) ≤ (C₂ : ℝ) * (2 * Real.sqrt T) := by positivity
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
      1 - ((C₁ : ℝ) * R * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)) := by linarith
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  nlinarith [htri, hcontr, norm_nonneg (fN - fstar)]

/-- **The stability modulus is an absolute constant.**  `partial_sol_const`'s
own hypotheses force `Λ ≤ 1/2`, so the factor `(1 - Λ)⁻¹` of `projFix_dist_le`
is at most `2`, independently of `N`, `T`, `R` and the nonlinear constants. -/
theorem projFix_le_two
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 < R) (N : ℕ)
    {L C₁ C₂ : ℝ≥0}
    {Nfun : lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun)
    (hsingle : ∀ u u' : lowerState (I := I) (M := M) g₀ a R,
      ‖Nfun u - Nfun u'‖ ≤
        (C₁ : ℝ) *
            max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u : _)‖
                ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u' : _)‖ *
              ‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) - (u' : _)‖ +
          (C₂ : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((u : _) - (u' : _))‖)
    (hsmall : (C₁ : ℝ) * R ≤ 1 / 8)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTlo : T ≤ 1 / (64 * ((C₂ : ℝ) + 1) ^ 2))
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
  refine (projFix_dist_le (I := I) (M := M) g₀ a hR N hLip hsingle hsmall hT hT1
    hTlo fstar fN hsB hNB hsE hNE).trans ?_
  have hΛ := lamHalf (C₁ := C₁) (C₂ := C₂) (R := R) (T := T) hR.le hsmall hT1 hTlo
  have hpos : (0 : ℝ) <
      1 - ((C₁ : ℝ) * R * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)) := by linarith
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [inv_le_comm₀ hpos (by norm_num)]
  linarith

/-- **The projected forcings converge.**  Any sequence whose distance to a
limit point is controlled by the truncation defect of that limit converges to
it, since `timeL2EigenProj_tendsto` sends the defect to zero.  Combined with
`projFix_le_two` (with `K = 2`) this is the Galerkin identification. -/
theorem projFix_tendsto (g₀ : SmoothRiemannianMetric I M) {σ T K : ℝ}
    (fstar : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 σ) T)
    (f : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 σ) T)
    (hK : ∀ N, ‖f N - fstar‖ ≤
      K * ‖timeL2EigenProj (I := I) (M := M) g₀ σ T N fstar - fstar‖) :
    Tendsto f atTop (𝓝 fstar) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun N => norm_nonneg _) hK ?_
  have h0 : Tendsto
      (fun N => ‖timeL2EigenProj (I := I) (M := M) g₀ σ T N fstar - fstar‖)
      atTop (𝓝 0) := by
    rw [← tendsto_iff_norm_sub_tendsto_zero]
    exact timeL2EigenProj_tendsto (I := I) (M := M) g₀ σ T fstar
  simpa using h0.const_mul K

omit [BoundarylessManifold I M] in
/-- **The Duhamel fields converge.**  The zero-seed Duhamel field is
`(1+T)`-Lipschitz in the forcing, so convergence of the projected forcings
transports to convergence of the projected trajectories in the solve's own
norm `L²([0,T]; H^{a+2})`. -/
theorem projField_tendsto (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (fstar : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hf : Tendsto f atTop (𝓝 fstar)) :
    Tendsto (fun N => maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (f N)) atTop
      (𝓝 (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) fstar)) := by
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  rw [tendsto_iff_norm_sub_tendsto_zero] at hf ⊢
  refine squeeze_zero (fun N => norm_nonneg _) (fun N =>
    maxRegDuhamelSolField_dist_le (I := I) (M := M) (h_compact := h_compact)
      (a := (a : ℝ)) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) (f N) fstar) ?_
  simpa using hf.const_mul (1 + T)

/-! ## The projected trajectory is `V_N`-valued -/

/-- **A truncated forcing is fixed by the truncation.**  Any time-`L²` field
which is almost everywhere a value of `projNfun` is its own truncation, by
idempotence of `Π_N`.  This is the trajectory-side hypothesis of the projected
energy identity: it applies to `proj_partial_sol`'s output forcing. -/
theorem projForce_fixed (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R T : ℝ}
    (N : ℕ)
    {Nfun : lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (u : ℝ → lowerState (I := I) (M := M) g₀ a R)
    (hg : ⇑gforce =ᵐ[timeMeasure T]
      fun t => projNfun (I := I) (M := M) g₀ a N Nfun (u t)) :
    timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforce = gforce := by
  refine MeasureTheory.Lp.ext ?_
  have hP : ⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforce)
      =ᵐ[timeMeasure T] fun t =>
        spatialEigenProj (I := I) (M := M) g₀ (a : ℝ) N (gforce t) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  filter_upwards [hP, hg] with t h1 h2
  rw [h1, h2]
  simp only [projNfun]
  exact spatialProj_idem (I := I) (M := M) g₀ (a : ℝ) N _

/-- **The projected trajectory is `V_N`-valued.**  The Duhamel field of a
truncated forcing is fixed by the truncation at the gained regularity
`H^{a+2}`, so pairing it against the truncated forcing in the Galerkin energy
identity is legitimate. -/
theorem projField_fixed (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1) (N : ℕ)
    {Nfun : lowerState (I := I) (M := M) g₀ a R →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (u : ℝ → lowerState (I := I) (M := M) g₀ a R)
    (hg : ⇑gforce =ᵐ[timeMeasure T]
      fun t => projNfun (I := I) (M := M) g₀ a N Nfun (u t)) :
    timeL2EigenProj (I := I) (M := M) g₀ ((a : ℝ) + 2) T N
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce) =
      maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce := by
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  have hfix := projForce_fixed (I := I) (M := M) g₀ a N gforce u hg
  have h := projDuhamel_zero (I := I) (M := M) g₀ hT hT1 N h_compact gforce
  rw [hfix] at h
  exact h.symm

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
