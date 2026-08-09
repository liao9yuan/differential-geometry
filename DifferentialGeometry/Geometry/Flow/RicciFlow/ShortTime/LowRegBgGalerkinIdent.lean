import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegGalerkinIdent
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgSolveAt

/-!
# Fixed-background Galerkin identification

This module identifies a background-aware low forcing with the limit of its
finite-dimensional projected forcings.  The Sobolev scale, eigenbasis, heat
operator, and spectral projections remain attached to the state metric `g₀`;
only `lowregNfun` uses the independent DeTurck background `g_bg`.
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

/-- A background-aware low forcing is the time-`L²(H¹)` limit of projected
forcings on the state-metric eigenspaces, with the whole projected trajectory
package retained for the energy argument. -/
theorem lowreg_proj_atBg (g₀ g_bg : SmoothRiemannianMetric I M)
    (K : LowRegBoundData) {Rcap T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (sol : MaxRegSolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsBgSolveAt (I := I) (M := M) g₀ g_bg K hT hT1 sol fLo Rcap) :
    ∃ (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T),
      Tendsto fseq atTop (𝓝 fLo) ∧
      ∀ N : ℕ,
        timeL2EigenProj (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T N (fseq N) =
            fseq N ∧
          (∀ᵐ t ∂(timeMeasure T),
            maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              (fseq N) t ∈
              lowerState (I := I) (M := M) g₀ 1 (lowregStateRad K.top K.slope K.outer K.realize)) ∧
          fseq N =ᵐ[timeMeasure T]
            (fun t => projNfun (I := I) (M := M) g₀ 1 N
              (lowregNfun (I := I) (M := M) g₀ g_bg hlo.hδ hlo.hCtop hlo.hB1
                hlo.hρ hlo.hP hlo.hreal)
              (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
                  (lowregStateRad_pos hlo.hCtop hlo.hB1 hlo.hρ hlo.hP).le)
                (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
                  (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
                  (fseq N)) t)) ∧
          timeH1.trace0 _ T (maxRegDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ)
              hT hT1 (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              (fseq N)) = 0 ∧
          timeH1.timeDeriv _ T (maxRegDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ)
              hT hT1 (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              (fseq N)) =
            timeScaleLaplacian (I := I) (M := M) ((1 : ℕ) : ℝ)
                (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
                  (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
                  (fseq N)) + fseq N ∧
          ‖fseq N‖ ≤ lowregStateRad K.top K.slope K.outer K.realize / 4 := by
  set R : ℝ := lowregStateRad K.top K.slope K.outer K.realize with hRdef
  have hRpos : 0 < R := lowregStateRad_pos hlo.hCtop hlo.hB1 hlo.hρ hlo.hP
  have hQnn : 0 ≤ lowregOuterRad K.top K.outer K.realize :=
    (lowregOuterRad_pos hlo.hCtop hlo.hρ hlo.hP).le
  set Nfun := lowregNfun (I := I) (M := M) g₀ g_bg hlo.hδ hlo.hCtop hlo.hB1
    hlo.hρ hlo.hP hlo.hreal
    with hNfundef
  -- the three tame coefficients, in the normalised form `partial_sol_tame` wants
  set A : ℝ≥0 := Real.toNNReal (K.top * lowregOuterRad K.top K.outer K.realize / R) with hAdef
  set B : ℝ≥0 := Real.toNNReal K.base with hBdef
  set C : ℝ≥0 := Real.toNNReal K.slope with hCdef
  have hAarg : 0 ≤ K.top * lowregOuterRad K.top K.outer K.realize / R :=
    div_nonneg (mul_nonneg hlo.hCtop hQnn) hRpos.le
  have hAcoe : (A : ℝ) = K.top * lowregOuterRad K.top K.outer K.realize / R :=
    Real.coe_toNNReal _ hAarg
  have hBcoe : (B : ℝ) = K.base := Real.coe_toNNReal _ hlo.hB0
  have hCcoe : (C : ℝ) = K.slope := Real.coe_toNNReal _ hlo.hB1
  have hAR : (A : ℝ) * R = K.top * lowregOuterRad K.top K.outer K.realize := by
    rw [hAcoe]
    exact div_mul_cancel₀ _ hRpos.ne'
  have hsmallA : (A : ℝ) * R ≤ 1 / 16 := by
    rw [hAR]; exact lowregOuterRad_small hlo.hCtop
  have hsmallC : (C : ℝ) * R ≤ 1 / 16 := by
    rw [hCcoe, hRdef]; exact lowregStateRad_small hlo.hB1
  have hsingle : ∀ u u' : lowerState (I := I) (M := M) g₀ 1 R,
      ‖Nfun u - Nfun u'‖ ≤
        (A : ℝ) * R *
            ‖(u : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) -
              (u' : _)‖ +
          (B : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((u : _) - (u' : _))‖ +
          (C : ℝ) *
              (‖(u : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))‖ +
                ‖(u' : tensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((u : _) - (u' : _))‖ := by
    intro u u'
    rw [hAR, hBcoe, hCcoe]
    exact hlo.htame u u'
  have hDnn : 0 ≤ K.zeroBd := le_trans (norm_nonneg _) hlo.hzero
  -- the horizon cap, read off the closed formula
  have hTB : T ≤ 1 / (64 * ((B : ℝ) + 1) ^ 2) := by
    rw [hBcoe]
    exact le_trans hlo.hTτ (le_trans (min_le_right _ _) (min_le_left _ _))
  -- for every truncation level, the projected solve produces a `V_N` forcing
  -- whose distance to `fLo` is at most twice the truncation defect of `fLo`
  have hex : ∀ N : ℕ,
      ∃ gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T,
        (timeL2EigenProj (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T N gforce =
            gforce ∧
          (∀ᵐ t ∂(timeMeasure T),
            maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              gforce t ∈ lowerState (I := I) (M := M) g₀ 1 R) ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => projNfun (I := I) (M := M) g₀ 1 N Nfun
              (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1 hRpos.le)
                (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
                  (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
                  gforce) t)) ∧
          timeH1.trace0 _ T (maxRegDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ)
              hT hT1 (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              gforce) = 0 ∧
          timeH1.timeDeriv _ T (maxRegDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ)
              hT hT1 (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              gforce) =
            timeScaleLaplacian (I := I) (M := M) ((1 : ℕ) : ℝ)
                (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
                  (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
                  gforce) + gforce ∧
          ‖gforce‖ ≤ R / 4) ∧
        ‖gforce - fLo‖ ≤
          2 * ‖timeL2EigenProj (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T N fLo -
            fLo‖ := by
    intro N
    obtain ⟨T₀, hT₀eq, _hT₀pos, hsol⟩ :=
      proj_partial_sol_tame (I := I) (M := M) g₀ 1 hRpos N Nfun hlo.hcont A B C K.zeroBd
        hDnn hlo.hzero hsmallA hsmallC hsingle
    have hTT₀ : T ≤ T₀ := by
      rw [hT₀eq, hBcoe]
      exact hlo.hTτ
    obtain ⟨u, gforce, hu, hstate, hgE, htr, hpde, hgball⟩ :=
      hsol hT hTT₀ hT1
    subst hu
    refine ⟨gforce, ⟨?_, hstate, hgE, htr, hpde, hgball⟩, ?_⟩
    · exact projForce_fixed (I := I) (M := M) g₀ 1 N gforce
        (fun t => aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1 hRpos.le)
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) gforce) t)
        hgE
    · exact projFixTame_le_two (I := I) (M := M) g₀ 1 hRpos N hlo.hcont hsingle
        hsmallA hsmallC hT hT1 hTB fLo gforce hlo.hball hgball hlo.hforce hgE
  choose fseq hpack hK using hex
  exact ⟨fseq, projFix_tendsto (I := I) (M := M) g₀ (K := 2) fLo fseq hK, hpack⟩

/-- Pointwise mode convergence for the background-aware projected sequence at
one explicit low-solve packet. -/
theorem lowreg_projMode_atBg (g₀ g_bg : SmoothRiemannianMetric I M)
    (K : LowRegBoundData) {Rcap T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (sol : MaxRegSolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsBgSolveAt (I := I) (M := M) g₀ g_bg K hT hT1 sol fLo Rcap) :
    ∃ (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T),
      Tendsto fseq atTop (𝓝 fLo) ∧
      (∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2), ∀ t ∈ Set.Icc (0 : ℝ) T,
        Tendsto (fun N => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) (fseq N) i) u) t) atTop
          (𝓝 (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t))) ∧
      ∀ N : ℕ,
        timeL2EigenProj (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T N (fseq N) =
            fseq N ∧
          (∀ᵐ t ∂(timeMeasure T),
            maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              (fseq N) t ∈
              lowerState (I := I) (M := M) g₀ 1 (lowregStateRad K.top K.slope K.outer K.realize)) ∧
          fseq N =ᵐ[timeMeasure T]
            (fun t => projNfun (I := I) (M := M) g₀ 1 N
              (lowregNfun (I := I) (M := M) g₀ g_bg hlo.hδ hlo.hCtop hlo.hB1
                hlo.hρ hlo.hP hlo.hreal)
              (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
                  (lowregStateRad_pos hlo.hCtop hlo.hB1 hlo.hρ hlo.hP).le)
                (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
                  (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
                  (fseq N)) t)) ∧
          timeH1.trace0 _ T (maxRegDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ)
              hT hT1 (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              (fseq N)) = 0 ∧
          timeH1.timeDeriv _ T (maxRegDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ)
              hT hT1 (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              (fseq N)) =
            timeScaleLaplacian (I := I) (M := M) ((1 : ℕ) : ℝ)
                (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
                  (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
                  (fseq N)) + fseq N ∧
          ‖fseq N‖ ≤ lowregStateRad K.top K.slope K.outer K.realize / 4 := by
  obtain ⟨fseq, hconv, hpack⟩ :=
    lowreg_proj_atBg (I := I) (M := M) g₀ g_bg K hT hT1 sol fLo hlo
  refine ⟨fseq, hconv, fun i t ht => ?_, hpack⟩
  have hmode : Tendsto (fun N => timeModeCoeff (I := I) (M := M) (fseq N) i)
      atTop (𝓝 (timeModeCoeff (I := I) (M := M) fLo i)) := by
    have hcl := ((tensorHsCoeffL (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (a := ((1 : ℕ) : ℝ)) i).compLpL 2 (timeMeasure T)).continuous.tendsto fLo
    simpa only [timeModeCoeff] using hcl.comp hconv
  exact tendsto_perModeConv_of_tendsto_timeL2
    (TensorEigenIdx.lambda (I := I) (M := M) i)
    (tensor_lambda_nonneg (I := I) (M := M) i) hmode ht

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
