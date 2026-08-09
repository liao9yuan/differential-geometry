import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifClassBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.EigenProjTameSol

/-!
# The order-one low-lane forcing is a limit of finite-dimensional forcings

The Galerkin route to an a-priori estimate on the low-regularity
Ricci--DeTurck forcing needs the solution to be identified with the limit of
finite-dimensional approximations: on the truncated space `V_N` all Sobolev
norms are finite a priori, so an energy hierarchy closes there, and only
afterwards is the bound passed to the limit by Fatou.

`IsLowSolve` (`ShortTime/UnifClassBounds.lean`) carries exactly the data that
makes this identification available -- the six numbers, the producer
certificates for `lowregNfun`, the horizon cap, the forcing ball and the a.e.
Nemytskii identity along the field's own Duhamel trajectory.  Feeding them to
the tame projection layer (`HeatSemigroup/EigenProjTameSol.lean`) gives, for
each truncation level `N`, a projected forcing solving the same fixed-point
equation on the same horizon in the same ball, whose distance to the true
forcing is at most twice the truncation defect of the true forcing alone.

## Main result

* `lowreg_proj_at` — an explicit low solve `fLo` is the `L²([0,T]; H^1)` limit of a
  sequence of `V_N`-valued forcings.  No compactness, no weak-* extraction and
  no uniqueness theorem is involved: the rate is `2‖Π_N fLo - fLo‖`.
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

/-- **The order-one low-lane forcing is a limit of `V_N`-valued forcings.**

A low solve `fLo` (`IsLowSolve`: the forcing of the order-one fixed-background
Ricci--DeTurck contraction, with its six numbers, producer certificates, horizon
cap, forcing ball and a.e. Nemytskii identity) is the `L²([0,T]; H^1)` limit of
a sequence `fseq N`, each fixed by the spectral truncation `Π_N`.

The `fseq N` are the forcings of the *projected* tame solve
(`proj_partial_sol_tame`): the truncated nonlinearity `Π_N ∘ lowregNfun`
inherits continuity, the static bound and the three-arm tame estimate with the
same constants, so the projected system runs on the same closed horizon in the
same ball of radius `lowregStateRad/4`.  Subtracting the two fixed-point
equations inside the one contraction (`projFixTame_le_two`) bounds
`‖fseq N - fLo‖` by `2‖Π_N fLo - fLo‖`, which tends to zero.

This is the identification step of the Galerkin argument, and it is the reason
`IsLowSolve` -- not merely a norm bound on `fLo` -- is the honest input of every
energy estimate on the order-one trajectory.

**The whole projected trajectory is exposed, not only its forcing.**  Besides
`fseq` and its convergence, the statement carries, for every truncation level
`N` and with the class numbers `δ, Ctop, B1, ρ, P` bound *once* (so every
constant below is `N`-free): the `Π_N`-fixedness of `fseq N`; the a-priori
state ball `‖U_N(t)‖_{H²} ≤ lowregStateRad Ctop B1 ρ P` a.e.; the truncated
Nemytskii identity `fseq N =ᵐ Π_N ∘ lowregNfun` along `U_N`; the zero seed;
the parabolic equation `∂_t U_N = Δ U_N + fseq N`; and the forcing ball.  These
are exactly the a-priori inputs an energy rung consumes, and they exist only
along the projected trajectory -- `proj_partial_sol_tame` produces all of them
in one shot, so exposing them costs nothing beyond not discarding them.

**The nonlinearity's own certificates stay explicit.**  The input
`IsLowSolveAt` fixes the sharp fibre range, smooth-core continuity, tame
constant, `lowregNfun` continuity and three-arm estimate at one literal tuple.
The output sequence is indexed by those same constants.  The compatibility
wrapper below destructs `IsLowSolve` once and re-exports the former interface;
the calibrated route calls this exact theorem directly. -/
theorem lowreg_proj_at (g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 D ρ P Rcap T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsLowSolveAt (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρ) (P := P)
      g₀ hT hT1 fLo Rcap) :
    ∃ (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T),
      Tendsto fseq atTop (𝓝 fLo) ∧
      ∀ N : ℕ,
        timeL2EigenProj (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T N (fseq N) =
            fseq N ∧
          (∀ᵐ t ∂(timeMeasure T),
            maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              (fseq N) t ∈
              lowerState (I := I) (M := M) g₀ 1 (lowregStateRad Ctop B1 ρ P)) ∧
          fseq N =ᵐ[timeMeasure T]
            (fun t => projNfun (I := I) (M := M) g₀ 1 N
              (lowregNfun (I := I) (M := M) g₀ g₀ hlo.hδ hlo.hCtop hlo.hB1
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
          ‖fseq N‖ ≤ lowregStateRad Ctop B1 ρ P / 4 := by
  classical
  obtain ⟨hδ, hCtop, hB1, hρ, hP, hreal, hδ0, hδ3, hcore, hB0, hcont, htame,
    hzero, hTτ, hball, hforce, -⟩ := hlo
  set R : ℝ := lowregStateRad Ctop B1 ρ P with hRdef
  have hRpos : 0 < R := lowregStateRad_pos hCtop hB1 hρ hP
  have hQnn : 0 ≤ lowregOuterRad Ctop ρ P := (lowregOuterRad_pos hCtop hρ hP).le
  set Nfun := lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal
    with hNfundef
  -- the three tame coefficients, in the normalised form `partial_sol_tame` wants
  set A : ℝ≥0 := Real.toNNReal (Ctop * lowregOuterRad Ctop ρ P / R) with hAdef
  set B : ℝ≥0 := Real.toNNReal B0 with hBdef
  set C : ℝ≥0 := Real.toNNReal B1 with hCdef
  have hAarg : 0 ≤ Ctop * lowregOuterRad Ctop ρ P / R :=
    div_nonneg (mul_nonneg hCtop hQnn) hRpos.le
  have hAcoe : (A : ℝ) = Ctop * lowregOuterRad Ctop ρ P / R :=
    Real.coe_toNNReal _ hAarg
  have hBcoe : (B : ℝ) = B0 := Real.coe_toNNReal _ hB0
  have hCcoe : (C : ℝ) = B1 := Real.coe_toNNReal _ hB1
  have hAR : (A : ℝ) * R = Ctop * lowregOuterRad Ctop ρ P := by
    rw [hAcoe]
    exact div_mul_cancel₀ _ hRpos.ne'
  have hsmallA : (A : ℝ) * R ≤ 1 / 16 := by
    rw [hAR]; exact lowregOuterRad_small hCtop
  have hsmallC : (C : ℝ) * R ≤ 1 / 16 := by
    rw [hCcoe, hRdef]; exact lowregStateRad_small hB1
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
    exact htame u u'
  have hDnn : 0 ≤ D := le_trans (norm_nonneg _) hzero
  -- the horizon cap, read off the closed formula
  have hTB : T ≤ 1 / (64 * ((B : ℝ) + 1) ^ 2) := by
    rw [hBcoe]
    exact le_trans hTτ (le_trans (min_le_right _ _) (min_le_left _ _))
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
      proj_partial_sol_tame (I := I) (M := M) g₀ 1 hRpos N Nfun hcont A B C D
        hDnn hzero hsmallA hsmallC hsingle
    have hTT₀ : T ≤ T₀ := by
      rw [hT₀eq, hBcoe]
      exact hTτ
    obtain ⟨u, gforce, hu, hstate, hgE, htr, hpde, hgball⟩ :=
      hsol hT hTT₀ hT1
    subst hu
    refine ⟨gforce, ⟨?_, hstate, hgE, htr, hpde, hgball⟩, ?_⟩
    · exact projForce_fixed (I := I) (M := M) g₀ 1 N gforce
        (fun t => aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1 hRpos.le)
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) gforce) t)
        hgE
    · exact projFixTame_le_two (I := I) (M := M) g₀ 1 hRpos N hcont hsingle
        hsmallA hsmallC hT hT1 hTB fLo gforce hball hgball hforce hgE
  choose fseq hpack hK using hex
  exact ⟨fseq, projFix_tendsto (I := I) (M := M) g₀ (K := 2) fLo fseq hK, hpack⟩

/-- Compatibility form of `lowreg_proj_at`.  It destructs the existential
`IsLowSolve` once, packages that same tuple explicitly, and re-exports the
original identification result. -/
theorem lowreg_proj_tendsto (g₀ : SmoothRiemannianMetric I M) {T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsLowSolve (I := I) (M := M) g₀ hT hT1 fLo) :
    ∃ (δ Ctop B1 ρ P : ℝ) (hδ : δ < 1) (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1)
      (hρ : 0 < ρ) (hP : 0 < P)
      (hreal : ∀ S : Integral.L2.SmoothCcTensor g₀ 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
          MetricRealization.gFibreOpBound (I := I) (M := M) g₀
            (MetricRealization.ccTensorBilinSymm (I := I) g₀ S) δ)
      (_hδ0 : 0 ≤ δ) (_hδ3 : δ ≤ 1 / 3)
      (_hcore : Continuous (coreN (I := I) (M := M) g₀ g₀ hδ
        (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
          hP.le hreal)))
      (B0 : ℝ) (_hB0 : 0 ≤ B0)
      (_hcont : Continuous
        (lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal))
      (_htame : ∀ u v : lowerState (I := I) (M := M) g₀ 1
          (lowregStateRad Ctop B1 ρ P),
        ‖lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal u -
            lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal v‖ ≤
          Ctop * lowregOuterRad Ctop ρ P *
              ‖(u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
            B0 *
              ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
                ((u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
            B1 *
                (‖(u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖ +
                  ‖(v.1 : tensorHs (I := I) (M := M) g₀ 0 2
                    (((1 : ℕ) : ℝ) + 2))‖) *
              ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
                ((u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2)) - v.1)‖)
      (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T),
      Tendsto fseq atTop (𝓝 fLo) ∧
      ∀ N : ℕ,
        timeL2EigenProj (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T N (fseq N) =
            fseq N ∧
          (∀ᵐ t ∂(timeMeasure T),
            maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              (fseq N) t ∈
              lowerState (I := I) (M := M) g₀ 1 (lowregStateRad Ctop B1 ρ P)) ∧
          fseq N =ᵐ[timeMeasure T]
            (fun t => projNfun (I := I) (M := M) g₀ 1 N
              (lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal)
              (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
                  (lowregStateRad_pos hCtop hB1 hρ hP).le)
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
          ‖fseq N‖ ≤ lowregStateRad Ctop B1 ρ P / 4 := by
  obtain ⟨δ, Ctop, B0, B1, D, ρ, P, hδ, hCtop, hB1, hρ, hP, hreal, hδ0, hδ3,
    hcore, hB0, hcont, htame, hzero, hTτ, hball, hforce⟩ := hlo
  have hat : IsLowSolveAt (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρ) (P := P)
      g₀ hT hT1 fLo (lowregStateRad Ctop B1 ρ P) :=
    ⟨hδ, hCtop, hB1, hρ, hP, hreal, hδ0, hδ3, hcore, hB0, hcont, htame,
      hzero, hTτ, hball, hforce, le_rfl⟩
  obtain ⟨fseq, hconv, hpack⟩ :=
    lowreg_proj_at (I := I) (M := M) g₀ hT hT1 fLo hat
  exact ⟨δ, Ctop, B1, ρ, P, hδ, hCtop, hB1, hρ, hP, hreal, hδ0, hδ3,
    hcore, B0, hB0, hcont, htame, fseq, hconv, hpack⟩

/-- Pointwise mode convergence for the projected sequence at one explicit
low-solve witness tuple. -/
theorem lowreg_projMode_at (g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 D ρ P Rcap T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsLowSolveAt (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρ) (P := P)
      g₀ hT hT1 fLo Rcap) :
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
              lowerState (I := I) (M := M) g₀ 1 (lowregStateRad Ctop B1 ρ P)) ∧
          fseq N =ᵐ[timeMeasure T]
            (fun t => projNfun (I := I) (M := M) g₀ 1 N
              (lowregNfun (I := I) (M := M) g₀ g₀ hlo.hδ hlo.hCtop hlo.hB1
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
          ‖fseq N‖ ≤ lowregStateRad Ctop B1 ρ P / 4 := by
  obtain ⟨fseq, hconv, hpack⟩ :=
    lowreg_proj_at (I := I) (M := M) g₀ hT hT1 fLo hlo
  refine ⟨fseq, hconv, fun i t ht => ?_, hpack⟩
  have hmode : Tendsto (fun N => timeModeCoeff (I := I) (M := M) (fseq N) i)
      atTop (𝓝 (timeModeCoeff (I := I) (M := M) fLo i)) := by
    have hcl := ((tensorHsCoeffL (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (a := ((1 : ℕ) : ℝ)) i).compLpL 2 (timeMeasure T)).continuous.tendsto fLo
    simpa only [timeModeCoeff] using hcl.comp hconv
  exact tendsto_perModeConv_of_tendsto_timeL2
    (TensorEigenIdx.lambda (I := I) (M := M) i)
    (tensor_lambda_nonneg (I := I) (M := M) i) hmode ht

/-- **The eigen-coordinates of the truncated forcings converge pointwise in
time.**  The mode-coordinate map is a bounded linear map on the time-`L²` space,
and `perModeConv` is continuous for the time-`L²` topology
(`tendsto_perModeConv_of_tendsto_timeL2`), so the identification
`lowreg_proj_tendsto` descends to every eigen-coordinate at every time of the
closed slab.

This is exactly the convergence hypothesis of `fatou_sq_mass`: with an
`N`-uniform bound on the truncated partial sums it yields the `σ`-weighted
spectral-mass bound on `fLo` itself.

Like `lowreg_proj_tendsto`, the statement hands back the whole projected
trajectory alongside the convergence -- including the re-exported nonlinearity
certificates (`0 ≤ δ ≤ 1/3`, `coreN`-continuity, `B0`, `lowregNfun`-continuity
and the three-arm tame estimate) -- so that a Fatou closure gets the mode limit,
the a-priori energy inputs and the rung's certificate block from **one**
package, at **one** tuple of constants. -/
theorem lowreg_projMode_tendsto (g₀ : SmoothRiemannianMetric I M) {T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsLowSolve (I := I) (M := M) g₀ hT hT1 fLo) :
    ∃ (δ Ctop B1 ρ P : ℝ) (hδ : δ < 1) (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1)
      (hρ : 0 < ρ) (hP : 0 < P)
      (hreal : ∀ S : Integral.L2.SmoothCcTensor g₀ 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
          MetricRealization.gFibreOpBound (I := I) (M := M) g₀
            (MetricRealization.ccTensorBilinSymm (I := I) g₀ S) δ)
      (_hδ0 : 0 ≤ δ) (_hδ3 : δ ≤ 1 / 3)
      (_hcore : Continuous (coreN (I := I) (M := M) g₀ g₀ hδ
        (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
          hP.le hreal)))
      (B0 : ℝ) (_hB0 : 0 ≤ B0)
      (_hcont : Continuous
        (lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal))
      (_htame : ∀ u v : lowerState (I := I) (M := M) g₀ 1
          (lowregStateRad Ctop B1 ρ P),
        ‖lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal u -
            lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal v‖ ≤
          Ctop * lowregOuterRad Ctop ρ P *
              ‖(u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
            B0 *
              ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
                ((u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
            B1 *
                (‖(u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖ +
                  ‖(v.1 : tensorHs (I := I) (M := M) g₀ 0 2
                    (((1 : ℕ) : ℝ) + 2))‖) *
              ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
                ((u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2)) - v.1)‖)
      (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T),
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
              lowerState (I := I) (M := M) g₀ 1 (lowregStateRad Ctop B1 ρ P)) ∧
          fseq N =ᵐ[timeMeasure T]
            (fun t => projNfun (I := I) (M := M) g₀ 1 N
              (lowregNfun (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal)
              (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
                  (lowregStateRad_pos hCtop hB1 hρ hP).le)
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
          ‖fseq N‖ ≤ lowregStateRad Ctop B1 ρ P / 4 := by
  obtain ⟨δ, Ctop, B1, ρ, P, hδ, hCtop, hB1, hρ, hP, hreal, hδ0, hδ3, hcore,
    B0, hB0, hcont, htame, fseq, hconv, hpack⟩ :=
    lowreg_proj_tendsto (I := I) (M := M) g₀ hT hT1 fLo hlo
  refine ⟨δ, Ctop, B1, ρ, P, hδ, hCtop, hB1, hρ, hP, hreal, hδ0, hδ3, hcore,
    B0, hB0, hcont, htame, fseq, hconv, fun i t ht => ?_, hpack⟩
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
