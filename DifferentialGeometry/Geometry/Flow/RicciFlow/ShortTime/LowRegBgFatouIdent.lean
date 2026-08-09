import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegFatouIdent
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgRungThree

/-!
# Fixed-background rung-three Fatou identification

This module frees the DeTurck background in the primitive rung-three Fatou
endpoint.  The projected mode coordinates and their spatial, forcing, and
time-derivative identifications are already polymorphic in the nonlinearity;
only the `coreN`/`lowregNfun` background slot and the ordered rung certificate
change here.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
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

/-- The fixed-background primitive Fatou endpoint at one exact ordered
rung-three certificate.  A projected forcing sequence with a uniform
time-integrated `H³` energy bound has an `N`- and time-uniform `H³` energy
bound, provided the stored rung-three absorption budget holds. -/
theorem lowregFatouE3AtBg
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 ρ P T Bd Ctop₂ Kr2 Kr1 Kcap ε : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hCtop : 0 ≤ Ctop) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ
      (lowregRealRad (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
        hP.le hreal)))
    (htame : ∀ u v : lowerState (I := I) (M := M) g₀ 1
        (lowregStateRad Ctop B1 ρ P),
      ‖lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal u -
          lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal v‖ ≤
        Ctop * lowregOuterRad Ctop ρ P *
            ‖(u.1 : tensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
          B0 *
            ‖galLowView (I := I) (M := M) g₀ 1
              ((u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
          B1 *
              (‖(u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2))‖ +
                ‖(v.1 : tensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖) *
            ‖galLowView (I := I) (M := M) g₀ 1
              ((u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖)
    (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hball : ∀ N : ℕ, ∀ᵐ t ∂(timeMeasure T),
      maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) (fseq N) t ∈
        lowerState (I := I) (M := M) g₀ 1 (lowregStateRad Ctop B1 ρ P))
    (hnem : ∀ N : ℕ, ⇑(fseq N) =ᵐ[timeMeasure T]
      fun t => projNfun (I := I) (M := M) g₀ 1 N
        (lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
            (lowregStateRad_pos hCtop hB1 hρ hP).le)
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
            (fseq N)) t))
    (hL2H3 : ∀ N : ℕ, ∫ t, galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (lowregProjMode (I := I) (M := M) g₀ fseq N) 3 t ∂(timeMeasure T) ≤ Bd)
    (hrung : IsRung3OrdBg (I := I) (M := M) g₀ g_bg Ctop₂ Kr2 Kr1 Kcap)
    (hε : 0 < ε)
    (habs : Ctop₂ * (Kcap * (δ / (1 - δ) ^ 2)) +
      Kr2 * lowregStateRad Ctop B1 ρ P +
      Kr1 * lowregStateRad Ctop B1 ρ P + ε < 1) :
    ∃ Φ : ℝ, ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (lowregProjMode (I := I) (M := M) g₀ fseq N) 3 t ≤ Φ := by
  classical
  set U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    lowregProjMode (I := I) (M := M) g₀ fseq with hU
  have hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T) :=
    fun N i _ => lowregProjMode_cont (I := I) (M := M) g₀ hT.le fseq N i
  have hUinit : ∀ N i, U N 0 i = 0 :=
    fun N i => lowregProjMode_zero (I := I) (M := M) g₀ fseq N i
  have hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      HasDerivWithinAt (fun s => U N s i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
          galTameForce (I := I) (M := M) g₀ 1
            (lowregStateRad_pos hCtop hB1 hρ hP).le
            (lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) i)
        (Set.Ici t) t := by
    intro N t ht i _
    refine lowregModeDeriv (I := I) (M := M) g₀ hT
      (lowregStateRad_pos hCtop hB1 hρ hP).le N fseq i ?_ ?_ ht
    · exact lowregForceCont (I := I) (M := M) g₀ g_bg hδ hCtop hB0 hB1 hρ hP hreal
        htame N (U N) (fun j _ => hUcont N j (by assumption)) i
    · exact lowregForceMode (I := I) (M := M) g₀
        (lowregStateRad_pos hCtop hB1 hρ hP).le hT hT1 N fseq (hball N) (hnem N) i
  set EE : ℕ → ℝ → ℝ := fun N => Set.IccExtend hT.le
    (fun p : Set.Icc (0 : ℝ) T => galerkinEnergy (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 p.1) with hEE
  have hEEc : ∀ N, Continuous (EE N) := by
    intro N
    exact Continuous.Icc_extend'
      (galerkinEnergy_continuousOn (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 (hUcont N)).restrict
  have hEEnn : ∀ N, ∀ s : ℝ, 0 ≤ EE N s := fun N s =>
    galerkinEnergy_nonneg (I := I) (M := M) _ _ _ _
  have hEEeq : ∀ N, ∀ s ∈ Set.Icc (0 : ℝ) T,
      EE N s = galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 s :=
    fun N s hs => Set.IccExtend_of_mem hT.le _ hs
  set Pr : ℕ → ℝ → ℝ := fun N t => ∫ s in (0 : ℝ)..t, EE N s with hPr
  have hPrHas : ∀ N, ∀ t : ℝ, HasDerivAt (Pr N) (EE N t) t := by
    intro N t
    exact intervalIntegral.integral_hasDerivAt_right
      ((hEEc N).intervalIntegrable 0 t)
      (hEEc N).aestronglyMeasurable.stronglyMeasurableAtFilter
      (hEEc N).continuousAt
  have hPr0 : ∀ N, Pr N 0 = 0 := fun N => intervalIntegral.integral_same
  have hPrnn : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Pr N t := by
    intro N t ht
    exact intervalIntegral.integral_nonneg ht.1 (fun s _ => hEEnn N s)
  have hPrcont : ∀ N, ContinuousOn (Pr N) (Set.Icc (0 : ℝ) T) := by
    intro N
    exact (continuous_iff_continuousAt.2
      (fun t => (hPrHas N t).continuousAt)).continuousOn
  have hPrderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (Pr N)
        (galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 t) (Set.Ici t) t := by
    intro N t ht
    have h := hPrHas N t
    rw [hEEeq N t ⟨ht.1, ht.2.le⟩] at h
    exact h.hasDerivWithinAt
  have hPrbd : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, Pr N t ≤ Bd := by
    intro N t ht
    have hTint : ∫ s in (0 : ℝ)..T, EE N s = ∫ s, galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 s ∂(timeMeasure T) := by
      rw [intervalIntegral.integral_congr
        (g := fun s => galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 s)
        (by rw [Set.uIcc_of_le hT.le]; exact fun s hs => hEEeq N s hs),
        intervalIntegral.integral_of_le hT.le, timeMeasure,
        MeasureTheory.integral_Icc_eq_integral_Ioc]
    have hsplit : Pr N t + ∫ s in t..T, EE N s = ∫ s in (0 : ℝ)..T, EE N s :=
      intervalIntegral.integral_add_adjacent_intervals
        ((hEEc N).intervalIntegrable 0 t) ((hEEc N).intervalIntegrable t T)
    have hrest : 0 ≤ ∫ s in t..T, EE N s :=
      intervalIntegral.integral_nonneg ht.2 (fun s _ => hEEnn N s)
    have hfin := hL2H3 N
    rw [← hTint] at hfin
    linarith
  exact hrung.2.2.2.2 hδ hδ0 hδ3 hCtop hB1 hρ hP hreal hcore hUcont hUderiv
    hUinit hPr0 hPrnn hPrcont hPrderiv hPrbd hε habs

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
