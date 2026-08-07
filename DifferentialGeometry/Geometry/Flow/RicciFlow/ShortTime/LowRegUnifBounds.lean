import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifClassBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifRealizeRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifNZeroClass
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifDenseTame
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds

/-!
# Class-uniform six-number input for the low-regularity solve

This file records the exact quantifier boundary needed for a common
fixed-point lifetime.  A single certified `LowRegBoundData` packet is chosen
before the varying metric, while every metric keeps its own spectral spaces and
its own proof of the analytic certificates in `IsLowBoundsAt`.

No all-rung Sobolev comparison belongs to this package.  Higher regularity is a
separate qualitative bootstrap after the common low solution has been built.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- One explicit low-solve coefficient packet supplies the exact analytic
certificates for every member of the order-three metric class. -/
structure IsLowBoundsUnif
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ)
    (K : LowRegBoundData) : Prop where
  bounds : ∀ g : SmoothRiemannianMetric I M,
    MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
    (∀ a : ℕ, a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
    IsLowBoundsAt (I := I) (M := M) g gBase K

/-- One horizon envelope dominates an exact analytic packet for every class
member.  The exact packet may vary with the metric; only the six scalar caps
are fixed before it. -/
structure IsLowBoundsCap
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ)
    (U : LowRegHorizonData) : Prop where
  bounds : ∀ g : SmoothRiemannianMetric I M,
    MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
    (∀ a : ℕ, a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
    ∃ K : LowRegBoundData,
      IsLowBoundsAt (I := I) (M := M) g gBase K ∧ IsLowBoundCap K U

/-- A literal common packet gives a common horizon envelope by reflexivity. -/
theorem IsLowBoundsUnif.toCaps
    {gBase : SmoothRiemannianMetric I M} {Λ : ℝ} {K : LowRegBoundData}
    (hK : IsLowBoundsUnif (I := I) (M := M) gBase Λ K) :
    IsLowBoundsCap (I := I) (M := M) gBase Λ K.toHorizon where
  bounds g hEq hjet :=
    ⟨K, hK.bounds g hEq hjet, boundCap_refl K⟩

/-- Every three-dimensional order-three metric class admits one literal
low-regularity coefficient packet, chosen before the class metric varies. -/
theorem exists_lowBounds
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ K : LowRegBoundData,
      IsLowBoundsUnif (I := I) (M := M) gBase Λ K := by
  obtain ⟨RD, hRD⟩ :=
    exists_lowRealize (I := I) (M := M) hDim gBase hΛ
  obtain ⟨ZD, hZD⟩ := exists_lowZero (I := I) (M := M) gBase hΛ
  obtain ⟨ρ, Ctop, B0, B1, hρ, hCtop, hB0, hB1, houter⟩ :=
    lowRegN_outer_unif (I := I) (M := M) hDim gBase hΛ
      hRD.threshold_nonneg hRD.threshold_lt
  let Q : ℝ := lowregOuterRad Ctop ρ RD.radius
  have hQpos : 0 < Q := by
    simpa only [Q] using lowregOuterRad_pos hCtop hρ hRD.radius_pos
  have hB1Q : 0 ≤ B1 Q := hB1 Q hQpos.le
  have hSpos : 0 < lowregStateRad Ctop (B1 Q) ρ RD.radius :=
    lowregStateRad_pos hCtop hB1Q hρ hRD.radius_pos
  have hQρ : Q ≤ ρ := by
    have hhalf := lowregOuterRad_le_rho
      (Ctop := Ctop) (ρ := ρ) (P := RD.radius)
    dsimp only [Q]
    linarith
  have hQP : Q ≤ RD.radius := by
    have hhalf := lowregOuterRad_le_P
      (Ctop := Ctop) (ρ := ρ) (P := RD.radius)
    dsimp only [Q]
    linarith
  have hSQ : lowregStateRad Ctop (B1 Q) ρ RD.radius ≤ Q := by
    have hhalf := lowregStateRad_le_Q
      (Ctop := Ctop) (B1 := B1 Q) (ρ := ρ) (P := RD.radius)
    linarith
  let K : LowRegBoundData := {
    threshold := RD.threshold
    top := Ctop
    base := B0 Q
    slope := B1 Q
    zeroBd := ZD.zeroBd
    outer := ρ
    realize := RD.radius
    threshold_lt := hRD.threshold_lt
    top_nonneg := hCtop
    base_nonneg := hB0 Q hQpos.le
    slope_nonneg := hB1Q
    zero_nonneg := hZD.zero_nonneg
    outer_pos := hρ
    realize_pos := hRD.radius_pos
  }
  refine ⟨K, { bounds := ?_ }⟩
  intro g hEq hjet
  have hreal := hRD.realize g hEq hjet
  have hrealQ : ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) T‖ ≤ Q →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) RD.threshold :=
    realizeOfLE (I := I) (M := M) g hQP hreal
  obtain ⟨hcont0, hcore0, htame0⟩ :=
    houter g hEq hjet hQpos.le hQρ hSpos hSQ hrealQ
  have hcore' : Continuous
      (coreN (I := I) (M := M) g gBase hRD.threshold_lt
        (lowregRealRad (I := I) (M := M) g
          (Ctop := Ctop) (B1 := B1 Q) (ρ := ρ)
          hRD.radius_pos.le hreal)) := by
    simpa only using hcore0
  have hzero0 := lowZero_nfun (I := I) (M := M) hZD g hEq hjet
    hRD.threshold_lt hCtop hB1Q hρ hRD.radius_pos hreal hcore'
  have hrealK : ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) T‖ ≤ K.realize →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) K.threshold := by
    simpa only [K] using hreal
  refine {
    threshold_nonneg := by simpa only [K] using hRD.threshold_nonneg
    threshold_le_third := by simpa only [K] using hRD.threshold_le_third
    hreal := hrealK
    hcont := ?_
    htame := ?_
    hzero := ?_
    core_cont := ?_ }
  · simpa only [K, Q, lowregNfun] using hcont0
  · simpa only [K, Q, lowregNfun] using htame0
  · simpa only [K, Q] using hzero0
  · simpa only [K, Q] using hcore'

/-- Every three-dimensional order-three metric class admits one common
low-regularity horizon envelope. -/
theorem lowreg_bounds_unif
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ U : LowRegHorizonData,
      IsLowBoundsCap (I := I) (M := M) gBase Λ U := by
  obtain ⟨K, hK⟩ := exists_lowBounds (I := I) (M := M) hDim gBase hΛ
  exact ⟨K.toHorizon, IsLowBoundsUnif.toCaps (I := I) (M := M) hK⟩

/-- A class-uniform six-number package gives one positive closed horizon and a
background-aware low solve for every member of the class.

This is only the fixed-point assembly.  The producer of `IsLowBoundsUnif` and
the qualitative smoothness bootstrap are separate theorems. -/
theorem unif_solve_of_bounds
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (K : LowRegBoundData)
    (hK : IsLowBoundsUnif (I := I) (M := M) gBase Λ K) :
    0 < lowregHorizon K.top K.base K.slope K.zeroBd K.outer K.realize ∧
      ∀ (g : SmoothRiemannianMetric I M)
        (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ)
        (hjet : ∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ),
        ∀ {T : ℝ} (hT : 0 < T)
          (_ : T ≤ lowregHorizon K.top K.base K.slope K.zeroBd K.outer K.realize)
          (hT1 : T ≤ 1),
          ∃ (u : MaxRegSolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
            (gforce : timeL2
              (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T),
            IsLowSolveBg (I := I) (M := M) g gBase K
              (hK.bounds g hEq hjet) hT hT1 u gforce := by
  refine ⟨lowregHorizon_pos K.top_nonneg K.base_nonneg K.slope_nonneg
    K.zero_nonneg K.outer_pos K.realize_pos, ?_⟩
  intro g hEq hjet T hT hTτ hT1
  exact lowreg_sol_of_data (I := I) (M := M) g gBase K
    (hK.bounds g hEq hjet) hT hTτ hT1

/-- A six-number envelope, rather than one literal packet, is enough to give a
common positive horizon.  Each metric keeps its exact packet and solution
witnesses, while `horizon_le_of_cap` transports the common time into that
metric's fixed-point engine. -/
theorem unif_solve_of_caps
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (U : LowRegHorizonData)
    (hU : IsLowBoundsCap (I := I) (M := M) gBase Λ U) :
    0 < lowregHorizon U.top U.base U.slope U.zeroBd U.outer U.realize ∧
      ∀ (g : SmoothRiemannianMetric I M)
        (_hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ)
        (_hjet : ∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ),
        ∀ {T : ℝ} (hT : 0 < T)
          (_ : T ≤ lowregHorizon U.top U.base U.slope U.zeroBd U.outer U.realize)
          (hT1 : T ≤ 1),
          ∃ (K : LowRegBoundData)
            (hK : IsLowBoundsAt (I := I) (M := M) g gBase K)
            (u : MaxRegSolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
            (gforce : timeL2
              (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T),
            IsLowBoundCap K U ∧
              IsLowSolveBg (I := I) (M := M) g gBase K hK hT hT1 u gforce := by
  refine ⟨lowregHorizon_pos U.top_nonneg U.base_nonneg U.slope_nonneg
    U.zero_nonneg U.outer_pos U.realize_pos, ?_⟩
  intro g hEq hjet T hT hTτ hT1
  obtain ⟨K, hK, hcap⟩ := hU.bounds g hEq hjet
  obtain ⟨u, gforce, hsol⟩ := lowreg_sol_of_data (I := I) (M := M) g gBase K hK
    hT (hTτ.trans (horizon_le_of_cap hcap)) hT1
  exact ⟨K, hK, u, gforce, hcap, hsol⟩

/-- Every three-dimensional order-three metric class admits low
Ricci--DeTurck fixed-point solutions on one positive common horizon. -/
theorem lowreg_solve_unif
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ U : LowRegHorizonData,
      0 < lowregHorizon U.top U.base U.slope U.zeroBd U.outer U.realize ∧
        ∀ (g : SmoothRiemannianMetric I M)
          (_hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ)
          (_hjet : ∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ),
          ∀ {T : ℝ} (hT : 0 < T)
            (_ : T ≤ lowregHorizon U.top U.base U.slope U.zeroBd U.outer U.realize)
            (hT1 : T ≤ 1),
            ∃ (K : LowRegBoundData)
              (hK : IsLowBoundsAt (I := I) (M := M) g gBase K)
              (u : MaxRegSolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
              (gforce : timeL2
                (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T),
              IsLowBoundCap K U ∧
                IsLowSolveBg (I := I) (M := M) g gBase K hK hT hT1 u gforce := by
  obtain ⟨U, hU⟩ := lowreg_bounds_unif (I := I) (M := M) hDim gBase hΛ
  obtain ⟨hpos, hsolve⟩ := unif_solve_of_caps (I := I) (M := M) gBase U hU
  exact ⟨U, hpos, hsolve⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
