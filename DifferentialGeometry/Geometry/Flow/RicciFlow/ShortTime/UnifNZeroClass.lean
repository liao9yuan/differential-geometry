import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifNZeroBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifDeTurckRHSOne

/-!
# Explicit class-uniform zero-state package

This module packages the already-proved uniform static Ricci--DeTurck one-jet
bound as the `zeroBd` face of the low-regularity common-time interface.  The
continuity of the smooth core remains an explicit input because it is produced
together with the future tame/A2/affine packet.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ### Explicit zero-state data and proof packages -/

/-- The scalar upper cap for the zero-state nonlinearity. -/
structure LowRegZeroData where
  zeroBd : ℝ

/-- One nonnegative zero-state cap works for every order-three class metric.

The realization and smooth-core continuity arguments stay local to each metric;
the scalar cap itself is fixed before the metric varies. -/
structure IsLowZeroUnif
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ)
    (Z : LowRegZeroData) : Prop where
  zero_nonneg : 0 ≤ Z.zeroBd
  zero : ∀ (g : SmoothRiemannianMetric I M),
    MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
    (∀ a : ℕ, a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
    ∀ {R δ : ℝ} (hR : 0 < R) (hδ : δ < 1)
      (hreal : ∀ T : SmoothCcTensor g 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) δ)
      (_hcore : Continuous
        (coreN (I := I) (M := M) g gBase hδ hreal)),
      ‖lowRegN (I := I) (M := M) g gBase hR hδ hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g 1 hR.le⟩‖ ≤ Z.zeroBd

/-- The closed zero-state cap built from a uniform static-field one-jet cap. -/
noncomputable def lowZeroData
    (gBase : SmoothRiemannianMetric I M) (Λ Ksup : ℝ) : LowRegZeroData where
  zeroBd := nZeroC Ksup Λ
    ((riemannianVolumeMeasure (I := I) (M := M) gBase).real Set.univ)
    (Module.finrank ℝ E)

/-- A supplied class-uniform static-field one-jet cap gives the explicit
zero-state package. -/
theorem lowZero_unif_of
    (gBase : SmoothRiemannianMetric I M) {Λ Ksup : ℝ}
    (hKsup : 0 ≤ Ksup)
    (hsup : ∀ g : SmoothRiemannianMetric I M,
      (∀ (x : M) (v : TangentSpace I x),
        Λ⁻¹ * gBase.inner x v v ≤ g.inner x v v ∧
          g.inner x v v ≤ Λ * gBase.inner x v v) →
      MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
      MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
      MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g gBase Λ →
      ∀ j : ℕ, j ≤ 1 → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
          ((iteratedCovGrad (I := I) g 0 2 j
            (deTurckRHSSection (I := I) gBase g)).toSection x) ≤ Ksup ^ 2) :
    IsLowZeroUnif (I := I) (M := M) gBase Λ
      (lowZeroData (I := I) (M := M) gBase Λ Ksup) := by
  refine ⟨?_, ?_⟩
  · exact nZeroC_nonneg hKsup Λ
      ((riemannianVolumeMeasure (I := I) (M := M) gBase).real Set.univ)
      (Module.finrank ℝ E)
  · intro g hEq hjet R δ hR hδ hreal hcore
    have hcomp : ∀ (x : M) (v : TangentSpace I x),
        Λ⁻¹ * gBase.inner x v v ≤ g.inner x v v ∧
          g.inner x v v ≤ Λ * gBase.inner x v v :=
      fun x v => hEq.2 x (Set.mem_univ x) v
    have hsupg := hsup g hcomp
      (hjet 1 (by norm_num)) (hjet 2 (by norm_num)) (hjet 3 (by norm_num))
    simpa only [lowZeroData] using
      nZero_unif (I := I) (M := M) gBase g hR hδ hreal hcore hKsup hEq hsupg

/-- Every fixed background and class parameter at least one admit one explicit
class-uniform zero-state package. -/
theorem exists_lowZero
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ Z : LowRegZeroData,
      IsLowZeroUnif (I := I) (M := M) gBase Λ Z := by
  obtain ⟨Ksup, hKsup, hsup⟩ :=
    unifKsupLeOne (I := I) (M := M) gBase hΛ
  exact ⟨lowZeroData (I := I) (M := M) gBase Λ Ksup,
    lowZero_unif_of (I := I) (M := M) gBase hKsup hsup⟩

/-- Read a class-uniform zero-state package in the exact six-number
`lowregNfun` shape consumed by `IsLowBoundsAt.hzero`. -/
theorem lowZero_nfun
    {gBase : SmoothRiemannianMetric I M} {Λ : ℝ} {Z : LowRegZeroData}
    (hZ : IsLowZeroUnif (I := I) (M := M) gBase Λ Z)
    (g : SmoothRiemannianMetric I M)
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ)
    (hjet : ∀ a : ℕ, a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ)
    {δ Ctop B1 ρ P : ℝ} (hδ : δ < 1) (hCtop : 0 ≤ Ctop)
    (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) T‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g gBase hδ
      (lowregRealRad (I := I) (M := M) g
        (Ctop := Ctop) (B1 := B1) (ρ := ρ) hP.le hreal))) :
    ‖lowregNfun (I := I) (M := M) g gBase hδ hCtop hB1 hρ hP hreal
      ⟨0, zero_mem_lowerState (I := I) (M := M) g 1
        (lowregStateRad_pos hCtop hB1 hρ hP).le⟩‖ ≤ Z.zeroBd := by
  simpa only [lowregNfun] using hZ.zero g hEq hjet
    (lowregStateRad_pos hCtop hB1 hρ hP) hδ
    (lowregRealRad (I := I) (M := M) g
      (Ctop := Ctop) (B1 := B1) (ρ := ρ) hP.le hreal) hcore

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
