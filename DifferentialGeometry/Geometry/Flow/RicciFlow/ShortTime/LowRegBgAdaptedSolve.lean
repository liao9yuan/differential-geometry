import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgSolveAt
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgRungPack

/-!
# The fixed-background adapted low solve

This module joins one fixed-background order-one solve with the metricwise
background rung-three and gate certificates.  The stored absorption budget is
evaluated at the solve packet's actual threshold and state radius.

The constructor `adaptedBg_of_given` is deliberately metricwise: it consumes an
already proved gate budget and does not choose a class-uniform threshold,
radius, packet, or lifetime.
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

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- A fixed-background low solve paired with one ordered rung-three certificate
and a coherent metricwise background gate package.  Its absorption budget uses
the threshold and state radius stored in `K`; no class-first choice is asserted.
-/
def IsAdaptedLowSolveBg (g₀ g_bg : SmoothRiemannianMetric I M)
    (K : LowRegBoundData) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      ((1 : ℕ) : ℝ) T)
    (gforce : timeL2
      (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (Rcap Ctop₂ Kr2 Kr1 Kcap : ℝ) : Prop :=
  IsBgSolveAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap ∧
    IsRung3OrdBg (I := I) (M := M) g₀ g_bg Ctop₂ Kr2 Kr1 Kcap ∧
    ∃ A B : ℝ, IsLowGateOrdBg (I := I) (M := M) g₀ g_bg A B ∧
      Ctop₂ * Kcap ≤ A ∧ Kr2 + Kr1 ≤ B ∧
      ∃ ε : ℝ, 0 < ε ∧
        A * (K.threshold / (1 - K.threshold) ^ 2) +
          B * lowregStateRad K.top K.slope K.outer K.realize + ε < 1

namespace IsAdaptedLowSolveBg

variable {g₀ g_bg : SmoothRiemannianMetric I M} {K : LowRegBoundData}
  {T Rcap Ctop₂ Kr2 Kr1 Kcap : ℝ} {hT : 0 < T} {hT1 : T ≤ 1}
  {u : MaxRegSolutionSpace (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
    ((1 : ℕ) : ℝ) T}
  {gforce : timeL2
    (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T}

/-- Read the exact fixed-background solve component of an adapted solve. -/
theorem toIsBgSolveAt
    (h : IsAdaptedLowSolveBg (I := I) (M := M) g₀ g_bg K hT hT1
      u gforce Rcap Ctop₂ Kr2 Kr1 Kcap) :
    IsBgSolveAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap :=
  h.1

/-- Read the underlying fixed-background fixed-point output. -/
theorem toIsLowSolveBg
    (h : IsAdaptedLowSolveBg (I := I) (M := M) g₀ g_bg K hT hT1
      u gforce Rcap Ctop₂ Kr2 Kr1 Kcap) :
    IsLowSolveBg (I := I) (M := M) g₀ g_bg K
      h.toIsBgSolveAt.bounds hT hT1 u gforce :=
  h.toIsBgSolveAt.solve

/-- Read the stored fixed-background ordered rung-three certificate. -/
theorem toIsRung3OrdBg
    (h : IsAdaptedLowSolveBg (I := I) (M := M) g₀ g_bg K hT hT1
      u gforce Rcap Ctop₂ Kr2 Kr1 Kcap) :
    IsRung3OrdBg (I := I) (M := M) g₀ g_bg Ctop₂ Kr2 Kr1 Kcap :=
  h.2.1

/-- Read the coherent background gate and the domination certificates for the
stored rung-three tuple. -/
theorem toGatePack
    (h : IsAdaptedLowSolveBg (I := I) (M := M) g₀ g_bg K hT hT1
      u gforce Rcap Ctop₂ Kr2 Kr1 Kcap) :
    ∃ A B : ℝ, IsLowGateOrdBg (I := I) (M := M) g₀ g_bg A B ∧
      Ctop₂ * Kcap ≤ A ∧ Kr2 + Kr1 ≤ B ∧
      ∃ ε : ℝ, 0 < ε ∧
        A * (K.threshold / (1 - K.threshold) ^ 2) +
          B * lowregStateRad K.top K.slope K.outer K.realize + ε < 1 :=
  h.2.2

/-- Read the rung-three absorption budget already discharged by an adapted
fixed-background solve. -/
theorem absorb
    (h : IsAdaptedLowSolveBg (I := I) (M := M) g₀ g_bg K hT hT1
      u gforce Rcap Ctop₂ Kr2 Kr1 Kcap) :
    ∃ ε : ℝ, 0 < ε ∧
      Ctop₂ * (Kcap * (K.threshold / (1 - K.threshold) ^ 2)) +
          Kr2 * lowregStateRad K.top K.slope K.outer K.realize +
          Kr1 * lowregStateRad K.top K.slope K.outer K.realize + ε < 1 := by
  obtain ⟨A, B, _hgate, hA, hB, ε, hε, hbudget⟩ := h.toGatePack
  have hR : 0 ≤ lowregStateRad K.top K.slope K.outer K.realize :=
    (lowregStateRad_pos h.1.hCtop h.1.hB1 h.1.hρ h.1.hP).le
  have hdom := rungGate_le hA hB h.1.hδ0 hR
  exact ⟨ε, hε, by linarith only [hdom, hbudget]⟩

end IsAdaptedLowSolveBg

/-- Package a given fixed-background solve and a given metricwise gate once
the gate budget has been proved for the solve packet's actual threshold and
state radius.  The rung-three tuple remains metricwise existential data. -/
theorem adaptedBg_of_given
    {g₀ g_bg : SmoothRiemannianMetric I M} {K : LowRegBoundData}
    {T Rcap : ℝ} {hT : 0 < T} {hT1 : T ≤ 1}
    {u : MaxRegSolutionSpace (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      ((1 : ℕ) : ℝ) T}
    {gforce : timeL2
      (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T}
    (hsolve : IsBgSolveAt (I := I) (M := M) g₀ g_bg K hT hT1
      u gforce Rcap)
    {A B : ℝ} (hgate : IsLowGateOrdBg (I := I) (M := M) g₀ g_bg A B)
    (hbudget : ∃ ε : ℝ, 0 < ε ∧
      A * (K.threshold / (1 - K.threshold) ^ 2) +
        B * lowregStateRad K.top K.slope K.outer K.realize + ε < 1) :
    ∃ Ctop₂ Kr2 Kr1 Kcap : ℝ,
      IsAdaptedLowSolveBg (I := I) (M := M) g₀ g_bg K hT hT1
        u gforce Rcap Ctop₂ Kr2 Kr1 Kcap := by
  obtain ⟨Ctop₂, Kr2, Kr1, Kcap, hrung, hA, hB⟩ := hgate.2.2.1
  exact ⟨Ctop₂, Kr2, Kr1, Kcap, hsolve, hrung,
    A, B, hgate, hA, hB, hbudget⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
