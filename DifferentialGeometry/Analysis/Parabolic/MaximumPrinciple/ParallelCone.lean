import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.ProperCone
import DifferentialGeometry.Geometry.Connection.ParallelTransport.InvariantCone

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff

universe u uE uH uF

variable {M : Type u}
variable (F : M → Type uF)
  [∀ x, NormedAddCommGroup (F x)]
  [∀ x, InnerProductSpace Real (F x)]

def transportedSectionFamily
    (P : LinearIsometricTransport F) (x₀ : M)
    (u : Real → ∀ x, F x) : Real → M → F x₀ :=
  fun t ↦ P.transportSectionTo F x₀ (u t)

@[simp]
theorem transportedSectionFamily_apply
    (P : LinearIsometricTransport F) (x₀ : M)
    (u : Real → ∀ x, F x) (t : Real) (x : M) :
    transportedSectionFamily F P x₀ u t x = P.transport x x₀ (u t x) :=
  rfl

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem parallelProperCone_heat_pot_supersolution_mem_of_potential_le
    [∀ x, CompleteSpace (F x)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (potential : Real → M → Real)
    (P : LinearIsometricTransport F)
    (C : ProperConeFamily F)
    (hC : IsParallelProperConeFamily F P C)
    (x₀ : M)
    (u : Real → ∀ x, F x)
    (hsol : IsInnerDualHeatPotSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G potential (C x₀)
        (transportedSectionFamily F P x₀ u))
    (B : Real)
    (hpotential : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, potential t x ≤ B)
    (hinit : ∀ x : M, u 0 x ∈ C x) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C x := by
  have hfixed : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M,
      transportedSectionFamily F P x₀ u t x ∈ C x₀ := by
    apply properCone_heat_pot_supersolution_mem_of_potential_le
      (I := I) G hT potential (C x₀) (transportedSectionFamily F P x₀ u)
      hsol B hpotential
    intro x
    exact (hC.transport_mem_iff F x x₀ (u 0 x)).2 (hinit x)
  intro t ht x
  apply (hC.transport_mem_iff F x x₀ (u t x)).1
  simpa using hfixed t ht x

theorem parallelProperCone_heat_supersolution_mem
    [∀ x, CompleteSpace (F x)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (P : LinearIsometricTransport F)
    (C : ProperConeFamily F)
    (hC : IsParallelProperConeFamily F P C)
    (x₀ : M)
    (u : Real → ∀ x, F x)
    (hsol : IsInnerDualHeatSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G (C x₀)
        (transportedSectionFamily F P x₀ u))
    (hinit : ∀ x : M, u 0 x ∈ C x) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C x := by
  exact parallelProperCone_heat_pot_supersolution_mem_of_potential_le
    (I := I) F G hT (fun _ _ ↦ 0) P C hC x₀ u hsol 0 (by simp) hinit

end

end DifferentialGeometry.Analysis.Parabolic
