import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.HeatPotential

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Set
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem heat_pot_comparison
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T) (V u v : Real → M → Real)
    (hu : IsHeatPotSubsolutionOn (RealTimeInterval.closed 0 T hT) G V u)
    (hv : IsHeatPotSupersolutionOn (RealTimeInterval.closed 0 T hT) G V v)
    (C : Real)
    (hV : ∀ t ∈ Set.Icc 0 T, ∀ x : M, V t x ≤ C)
    (hinit : ∀ x : M, u 0 x ≤ v 0 x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x ≤ v t x := by
  have hdiff : IsHeatPotSupersolutionOn (RealTimeInterval.closed 0 T hT) G V
      (fun t x => v t x - u t x) :=
    hv.sub hu
  have hnonneg := heat_pot_supersolution_nonneg (I := I) G hT V
    (fun t x => v t x - u t x) hdiff C hV
    (fun x => sub_nonneg.mpr (hinit x))
  intro t ht x
  exact sub_nonneg.mp (hnonneg t ht x)

theorem heat_pot_eq_of_initial_eq
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T) (V u v : Real → M → Real)
    (hu : IsHeatPotOn (RealTimeInterval.closed 0 T hT) G V u)
    (hv : IsHeatPotOn (RealTimeInterval.closed 0 T hT) G V v)
    (C : Real)
    (hV : ∀ t ∈ Set.Icc 0 T, ∀ x : M, V t x ≤ C)
    (hinit : ∀ x : M, u 0 x = v 0 x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x = v t x := by
  have huv := heat_pot_comparison (I := I) G hT V u v
    hu.toSubsolution hv.toSupersolution C hV
    (fun x => (hinit x).le)
  have hvu := heat_pot_comparison (I := I) G hT V v u
    hv.toSubsolution hu.toSupersolution C hV
    (fun x => (hinit x).symm.le)
  intro t ht x
  exact le_antisymm (huv t ht x) (hvu t ht x)

theorem heat_comparison
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T) (u v : Real → M → Real)
    (hu : IsHeatOn (RealTimeInterval.closed 0 T hT) G u)
    (hv : IsHeatOn (RealTimeInterval.closed 0 T hT) G v)
    (hinit : ∀ x : M, u 0 x ≤ v 0 x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x ≤ v t x := by
  exact heat_pot_comparison (I := I) G hT (fun _ _ => 0) u v
    hu.toSubsolution hv.toSupersolution 0
    (by simp) hinit

theorem heat_eq_of_initial_eq
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T) (u v : Real → M → Real)
    (hu : IsHeatOn (RealTimeInterval.closed 0 T hT) G u)
    (hv : IsHeatOn (RealTimeInterval.closed 0 T hT) G v)
    (hinit : ∀ x : M, u 0 x = v 0 x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x = v t x := by
  exact heat_pot_eq_of_initial_eq (I := I) G hT (fun _ _ => 0) u v hu hv 0
    (by simp) hinit

end

end DifferentialGeometry.Analysis.Parabolic
