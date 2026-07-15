import DifferentialGeometry.Analysis.Calculus.MapConvergence
import Mathlib.Analysis.ODE.Basic

set_option autoImplicit false

/-!
# Compact-open C∞ stability for ODE endpoints

This module records the analysis-layer endpoint needed to pass compact-open
`C∞` convergence of time-dependent vector fields and initial data to selected
solution families at a fixed terminal time.  It is independent of metrics,
normal coordinates, and Ricci-flow compactness data.
-/

namespace DifferentialGeometry
namespace HCGCompactness

open scoped ContDiff

/-- `C∞` stability, in the initial parameter, of selected solutions of
a time-dependent ODE on a common compact time interval. -/
theorem MapCInfConvOnCompacts.ode_solutionAt
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {A : Set P} {J : Set ℝ} {V : Set X}
    (hA : IsOpen A)
    (hJ : IsOpen J)
    (hV : IsOpen V)
    {t₀ t₁ : ℝ}
    (ht₀₁ : t₀ ≤ t₁)
    (hI : Set.Icc t₀ t₁ ⊆ J)
    {v : ℕ → ℝ → X → X}
    {vInf : ℝ → X → X}
    (hv_cd :
      ∀ n, ContDiffOn ℝ ∞
        (fun q : ℝ × X => v n q.1 q.2) (J ×ˢ V))
    (hvInf_cd :
      ContDiffOn ℝ ∞
        (fun q : ℝ × X => vInf q.1 q.2) (J ×ˢ V))
    (hv_conv :
      MapCInfConvOnCompacts (J ×ˢ V)
        (fun n q => v n q.1 q.2)
        (fun q => vInf q.1 q.2))
    {a : ℕ → P → X}
    {aInf : P → X}
    (ha_cd : ∀ n, ContDiffOn ℝ ∞ (a n) A)
    (haInf_cd : ContDiffOn ℝ ∞ aInf A)
    (ha_conv : MapCInfConvOnCompacts A a aInf)
    {γ : ℕ → P → ℝ → X}
    {γInf : P → ℝ → X}
    (hγ :
      ∀ n p, p ∈ A →
        γ n p t₀ = a n p ∧
        IsIntegralCurveOn
          (γ n p) (v n) (Set.Icc t₀ t₁))
    (hγInf :
      ∀ p, p ∈ A →
        γInf p t₀ = aInf p ∧
        IsIntegralCurveOn
          (γInf p) vInf (Set.Icc t₀ t₁))
    (hstayInf :
      ∀ p ∈ A, ∀ t ∈ Set.Icc t₀ t₁,
        γInf p t ∈ V) :
    MapCInfConvOnCompacts A
      (fun n p => γ n p t₁)
      (fun p => γInf p t₁) := by
  sorry

end HCGCompactness
end DifferentialGeometry
