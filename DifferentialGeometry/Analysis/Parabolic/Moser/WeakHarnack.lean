import DifferentialGeometry.Analysis.Parabolic.Moser.Crossover
import DifferentialGeometry.Analysis.Parabolic.Moser.LocalBoundedness
import DifferentialGeometry.Analysis.Parabolic.Moser.ReverseHolder

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem weak_harnack_of_localized_crossover
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p a τ t₁ A C : ℝ} (hp : 2 ≤ p) (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun s => u s x) t)
    (hcrossover :
      A * moserLocalizedMass (I := I) (M := M) (Module.finrank ℝ E) rho
          (fun s y => (u s y)⁻¹) p a τ t₁ 0 ≤ C) :
    ∀ t ∈ Ioo τ t₁, ∀ x : M, 1 < rho.toFun x →
      A ^ (1 / p) ≤
        C ^ (1 / p) *
          moserLocalBoundFactor (I := I) (M := M) g hdim rho p a τ t₁ * u t x := by
  let D := moserLocalizedMass (I := I) (M := M) (Module.finrank ℝ E) rho
    (fun s y => (u s y)⁻¹) p a τ t₁ 0
  let B := moserLocalBoundFactor (I := I) (M := M) g hdim rho p a τ t₁
  have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hD : 0 ≤ D := by
    exact moserLocalizedMass_nonneg (I := I) (M := M) (Module.finrank ℝ E) rho
      (fun s y => (u s y)⁻¹) haτ hτt₁ (fun s y => (inv_pos.mpr (hpos s y)).le) 0
  have hB : 0 ≤ B := (Real.exp_pos _).le
  intro t ht x hx
  have hreciprocal := reciprocal_local_boundedness_of_supersolution
    (I := I) (M := M) g hdim rho u hu hpos hp haτ hτt₁ hpde t ht x hx
  have hreciprocal' :
      (u t x)⁻¹ ≤ B * D ^ (1 / p) := by
    simpa only [moserLocalBound, moserNormalizedMass,
      parabolicMoserExponent_zero, D, B] using hreciprocal
  simpa only [D, B, mul_assoc] using
    weak_harnack_of_crossover (hpos t x) hA hD hB hC hp_pos
      hcrossover hreciprocal'

end DifferentialGeometry.Analysis.Parabolic.Moser

end
