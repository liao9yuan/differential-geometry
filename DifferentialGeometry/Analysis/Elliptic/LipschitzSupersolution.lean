import DifferentialGeometry.Analysis.Elliptic.WeakLaplacian
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Lipschitz

open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace IsLapLEDistribOn

/-- A distributional Laplacian upper bound for an intrinsic-Lipschitz function
gives the corresponding first-order energy lower bound against smooth
nonnegative compactly supported tests. -/
theorem neg_int_le_energy
    (g : SmoothRiemannianMetric I M)
    {u b : M → Real} {U : Set M} {L : NNReal}
    (h : IsLapLEDistribOn (I := I) g u b U)
    (hu : ∀ x y, edist (u x) (u y) ≤ (L : ENNReal) *
      riemannianEDistOf (I := I) g x y)
    (φ : C^∞⟮I, M; Real⟯)
    (hφ : φ ∈ compactlySupportedSmoothFunctions I M)
    (hφU : tsupport (φ : M → Real) ⊆ U)
    (hφ0 : ∀ x : M, 0 ≤ φ x) :
    -(∫ x, b x * φ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
      ∫ x, tangentSectionAction (I := I) (grad_g (I := I) g φ) u x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hgrad_cs : HasCompactSupport
      (grad_g (I := I) g φ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :=
    hasCompactSupport_grad_g (I := I) g φ hφ
  have hgreen := (lip_green_comp (I := I) g
    (grad_g (I := I) g φ) hgrad_cs hu).2
  calc
    -(∫ x, b x * φ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
        -(∫ x, u x * Δ_g (I := I) g φ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) :=
      neg_le_neg (h.test_le φ hφ hφU hφ0)
    _ = ∫ x, tangentSectionAction (I := I) (grad_g (I := I) g φ) u x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      simpa only [Δ_g_def] using hgreen.symm

/-- A nonpositive distributional Laplacian gives nonnegative first-order
energy against smooth nonnegative compactly supported tests. -/
theorem lip_energy_nonneg
    (g : SmoothRiemannianMetric I M)
    {u : M → Real} {U : Set M} {L : NNReal}
    (h : IsLapLEDistribOn (I := I) g u (fun _ ↦ 0) U)
    (hu : ∀ x y, edist (u x) (u y) ≤ (L : ENNReal) *
      riemannianEDistOf (I := I) g x y)
    (φ : C^∞⟮I, M; Real⟯)
    (hφ : φ ∈ compactlySupportedSmoothFunctions I M)
    (hφU : tsupport (φ : M → Real) ⊆ U)
    (hφ0 : ∀ x : M, 0 ≤ φ x) :
    0 ≤ ∫ x, tangentSectionAction (I := I) (grad_g (I := I) g φ) u x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  simpa only [zero_mul, integral_zero, neg_zero] using
    h.neg_int_le_energy (I := I) g hu φ hφ hφU hφ0

end IsLapLEDistribOn
end DifferentialGeometry
