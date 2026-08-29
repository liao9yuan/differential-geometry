import DifferentialGeometry.Geometry.Comparison.BusemannLaplacian
import DifferentialGeometry.Geometry.Comparison.BusemannLine

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold

namespace DifferentialGeometry

open Geometry.Curvature
open Geometry.Riemannian
open Geometry.Riemannian.BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
/-- The sum of the two Busemann functions determined by a minimizing line has
nonpositive distributional Laplacian under nonnegative Ricci curvature. -/
theorem buse_pair_lap
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 0 < Module.finrank ℝ E - 1)
    (hRic : RicciBoundedBelow (I := I) g 0) :
    IsLapLEDistribOn (I := I) g
      (fun x : M ↦ busemann (I := I) γ x +
        busemann (I := I) (fun t : ℝ ↦ γ (-t)) x)
      (fun _ : M ↦ 0) univ := by
  have hpos := busemann_lap (I := I) g hEnorm hγ.pos_ray hd hRic
  have hneg := busemann_lap (I := I) g hEnorm hγ.neg_ray hd hRic
  have hsum := hpos.add hneg
  have hu :
      busemann (I := I) γ + busemann (I := I) (fun t : ℝ ↦ γ (-t)) =
        fun x : M ↦ busemann (I := I) γ x +
          busemann (I := I) (fun t : ℝ ↦ γ (-t)) x := by
    funext x
    simp only [Pi.add_apply]
  have hz :
      ((fun _ : M ↦ (0 : ℝ)) + fun _ : M ↦ (0 : ℝ)) =
        fun _ : M ↦ (0 : ℝ) := by
    funext x
    simp only [Pi.add_apply, zero_add]
  rw [hu, hz] at hsum
  exact hsum

end DifferentialGeometry
