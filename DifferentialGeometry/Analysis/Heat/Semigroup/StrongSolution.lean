import DifferentialGeometry.Analysis.Heat.Semigroup.MildSolutionPDE
import DifferentialGeometry.Analysis.Heat.Smoothing.SmoothingOfClosed

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

def IsStrongSolutionAt
    (g : SmoothRiemannianMetric I M)
    (u f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (t : ℝ) : Prop :=
  ∃ u_h : laplacianDomain (I := I) (M := M) g,
    H1ComplToLp (I := I) (M := M) g (u_h : H1Compl g) = u t ∧
      HasDerivAt u (laplacianOp (I := I) (M := M) g u_h + f t) t

def IsStrongSolutionOn
    (g : SmoothRiemannianMetric I M)
    (u f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (s : Set ℝ) : Prop :=
  ∀ t ∈ s, IsStrongSolutionAt (I := I) (M := M) g u f t

theorem mildSolution_hasDerivAt_laplacianOp_add_of_lift
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) {t : ℝ} (ht : 0 < t)
    {v : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hderiv : HasDerivAt (mildSolution (I := I) (M := M) g u_0 f) v t)
    (u_h : laplacianDomain (I := I) (M := M) g)
    (hu_h : H1ComplToLp (I := I) (M := M) g (u_h : H1Compl g) =
      mildSolution (I := I) (M := M) g u_0 f t) :
    HasDerivAt (mildSolution (I := I) (M := M) g u_0 f)
      (laplacianOp (I := I) (M := M) g u_h + f t) t := by
  have hv : v = laplacianOp (I := I) (M := M) g u_h + f t := by
    set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
    apply b.repr.injective
    ext i
    rw [b.repr_apply_apply, b.repr_apply_apply]
    have hinner : HasDerivAt
        (fun s : ℝ => ⟪b i, mildSolution (I := I) (M := M) g u_0 f s⟫_ℝ)
        ⟪b i, v⟫_ℝ t := by
      have hcomp := (innerSL (𝕜 := ℝ)
        (E := Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
        (b i)).hasFDerivAt.comp_hasDerivAt t hderiv
      simpa [Function.comp_def, innerSL_apply_apply] using hcomp
    have hmodal := hasDerivAt_mildSolution_inner_basis
      (I := I) (M := M) g u_0 hf ht i
    have hcoeff := hinner.unique hmodal
    rw [inner_add_right,
      laplacianOp_inner_eigenbasis (I := I) (M := M) g u_h i,
      hu_h]
    exact hcoeff
  simpa [hv] using hderiv

theorem mildSolution_isStrongSolutionAt_of_differentiable
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) {t : ℝ} (ht : 0 < t)
    (hdiff : DifferentiableAt ℝ (mildSolution (I := I) (M := M) g u_0 f) t)
    (u_h : laplacianDomain (I := I) (M := M) g)
    (hu_h : H1ComplToLp (I := I) (M := M) g (u_h : H1Compl g) =
      mildSolution (I := I) (M := M) g u_0 f t) :
    IsStrongSolutionAt (I := I) (M := M) g
      (mildSolution (I := I) (M := M) g u_0 f) f t := by
  refine ⟨u_h, hu_h, ?_⟩
  exact mildSolution_hasDerivAt_laplacianOp_add_of_lift
    (I := I) (M := M) g u_0 hf ht hdiff.hasDerivAt u_h hu_h

theorem heatSemigroup_isStrongSolutionAt
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {t : ℝ} (ht : 0 < t) :
    IsStrongSolutionAt (I := I) (M := M) g
      (fun s : ℝ => heatSemigroup (I := I) (M := M) g s u_0)
      (fun _ => 0) t := by
  let u_h : laplacianDomain (I := I) (M := M) g :=
    ⟨heatSemigroupExplicitLift (I := I) (M := M) g 0 t u_0,
      heatSemigroupExplicitLift_zero_mem_laplacianDomain
        (I := I) (M := M) g t u_0⟩
  refine ⟨u_h, ?_, ?_⟩
  · exact H1ComplToLp_heatSemigroupExplicitLift (I := I) (M := M) g 0 ht u_0
  · simpa [u_h] using
      hasDerivAt_heatSemigroup_eq_laplacianOp (I := I) (M := M) g ht u_0

theorem heatSemigroup_isStrongSolutionOn
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    IsStrongSolutionOn (I := I) (M := M) g
      (fun s : ℝ => heatSemigroup (I := I) (M := M) g s u_0)
      (fun _ => 0) (Set.Ioi 0) := by
  intro t ht
  exact heatSemigroup_isStrongSolutionAt (I := I) (M := M) g u_0 ht

theorem mildSolution_zero_forcing_isStrongSolutionAt
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {t : ℝ} (ht : 0 < t) :
    IsStrongSolutionAt (I := I) (M := M) g
      (mildSolution (I := I) (M := M) g u_0 (fun _ => 0))
      (fun _ => 0) t := by
  have hpath : mildSolution (I := I) (M := M) g u_0 (fun _ => 0) =
      fun s => heatSemigroup (I := I) (M := M) g s u_0 := by
    funext s
    exact mildSolution_zero_forcing (I := I) (M := M) g u_0 s
  rw [hpath]
  exact heatSemigroup_isStrongSolutionAt (I := I) (M := M) g u_0 ht

theorem mildSolution_zero_forcing_isStrongSolutionOn
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    IsStrongSolutionOn (I := I) (M := M) g
      (mildSolution (I := I) (M := M) g u_0 (fun _ => 0))
      (fun _ => 0) (Set.Ioi 0) := by
  intro t ht
  exact mildSolution_zero_forcing_isStrongSolutionAt
    (I := I) (M := M) g u_0 ht

end HeatEquation
end Analysis
end DifferentialGeometry

end
