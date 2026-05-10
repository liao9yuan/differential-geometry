import RicciFlower.Analysis.Measure
import DifferentialGeometry.Integral.DivergenceTheorem.Green

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RicciFlower
namespace Analysis
namespace Green

noncomputable section

open DifferentialGeometry.Integral.DivergenceTheorem
open MeasureTheory
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Gradient for the metric selected by a realized metric family at a time. -/
abbrev gradientAt [I.Boundaryless] [T2Space M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Time) (t : Time)
    {f : M → Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  grad_g (I := I) (Measure.metricForMeasure (I := I) (M := M) (G.metric t)) hf

/-- Laplacian for the metric selected by a realized metric family at a time. -/
abbrev laplacianAt [I.Boundaryless] [T2Space M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Time) (t : Time)
    {f : M → Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f) :
    M → Real :=
  Δ_g (I := I) (M := M) (Measure.metricForMeasure (I := I) (M := M) (G.metric t)) hf

theorem integration_by_parts_at
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Time) (t : Time)
    {f : M → Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (hX : HasCompactSupport X) :
    ∫ x, tangentSectionAction (I := I) X f x
        ∂(Measure.volumeMeasureAt (I := I) (M := M) G t)
      =
      -∫ x, f x * divergence_g (I := I)
        (Measure.metricForMeasure (I := I) (M := M) (G.metric t)) X x
        ∂(Measure.volumeMeasureAt (I := I) (M := M) G t) := by
  simpa [Measure.volumeMeasureAt] using
    (integral_tangentSectionAction_eq_neg_integral_smul_divergence
      (I := I) (M := M) (Measure.metricForMeasure (I := I) (M := M) (G.metric t))
      hf X hX)

theorem green_first_identity_at
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Time) (t : Time)
    {f h : M → Real}
    (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (hh : ContMDiff I 𝓘(Real, Real) ∞ h)
    (hh_supp : HasCompactSupport h) :
    ∫ x, (Measure.metricForMeasure (I := I) (M := M) (G.metric t)).inner x
        (gradientAt (I := I) (M := M) G t hf x)
        (gradientAt (I := I) (M := M) G t hh x)
        ∂(Measure.volumeMeasureAt (I := I) (M := M) G t)
      =
      -∫ x, f x * laplacianAt (I := I) (M := M) G t hh x
        ∂(Measure.volumeMeasureAt (I := I) (M := M) G t) := by
  simpa [Measure.volumeMeasureAt, gradientAt, laplacianAt] using
    (integral_inner_grad_eq_neg_integral_smul_laplacian
      (I := I) (M := M) (Measure.metricForMeasure (I := I) (M := M) (G.metric t))
      hf hh hh_supp)

theorem green_second_identity_at
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Time) (t : Time)
    {f h : M → Real}
    (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (hh : ContMDiff I 𝓘(Real, Real) ∞ h) :
    ∫ x, (f x * laplacianAt (I := I) (M := M) G t hh x
          - h x * laplacianAt (I := I) (M := M) G t hf x)
        ∂(Measure.volumeMeasureAt (I := I) (M := M) G t) = 0 := by
  simpa [Measure.volumeMeasureAt, laplacianAt] using
    (integral_smul_laplacian_sub_eq_zero
      (I := I) (M := M) (Measure.metricForMeasure (I := I) (M := M) (G.metric t))
      hf hh)

theorem integral_laplacianAt_eq_zero
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Time) (t : Time)
    {f : M → Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f) :
    ∫ x, laplacianAt (I := I) (M := M) G t hf x
        ∂(Measure.volumeMeasureAt (I := I) (M := M) G t) = 0 := by
  let hconst : ContMDiff I 𝓘(Real, Real) ∞ (fun _ : M => (1 : Real)) :=
    contMDiff_const
  have hgreen := green_second_identity_at (I := I) (M := M) G t hconst hf
  have hzero : ∀ x : M,
      laplacianAt (I := I) (M := M) G t hconst x = 0 := by
    intro x
    simpa [laplacianAt] using
      (Δ_g_const (I := I)
        (Measure.metricForMeasure (I := I) (M := M) (G.metric t)) (1 : Real) x)
  calc
    ∫ x, laplacianAt (I := I) (M := M) G t hf x
        ∂(Measure.volumeMeasureAt (I := I) (M := M) G t)
        =
      ∫ x, ((1 : Real) * laplacianAt (I := I) (M := M) G t hf x -
            f x * laplacianAt (I := I) (M := M) G t hconst x)
        ∂(Measure.volumeMeasureAt (I := I) (M := M) G t) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            change laplacianAt (I := I) (M := M) G t hf x =
              (1 : Real) * laplacianAt (I := I) (M := M) G t hf x -
                f x * laplacianAt (I := I) (M := M) G t hconst x
            rw [hzero x]
            ring
    _ = 0 := hgreen

end

end Green
end Analysis
end RicciFlower
