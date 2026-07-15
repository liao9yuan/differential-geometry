import DifferentialGeometry.Geometry.Metric.TensorInner.MetricGeodesicSpray

set_option autoImplicit false

/-!
# Convergence of normal-coordinate geodesic data

This file is the geometric specialization layer between converging coordinate
metrics and the generic ODE stability API.  The first result exposes convergence
of the corresponding proof-independent geodesic sprays.
-/

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [CompleteSpace E] [FiniteDimensional Real E]

/-- Smooth compact-open convergence of coercive normal-coordinate metrics
implies smooth compact-open convergence of their geodesic sprays. -/
theorem normalGeodesicSpray_conv
    {U : Set E} (hU : IsOpen U)
    {g : ℕ → E → E →L[Real] E →L[Real] Real}
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hg_cd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (g n) U)
    (hgInf_cd : ContDiffOn Real (∞ : WithTop ℕ∞) gInf U)
    (hg_co : ∀ n x, x ∈ U → IsCoercive (g n x))
    (hgInf_co : ∀ x, x ∈ U → IsCoercive (gInf x))
    (hg_conv : MapCInfConvOnCompacts U g gInf) :
    MapCInfConvOnCompacts (U ×ˢ Set.univ)
      (fun n => MetricKoszul.metricSpray (g n))
      (MetricKoszul.metricSpray gInf) :=
  MetricKoszul.metricSpray_conv hU hg_cd hgInf_cd hg_co hgInf_co hg_conv

end HCGCompactness
end DifferentialGeometry
