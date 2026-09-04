import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CGT

/-- A short scale with strict core, fence, and curvature budgets. -/
theorem exists_short_scale
    {R a K : Real} (h4aR : 4 * a < R)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2) :
    ∃ L : Real,
      2 * a < L ∧
      a + L < 3 * R / 4 ∧
      K * L ^ 2 < (Real.pi / 2) ^ 2 := by
  let cap : Real := 3 * R / 4 - a
  have h2aCap : 2 * a < cap := by
    dsimp only [cap]
    linarith
  have hcont :
      Continuous (fun L : Real => K * L ^ 2) :=
    continuous_const.mul (continuous_id.pow 2)
  have hcurv :
      ∀ᶠ L in 𝓝 (2 * a), K * L ^ 2 < (Real.pi / 2) ^ 2 :=
    hcont.continuousAt (Iio_mem_nhds hsmall)
  have hcurvGT :
      ∀ᶠ L in 𝓝[>] (2 * a), K * L ^ 2 < (Real.pi / 2) ^ 2 :=
    hcurv.filter_mono inf_le_left
  have hwindow :
      ∀ᶠ L in 𝓝[>] (2 * a), L ∈ Set.Ioo (2 * a) cap :=
    Ioo_mem_nhdsGT h2aCap
  obtain ⟨L, hcurvL, hL, hLcap⟩ :=
    (hcurvGT.and hwindow).exists
  refine ⟨L, hL, ?_, hcurvL⟩
  dsimp only [cap] at hLcap
  linarith

end CGT
end Riemannian
end Geometry
end DifferentialGeometry
