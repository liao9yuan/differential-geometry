import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Vanishing of the chart-basis Lie bracket at the base point

The chart-basis tangent-bundle sections `chartBasisVecFiber x₀ i` (defined in
`Integral.Measure.ChartDensity`) are obtained by transporting a fixed model-space basis
vector through the inverse of the tangent-bundle trivialization centred at `x₀`. On the
base set of that trivialization (which is the chart source `(chartAt H x₀).source`), the
chart pullback of such a section is *constant* — it equals the fixed model-space basis
vector. Consequently the manifold Lie bracket of any two chart-basis sections vanishes at
the base point: these are coordinate vector fields, and coordinate vector fields commute.

This is the chart-coordinate statement `[∂ⱼ, ∂ₖ](x₀) = 0`. It does **not** assert that the
Christoffel symbols vanish, only that the bracket of two coordinate frame fields is zero.

## Main results

* `chartBasisVecFiber_symmL_apply` — on the base set, `chartBasisVecFiber x₀ i x` is the
  image of the model-basis vector under the inverse trivialization `symmL`.
* `chartBasisVecFiber_pullback_eq_const` — the chart pullback of `chartBasisVecFiber x₀ i`
  through `(extChartAt I x₀).symm` is eventually constant near `extChartAt I x₀ x₀`.
* `mlieBracket_chartBasisVec_self_eq_zero` — the manifold Lie bracket of two chart-basis
  sections vanishes at the base point.

The construction mirrors `DifferentialGeometry.Coordinates.coordinateFrameAt_bracket_zero`
in `Coordinates.CoordinateFrame`, specialised to the `chartBasisVecFiber` carrier used by
the chart-Riemann bridge.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The base set of the tangent-bundle trivialization at `x₀` is the chart source. -/
private lemma chartBasis_baseSet_eq_chartSource (x₀ : M) :
    (trivializationAt E (TangentSpace I) x₀).baseSet = (chartAt H x₀).source := by
  rfl

/-- On the base set, the chart-basis fiber vector is the inverse trivialization `symmL`
applied to the fixed model-basis vector. This rewrites the bare `Trivialization.symm`
appearing in the definition of `chartBasisVecFiber` into the continuous-linear `symmL`
form, which `TangentBundle.symmL_trivializationAt` identifies with a chart derivative. -/
private lemma chartBasisVecFiber_symmL_apply (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    chartBasisVecFiber (I := I) x₀ i x =
      (trivializationAt E (TangentSpace I) x₀).symmL ℝ x ((chartModelBasis E) i) := by
  rw [Trivialization.symmL_apply]
  rfl

/-- On the chart domain, the chart-basis section is the derivative of `(extChartAt I x₀).symm`
applied to the fixed model-space basis vector. This is the analogue of
`Coordinates.coordinateFrameAt_apply_of_mem` for the `chartBasisVecFiber` carrier. -/
private lemma chartBasisVecFiber_apply_of_mem {x₀ x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := I) x₀ i x =
      (mfderiv[Set.range I] (extChartAt I x₀).symm (extChartAt I x₀ x))
        ((chartModelBasis E) i) := by
  have hx_src : x ∈ (chartAt H x₀).source := by
    rwa [chartBasis_baseSet_eq_chartSource (I := I) x₀] at hx
  rw [chartBasisVecFiber_symmL_apply (I := I) x₀ i x]
  exact congrArg (fun L : E →L[ℝ] TangentSpace I x => L ((chartModelBasis E) i))
    (TangentBundle.symmL_trivializationAt (I := I) (𝕜 := ℝ) hx_src)

/-- The chart pullback of the chart-basis section through `(extChartAt I x₀).symm` is
eventually equal, near `extChartAt I x₀ x₀`, to the constant model-space basis vector.
This expresses that `chartBasisVecFiber x₀ i` is a coordinate vector field. -/
private lemma chartBasisVecFiber_pullback_eq_const (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm
        (chartBasisVecFiber (I := I) x₀ i) (Set.range I)
      =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        fun _ : E => ((chartModelBasis E) i : E) := by
  haveI : IsManifold I (1 : WithTop ℕ∞) M :=
    IsManifold.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
  simp only [VectorField.mpullbackWithin_apply]
  have hy_src : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x₀).map_target hy
  have hy_base : (extChartAt I x₀).symm y ∈
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rwa [chartBasis_baseSet_eq_chartSource (I := I) x₀]
  rw [chartBasisVecFiber_apply_of_mem (I := I) hy_base i]
  rw [(extChartAt I x₀).right_inv hy]
  exact ContinuousLinearMap.IsInvertible.inverse_apply_self
    (isInvertible_mfderivWithin_extChartAt_symm (I := I) hy)
    ((chartModelBasis E) i)

/-- The Lie bracket within a set of two constant model-space vector fields vanishes. -/
private lemma lieBracketWithin_const_const {s : Set E} {x v w : E} :
    VectorField.lieBracketWithin ℝ (fun _ : E => v) (fun _ : E => w) s x = 0 := by
  simp [VectorField.lieBracketWithin]

/-- **Chart-basis bracket vanishing at the base point.**

The manifold Lie bracket of two chart-basis sections `chartBasisVecFiber x₀ j` and
`chartBasisVecFiber x₀ k` vanishes at the base point `x₀`: these are coordinate vector
fields, so they commute. This is the chart-coordinate statement `[∂ⱼ, ∂ₖ](x₀) = 0`. It is
the input that lets the section-level Riemann formula `riemannSec` drop its
`∇_{[X, Y]} Z` correction term when `X, Y` are chart-basis sections extending the canonical
model basis at `x₀`.

No Christoffel-vanishing claim is made here. -/
theorem mlieBracket_chartBasisVec_self_eq_zero (x₀ : M)
    (j k : Fin (Module.finrank ℝ E)) :
    VectorField.mlieBracket I
        (chartBasisVecFiber (I := I) x₀ j)
        (chartBasisVecFiber (I := I) x₀ k) x₀ = 0 := by
  rw [← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_apply]
  have hleft :
      VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm
          (chartBasisVecFiber (I := I) x₀ j) (Set.range I)
        =ᶠ[𝓝[(extChartAt I x₀).symm ⁻¹' Set.univ ∩ Set.range I]
            (extChartAt I x₀ x₀)]
          fun _ : E => ((chartModelBasis E) j : E) := by
    simpa using chartBasisVecFiber_pullback_eq_const (I := I) x₀ j
  have hright :
      VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm
          (chartBasisVecFiber (I := I) x₀ k) (Set.range I)
        =ᶠ[𝓝[(extChartAt I x₀).symm ⁻¹' Set.univ ∩ Set.range I]
            (extChartAt I x₀ x₀)]
          fun _ : E => ((chartModelBasis E) k : E) := by
    simpa using chartBasisVecFiber_pullback_eq_const (I := I) x₀ k
  rw [Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem hleft hright (by simp)]
  rw [lieBracketWithin_const_const]
  exact ContinuousLinearMap.map_zero _

end Connection
end Integral
end DifferentialGeometry
