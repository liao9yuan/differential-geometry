import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Manifold
import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.LiftedMetricSmoothness
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Basic

/-!
# Chart-pullback naturality of `chartBasisVecFiber` under the universal cover

The chart-local frame vectors `chartBasisVecFiber α' i x'` on the universal
cover identify, under the projection `proj : UC M → M`, with the chart-local
frame vectors on the base manifold at the projected points.

Concretely, for `x' ∈ (coverChartAt α').source`,
```
chartBasisVecFiber α' i x' = chartBasisVecFiber (proj α') i (proj x')
```
viewed through the definitional identification
`TangentSpace I x' = E = TangentSpace I (proj x')`.

The proof unfolds `chartBasisVecFiber` to the inverse tangent trivialisation
applied to the fixed model-space basis vector, rewrites both sides through
`TangentBundle.symmL_trivializationAt_eq_core`, and concludes by
`uc_tangentBundleCore_coordChange_agree`.
-/

open Set Function Filter
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Integral.Measure
  (SmoothRiemannianMetric chartBasisVecFiber chartModelBasis)

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]

/-- **`chartBasisVecFiber` is natural under universal-cover projection.**

For any chart anchor `α' : UC M`, basis index `i`, and cover-point
`x' ∈ (chartAt H α').source` (equivalently `x' ∈ (coverChartAt α').source`,
since `chartAt H α' = coverChartAt α'` by the universal-cover charted-space
instance), the cover-side chart-basis fibre vector at `x'` (defined via the
inverse tangent trivialisation centred at `α'`) identifies with the
base-side chart-basis fibre vector at `proj x'` (defined via the inverse
tangent trivialisation centred at `proj α'`), through the definitional
identification of the tangent fibres with `E`.

Proof. Both sides unfold to `triv.symmL ℝ x (chartModelBasis E i)`,
the difference being whether `triv` is `trivializationAt E (TangentSpace I)`
on `UC M` (with base point `α'`, fibre point `x'`) or on `M` (with base
point `proj α'`, fibre point `proj x'`). On the chart source, the
membership hypothesis unfolds, via `coverChartAt_source_eq`, to give in
particular `proj x' ∈ (chartAt H (proj α')).source`. By
`TangentBundle.symmL_trivializationAt_eq_core`, each side equals the
corresponding `tangentBundleCore.coordChange` evaluated at the chart-source
membership; by `uc_tangentBundleCore_coordChange_agree`, the cover-side
`coordChange` agrees with the base-side `coordChange` at the projected
point. The result follows by applying both sides to `chartModelBasis E i`.
-/
theorem chartBasisVecFiber_lifted
    (g : SmoothRiemannianMetric I M)
    (α' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (i : Fin (Module.finrank ℝ E))
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (hx' : x' ∈ (chartAt H α').source) :
    chartBasisVecFiber (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        α' i x' =
      chartBasisVecFiber (I := I) (M := M)
        (proj (X := M) α') i (proj (X := M) x') := by
  let _ := g  -- suppress unused-variable warning
  -- The membership in `(chartAt H α').source` is the same as in
  -- `(coverChartAt α').source` by the charted-space instance.
  have hx'_cover : x' ∈ (coverChartAt α').source := hx'
  -- Unpack the source structure to extract `proj x' ∈ (chartAt H (proj α')).source`.
  have hx'_inter : x' ∈ (localSection (M := M) α').source ∩
      (localSection (M := M) α') ⁻¹' (chartAt H (proj α')).source := by
    have hsrc : ((coverChartAt α') :
        OpenPartialHomeomorph
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H).source
        = (localSection α').source ∩
          (localSection α') ⁻¹' (chartAt H (proj α')).source :=
      coverChartAt_source_eq α'
    rw [hsrc] at hx'_cover; exact hx'_cover
  obtain ⟨_hLSsrc, hLSchart⟩ := hx'_inter
  -- `localSection α' x' = proj x'`, so `proj x' ∈ (chartAt H (proj α')).source`.
  have hLS_x' : (localSection α') x' = proj x' := by
    have := congrArg (fun f => f x') (proj_eq_localSection α')
    simpa using this.symm
  have hprojx'_chartM : proj x' ∈ (chartAt H (proj α')).source := by
    rw [Set.mem_preimage, hLS_x'] at hLSchart
    exact hLSchart
  -- Replace `.symm` by `.symmL ℝ _` on both sides (definitional equality from
  -- the `@[simps -fullyApplied apply]` attribute on `symmL`).
  have hLHS_symm :
      chartBasisVecFiber (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          α' i x'
        = (trivializationAt E (TangentSpace I :
            DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
              → Type _) α').symmL ℝ x' (chartModelBasis E i) := by
    change (trivializationAt E (TangentSpace I :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
          → Type _) α').symm x' (chartModelBasis E i)
      = (trivializationAt E (TangentSpace I :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
            → Type _) α').symmL ℝ x' (chartModelBasis E i)
    rw [Bundle.Trivialization.symmL_apply]
  have hRHS_symm :
      chartBasisVecFiber (I := I) (M := M)
          (proj (X := M) α') i (proj (X := M) x')
        = (trivializationAt E (TangentSpace I : M → Type _)
            (proj α')).symmL ℝ (proj x') (chartModelBasis E i) := by
    change (trivializationAt E (TangentSpace I : M → Type _) (proj α')).symm
        (proj x') (chartModelBasis E i)
      = (trivializationAt E (TangentSpace I : M → Type _)
          (proj α')).symmL ℝ (proj x') (chartModelBasis E i)
    rw [Bundle.Trivialization.symmL_apply]
  rw [hLHS_symm, hRHS_symm]
  -- Both sides are now `triv.symmL ℝ b (chartModelBasis E i)`. Rewrite via
  -- the `_eq_core` lemma on each side and apply
  -- `uc_tangentBundleCore_coordChange_agree`.
  have hSymmL :
      ((trivializationAt E (TangentSpace I :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
            → Type _) α').symmL ℝ x' : E →L[ℝ] E)
        = ((trivializationAt E (TangentSpace I : M → Type _)
            (proj α')).symmL ℝ (proj x') : E →L[ℝ] E) := by
    rw [TangentBundle.symmL_trivializationAt_eq_core (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (b₀ := α') (b := x') hx',
        TangentBundle.symmL_trivializationAt_eq_core (I := I) (M := M)
          (b₀ := proj α') (b := proj x') hprojx'_chartM]
    -- Now both sides are tangent-bundle coordChanges; apply the agree lemma.
    exact uc_tangentBundleCore_coordChange_agree (I := I) α' x'
      ⟨hx', mem_chart_source H x'⟩
  -- Apply the equality of continuous linear maps to the model-basis vector.
  have hAt := congrArg (fun L : E →L[ℝ] E => L (chartModelBasis E i)) hSymmL
  -- The fibre-type identification `TangentSpace I x' = E` is definitional,
  -- and the resulting equation lives in `E`; we just hand it over.
  exact hAt

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
