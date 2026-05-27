import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Manifold
import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.LiftedMetricSmoothness
import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Riemannian
import DifferentialGeometry.Integral.Measure.ChartDensity
import DifferentialGeometry.Geometry.Hessian
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
  (SmoothRiemannianMetric chartBasisVecFiber chartModelBasis chartGramMatrix)
open DifferentialGeometry.Integral.DivergenceTheorem
  (chartInvGramMatrix chartGramOnE chartChristoffel partialDeriv)

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
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

/-- **`chartGramMatrix` is natural under universal-cover projection.**

For any chart anchor `α' : UC M`, indices `i j : Fin (finrank ℝ E)`, and a
cover-point `x' ∈ (chartAt H α').source`, the Gram matrix entry of the
lifted metric on the universal cover equals the corresponding entry of
the base-side Gram matrix at the projected points.

Proof. Both sides unfold via `chartGramMatrix_apply` (a `rfl`-style simp
lemma) to inner products of the chart-basis fibre vectors. The lifted
metric is defined by `(liftedMetric g).inner x' v w = g.inner (proj x') v w`
(definitional from the `liftedMetric` `def`), and
`chartBasisVecFiber_lifted` identifies the cover-side basis fibre vector
at `x'` with the base-side one at `proj x'` (through the definitional
identification of the tangent fibre with `E`). Combining these three
rewrites yields the claim. -/
theorem chartGramMatrix_lifted
    (g : SmoothRiemannianMetric I M)
    (α' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (i j : Fin (Module.finrank ℝ E))
    (hx' : x' ∈ (chartAt H α').source) :
    chartGramMatrix
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' x' i j =
      chartGramMatrix (M := M) g
        (proj (X := M) α') (proj (X := M) x') i j := by
  -- Unfold both sides via the `rfl`-style `chartGramMatrix_apply` simp lemma.
  rw [DifferentialGeometry.Integral.Measure.chartGramMatrix_apply
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' x' i j,
      DifferentialGeometry.Integral.Measure.chartGramMatrix_apply
        (I := I) (M := M) g (proj α') (proj x') i j]
  -- Rewrite the two cover-side chart-basis fibre vectors at `x'` via the
  -- proven naturality lemma, replacing them by the base-side fibre vectors
  -- at `proj x'`.
  rw [chartBasisVecFiber_lifted (I := I) (M := M) g α' i x' hx',
      chartBasisVecFiber_lifted (I := I) (M := M) g α' j x' hx']
  -- The remaining equality is the defining identity of the lifted inner
  -- product: `(liftedMetric g).inner x' v w = g.inner (proj x') v w` is
  -- `rfl` from the `liftedMetric` `def`.
  rfl

/-- **Chart-basepoint coordinate identity under the universal cover.**

For any cover-point `x' ∈ (chartAt H α').source`, the extended-chart
coordinate of `x'` in the cover-chart at `α'` agrees with the
extended-chart coordinate of `proj x'` in the base-chart at `proj α'`.
Direct consequence of `uc_coverChartAt_extend_conjugacy` applied
pointwise at `x'`, identifying `extChartAt I α' = (coverChartAt α').extend I`
and using `localSection α' x' = proj x'`. -/
lemma extChartAt_proj_eq
    (α' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    extChartAt I α' x' = extChartAt I (proj (X := M) α') (proj (X := M) x') := by
  -- `extChartAt I α' = (coverChartAt α').extend I` by the charted-space instance,
  -- and `extChartAt I (proj α') = (chartAt H (proj α')).extend I` by definition.
  have hConj := (uc_coverChartAt_extend_conjugacy (I := I) α').1
  have := congrArg (fun f => f x') hConj
  simp only [Function.comp_apply] at this
  -- `localSection α' x' = proj x'` because `localSection α'` coincides
  -- with `proj` as a function.
  have hLS : (localSection α') x' = proj x' := by
    have := congrArg (fun f => f x') (proj_eq_localSection α')
    simpa using this.symm
  -- Convert through `coverChartAt`'s extend to `extChartAt` and rewrite.
  change ((coverChartAt α').extend I) x' = _ at this
  rw [hLS] at this
  exact this

/-- **`chartChristoffel` is natural under universal-cover projection.**

For any chart anchor `α' : UC M`, lower indices `i j` and upper index `k`,
and a cover-point `x' ∈ (chartAt H α').source`, the chart-coordinate
Christoffel symbol of the lifted metric on the universal cover at the
chart-coordinate of `x'` equals the chart-coordinate Christoffel symbol
of the base metric at the chart-coordinate of `proj x'` in the base chart
at `proj α'`.

Proof outline:

1. By `extChartAt_proj_eq`, the two chart-coordinate base points agree:
   `extChartAt I α' x' = extChartAt I (proj α') (proj x')`. Call the common
   value `y₀`. After this rewrite both sides of the conclusion are evaluated
   at the same `y₀ : E`.

2. Unfolding `chartChristoffel_def`, the `chartInvGramMatrix` factor on each
   side becomes `chartInvGramMatrix (lifted/base metric) anchor manifold-point k l`
   where the manifold point is `(extChartAt I anchor).symm y₀` — which is
   `x'` on the cover side (by `extChartAt_left_inv` on the `coverChartAt`
   source) and `proj x'` on the base side (by `extend_left_inv` on the
   `chartAt H (proj α')` source, with the latter membership extracted from
   the source-structure description `coverChartAt_source_eq`).
   By `chartGramMatrix_lifted` the cover-side Gram matrix at `x'` agrees
   entry-by-entry with the base-side Gram matrix at `proj x'`, so the two
   matrices are equal (Matrix-extensionality) and hence their inverses
   are equal (`congrArg`).

3. For the `partialDeriv` factor, the inner factor `chartGramOnE` on each
   side is a function `E → ℝ`. We show these two functions are eventually
   equal at `y₀` (`=ᶠ[𝓝 y₀]`) by producing an open neighbourhood of `y₀` on
   which the pointwise identity holds — concretely, the neighbourhood is
   carved out by openness of two preimages:
     (a) `(extChartAt I α').symm ⁻¹' (chartAt H α').source` (open by
          continuity of the inverse on its source),
     (b) `(extChartAt I (proj α')).symm ⁻¹' (localSection α').target`
          (open by continuity of the base-side chart inverse plus openness
          of the local-section target).
   On their intersection, the conjugacy identifies the cover-side chart
   inverse with `(localSection α').symm` composed with the base-side chart
   inverse, and `proj ((localSection α').symm w) = w` for `w` in the
   local-section target (via `localSection`-vs-`proj` agreement). The
   pointwise Gram-matrix identity then follows from `chartGramMatrix_lifted`
   applied at the appropriate cover-side point.
   `Filter.EventuallyEq.fderiv_eq` then propagates the equality of
   functions to equality of their Fréchet derivatives at `y₀`, hence
   to equality of `partialDeriv` (which is `fderiv` applied to the model
   basis vector). -/
theorem chartChristoffel_lifted
    (g : SmoothRiemannianMetric I M)
    (α' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (hx' : x' ∈ (chartAt H α').source)
    (i j k : Fin (Module.finrank ℝ E)) :
    chartChristoffel
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' i j k (extChartAt I α' x') =
      chartChristoffel (M := M) g (proj (X := M) α') i j k
        (extChartAt I (proj (X := M) α') (proj (X := M) x')) := by
  classical
  -- Common chart-coordinate base point.
  set y₀ : E := extChartAt I α' x' with hy₀_def
  -- `extChartAt I α' x' = extChartAt I (proj α') (proj x')` (chart-basepoint identity).
  have hy_eq : extChartAt I α' x' = extChartAt I (proj α') (proj x') :=
    extChartAt_proj_eq (I := I) (M := M) α' x'
  -- Rewrite the RHS to also be evaluated at `y₀`.
  rw [show extChartAt I (proj (X := M) α') (proj (X := M) x') = y₀ from hy_eq.symm]
  -- Unfold `chartChristoffel_def` on both sides.
  rw [DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel_def
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) α' i j k y₀,
      DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel_def
        (I := I) (M := M) g (proj α') i j k y₀]
  -- The shared structure is `(1/2) * ∑ l, A k l * B l`. We show pointwise
  -- equality of the summands. Both factors will be shown equal:
  -- (i) the inverse-Gram coefficient `A k l`;
  -- (ii) the partial-derivative bracket `B l`.
  congr 1
  refine Finset.sum_congr rfl ?_
  intro l _
  -- Cover-side manifold point under the chart inverse: it is exactly `x'`.
  have hx'_ext : x' ∈ (extChartAt I α').source := by
    rw [extChartAt_source]; exact hx'
  have hsymm_LHS : (extChartAt I α').symm y₀ = x' := by
    rw [hy₀_def]
    exact (extChartAt I α').left_inv hx'_ext
  -- Base-side: `proj x' ∈ (chartAt H (proj α')).source`, extracted from `hx'`
  -- via the source-structure description.
  have hx'_inter : x' ∈ (localSection (M := M) α').source ∩
      (localSection (M := M) α') ⁻¹' (chartAt H (proj α')).source := by
    have hsrc : ((coverChartAt α') :
        OpenPartialHomeomorph
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H).source
        = (localSection α').source ∩
          (localSection α') ⁻¹' (chartAt H (proj α')).source :=
      coverChartAt_source_eq α'
    have hx'_cover : x' ∈ (coverChartAt α').source := hx'
    rw [hsrc] at hx'_cover; exact hx'_cover
  obtain ⟨hx'_LSsrc, hx'_LSchart⟩ := hx'_inter
  have hLS_x' : (localSection α') x' = proj x' := by
    have := congrArg (fun f => f x') (proj_eq_localSection α')
    simpa using this.symm
  have hproj_x'_chart : proj x' ∈ (chartAt H (proj α')).source := by
    rw [Set.mem_preimage, hLS_x'] at hx'_LSchart
    exact hx'_LSchart
  have hproj_x'_ext : proj x' ∈ (extChartAt I (proj α')).source := by
    rw [extChartAt_source]; exact hproj_x'_chart
  have hsymm_RHS : (extChartAt I (proj α')).symm y₀ = proj x' := by
    -- `y₀ = extChartAt I (proj α') (proj x')` (using `hy_eq`).
    rw [hy₀_def, hy_eq]
    exact (extChartAt I (proj α')).left_inv hproj_x'_ext
  -- Rewrite the inverse-Gram coefficients on both sides via the manifold-point
  -- identifications.
  rw [hsymm_LHS, hsymm_RHS]
  -- Now both inverse-Gram factors are evaluated at the same `(k, l)` indices,
  -- on the cover at `x'`, on the base at `proj x'`. They agree because
  -- the Gram matrices agree at corresponding points by `chartGramMatrix_lifted`,
  -- so their inverses (entrywise) agree.
  -- Step A: Show the matrices agree as full matrices.
  have hGramMatEq :
      chartGramMatrix
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' x' =
        chartGramMatrix (M := M) g (proj α') (proj x') := by
    ext p q
    exact chartGramMatrix_lifted (I := I) (M := M) g α' x' p q hx'
  -- Step B: From matrix equality, the inverse-Gram entries agree.
  have hInvGramEq :
      chartInvGramMatrix
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' x' k l =
        chartInvGramMatrix (M := M) g (proj α') (proj x') k l := by
    -- `chartInvGramMatrix` is definitionally the `Matrix.inverse` (`⁻¹`) of
    -- `chartGramMatrix`.
    change (chartGramMatrix
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' x')⁻¹ k l =
        (chartGramMatrix (M := M) g (proj α') (proj x'))⁻¹ k l
    rw [hGramMatEq]
  rw [hInvGramEq]
  -- Now the only remaining piece is that the partial-derivative bracket agrees.
  congr 1
  -- The bracket is `∂_i G_{l j} + ∂_j G_{l i} - ∂_l G_{i j}` (of the lifted
  -- vs. base `chartGramOnE`). We will show each of the three `partialDeriv`
  -- terms agrees individually. They all reduce to the same `fderiv`-eq via
  -- `Filter.EventuallyEq.fderiv_eq`.
  -- Build the `=ᶠ[𝓝 y₀]` between `chartGramOnE` on lifted vs base, for
  -- any pair of indices `(p, q)`.
  have hGramOnE_eventuallyEq :
      ∀ (p q : Fin (Module.finrank ℝ E)),
        chartGramOnE
            (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
            (liftedMetric (I := I) g) α' p q
          =ᶠ[𝓝 y₀]
        chartGramOnE (M := M) g (proj α') p q := by
    intro p q
    -- Carve out the open neighborhood of `y₀` on which both functions agree.
    -- The two preimage conditions:
    -- (a) `(extChartAt I α').symm y ∈ (chartAt H α').source`;
    -- (b) `(extChartAt I (proj α')).symm y ∈ (localSection α').target`.
    -- The cover-side condition is open by continuityAt of the chart inverse;
    -- so is the base-side condition.
    -- Cover-side preimage is a nbhd of y₀:
    -- Source of the cover-chart at `α'`, with explicit space annotation.
    set ECov : OpenPartialHomeomorph
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H :=
      coverChartAt α' with hECov_def
    have hContCoverInv : ContinuousAt (ECov.extend I).symm y₀ := by
      -- `y₀ = ECov.extend I x'` so this is continuityAt the
      -- image of `x' ∈ ECov.source`.
      have : (ECov.extend I) x' = y₀ := by
        rw [hy₀_def]
        rfl
      rw [← this]
      exact OpenPartialHomeomorph.continuousAt_extend_symm (I := I) ECov hx'
    have hOpenCoverSrc : IsOpen ECov.source := ECov.open_source
    have hCoverSrc_mem : (ECov.extend I).symm y₀ ∈ ECov.source := by
      -- `(ECov.extend I).symm y₀ = x'` since
      -- `y₀ = (ECov.extend I) x'` and `x' ∈ source`.
      have hy₀_alt : (ECov.extend I) x' = y₀ := by
        rw [hy₀_def]; rfl
      have : (ECov.extend I).symm ((ECov.extend I) x') = x' :=
        OpenPartialHomeomorph.extend_left_inv (I := I) ECov hx'
      rw [hy₀_alt] at this
      rw [this]
      exact hx'
    -- The cover-side condition is in 𝓝 y₀.
    have hPreCover : (ECov.extend I).symm ⁻¹' ECov.source ∈ 𝓝 y₀ :=
      hContCoverInv (hOpenCoverSrc.mem_nhds hCoverSrc_mem)
    -- Base-side: similar treatment for `(localSection α').target`.
    set EBase : OpenPartialHomeomorph M H := chartAt H (proj α') with hEBase_def
    have hContBaseInv : ContinuousAt (EBase.extend I).symm y₀ := by
      -- `y₀ = (EBase.extend I) (proj x')` by `hy_eq`.
      have hy₀_base : (EBase.extend I) (proj x') = y₀ := by
        change extChartAt I (proj α') (proj x') = y₀
        exact hy_eq.symm
      rw [← hy₀_base]
      exact OpenPartialHomeomorph.continuousAt_extend_symm (I := I)
        EBase hproj_x'_chart
    have hOpenLSTgt : IsOpen (localSection α').target := (localSection α').open_target
    have hLSTgt_mem : (EBase.extend I).symm y₀ ∈ (localSection α').target := by
      -- `(EBase.extend I).symm y₀ = proj x'` and `proj x' ∈ target`.
      have hy₀_base : (EBase.extend I) (proj x') = y₀ := by
        change extChartAt I (proj α') (proj x') = y₀
        exact hy_eq.symm
      have hinv : (EBase.extend I).symm ((EBase.extend I) (proj x')) = proj x' :=
        OpenPartialHomeomorph.extend_left_inv (I := I) EBase hproj_x'_chart
      rw [hy₀_base] at hinv
      rw [hinv]
      -- `proj x' ∈ (localSection α').target`: since `localSection α' x' = proj x'`
      -- and `x' ∈ (localSection α').source`, `map_source` gives it.
      have := (localSection α').map_source hx'_LSsrc
      rwa [hLS_x'] at this
    have hPreBase : (EBase.extend I).symm ⁻¹' (localSection α').target ∈ 𝓝 y₀ :=
      hContBaseInv (hOpenLSTgt.mem_nhds hLSTgt_mem)
    -- Combine and filter-upwards.
    filter_upwards [hPreCover, hPreBase] with y hyCover hyBase
    -- `hyCover : (ECov.extend I).symm y ∈ ECov.source`.
    -- `hyBase  : (EBase.extend I).symm y ∈ (localSection α').target`.
    -- Goal: `chartGramOnE (liftedMetric g) α' p q y = chartGramOnE g (proj α') p q y`.
    change chartGramMatrix
            (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
            (liftedMetric (I := I) g) α' ((extChartAt I α').symm y) p q
        = chartGramMatrix (M := M) g (proj α')
            ((extChartAt I (proj α')).symm y) p q
    -- Identify `(extChartAt I α').symm y` with `(localSection α').symm ∘ chart-inverse`.
    have hConjSymm := (uc_coverChartAt_extend_conjugacy (I := I) α').2
    have hSymmDecomp : (extChartAt I α').symm y =
        (localSection α').symm ((EBase.extend I).symm y) := by
      change (ECov.extend I).symm y = (localSection α').symm ((EBase.extend I).symm y)
      have := congrArg (fun f => f y) hConjSymm
      simpa [Function.comp_apply] using this
    -- Apply `chartGramMatrix_lifted` at the cover-side point.
    -- `chartAt H α' = ECov = coverChartAt α'` by the charted-space instance.
    have hsrc_cover_y : (extChartAt I α').symm y ∈ (chartAt H α').source := by
      change (ECov.extend I).symm y ∈ ECov.source
      exact hyCover
    -- Apply the Gram-matrix naturality at `(extChartAt I α').symm y`.
    rw [chartGramMatrix_lifted (I := I) (M := M) g α'
          ((extChartAt I α').symm y) p q hsrc_cover_y]
    -- Now show `proj ((extChartAt I α').symm y) = (extChartAt I (proj α')).symm y`.
    have hProj_eq : proj ((extChartAt I α').symm y)
        = (extChartAt I (proj α')).symm y := by
      rw [hSymmDecomp]
      -- `proj ((localSection α').symm w) = w` on `(localSection α').target`,
      -- via `proj = localSection` and `left_inv` / `right_inv` of the
      -- partial homeomorphism.
      have hproj_eq_LS :
          proj ((localSection α').symm ((EBase.extend I).symm y))
            = (localSection α')
                ((localSection α').symm ((EBase.extend I).symm y)) := by
        have := congrArg
            (fun f => f ((localSection α').symm ((EBase.extend I).symm y)))
            (proj_eq_localSection α')
        simpa using this
      rw [hproj_eq_LS, (localSection α').right_inv hyBase]
      rfl
    rw [hProj_eq]
  -- Combine into the three partialDeriv terms. The triplet is
  -- `partialDeriv i G_{l j} + partialDeriv j G_{l i} - partialDeriv l G_{i j}`.
  have hP_ij_lj :
      partialDeriv (E := E) i
          (chartGramOnE
            (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
            (liftedMetric (I := I) g) α' l j) y₀
        = partialDeriv (E := E) i
            (chartGramOnE (M := M) g (proj α') l j) y₀ := by
    -- `partialDeriv i u y = fderiv ℝ u y (chartModelBasis E i)`.
    change fderiv ℝ
        (chartGramOnE
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' l j) y₀
        (DifferentialGeometry.Integral.Measure.chartModelBasis E i)
      = fderiv ℝ
          (chartGramOnE (M := M) g (proj α') l j) y₀
        (DifferentialGeometry.Integral.Measure.chartModelBasis E i)
    rw [Filter.EventuallyEq.fderiv_eq (hGramOnE_eventuallyEq l j)]
  have hP_ji_li :
      partialDeriv (E := E) j
          (chartGramOnE
            (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
            (liftedMetric (I := I) g) α' l i) y₀
        = partialDeriv (E := E) j
            (chartGramOnE (M := M) g (proj α') l i) y₀ := by
    change fderiv ℝ
        (chartGramOnE
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' l i) y₀
        (DifferentialGeometry.Integral.Measure.chartModelBasis E j)
      = fderiv ℝ
          (chartGramOnE (M := M) g (proj α') l i) y₀
        (DifferentialGeometry.Integral.Measure.chartModelBasis E j)
    rw [Filter.EventuallyEq.fderiv_eq (hGramOnE_eventuallyEq l i)]
  have hP_lij :
      partialDeriv (E := E) l
          (chartGramOnE
            (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
            (liftedMetric (I := I) g) α' i j) y₀
        = partialDeriv (E := E) l
            (chartGramOnE (M := M) g (proj α') i j) y₀ := by
    change fderiv ℝ
        (chartGramOnE
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) α' i j) y₀
        (DifferentialGeometry.Integral.Measure.chartModelBasis E l)
      = fderiv ℝ
          (chartGramOnE (M := M) g (proj α') i j) y₀
        (DifferentialGeometry.Integral.Measure.chartModelBasis E l)
    rw [Filter.EventuallyEq.fderiv_eq (hGramOnE_eventuallyEq i j)]
  rw [hP_ij_lj, hP_ji_li, hP_lij]

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
