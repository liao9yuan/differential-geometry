import DifferentialGeometry.Integral.Connection.CovApplyCovRSChartBasisExtension
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.CovDerivComponentSecondFormula
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.CovDerivChartForm

/-!
# Equality of the chart-α raw component of the globally smooth extension with the
chart-α coordinate component of the first covariant derivative

For a smooth Riemannian manifold `(M, g)` modelled on a real inner-product space
`E`, a chart-centre `α : M`, a chart coordinate index `k`, and a smooth
compactly-supported `(r, s)`-tensor section `T₀`, the global smooth extension
`S_k_ext` (built in `covApply_covRS_chartBasis_globalSmoothExtension`) of the
chart-basis-applied bundled covariant derivative
`covApply cov_RS (chartBasisVecFiber α k) T₀.toSection` agrees, on an open
neighbourhood of any chart-α Levi-Civita good-set point `b₀`, with the
chart-frame covariant derivative
`chartTensorRSCovariantDerivative r s g α T₀.toSection (chartBasisVecFiber α k)`.

This file packages the chart-α `(Idx, Jdx)` raw scalar component of `S_k_ext`,
pulled back to the Euclidean chart target, into an equality with the
chart-α coordinate component of the first covariant derivative
`covDerivComponentEuclid g r s α T₀ k Idx Jdx`, on an open neighbourhood (in
the Euclidean chart target) of the chart-Euclidean image of `b₀`.

The proof chains:

1. **B.2.c.i** (`covApply_covRS_chartBasis_globalSmoothExtension`) — produces
   `S_k_ext`, an open set `U ⊆ chartLeviCivitaGoodSet α` containing `b₀`, and the
   pointwise identity `S_k_ext y = covApply cov_RS (chartBasisVecFiber α k)
   T₀.toSection y` for `y ∈ U`.
2. **Definitional unfolding of `covApply`** — rewrites the right-hand side as
   `cov.toFun T₀.toSection y (chartBasisVecFiber α k y) =
   tensorCovDerivAt g r s T₀ y (chartBasisVecFiber α k y)`.
3. **`tensorCovDerivAt_eq_chartTensorRSCovariantDerivative`** — replaces the
   bundled covariant derivative by the chart-frame one on the good set.
4. **`covDerivComponentEuclid_def`** — equates the chart-frame raw component
   with `covDerivComponentEuclid`.

## Main result

* `chartPushedRaw_tensorChartComponentRaw_S_k_ext_eqOn_covDerivComponentEuclid`
  — the headline: the chart-pushed raw chart-α `(Idx, Jdx)` scalar component
  of the global smooth extension `S_k_ext` agrees on an open neighbourhood
  (in the Euclidean chart target) of `toEuclidean ((extChartAt I α) b₀)` with
  `covDerivComponentEuclid g r s α T₀ k Idx Jdx`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators
open Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart

/-! ## The open neighbourhood `V` of `toEuclidean ((extChartAt I α) b₀)`

For a manifold-open set `U ⊆ chartLeviCivitaGoodSet α` containing `b₀`, we
build the open set `V` in `EuclideanSpace` consisting of those `y` in the
Euclidean chart target whose chart-pullback `(extChartAt I α).symm
(toEuclidean.symm y)` lies in `U`. This is precisely the chart-Euclidean
preimage of `U` intersected with the chart target image. -/

/-- The Euclidean-side neighbourhood corresponding to `U ⊆ M`. -/
private def euclidNeighbourhood (α : M) (U : Set M) :
    Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
  chartTargetEuclid (I := I) (M := M) α ∩
    {y | (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ U}

private lemma euclidNeighbourhood_mem_iff (α : M) (U : Set M)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))} :
    y ∈ euclidNeighbourhood (I := I) (M := M) α U ↔
      y ∈ chartTargetEuclid (I := I) (M := M) α ∧
      (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ U := Iff.rfl

private lemma euclidNeighbourhood_subset_chartTargetEuclid
    (α : M) (U : Set M) :
    euclidNeighbourhood (I := I) (M := M) α U ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  intro y hy; exact hy.1

private lemma euclidNeighbourhood_isOpen
    (α : M) {U : Set M} (hU_open : IsOpen U) :
    IsOpen (euclidNeighbourhood (I := I) (M := M) α U) := by
  classical
  -- The chart-target image is open under the boundaryless assumption.
  have hchartT_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  -- `toEuclidean.symm` is continuous globally; `(extChartAt I α).symm` is
  -- continuous on `(extChartAt I α).target`; the composition sends
  -- `chartTargetEuclid α` into `(extChartAt I α).target`.
  have hcont_te : Continuous
      ((toEuclidean (E := E)).symm :
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E) :=
    (toEuclidean (E := E)).symm.continuous
  have hcont_extsymm :
      ContinuousOn (extChartAt I α).symm (extChartAt I α).target :=
    continuousOn_extChartAt_symm α
  have hmap_target : MapsTo
      ((toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α)
      (extChartAt I α).target := by
    intro y hy
    -- `y ∈ toEuclidean '' (extChartAt I α).target`: there is `z ∈ target` with
    -- `toEuclidean z = y`, hence `toEuclidean.symm y = z ∈ target`.
    rcases hy with ⟨z, hz_target, hz_eq⟩
    have hyz : (toEuclidean (E := E)).symm y = z := by
      rw [← hz_eq]; exact (toEuclidean (E := E)).symm_apply_apply _
    rw [hyz]
    exact hz_target
  have hcont_comp :
      ContinuousOn
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α) :=
    hcont_extsymm.comp hcont_te.continuousOn hmap_target
  -- The set under question is the intersection of `chartTargetEuclid α`
  -- with the preimage of `U` under the composition.
  have hset_eq :
      euclidNeighbourhood (I := I) (M := M) α U =
        chartTargetEuclid (I := I) (M := M) α ∩
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
              (extChartAt I α).symm ((toEuclidean (E := E)).symm y)) ⁻¹' U := rfl
  rw [hset_eq]
  exact hcont_comp.isOpen_inter_preimage hchartT_open hU_open

private lemma toEuclidean_extChartAt_mem_euclidNeighbourhood
    (α : M) {U : Set M} (hU_sub_good : U ⊆ chartLeviCivitaGoodSet (I := I) α)
    {b₀ : M} (hb₀_U : b₀ ∈ U) :
    toEuclidean ((extChartAt I α) b₀) ∈
      euclidNeighbourhood (I := I) (M := M) α U := by
  classical
  -- `b₀ ∈ U ⊆ chartLeviCivitaGoodSet α ⊆ extChartAt I α.source`.
  have hb₀_good : b₀ ∈ chartLeviCivitaGoodSet (I := I) α := hU_sub_good hb₀_U
  have hb₀_src : b₀ ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb₀_good
  -- `(extChartAt I α) b₀ ∈ (extChartAt I α).target` follows from being in
  -- the source.
  have hb₀_tgt : (extChartAt I α) b₀ ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb₀_src
  refine ⟨?_, ?_⟩
  · -- `toEuclidean ((extChartAt I α) b₀) ∈ chartTargetEuclid α`.
    exact ⟨(extChartAt I α) b₀, hb₀_tgt, rfl⟩
  · -- The chart-pullback returns `b₀`.
    change (extChartAt I α).symm
        ((toEuclidean (E := E)).symm (toEuclidean ((extChartAt I α) b₀))) ∈ U
    have hsymm_te : (toEuclidean (E := E)).symm
        (toEuclidean ((extChartAt I α) b₀)) =
        (extChartAt I α) b₀ :=
      (toEuclidean (E := E)).symm_apply_apply _
    rw [hsymm_te]
    have hleft_inv : (extChartAt I α).symm ((extChartAt I α) b₀) = b₀ :=
      (extChartAt I α).left_inv hb₀_src
    rw [hleft_inv]
    exact hb₀_U

/-! ## The headline -/

/-- **Equality of the chart-α `(Idx, Jdx)` raw component of the globally
smooth extension with `covDerivComponentEuclid`.**

For a chart-α Levi-Civita good-set point `b₀`, the global smooth extension
`S_k_ext` of the chart-basis-applied bundled covariant derivative agrees with
the chart-α `(Idx, Jdx)` raw component formula on an open neighbourhood (in
the Euclidean chart target) of `toEuclidean ((extChartAt I α) b₀)`:

```
chartPushedRaw I α (b ↦ tensorChartComponentProjection r s Idx Jdx
  ((triv α).continuousLinearMapAt ℝ b (S_k_ext.toFun b))) y
=
covDerivComponentEuclid g r s α T₀ k Idx Jdx y
```

for all `y ∈ V`, where `V ⊆ chartTargetEuclid α` is the open neighbourhood. -/
theorem chartPushedRaw_tensorChartComponentRaw_S_k_ext_eqOn_covDerivComponentEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s) (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b₀ : M} (hb₀ : b₀ ∈ chartLeviCivitaGoodSet (I := I) α) :
    ∃ S_k_ext : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
                       fun b : M => TensorRSSpace r s I b⟯,
    ∃ V : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
      IsOpen V ∧
      toEuclidean ((extChartAt I α) b₀) ∈ V ∧
      Set.EqOn
        (chartPushedRaw I α
          (fun b : M =>
            tensorChartComponentProjection r s Idx Jdx
              ((trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ
                b (S_k_ext.toFun b))))
        (covDerivComponentEuclid (I := I) (M := M) g r s α T₀ k Idx Jdx)
        V := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  -- Step 1: apply B.2.c.i to obtain `S_k_ext`, the open set `U ⊆
  -- chartLeviCivitaGoodSet α` containing `b₀`, and the pointwise identity.
  obtain ⟨S_k_ext, U, hU_open, hb₀_U, hU_sub_good, hU_eq⟩ :=
    covApply_covRS_chartBasis_globalSmoothExtension
      (I := I) (M := M) g r s α T₀ k (b₀ := b₀) hb₀
  -- Step 2: build the Euclidean-side neighbourhood `V`.
  set V : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    euclidNeighbourhood (I := I) (M := M) α U with hV_def
  have hV_open : IsOpen V :=
    euclidNeighbourhood_isOpen (I := I) (M := M) α hU_open
  have hb₀_V : toEuclidean ((extChartAt I α) b₀) ∈ V :=
    toEuclidean_extChartAt_mem_euclidNeighbourhood
      (I := I) (M := M) α hU_sub_good hb₀_U
  refine ⟨S_k_ext, V, hV_open, hb₀_V, ?_⟩
  -- Step 3: prove `EqOn` on `V`. Take `y ∈ V`. By `chartPushedRaw_apply_of_mem`,
  -- the LHS equals the inner expression at `b := (extChartAt I α).symm
  -- (toEuclidean.symm y)`. By `covDerivComponentEuclid_def`, the RHS equals
  -- the same expression but with the inner argument
  -- `chartTensorRSCovariantDerivative r s g α T₀.toSection
  -- (chartBasisVecFiber α k) b` instead of `S_k_ext.toFun b`. The two inner
  -- arguments agree by the chain (B.2.c.i + definitional + agreement on the
  -- good set).
  intro y hy
  -- `y ∈ chartTargetEuclid α` and `b := (extChartAt I α).symm (toEuclidean.symm
  -- y) ∈ U`.
  have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := hy.1
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_U : b ∈ U := hy.2
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hU_sub_good hb_U
  -- LHS: rewrite chartPushedRaw.
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy_target]
  -- LHS now: `tensorChartComponentProjection r s Idx Jdx
  --   ((triv α).continuousLinearMapAt ℝ b (S_k_ext.toFun b))`.
  -- RHS: rewrite covDerivComponentEuclid via its def.
  rw [covDerivComponentEuclid_def]
  -- Both sides are `tensorChartComponentProjection r s Idx Jdx ∘
  -- (triv α).continuousLinearMapAt ℝ b ∘ (some expression at b)`; show the
  -- inner arguments agree.
  congr 1
  -- Goal: `(triv α).continuousLinearMapAt ℝ b (S_k_ext.toFun b)
  --      = (triv α).continuousLinearMapAt ℝ b
  --          (chartTensorRSCovariantDerivative r s g α T₀.toSection
  --            (chartBasisVecFiber α k) b)`.
  -- Reduce to equality of the inner arguments to `continuousLinearMapAt`.
  congr 1
  -- Goal: `S_k_ext.toFun b = chartTensorRSCovariantDerivative r s g α
  --   T₀.toSection (chartBasisVecFiber α k) b`.
  -- Chain through `tensorCovDerivAt`:
  -- (a) `S_k_ext.toFun b = covApply cov_RS (chartBasisVecFiber α k)
  --     T₀.toSection b` (B.2.c.i, on U).
  have hStep_BTCi : (S_k_ext : Π b' : M, TensorRSSpace r s I b') b =
      covApply
        (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
        (chartBasisVecFiber (I := I) α k) T₀.toSection b := hU_eq b hb_U
  -- `S_k_ext.toFun = ⇑S_k_ext` (DFunLike coercion); confirm by `rfl`.
  have hSk_unfold :
      S_k_ext.toFun b = (S_k_ext : Π b' : M, TensorRSSpace r s I b') b := rfl
  rw [hSk_unfold, hStep_BTCi]
  -- (b) `covApply cov X Z b = cov.toFun Z b (X b)`.
  rw [covApply_apply]
  -- (c) `cov.toFun T₀.toSection b (chartBasisVecFiber α k b) =
  --     tensorCovDerivAt g r s T₀ b (chartBasisVecFiber α k b)`.
  have hCovDerivAt : (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun T₀.toSection b
        (chartBasisVecFiber (I := I) α k b) =
      tensorCovDerivAt (I := I) (M := M) g r s T₀ b
        (chartBasisVecFiber (I := I) α k b) := by
    rw [tensorCovDerivAt_def]
  rw [hCovDerivAt]
  -- (d) On the chart-α good set, `tensorCovDerivAt = chartTensorRSCov`.
  exact tensorCovDerivAt_eq_chartTensorRSCovariantDerivative
    (I := I) (M := M) g r s T₀ α k (b := b) hb_good

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
