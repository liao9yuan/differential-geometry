import DifferentialGeometry.Integral.Connection.CovApplyCovRSChartBasisExtension
import DifferentialGeometry.Integral.Connection.TensorRSCovariantDerivativeCongrLocally
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.SkExtChartComponentEqCovDerivEuclid

/-!
# The chart-α `(Idx, Jdx)` projection of the bundle-level second covariant
derivative `(∇²T₀)(B^α_k, B^α_l)` at a chart-α good-set point, expressed via
the global smooth extension `S_k_ext` and the chart-coordinate first-derivative
formula.

For a smooth Riemannian manifold `(M, g)` modelled on a real inner-product
space `E`, a chart-centre `α : M`, chart-coordinate indices `k, l`, a smooth
compactly-supported `(r, s)`-tensor section `T₀ : SmoothCcTensor g r s`, a
component multi-index pair `(Idx, Jdx)`, and a chart-α Levi-Civita good-set
point `b₀`, this file equates, on an open neighbourhood `U ∋ b₀` of `b₀`,

```
tensorChartComponentProjection r s Idx Jdx
  ((triv α).clmAt b ((cov_RS).toFun
      (covApply cov_RS (chartBasisVecFiber α k) T₀.toSection) b
      (chartBasisVecFiber α l b)))
= covDerivComponentEuclid g r s α (S_k_packed) l Idx Jdx
    (toEuclidean ((extChartAt I α) b))
```

The `S_k_packed : SmoothCcTensor g r s` is the `SmoothCcTensor` packaging of
the global smooth extension `S_k_ext` (whose underlying section is the smooth
extension from the chart-basis-applied covariant derivative produced by
B.2.c.i `covApply_covRS_chartBasis_globalSmoothExtension`). The compact-support
hypothesis on the underlying map is supplied by `HasCompactSupport.of_compactSpace`,
since `[CompactSpace M]` is in scope.

The proof composes three ingredients:

1. **B.2.c.i** (`covApply_covRS_chartBasis_globalSmoothExtension`): produces
   `S_k_ext` and an open set `U ⊆ chartLeviCivitaGoodSet α` containing `b₀`,
   on which `S_k_ext.toFun y = covApply cov_RS (chartBasisVecFiber α k)
   T₀.toSection y`.
2. **B.2.c.ii** (`tensorRSCovariantDerivative_congr_of_eventuallyEq`): two
   sections that agree on a neighbourhood of a point have equal
   covariant derivatives at that point, given joint differentiability.
3. **The chart-coordinate first-derivative formula** in the form
   `covDerivComponentEuclid_def`, combined with the bundle/chart-frame bridge
   `tensorCovDerivAt_eq_chartTensorRSCovariantDerivative` on the good set.

## Main result

* `chartα_proj_secondCovDeriv_eq_chartCoord_first_deriv_of_Sk_ext` — the
  headline of this file: the chart-α `(Idx, Jdx)` projection of the
  bundle-level second covariant derivative `(∇²T₀)(B^α_k, B^α_l)` at a
  chart-α good-set point equals the chart-coordinate first-derivative
  `covDerivComponentEuclid` of the global smooth extension `S_k_ext`,
  evaluated in the `l`-direction at the chart-Euclidean image of the point.
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

/-! ## Packaging a globally smooth `(r, s)`-tensor section as `SmoothCcTensor`

Under `[CompactSpace M]` every function `M → _` has compact support
automatically (`HasCompactSupport.of_compactSpace`). Hence a globally smooth
section of the `(r, s)`-tensor bundle can be wrapped as a `SmoothCcTensor g r s`
with no further hypothesis. -/

/-- Package a globally smooth `(r, s)`-tensor section as a `SmoothCcTensor`,
using the ambient `[CompactSpace M]` to supply compact support. -/
private def packageAsCc
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
                fun b : M => TensorRSSpace r s I b⟯) :
    SmoothCcTensor g r s where
  toSection := S
  hasCompactSupport := HasCompactSupport.of_compactSpace _

private lemma packageAsCc_toSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
                fun b : M => TensorRSSpace r s I b⟯) :
    (packageAsCc (I := I) (M := M) g r s S).toSection = S := rfl

/-! ## The headline -/

/-- **Chart-α `(Idx, Jdx)` projection of the bundle-level second covariant
derivative at a good-set point, expressed via the smooth extension `S_k_ext`
and the chart-coordinate first-derivative formula.**

For a chart-α Levi-Civita good-set point `b₀`, there exists a global smooth
extension `S_k_ext` of `covApply cov_RS (chartBasisVecFiber α k) T₀.toSection`
(supplied by B.2.c.i) and an open neighbourhood `U ⊆ chartLeviCivitaGoodSet α`
of `b₀` such that, for every `b ∈ U`, the chart-α `(Idx, Jdx)` projection of
`(cov_RS).toFun (covApply cov_RS (chartBasisVecFiber α k) T₀.toSection) b
(chartBasisVecFiber α l b)` (i.e. the bundle-level second covariant derivative
of `T₀` evaluated along the chart-α basis at index `k`, then differentiated and
evaluated along the chart-α basis at index `l`) equals the chart-coordinate
first-derivative formula `covDerivComponentEuclid g r s α S_k_packed l Idx Jdx`
applied to `S_k_packed` (the `SmoothCcTensor` packaging of `S_k_ext`) at the
chart-Euclidean image of `b`. -/
theorem chartα_proj_secondCovDeriv_eq_chartCoord_first_deriv_of_Sk_ext
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (k l : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b₀ : M} (hb₀ : b₀ ∈ chartLeviCivitaGoodSet (I := I) α) :
    ∃ S_k_ext : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
                       fun b : M => TensorRSSpace r s I b⟯,
    ∃ U : Set M, IsOpen U ∧ b₀ ∈ U ∧ U ⊆ chartLeviCivitaGoodSet (I := I) α ∧
      ∀ b ∈ U,
        tensorChartComponentProjection (E := E) r s Idx Jdx
            ((trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g))
                  (chartBasisVecFiber (I := I) α k) T₀.toSection) b
                (chartBasisVecFiber (I := I) α l b))) =
        covDerivComponentEuclid (I := I) (M := M) g r s α
          (packageAsCc (I := I) (M := M) g r s S_k_ext) l Idx Jdx
          ((toEuclidean (E := E)) ((extChartAt I α) b)) := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  -- Step 1: invoke B.2.c.i to obtain `S_k_ext`, the open neighbourhood `U`, and
  -- the pointwise agreement on `U` between `S_k_ext.toFun` and the raw
  -- chart-basis-applied bundled covariant derivative.
  obtain ⟨S_k_ext, U, hU_open, hb₀_U, hU_sub_good, hU_eq⟩ :=
    covApply_covRS_chartBasis_globalSmoothExtension
      (I := I) (M := M) g r s α T₀ k (b₀ := b₀) hb₀
  refine ⟨S_k_ext, U, hU_open, hb₀_U, hU_sub_good, ?_⟩
  -- Step 2: prove the pointwise identity for `b ∈ U`.
  intro b hb_U
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hU_sub_good hb_U
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb_good
  -- Abbreviations.
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  set σ : Π y : M, TensorRSSpace r s I y :=
    covApply cov (chartBasisVecFiber (I := I) α k) T₀.toSection with hσ_def
  set σ' : Π y : M, TensorRSSpace r s I y :=
    fun y : M => (S_k_ext : Π y' : M, TensorRSSpace r s I y') y with hσ'_def
  set S_k_packed : SmoothCcTensor g r s :=
    packageAsCc (I := I) (M := M) g r s S_k_ext with hS_k_packed_def
  -- Step 3: identify `σ'` with `S_k_packed.toSection`.
  have hσ'_eq_packed :
      σ' = (fun y : M => S_k_packed.toSection y) := by
    funext y
    simp [hσ'_def, hS_k_packed_def, packageAsCc_toSection]
  -- Step 4: `S_k_ext` and `σ` agree eventually at `b ∈ U` (i.e. on `U`,
  -- an open neighbourhood of `b`).
  have hagree_σ_σ' : ∀ᶠ y in 𝓝 b, σ y = σ' y := by
    have hU_nhds : U ∈ 𝓝 b := hU_open.mem_nhds hb_U
    refine Filter.eventually_of_mem hU_nhds (fun y hy_U => ?_)
    -- On `U`, `S_k_ext.toFun y = covApply … y`, so `σ y = σ' y`.
    have hSk_y :
        (S_k_ext : Π y' : M, TensorRSSpace r s I y') y =
          covApply cov (chartBasisVecFiber (I := I) α k) T₀.toSection y :=
      hU_eq y hy_U
    -- `σ y = covApply cov … y`; `σ' y = S_k_ext.toFun y`.
    change covApply cov (chartBasisVecFiber (I := I) α k) T₀.toSection y =
        (S_k_ext : Π y' : M, TensorRSSpace r s I y') y
    exact hSk_y.symm
  -- Step 5: `σ'` is `MDifferentiableAt` at `b` in total-space form
  -- (the underlying section of `S_k_ext` is globally smooth).
  have hσ'_total_smooth :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y (σ' y)) :=
    S_k_ext.contMDiff
  have hσ'_total_mdiff :
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y (σ' y)) b :=
    (hσ'_total_smooth b).mdifferentiableAt (by simp)
  -- Step 6: `σ` is `MDifferentiableAt` at `b` by EventuallyEq with `σ'`,
  -- in the total-space form.
  have htotal_agree :
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y (σ y)) =ᶠ[𝓝 b]
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y (σ' y)) := by
    refine hagree_σ_σ'.mono (fun y hy => ?_)
    -- `TotalSpace.mk'` is pointwise: agreement at `y` lifts to total-space.
    change TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (σ y) =
      TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (σ' y)
    rw [hy]
  have hσ_total_mdiff :
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y (σ y)) b :=
    (htotal_agree.mdifferentiableAt_iff (𝕜 := ℝ) (I := I)
      (I' := I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))).mpr hσ'_total_mdiff
  -- Step 7: by locality (B.2.c.ii), `cov.toFun σ b = cov.toFun σ' b`.
  have hcov_loc : cov.toFun σ b = cov.toFun σ' b :=
    tensorRSCovariantDerivative_congr_of_eventuallyEq
      (I := I) (M := M) g r s
      (σ := σ) (σ' := σ') (x := b) hagree_σ_σ' hσ_total_mdiff hσ'_total_mdiff
  -- Step 8: apply at the vector `chartBasisVecFiber α l b`.
  have hcov_loc_at_v :
      cov.toFun σ b (chartBasisVecFiber (I := I) α l b) =
      cov.toFun σ' b (chartBasisVecFiber (I := I) α l b) := by
    rw [hcov_loc]
  -- Step 9: rewrite `σ' = S_k_packed.toSection` pointwise.
  have hcov_σ'_eq_packed :
      cov.toFun σ' b (chartBasisVecFiber (I := I) α l b) =
      cov.toFun (fun y : M => S_k_packed.toSection y) b
        (chartBasisVecFiber (I := I) α l b) := by
    rw [hσ'_eq_packed]
  -- Step 10: identify the bundle covariant derivative at the chart-basis with
  -- `tensorCovDerivAt` (definitional unfolding).
  have hcov_tensor :
      cov.toFun (fun y : M => S_k_packed.toSection y) b
        (chartBasisVecFiber (I := I) α l b) =
      tensorCovDerivAt (I := I) (M := M) g r s S_k_packed b
        (chartBasisVecFiber (I := I) α l b) := by
    rw [tensorCovDerivAt_def]
  -- Step 11: on the good set, `tensorCovDerivAt = chartTensorRSCovariantDerivative
  -- … (chartBasisVecFiber α l) b` (with `m := l`).
  have hcov_chart :
      tensorCovDerivAt (I := I) (M := M) g r s S_k_packed b
        (chartBasisVecFiber (I := I) α l b) =
      chartTensorRSCovariantDerivative (I := I) r s g α S_k_packed.toSection
        (chartBasisVecFiber (I := I) α l) b :=
    tensorCovDerivAt_eq_chartTensorRSCovariantDerivative
      (I := I) (M := M) g r s S_k_packed α l (b := b) hb_good
  -- Step 12: assemble all the rewrites for the inner argument.
  have hinner :
      cov.toFun σ b (chartBasisVecFiber (I := I) α l b) =
      chartTensorRSCovariantDerivative (I := I) r s g α S_k_packed.toSection
        (chartBasisVecFiber (I := I) α l) b := by
    rw [hcov_loc_at_v, hcov_σ'_eq_packed, hcov_tensor, hcov_chart]
  -- Step 13: rewrite the LHS using `hinner`. The LHS is the
  -- `tensorChartComponentProjection` of the `continuousLinearMapAt`-wrapped
  -- value of `cov.toFun σ b (chartBasisVecFiber α l b)`.
  rw [hinner]
  -- Step 14: the RHS now matches `covDerivComponentEuclid_def` applied to
  -- `S_k_packed` with `m := l` at `y := toEuclidean ((extChartAt I α) b)`. By
  -- chart left-inverse on the good set, the `(extChartAt I α).symm
  -- (toEuclidean.symm (toEuclidean ((extChartAt I α) b)))` equals `b`.
  rw [covDerivComponentEuclid_def]
  -- Goal now has both sides as
  -- `tensorChartComponentProjection r s Idx Jdx
  --   ((triv α).continuousLinearMapAt ℝ b'
  --     (chartTensorRSCovariantDerivative r s g α S_k_packed.toSection
  --       (chartBasisVecFiber α l) b'))`
  -- where `b' = (extChartAt I α).symm (toEuclidean.symm (toEuclidean ((extChartAt I α) b)))`.
  -- Reduce `b'` to `b`.
  have hsymm_te :
      (toEuclidean (E := E)).symm
        ((toEuclidean (E := E)) ((extChartAt I α) b)) =
        (extChartAt I α) b :=
    (toEuclidean (E := E)).symm_apply_apply _
  have hleft_inv : (extChartAt I α).symm ((extChartAt I α) b) = b :=
    (extChartAt I α).left_inv hb_src
  -- Now rewrite the RHS so `b' = b`.
  rw [hsymm_te, hleft_inv]

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
