import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartJUniformBoundLocallyConstant
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChristoffelCorrectionUniformBound
import DifferentialGeometry.Integral.Connection.ChartTensor0SCovariantDerivative

/-!
# Uniform operator-norm bound for the chart Levi-Civita parallel CLM

For a closed Riemannian manifold `(M, g)` admitting a locally constant chart
selection, the chart Levi-Civita parallel CLM
`chartLeviCivitaParallelCLM g α b (chartBasisVecFiber α j)` has a uniform
operator-norm bound on `tsupport (chartAtlasPOU I M α)`, with constant
depending only on `g`, the chart at `α`, and the model space `E`.

This bound is the natural composition of:

* γ2.1 (`chartJ_opNorm_isBounded_on_compact` and the inverse-side counterpart)
  giving uniform op-norm bounds on `chartJ α b` and `chartJinv α b` over any
  compact subset of `(chartAt H α).source`.
* γ2.5.A.a (`christoffelCorrection_opNorm_isBounded_on_pouTsupport`) giving a
  uniform op-norm bound on the Christoffel correction CLM.
* The model-space basis vectors `(chartModelBasis E) j` being finite in
  number, hence admitting a uniform-norm sup.

The chart Levi-Civita parallel CLM is the composition
`(trivFromE α b) ∘ (christoffelCorrection g α b (trivToE α b (X b)))`. Op-norm
submultiplicativity reduces the bound to bounding each factor.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Finset
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Geometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]

/-- A finite-dimensional inner-product space is automatically complete; we
package it as a local instance so that the `chartLeviCivitaParallelCLM`
infrastructure (which requires `[CompleteSpace E]`) is usable here. -/
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## Abbreviations -/

/-- The closed support of the canonical POU weight at `α` (a compact subset of
`(chartAt H α).source` on a closed manifold). -/
private def pouTsupportSet (α : M) : Set M :=
  tsupport (fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)

private theorem pouTsupportSet_isCompact (α : M) :
    IsCompact (pouTsupportSet (I := I) (M := M) α) :=
  (isClosed_tsupport _).isCompact

private theorem pouTsupportSet_subset_chartAt_source (α : M) :
    pouTsupportSet (I := I) (M := M) α ⊆ (chartAt H α).source :=
  (chartAtlasPOU_isSubordinate I M) α

/-! ## Model-side basis sup -/

/-- The model-space basis vector norm sup. Local copy since the one in
`ChristoffelCorrectionUniformBound.lean` is private to that file. -/
private noncomputable def chartModelBasisVecSup' (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] : ℝ :=
  (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sup'
    (by
      refine Finset.univ_nonempty_iff.mpr ?_
      exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩)
    (fun k => ‖(chartModelBasis E) k‖)

private lemma chartModelBasisVecSup'_nonneg :
    0 ≤ chartModelBasisVecSup' E := by
  classical
  unfold chartModelBasisVecSup'
  have hne : (Finset.univ : Finset (Fin (Module.finrank ℝ E))).Nonempty := by
    refine Finset.univ_nonempty_iff.mpr ?_
    exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  obtain ⟨k₀, hk₀⟩ := hne
  have h_nn : (0 : ℝ) ≤ ‖(chartModelBasis E) k₀‖ := norm_nonneg _
  exact h_nn.trans (Finset.le_sup'
    (f := fun k => ‖(chartModelBasis E) k‖) hk₀)

private lemma norm_basis_le_chartModelBasisVecSup'
    (k : Fin (Module.finrank ℝ E)) :
    ‖(chartModelBasis E) k‖ ≤ chartModelBasisVecSup' E := by
  classical
  unfold chartModelBasisVecSup'
  exact Finset.le_sup'
    (f := fun k => ‖(chartModelBasis E) k‖)
    (Finset.mem_univ _)

/-! ## Part B: uniform op-norm bound on
`chartLeviCivitaParallelCLM g α b (chartBasisVecFiber α j)` -/

/-- The chart Levi-Civita parallel CLM at `b`, applied to the vector field
`chartBasisVecFiber α j`, decomposes as the composition of `trivFromE α b`
with the Christoffel correction in the model-side basis vector `chartJ α b
(chartBasisVecFiber α j b)`. -/
private lemma chartLeviCivitaParallelCLM_chartBasisVecFiber_opNorm_le_factors
    (g : SmoothRiemannianMetric I M) (α b : M)
    (j : Fin (Module.finrank ℝ E))
    (C_J C_Jinv C_χ : ℝ)
    (hCJ : ‖chartJ (I := I) (M := M) α b‖ ≤ C_J) (_hCJ_nn : 0 ≤ C_J)
    (hCJinv : ‖chartJinv (I := I) (M := M) α b‖ ≤ C_Jinv) (hCJinv_nn : 0 ≤ C_Jinv)
    (hCχ : ∀ Y : E, ‖christoffelCorrection (I := I) g α b Y‖ ≤ C_χ * ‖Y‖)
    (hCχ_nn : 0 ≤ C_χ) :
    ‖chartLeviCivitaParallelCLM (I := I) g α b (chartBasisVecFiber (I := I) α j)‖ ≤
      C_Jinv * C_χ * (C_J * C_Jinv * ‖(chartModelBasis E) j‖) := by
  classical
  -- Step 1: unfold the definition of `chartLeviCivitaParallelCLM`.
  unfold chartLeviCivitaParallelCLM
  -- Now the goal is `‖(trivFromE α b).comp (christoffelCorrection g α b (trivToE α b (X b)))‖ ≤ ...`
  -- with `X = chartBasisVecFiber α j`, hence `X b = chartBasisVecFiber α j b`.
  -- Step 2: bound by ‖trivFromE α b‖ * ‖christoffelCorrection g α b (trivToE α b (X b))‖.
  set Y : E :=
    trivToE (I := I) α b
      ((chartBasisVecFiber (I := I) α j b : TangentSpace I b)) with hY_def
  have h_comp_le :
      ‖(trivFromE (I := I) α b).comp
          (christoffelCorrection (I := I) g α b Y)‖ ≤
        ‖trivFromE (I := I) α b‖ *
          ‖christoffelCorrection (I := I) g α b Y‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  -- Step 3: bound the christoffel correction op-norm by `C_χ * ‖Y‖`.
  have h_χ_le : ‖christoffelCorrection (I := I) g α b Y‖ ≤ C_χ * ‖Y‖ := hCχ Y
  -- Step 4: identify `trivFromE α b` with `chartJinv α b` and bound by `C_Jinv`.
  have h_trivFromE_norm : ‖trivFromE (I := I) α b‖ = ‖chartJinv (I := I) (M := M) α b‖ :=
    rfl
  have h_trivFromE_le : ‖trivFromE (I := I) α b‖ ≤ C_Jinv := by
    rw [h_trivFromE_norm]; exact hCJinv
  have h_trivFromE_nn : 0 ≤ ‖trivFromE (I := I) α b‖ := norm_nonneg _
  -- Step 5: bound `‖Y‖` where `Y = trivToE α b (chartBasisVecFiber α j b)`.
  -- We have `chartBasisVecFiber α j b = trivFromE α b ((chartModelBasis E) j)`.
  have h_X_eq : (chartBasisVecFiber (I := I) α j b : TangentSpace I b) =
      trivFromE (I := I) α b ((chartModelBasis E) j) := rfl
  have h_Y_le : ‖Y‖ ≤ ‖chartJ (I := I) (M := M) α b‖ *
      (‖chartJinv (I := I) (M := M) α b‖ * ‖(chartModelBasis E) j‖) := by
    rw [hY_def, h_X_eq]
    -- ‖trivToE α b (trivFromE α b (e_j))‖ ≤ ‖trivToE α b‖ * ‖trivFromE α b‖ * ‖e_j‖.
    have h1 :
        ‖trivToE (I := I) α b (trivFromE (I := I) α b ((chartModelBasis E) j))‖ ≤
          ‖trivToE (I := I) α b‖ *
            ‖trivFromE (I := I) α b ((chartModelBasis E) j)‖ :=
      (trivToE (I := I) α b).le_opNorm _
    have h2 :
        ‖trivFromE (I := I) α b ((chartModelBasis E) j)‖ ≤
          ‖trivFromE (I := I) α b‖ * ‖(chartModelBasis E) j‖ :=
      (trivFromE (I := I) α b).le_opNorm _
    have h_triv_J : ‖trivToE (I := I) α b‖ = ‖chartJ (I := I) (M := M) α b‖ := rfl
    have h_triv_Jinv : ‖trivFromE (I := I) α b‖ =
        ‖chartJinv (I := I) (M := M) α b‖ := rfl
    have h_J_nn : 0 ≤ ‖trivToE (I := I) α b‖ := norm_nonneg _
    calc ‖trivToE (I := I) α b (trivFromE (I := I) α b ((chartModelBasis E) j))‖
        ≤ ‖trivToE (I := I) α b‖ *
            ‖trivFromE (I := I) α b ((chartModelBasis E) j)‖ := h1
      _ ≤ ‖trivToE (I := I) α b‖ *
            (‖trivFromE (I := I) α b‖ * ‖(chartModelBasis E) j‖) :=
            mul_le_mul_of_nonneg_left h2 h_J_nn
      _ = ‖chartJ (I := I) (M := M) α b‖ *
            (‖chartJinv (I := I) (M := M) α b‖ * ‖(chartModelBasis E) j‖) := by
            rw [h_triv_J, h_triv_Jinv]
  -- Step 6: bound `‖Y‖ ≤ C_J * (C_Jinv * ‖(chartModelBasis E) j‖)` using
  -- the input constants.
  have hej_nn : 0 ≤ ‖(chartModelBasis E) j‖ := norm_nonneg _
  have h_J_nn : 0 ≤ ‖chartJ (I := I) (M := M) α b‖ := norm_nonneg _
  have h_Jinv_nn : 0 ≤ ‖chartJinv (I := I) (M := M) α b‖ := norm_nonneg _
  have h_Y_le' : ‖Y‖ ≤ C_J * (C_Jinv * ‖(chartModelBasis E) j‖) := by
    refine h_Y_le.trans ?_
    have h_inner_le :
        ‖chartJinv (I := I) (M := M) α b‖ * ‖(chartModelBasis E) j‖ ≤
          C_Jinv * ‖(chartModelBasis E) j‖ :=
      mul_le_mul_of_nonneg_right hCJinv hej_nn
    have h_inner_nn :
        0 ≤ ‖chartJinv (I := I) (M := M) α b‖ * ‖(chartModelBasis E) j‖ :=
      mul_nonneg h_Jinv_nn hej_nn
    calc
      ‖chartJ (I := I) (M := M) α b‖ *
          (‖chartJinv (I := I) (M := M) α b‖ * ‖(chartModelBasis E) j‖)
          ≤ ‖chartJ (I := I) (M := M) α b‖ *
              (C_Jinv * ‖(chartModelBasis E) j‖) :=
            mul_le_mul_of_nonneg_left h_inner_le h_J_nn
      _ ≤ C_J * (C_Jinv * ‖(chartModelBasis E) j‖) := by
            have h_rhs_nn : 0 ≤ C_Jinv * ‖(chartModelBasis E) j‖ :=
              mul_nonneg hCJinv_nn hej_nn
            exact mul_le_mul_of_nonneg_right hCJ h_rhs_nn
  -- Step 7: bound the Christoffel correction by C_χ * ‖Y‖ ≤ C_χ * (C_J * C_Jinv * ‖e_j‖).
  have h_χ_le' :
      ‖christoffelCorrection (I := I) g α b Y‖ ≤
        C_χ * (C_J * (C_Jinv * ‖(chartModelBasis E) j‖)) := by
    refine h_χ_le.trans ?_
    exact mul_le_mul_of_nonneg_left h_Y_le' hCχ_nn
  -- Step 8: combine everything.
  -- `‖comp‖ ≤ ‖trivFromE‖ * ‖christoffelCorrection ...‖`
  -- `≤ C_Jinv * (C_χ * (C_J * (C_Jinv * ‖e_j‖)))`
  -- `= C_Jinv * C_χ * (C_J * C_Jinv * ‖e_j‖)`.
  have h_χ_nn : 0 ≤ ‖christoffelCorrection (I := I) g α b Y‖ := norm_nonneg _
  have h_step1 :
      ‖trivFromE (I := I) α b‖ *
          ‖christoffelCorrection (I := I) g α b Y‖ ≤
        C_Jinv * (C_χ * (C_J * (C_Jinv * ‖(chartModelBasis E) j‖))) := by
    have h_first :
        ‖trivFromE (I := I) α b‖ *
            ‖christoffelCorrection (I := I) g α b Y‖ ≤
          C_Jinv * ‖christoffelCorrection (I := I) g α b Y‖ :=
      mul_le_mul_of_nonneg_right h_trivFromE_le h_χ_nn
    have h_second :
        C_Jinv * ‖christoffelCorrection (I := I) g α b Y‖ ≤
          C_Jinv * (C_χ * (C_J * (C_Jinv * ‖(chartModelBasis E) j‖))) :=
      mul_le_mul_of_nonneg_left h_χ_le' hCJinv_nn
    linarith
  have h_rearrange :
      C_Jinv * (C_χ * (C_J * (C_Jinv * ‖(chartModelBasis E) j‖))) =
        C_Jinv * C_χ * (C_J * C_Jinv * ‖(chartModelBasis E) j‖) := by ring
  linarith

/-- **Uniform operator-norm bound for the chart Levi-Civita parallel CLM
applied to a chart-basis vector field, on `tsupport (chartAtlasPOU I M α)`.**

For a closed Riemannian manifold `(M, g)` with a locally constant chart
selection at the model, there exists a non-negative constant `C` depending
only on `g`, the chart at `α`, and the model space `E`, such that for every
`b` in the closed support of the canonical chart-atlas partition-of-unity
weight at `α` and every model-basis index `j`,

  `‖chartLeviCivitaParallelCLM g α b (chartBasisVecFiber α j)‖ ≤ C`

where the norm is the operator norm of the continuous linear map
`TangentSpace I b →L[ℝ] TangentSpace I b`. The constant `C` is independent
of `b` and `j`. -/
theorem chartLeviCivitaParallelCLM_chartBasisVec_opNorm_isBounded_on_pouTsupport
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ pouTsupportSet (I := I) (M := M) α →
        ∀ (j : Fin (Module.finrank ℝ E)),
          ‖chartLeviCivitaParallelCLM (I := I) g α b
              (chartBasisVecFiber (I := I) α j)‖ ≤ C := by
  classical
  -- Set up the compact base set.
  set K : Set M := pouTsupportSet (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := pouTsupportSet_isCompact (I := I) (M := M) α
  have hK_sub : K ⊆ (chartAt H α).source :=
    pouTsupportSet_subset_chartAt_source (I := I) (M := M) α
  -- γ2.1: uniform bounds on `‖chartJ α b‖` and `‖chartJinv α b‖`.
  obtain ⟨C_J, hCJ_pos, hCJ_bound⟩ :=
    chartJ_opNorm_isBounded_on_compact (I := I) (M := M) h_atlas α hK_compact hK_sub
  obtain ⟨C_Jinv, hCJinv_pos, hCJinv_bound⟩ :=
    chartJinv_opNorm_isBounded_on_compact (I := I) (M := M)
      h_atlas α hK_compact hK_sub
  have hCJ_nn : 0 ≤ C_J := le_of_lt hCJ_pos
  have hCJinv_nn : 0 ≤ C_Jinv := le_of_lt hCJinv_pos
  -- γ2.5.A.a: uniform bound on `christoffelCorrection g α b Y`.
  obtain ⟨C_χ, hCχ_nn, hCχ_bound⟩ :=
    christoffelCorrection_opNorm_isBounded_on_pouTsupport
      (I := I) (M := M) h_atlas g α
  -- Maximum norm of model basis vectors.
  set C_e : ℝ := chartModelBasisVecSup' E with hCe_def
  have hCe_nn : 0 ≤ C_e := chartModelBasisVecSup'_nonneg
  -- The headline constant.
  set C : ℝ := C_Jinv * C_χ * (C_J * C_Jinv * C_e) with hC_def
  have hC_nn : 0 ≤ C := by positivity
  refine ⟨C, hC_nn, ?_⟩
  intro b hb j
  -- Apply the factored bound.
  have h_CJ : ‖chartJ (I := I) (M := M) α b‖ ≤ C_J := hCJ_bound b hb
  have h_CJinv : ‖chartJinv (I := I) (M := M) α b‖ ≤ C_Jinv := hCJinv_bound b hb
  have h_Cχ : ∀ Y : E, ‖christoffelCorrection (I := I) g α b Y‖ ≤ C_χ * ‖Y‖ :=
    fun Y => hCχ_bound (b := b) hb Y
  have h_factored :=
    chartLeviCivitaParallelCLM_chartBasisVecFiber_opNorm_le_factors
      (I := I) (M := M) g α b j C_J C_Jinv C_χ
      h_CJ hCJ_nn h_CJinv hCJinv_nn h_Cχ hCχ_nn
  -- And finally bound `‖(chartModelBasis E) j‖ ≤ C_e`.
  have h_ej_le : ‖(chartModelBasis E) j‖ ≤ C_e :=
    norm_basis_le_chartModelBasisVecSup' (E := E) j
  have h_ej_nn : 0 ≤ ‖(chartModelBasis E) j‖ := norm_nonneg _
  -- `‖...‖ ≤ C_Jinv * C_χ * (C_J * C_Jinv * ‖e_j‖) ≤ C_Jinv * C_χ * (C_J * C_Jinv * C_e) = C`.
  have h_inner_nn : 0 ≤ C_J * C_Jinv := mul_nonneg hCJ_nn hCJinv_nn
  have h_outer_nn : 0 ≤ C_Jinv * C_χ := mul_nonneg hCJinv_nn hCχ_nn
  have h_inner_le :
      C_J * C_Jinv * ‖(chartModelBasis E) j‖ ≤ C_J * C_Jinv * C_e :=
    mul_le_mul_of_nonneg_left h_ej_le h_inner_nn
  have h_outer_le :
      C_Jinv * C_χ * (C_J * C_Jinv * ‖(chartModelBasis E) j‖) ≤
        C_Jinv * C_χ * (C_J * C_Jinv * C_e) :=
    mul_le_mul_of_nonneg_left h_inner_le h_outer_nn
  linarith

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaParallelCLM_chartBasisVec_opNorm_isBounded_on_pouTsupport
end Sanity
