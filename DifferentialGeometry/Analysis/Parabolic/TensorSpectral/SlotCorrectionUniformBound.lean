import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartJUniformBoundLocallyConstant
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChristoffelCorrectionUniformBound
import DifferentialGeometry.Integral.Connection.ChartTensor0SCovariantDerivative
import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivative
import DifferentialGeometry.Tensor.RSTensor.TensorRSSpaceNormBridge

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

/-! ## Part C: uniform op-norm bound on the input / output slot corrections

The chart-frame covariant derivative `chartTensorRSCovariantDerivative` on an
`(r, s)`-tensor section is the difference of an intrinsic chart Fréchet
derivative term and two sums of *slot corrections*:

* `chartTensorRSInputSlotCorrection r s g α T X b k` — for each input slot
  `k : Fin r`, the composition `T b ∘ substCLM_k`, where `substCLM_k`
  substitutes the `k`-th tangent argument of the input `(0, r)`-tensor by
  `chartLeviCivitaParallelCLM g α b X`.
* `chartTensorRSOutputSlotCorrection r s g α T X b l` — for each output slot
  `l : Fin s`, the composition `substCLM_l ∘ T b`, with analogous
  substitution on the output `(0, s)`-tensor.

This section proves uniform bounds

`‖chartTensorRSInputSlotCorrection r s g α T (chartBasisVecFiber α j) b k‖
    ≤ M_F * ‖T b‖`

(and the analogous lower-slot bound) for every section `T`, every
`b` in `tsupport (chartAtlasPOU I M α)`, every input slot `k`, and every
model-basis index `j`. The bound on the output side is analogous.

The proof factors the slot correction CLM as a composition

`T b .comp (CLE.symm ∘ compContinuousLinearMapL Ψ ∘ CLE)`

(for the input side) and bounds:

* `‖T b .comp substCLM x‖_{Tensor0SSpace s}
    ≤ ‖T b‖_{TensorRSSpace} * ‖substCLM x‖_{Tensor0SSpace r}`
  via `tensorRSSpace_norm_apply_le` (Part C.a);
* `‖substCLM x‖ ≤ ‖compContinuousLinearMapL Ψ‖ * ‖x‖`
  via norm-preservation of the bundle-to-model CLE and the standard
  `ContinuousLinearMap.le_opNorm`;
* `‖compContinuousLinearMapL Ψ‖ ≤ ∏ ‖Ψ i‖` (Mathlib
  `norm_compContinuousLinearMapL_le`);
* `∏ ‖Ψ i‖ ≤ ‖Φ‖` where `Ψ = tangentSlotCLM r k Φ`, using
  `‖id‖ ≤ 1` for non-slot entries.

The norm `‖Φ‖ = ‖chartLeviCivitaParallelCLM g α b (chartBasisVecFiber α j)‖`
is bounded uniformly on `tsupport (chartAtlasPOU I M α)` by Part B above.
-/

/-! ### Slot-substitution pointwise bound -/

/-- Pointwise upper bound on `tensorSlotSubstCLM` in the model fibre norm.
The argument proceeds in three steps:

1. By definition, `tensorSlotSubstCLM n b Φ x = CLE.symm (compCLML Φ (CLE x))`.
2. CLE / CLE.symm preserve norms (Part C.a's `tensor0SSpace_continuousLinearEquiv_norm_apply` /
   `_symm_norm_apply`), so the LHS norm equals `‖compCLML Φ (CLE x)‖`.
3. `compCLML Φ` is a CLM with op-norm `≤ ∏ ‖Φ i‖` (Mathlib's
   `norm_compContinuousLinearMapL_le`), so the standard CLM bound gives
   `‖compCLML Φ (CLE x)‖ ≤ (∏ ‖Φ i‖) * ‖CLE x‖ = (∏ ‖Φ i‖) * ‖x‖`. -/
private lemma tensorSlotSubstCLM_apply_norm_le (n : ℕ) (b : M)
    (Φ : Fin n → (TangentSpace I b →L[ℝ] TangentSpace I b))
    (x : Tensor0SSpace n I b) :
    ‖tensorSlotSubstCLM (I := I) n b Φ x‖ ≤
      (∏ i : Fin n, ‖Φ i‖) * ‖x‖ := by
  classical
  -- Step 1: substCLM x = CLE.symm (compCLML Φ (CLE x)) by definition.
  have hsubst_eq :
      tensorSlotSubstCLM (I := I) n b Φ x =
        (tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b).symm
          ((ContinuousMultilinearMap.compContinuousLinearMapL
              (𝕜 := ℝ) (E := fun _ : Fin n => E) (F := ℝ) Φ)
            ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b) x)) := by
    change ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b).symm
          : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ →L[ℝ]
              Tensor0SSpace n I b).comp
        ((tangentCompCLML_E (I := I) (M := M) n b Φ).comp
          ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b)
            : Tensor0SSpace n I b →L[ℝ]
              ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ)) x =
        (tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b).symm
          ((ContinuousMultilinearMap.compContinuousLinearMapL
              (𝕜 := ℝ) (E := fun _ : Fin n => E) (F := ℝ) Φ)
            ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b) x))
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rfl
  rw [hsubst_eq]
  -- Step 2: CLE.symm preserves the norm.
  rw [tensor0SSpace_continuousLinearEquiv_symm_norm_apply (𝕜 := ℝ) (E := E)
      (I := I) (M := M) n b _]
  -- Step 3: bound compCLML Φ via its op-norm.
  have hopBound :
      ‖ContinuousMultilinearMap.compContinuousLinearMapL
          (𝕜 := ℝ) (E := fun _ : Fin n => E) (F := ℝ) Φ‖ ≤
        ∏ i : Fin n, ‖Φ i‖ :=
    ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
      (𝕜 := ℝ) (E := fun _ : Fin n => E) ℝ Φ
  have hCLEx_nn :
      0 ≤ ‖(tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b) x‖ :=
    norm_nonneg _
  have hCLM_le :
      ‖(ContinuousMultilinearMap.compContinuousLinearMapL
            (𝕜 := ℝ) (E := fun _ : Fin n => E) (F := ℝ) Φ)
          ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b) x)‖ ≤
        ‖ContinuousMultilinearMap.compContinuousLinearMapL
            (𝕜 := ℝ) (E := fun _ : Fin n => E) (F := ℝ) Φ‖ *
          ‖(tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b) x‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have hCLM_le' :
      ‖(ContinuousMultilinearMap.compContinuousLinearMapL
            (𝕜 := ℝ) (E := fun _ : Fin n => E) (F := ℝ) Φ)
          ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b) x)‖ ≤
        (∏ i : Fin n, ‖Φ i‖) *
          ‖(tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b) x‖ :=
    hCLM_le.trans (mul_le_mul_of_nonneg_right hopBound hCLEx_nn)
  -- Rewrite ‖CLE x‖ = ‖x‖.
  rw [tensor0SSpace_continuousLinearEquiv_norm_apply (𝕜 := ℝ) (E := E)
      (I := I) (M := M) n b x] at hCLM_le'
  exact hCLM_le'

/-! ### Bound on `tangentSlotCLM`'s pointwise factor product -/

/-- Sup-style bound on the slot-CLM factor at slot `k`. -/
private lemma tangentSlotCLM_factor_norm_le (n : ℕ) (b : M)
    (k : Fin n) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b)
    (i : Fin n) :
    ‖tangentSlotCLM (I := I) n k Φ i‖ ≤ max ‖Φ‖ 1 := by
  classical
  by_cases hi : i = k
  · rw [hi, tangentSlotCLM_self]
    exact le_max_left _ _
  · rw [tangentSlotCLM_other (I := I) n k Φ hi]
    have h_id : ‖(ContinuousLinearMap.id ℝ (TangentSpace I b))‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    exact h_id.trans (le_max_right _ _)

/-- Product bound on the `tangentSlotCLM` factor — at slot `k` the norm is
`‖Φ‖`, at every other slot it is `‖id‖ ≤ 1`. We absorb the `id` factors into
the constant `1`, yielding `∏ ≤ ‖Φ‖` when `n ≥ 1` and `∏ = 1` when `n = 0`.
We state the bound `∏ ≤ (max ‖Φ‖ 1) ^ n` which handles all cases. -/
private lemma tangentSlotCLM_prod_norm_le (n : ℕ) (b : M)
    (k : Fin n) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b) :
    (∏ i : Fin n, ‖tangentSlotCLM (I := I) n k Φ i‖) ≤
      (max ‖Φ‖ 1) ^ n := by
  classical
  have h_pow : (max ‖Φ‖ 1) ^ n = ∏ _i : Fin n, max ‖Φ‖ 1 := by
    rw [Finset.prod_const]; simp
  rw [h_pow]
  refine Finset.prod_le_prod ?_ ?_
  · intro i _; exact norm_nonneg _
  · intro i _; exact tangentSlotCLM_factor_norm_le (I := I) n b k Φ i

/-! ### The headline uniform op-norm bound — input slot

The key headline bound on `chartTensorRSInputSlotCorrection`, in
`TensorRSSpace`-norm, by a constant times `‖T b‖`. -/

theorem chartTensorRSInputSlotCorrection_norm_le_const_on_pouTsupport
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ M_F : ℝ, 0 ≤ M_F ∧
      ∀ (T : Π b' : M, TensorRSSpace r s I b') {b : M},
        b ∈ pouTsupportSet (I := I) (M := M) α →
        ∀ (j : Fin (Module.finrank ℝ E)) (k : Fin r),
          ‖chartTensorRSInputSlotCorrection (I := I) r s g α T
              (chartBasisVecFiber (I := I) α j) b k‖ ≤
            M_F * ‖T b‖ := by
  classical
  -- Part B: uniform bound on `chartLeviCivitaParallelCLM`.
  obtain ⟨C_B, hC_B_nn, hC_B⟩ :=
    chartLeviCivitaParallelCLM_chartBasisVec_opNorm_isBounded_on_pouTsupport
      (I := I) (M := M) h_atlas g α
  -- Build the headline constant.
  set M_F : ℝ := (max C_B 1) ^ r with hM_F_def
  have hM_F_nn : 0 ≤ M_F := by
    have h1 : 0 ≤ max C_B 1 := le_trans zero_le_one (le_max_right _ _)
    exact pow_nonneg h1 r
  refine ⟨M_F, hM_F_nn, ?_⟩
  intro T b hb j k
  -- Set abbreviations.
  set Φ : TangentSpace I b →L[ℝ] TangentSpace I b :=
    chartLeviCivitaParallelCLM (I := I) g α b
      (chartBasisVecFiber (I := I) α j) with hΦ_def
  set Ψ : Fin r → (TangentSpace I b →L[ℝ] TangentSpace I b) :=
    tangentSlotCLM (I := I) r k Φ with hΨ_def
  -- Φ is bounded by C_B on tsupport.
  have hΦ_norm : ‖Φ‖ ≤ C_B := hC_B (b := b) hb j
  -- Product bound on Ψ.
  have hΨ_prod : (∏ i : Fin r, ‖Ψ i‖) ≤ (max ‖Φ‖ 1) ^ r := by
    rw [hΨ_def]
    exact tangentSlotCLM_prod_norm_le (I := I) r b k Φ
  -- (max ‖Φ‖ 1) ^ r ≤ (max C_B 1) ^ r.
  have h_max_le : max ‖Φ‖ 1 ≤ max C_B 1 :=
    max_le_max hΦ_norm le_rfl
  have h_max_nn : 0 ≤ max ‖Φ‖ 1 := le_trans zero_le_one (le_max_right _ _)
  have hΨ_prod_le_C : (∏ i : Fin r, ‖Ψ i‖) ≤ M_F := by
    refine hΨ_prod.trans ?_
    rw [hM_F_def]
    exact pow_le_pow_left₀ h_max_nn h_max_le r
  -- Now apply `tensorRSSpace_opNorm_le_bound`.
  -- For any x : Tensor0SSpace r I b, bound ‖(slot correction) x‖.
  -- The constant for the opNorm_le_bound call is `M_F * ‖T b‖`.
  have hRHS_nn : 0 ≤ M_F * ‖T b‖ :=
    mul_nonneg hM_F_nn (norm_nonneg _)
  refine tensorRSSpace_opNorm_le_bound (𝕜 := ℝ) (E := E) (I := I) (M := M)
    (chartTensorRSInputSlotCorrection (I := I) r s g α T
      (chartBasisVecFiber (I := I) α j) b k) hRHS_nn ?_
  intro x
  -- Unfold the slot correction.
  -- (chartTensorRSInputSlotCorrection ... : TensorRSSpace r s I b)
  --   = (T b : Tensor0SSpace r → Tensor0SSpace s) ∘ (substCLM r b Ψ).
  -- Apply at x.
  have hcomp : (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
      chartTensorRSInputSlotCorrection (I := I) r s g α T
        (chartBasisVecFiber (I := I) α j) b k) x =
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
        (tensorSlotSubstCLM (I := I) r b Ψ x) := by
    -- chartTensorRSInputSlotCorrection unfolds to T b .comp (substCLM r b Ψ).
    change ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b).comp
        (tensorSlotSubstCLM (I := I) r b Ψ)) x =
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
        (tensorSlotSubstCLM (I := I) r b Ψ x)
    rw [ContinuousLinearMap.comp_apply]
  rw [hcomp]
  -- ‖T b (substCLM Ψ x)‖ ≤ ‖T b‖_RS * ‖substCLM Ψ x‖
  have hT_apply :
      ‖(show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (tensorSlotSubstCLM (I := I) r b Ψ x)‖ ≤
        ‖T b‖ * ‖tensorSlotSubstCLM (I := I) r b Ψ x‖ :=
    tensorRSSpace_norm_apply_le (𝕜 := ℝ) (E := E) (I := I) (M := M) (T b) _
  -- ‖substCLM Ψ x‖ ≤ (∏ ‖Ψ i‖) * ‖x‖.
  have hsubst :
      ‖tensorSlotSubstCLM (I := I) r b Ψ x‖ ≤
        (∏ i : Fin r, ‖Ψ i‖) * ‖x‖ :=
    tensorSlotSubstCLM_apply_norm_le (I := I) r b Ψ x
  -- Combine.
  have hTb_nn : 0 ≤ ‖T b‖ := norm_nonneg _
  have hx_nn : 0 ≤ ‖x‖ := norm_nonneg _
  have h_step1 :
      ‖T b‖ * ‖tensorSlotSubstCLM (I := I) r b Ψ x‖ ≤
        ‖T b‖ * ((∏ i : Fin r, ‖Ψ i‖) * ‖x‖) :=
    mul_le_mul_of_nonneg_left hsubst hTb_nn
  have h_inner_nn : 0 ≤ (∏ i : Fin r, ‖Ψ i‖) * ‖x‖ :=
    mul_nonneg (Finset.prod_nonneg (fun i _ => norm_nonneg _)) hx_nn
  -- ‖T b‖ * ((∏ ‖Ψ i‖) * ‖x‖) ≤ ‖T b‖ * (M_F * ‖x‖).
  have h_step2 :
      ‖T b‖ * ((∏ i : Fin r, ‖Ψ i‖) * ‖x‖) ≤
        ‖T b‖ * (M_F * ‖x‖) := by
    have h_prod_factor : (∏ i : Fin r, ‖Ψ i‖) * ‖x‖ ≤ M_F * ‖x‖ :=
      mul_le_mul_of_nonneg_right hΨ_prod_le_C hx_nn
    exact mul_le_mul_of_nonneg_left h_prod_factor hTb_nn
  have h_rearrange : ‖T b‖ * (M_F * ‖x‖) = M_F * ‖T b‖ * ‖x‖ := by ring
  -- Chain via le_trans.
  have hChain1 :
      ‖(show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (tensorSlotSubstCLM (I := I) r b Ψ x)‖ ≤
        ‖T b‖ * ((∏ i : Fin r, ‖Ψ i‖) * ‖x‖) :=
    hT_apply.trans h_step1
  have hChain2 :
      ‖(show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (tensorSlotSubstCLM (I := I) r b Ψ x)‖ ≤
        ‖T b‖ * (M_F * ‖x‖) :=
    hChain1.trans h_step2
  rw [h_rearrange] at hChain2
  exact hChain2

/-! ### The headline uniform op-norm bound — output slot

The output side is structurally identical but with the substitution acting
on the *output* `(0, s)`-tensor rather than the input `(0, r)`-tensor. The
factorisation is `substCLM_l .comp T b`, so the argument is dual:
`‖substCLM_l (T b x)‖ ≤ ‖substCLM_l‖ * ‖T b x‖ ≤ ‖substCLM_l‖ * ‖T b‖ * ‖x‖`. -/

theorem chartTensorRSOutputSlotCorrection_norm_le_const_on_pouTsupport
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ M_F : ℝ, 0 ≤ M_F ∧
      ∀ (T : Π b' : M, TensorRSSpace r s I b') {b : M},
        b ∈ pouTsupportSet (I := I) (M := M) α →
        ∀ (j : Fin (Module.finrank ℝ E)) (l : Fin s),
          ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T
              (chartBasisVecFiber (I := I) α j) b l‖ ≤
            M_F * ‖T b‖ := by
  classical
  -- Part B: uniform bound on `chartLeviCivitaParallelCLM`.
  obtain ⟨C_B, hC_B_nn, hC_B⟩ :=
    chartLeviCivitaParallelCLM_chartBasisVec_opNorm_isBounded_on_pouTsupport
      (I := I) (M := M) h_atlas g α
  -- Build the headline constant.
  set M_F : ℝ := (max C_B 1) ^ s with hM_F_def
  have hM_F_nn : 0 ≤ M_F := by
    have h1 : 0 ≤ max C_B 1 := le_trans zero_le_one (le_max_right _ _)
    exact pow_nonneg h1 s
  refine ⟨M_F, hM_F_nn, ?_⟩
  intro T b hb j l
  -- Set abbreviations.
  set Φ : TangentSpace I b →L[ℝ] TangentSpace I b :=
    chartLeviCivitaParallelCLM (I := I) g α b
      (chartBasisVecFiber (I := I) α j) with hΦ_def
  set Ψ : Fin s → (TangentSpace I b →L[ℝ] TangentSpace I b) :=
    tangentSlotCLM (I := I) s l Φ with hΨ_def
  -- Φ is bounded by C_B on tsupport.
  have hΦ_norm : ‖Φ‖ ≤ C_B := hC_B (b := b) hb j
  -- Product bound on Ψ (now on Fin s, slot l).
  have hΨ_prod : (∏ i : Fin s, ‖Ψ i‖) ≤ (max ‖Φ‖ 1) ^ s := by
    rw [hΨ_def]
    exact tangentSlotCLM_prod_norm_le (I := I) s b l Φ
  -- (max ‖Φ‖ 1) ^ s ≤ (max C_B 1) ^ s.
  have h_max_le : max ‖Φ‖ 1 ≤ max C_B 1 :=
    max_le_max hΦ_norm le_rfl
  have h_max_nn : 0 ≤ max ‖Φ‖ 1 := le_trans zero_le_one (le_max_right _ _)
  have hΨ_prod_le_C : (∏ i : Fin s, ‖Ψ i‖) ≤ M_F := by
    refine hΨ_prod.trans ?_
    rw [hM_F_def]
    exact pow_le_pow_left₀ h_max_nn h_max_le s
  -- Apply `tensorRSSpace_opNorm_le_bound`.
  have hRHS_nn : 0 ≤ M_F * ‖T b‖ :=
    mul_nonneg hM_F_nn (norm_nonneg _)
  refine tensorRSSpace_opNorm_le_bound (𝕜 := ℝ) (E := E) (I := I) (M := M)
    (chartTensorRSOutputSlotCorrection (I := I) r s g α T
      (chartBasisVecFiber (I := I) α j) b l) hRHS_nn ?_
  intro x
  -- Unfold: chartTensorRSOutputSlotCorrection = substCLM_l.comp T b. Apply at x.
  have hcomp : (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
      chartTensorRSOutputSlotCorrection (I := I) r s g α T
        (chartBasisVecFiber (I := I) α j) b l) x =
      tensorSlotSubstCLM (I := I) s b Ψ
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x) := by
    change ((tensorSlotSubstCLM (I := I) s b Ψ).comp
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)) x =
      tensorSlotSubstCLM (I := I) s b Ψ
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x)
    rw [ContinuousLinearMap.comp_apply]
  rw [hcomp]
  -- ‖substCLM Ψ (T b x)‖ ≤ (∏ ‖Ψ i‖) * ‖T b x‖.
  have hsubst :
      ‖tensorSlotSubstCLM (I := I) s b Ψ
          ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x)‖ ≤
        (∏ i : Fin s, ‖Ψ i‖) *
          ‖(show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x‖ :=
    tensorSlotSubstCLM_apply_norm_le (I := I) s b Ψ _
  -- ‖T b x‖ ≤ ‖T b‖_RS * ‖x‖.
  have hT_apply :
      ‖(show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x‖ ≤
        ‖T b‖ * ‖x‖ :=
    tensorRSSpace_norm_apply_le (𝕜 := ℝ) (E := E) (I := I) (M := M) (T b) x
  -- Combine: ‖substCLM Ψ (T b x)‖ ≤ (∏ ‖Ψ i‖) * ‖T b‖ * ‖x‖ ≤ M_F * ‖T b‖ * ‖x‖.
  have hTb_nn : 0 ≤ ‖T b‖ := norm_nonneg _
  have hx_nn : 0 ≤ ‖x‖ := norm_nonneg _
  have h_prod_nn : 0 ≤ ∏ i : Fin s, ‖Ψ i‖ :=
    Finset.prod_nonneg (fun i _ => norm_nonneg _)
  -- (∏ ‖Ψ i‖) * ‖T b x‖ ≤ (∏ ‖Ψ i‖) * (‖T b‖ * ‖x‖).
  have h_step1 :
      (∏ i : Fin s, ‖Ψ i‖) *
        ‖(show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x‖ ≤
      (∏ i : Fin s, ‖Ψ i‖) * (‖T b‖ * ‖x‖) :=
    mul_le_mul_of_nonneg_left hT_apply h_prod_nn
  -- (∏ ‖Ψ i‖) * (‖T b‖ * ‖x‖) ≤ M_F * (‖T b‖ * ‖x‖).
  have h_step2 :
      (∏ i : Fin s, ‖Ψ i‖) * (‖T b‖ * ‖x‖) ≤
        M_F * (‖T b‖ * ‖x‖) := by
    have h_inner_nn : 0 ≤ ‖T b‖ * ‖x‖ := mul_nonneg hTb_nn hx_nn
    exact mul_le_mul_of_nonneg_right hΨ_prod_le_C h_inner_nn
  have h_rearrange : M_F * (‖T b‖ * ‖x‖) = M_F * ‖T b‖ * ‖x‖ := by ring
  -- Chain the bounds.
  have hChain1 :
      ‖tensorSlotSubstCLM (I := I) s b Ψ
          ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x)‖ ≤
        (∏ i : Fin s, ‖Ψ i‖) * (‖T b‖ * ‖x‖) :=
    hsubst.trans h_step1
  have hChain2 :
      ‖tensorSlotSubstCLM (I := I) s b Ψ
          ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x)‖ ≤
        M_F * (‖T b‖ * ‖x‖) :=
    hChain1.trans h_step2
  rw [h_rearrange] at hChain2
  exact hChain2

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaParallelCLM_chartBasisVec_opNorm_isBounded_on_pouTsupport
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTensorRSInputSlotCorrection_norm_le_const_on_pouTsupport
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTensorRSOutputSlotCorrection_norm_le_const_on_pouTsupport
end Sanity
