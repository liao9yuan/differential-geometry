import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SlotUniformBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartJUniformBoundLocallyConstant
import DifferentialGeometry.Integral.Connection.LeviCivitaChartLocal
import DifferentialGeometry.Integral.Connection.ChartTensor0SCovariantDerivative

/-!
# Uniform operator-norm bound for `chartLeviCivitaParallelCLM` along a general vector field

The headline statement extends the basis-vector bound
`chartLeviCivitaParallelCLM_chartBasisVec_opNorm_isBounded_on_pouTsupport`
to a general tangent vector argument: there exists a constant `C ≥ 0` such
that for every `b` in the closed support of the canonical chart-atlas
partition-of-unity weight at `α` and every vector-field section `X`, the
operator norm `‖chartLeviCivitaParallelCLM g α b X‖` is bounded by
`C * ‖X b‖`.

The key observation is that `chartLeviCivitaParallelCLM g α b X` only
depends on the value `X b` at the point `b`, via the formula

  `chartLeviCivitaParallelCLM g α b X = (trivFromE α b).comp
      (christoffelCorrection g α b (trivToE α b (X b)))`.

The proof factors through the Christoffel-correction op-norm bound and the
two trivialization op-norm bounds (`chartJ`, `chartJinv`), all of which are
uniformly bounded on the partition-of-unity tsupport under the locality
hypothesis `HasLocallyConstantChartAt H M`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Finset
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry
open DifferentialGeometry.Tensor
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## Factored op-norm bound for a general vector argument

The chart Levi-Civita parallel CLM at `b` along the section `X` is
`(trivFromE α b).comp (christoffelCorrection g α b (trivToE α b (X b)))`.
Its operator norm is therefore bounded by

  `‖trivFromE α b‖ * ‖christoffelCorrection g α b (trivToE α b (X b))‖`,

and the Christoffel-correction op-norm is bounded by `C_χ * ‖trivToE α b (X b)‖`.
Both `‖trivFromE α b‖` and `‖trivToE α b (X b)‖ ≤ ‖trivToE α b‖ * ‖X b‖` admit
uniform bounds on the POU tsupport. -/

private lemma chartLeviCivitaParallelCLM_general_opNorm_le_factors
    (g : SmoothRiemannianMetric I M) (α b : M)
    (X : Π b' : M, TangentSpace I b')
    (C_J C_Jinv C_χ : ℝ)
    (hCJ : ‖chartJ (I := I) (M := M) α b‖ ≤ C_J) (_hCJ_nn : 0 ≤ C_J)
    (hCJinv : ‖chartJinv (I := I) (M := M) α b‖ ≤ C_Jinv) (hCJinv_nn : 0 ≤ C_Jinv)
    (hCχ : ∀ Y : E, ‖christoffelCorrection (I := I) g α b Y‖ ≤ C_χ * ‖Y‖)
    (hCχ_nn : 0 ≤ C_χ) :
    ‖chartLeviCivitaParallelCLM (I := I) g α b X‖ ≤
      C_Jinv * C_χ * C_J * ‖X b‖ := by
  classical
  -- Step 1: unfold the definition.
  unfold chartLeviCivitaParallelCLM
  -- Step 2: bound the composition by the product of op-norms.
  set Y : E := trivToE (I := I) α b (X b) with hY_def
  have h_comp_le :
      ‖(trivFromE (I := I) α b).comp
          (christoffelCorrection (I := I) g α b Y)‖ ≤
        ‖trivFromE (I := I) α b‖ *
          ‖christoffelCorrection (I := I) g α b Y‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  -- Step 3: identify ‖trivFromE α b‖ = ‖chartJinv α b‖, ≤ C_Jinv.
  have h_trivFromE_norm :
      ‖trivFromE (I := I) α b‖ = ‖chartJinv (I := I) (M := M) α b‖ := rfl
  have h_trivFromE_le : ‖trivFromE (I := I) α b‖ ≤ C_Jinv := by
    rw [h_trivFromE_norm]; exact hCJinv
  have h_trivFromE_nn : 0 ≤ ‖trivFromE (I := I) α b‖ := norm_nonneg _
  -- Step 4: bound ‖Y‖ = ‖trivToE α b (X b)‖ ≤ ‖trivToE α b‖ * ‖X b‖ ≤ C_J * ‖X b‖.
  have h_Y_le_triv :
      ‖Y‖ ≤ ‖trivToE (I := I) α b‖ * ‖X b‖ := by
    rw [hY_def]
    exact (trivToE (I := I) α b).le_opNorm (X b)
  have h_triv_J : ‖trivToE (I := I) α b‖ = ‖chartJ (I := I) (M := M) α b‖ := rfl
  have h_Xb_nn : 0 ≤ ‖X b‖ := norm_nonneg _
  have h_Y_le : ‖Y‖ ≤ C_J * ‖X b‖ := by
    refine h_Y_le_triv.trans ?_
    rw [h_triv_J]
    exact mul_le_mul_of_nonneg_right hCJ h_Xb_nn
  -- Step 5: bound the Christoffel correction at Y.
  have h_χ_Y : ‖christoffelCorrection (I := I) g α b Y‖ ≤ C_χ * ‖Y‖ := hCχ Y
  have h_Y_nn : 0 ≤ ‖Y‖ := norm_nonneg _
  have h_χ_le : ‖christoffelCorrection (I := I) g α b Y‖ ≤ C_χ * (C_J * ‖X b‖) :=
    h_χ_Y.trans (mul_le_mul_of_nonneg_left h_Y_le hCχ_nn)
  -- Step 6: combine.
  have h_χ_nn : 0 ≤ ‖christoffelCorrection (I := I) g α b Y‖ := norm_nonneg _
  have h_step1 :
      ‖trivFromE (I := I) α b‖ *
          ‖christoffelCorrection (I := I) g α b Y‖ ≤
        C_Jinv * ‖christoffelCorrection (I := I) g α b Y‖ :=
    mul_le_mul_of_nonneg_right h_trivFromE_le h_χ_nn
  have h_step2 :
      C_Jinv * ‖christoffelCorrection (I := I) g α b Y‖ ≤
        C_Jinv * (C_χ * (C_J * ‖X b‖)) :=
    mul_le_mul_of_nonneg_left h_χ_le hCJinv_nn
  have h_rearrange :
      C_Jinv * (C_χ * (C_J * ‖X b‖)) = C_Jinv * C_χ * C_J * ‖X b‖ := by ring
  linarith

/-! ## Headline: uniform op-norm bound on `tsupport (chartAtlasPOU I M α)`

The compact base set is the closed support of the canonical chart-atlas
partition-of-unity weight at `α`, expressed as
`tsupport (fun x => (chartAtlasPOU I M α : M → ℝ) x)`. It is the same
compact-in-chart-source set used by the basis-vector bound
`chartLeviCivitaParallelCLM_chartBasisVec_opNorm_isBounded_on_pouTsupport`. -/

/-- **Uniform operator-norm bound for `chartLeviCivitaParallelCLM g α b X` on
`tsupport (chartAtlasPOU I M α)`, for a general tangent vector argument.**

For a closed Riemannian manifold `(M, g)` with a locally constant chart
selection at the model, there exists a non-negative constant `C` depending
only on `g`, the chart at `α`, and the locality hypothesis, such that for
every `b` in the closed support of the canonical chart-atlas
partition-of-unity weight at `α` and every vector-field section
`X : Π b', TangentSpace I b'`, the chart Levi-Civita parallel CLM satisfies

  `‖chartLeviCivitaParallelCLM g α b X‖ ≤ C * ‖X b‖`.

The constant `C` is independent of `b` and `X`. The CLM only depends on the
section `X` through its value `X b` at the point `b`, so the right-hand side
`C * ‖X b‖` is the natural quantity. -/
theorem chartLeviCivitaParallelCLM_general_X_opNorm_isBounded_on_pouTsupport
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ X : Π b' : M, TangentSpace I b',
          ‖chartLeviCivitaParallelCLM (I := I) g α b X‖ ≤ C * ‖X b‖ := by
  classical
  -- Set up the compact base set.
  set K : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_def
  have hK_compact : IsCompact K := pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  -- Step 1: uniform bound on ‖chartJ α b‖ on K.
  obtain ⟨C_J, hCJ_pos, hCJ_bound⟩ :=
    chartJ_opNorm_isBounded_on_compact (I := I) (M := M) h_atlas α hK_compact hK_sub
  have hCJ_nn : 0 ≤ C_J := le_of_lt hCJ_pos
  -- Step 2: uniform bound on ‖chartJinv α b‖ on K.
  obtain ⟨C_Jinv, hCJinv_pos, hCJinv_bound⟩ :=
    chartJinv_opNorm_isBounded_on_compact (I := I) (M := M)
      h_atlas α hK_compact hK_sub
  have hCJinv_nn : 0 ≤ C_Jinv := le_of_lt hCJinv_pos
  -- Step 3: uniform bound on ‖christoffelCorrection g α b‖ on the POU tsupport.
  obtain ⟨C_χ, hCχ_nn, hCχ_bound⟩ :=
    christoffelCorrection_opNorm_isBounded_on_pouTsupport
      (I := I) (M := M) h_atlas g α
  -- Set the headline constant.
  set C : ℝ := C_Jinv * C_χ * C_J with hC_def
  have hC_nn : 0 ≤ C := by positivity
  refine ⟨C, hC_nn, ?_⟩
  intro b hb X
  have h_CJ : ‖chartJ (I := I) (M := M) α b‖ ≤ C_J := hCJ_bound b hb
  have h_CJinv : ‖chartJinv (I := I) (M := M) α b‖ ≤ C_Jinv := hCJinv_bound b hb
  have h_Cχ : ∀ Y : E, ‖christoffelCorrection (I := I) g α b Y‖ ≤ C_χ * ‖Y‖ :=
    fun Y => hCχ_bound (b := b) hb Y
  exact
    chartLeviCivitaParallelCLM_general_opNorm_le_factors (I := I) (M := M)
      g α b X C_J C_Jinv C_χ
      h_CJ hCJ_nn h_CJinv hCJinv_nn h_Cχ hCχ_nn

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaParallelCLM_general_X_opNorm_isBounded_on_pouTsupport
end Sanity
