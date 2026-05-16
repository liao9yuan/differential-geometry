import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartJUniformBoundLocallyConstant
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChristoffelBound
import DifferentialGeometry.Integral.Connection.LeviCivitaChartLocal
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Uniform operator-norm bound on `christoffelCorrection` over `tsupport (POU α)`

For a closed Riemannian manifold `(M, g)` admitting a locally constant chart
selection, the chart-local Christoffel-correction CLM

  `christoffelCorrection g α b Y : TangentSpace I b →L[ℝ] E`

is uniformly operator-norm bounded over `b ∈ tsupport (chartAtlasPOU I M α)`
by a constant times `‖Y‖`. The constant depends on `g` and the chart at `α`
but is independent of `b` and `Y`.

The bound is the natural product of three uniform ingredients:

* `‖chartJ α b‖ ≤ C_J` uniformly on `tsupport (POU α)` (from the locally
  constant chart hypothesis, by Mathlib's `coordChangeL` identification on
  a locality neighbourhood).
* `|chartChristoffel g α i j k (extChartAt I α b)| ≤ C_Γ` uniformly on
  `tsupport (POU α)` (by continuity of the finitely many Christoffel
  symbols on the compact chart image, under the boundaryless hypothesis).
* The model-space coordinate functionals `(chartModelBasis E).coord i` and
  the model-space basis vectors `(chartModelBasis E) k` are independent of
  `b` and finite in number, so their operator norms admit a sup.

Combined via `ContinuousLinearMap.opNorm_comp_le` and
`ContinuousLinearMap.norm_smulRight_apply`, these give a uniform op-norm
bound on each of the `n^3` rank-one summands of the triple finite sum
defining `christoffelCorrection`, hence on the sum itself.
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]

/-! ## Compactness and chart-source containment of `tsupport (POU α)` -/

/-- The closed support of the canonical POU weight at `α` is compact on a
closed manifold. -/
private theorem pouTsupport_isCompact (α : M) :
    IsCompact (tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
  (isClosed_tsupport _).isCompact

/-- The closed support of the canonical POU weight at `α` is contained in the
chart source at `α` by subordinacy of the chart-atlas partition of unity. -/
private theorem pouTsupport_subset_chartAt_source (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      (chartAt H α).source :=
  (chartAtlasPOU_isSubordinate I M) α

/-! ## Finite suprema of model-side constants -/

/-- The model-space coordinate functional sup. This is a positive constant
depending only on the dimension and the model space `E`. -/
private noncomputable def chartModelBasisCoordSup (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] : ℝ :=
  (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sup'
    (by
      refine Finset.univ_nonempty_iff.mpr ?_
      exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩)
    (fun i => ‖((chartModelBasis E).coord i).toContinuousLinearMap‖)

/-- The model-space basis vector norm sup. -/
private noncomputable def chartModelBasisVecSup (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] : ℝ :=
  (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sup'
    (by
      refine Finset.univ_nonempty_iff.mpr ?_
      exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩)
    (fun k => ‖(chartModelBasis E) k‖)

private lemma chartModelBasisCoordSup_nonneg :
    0 ≤ chartModelBasisCoordSup E := by
  classical
  unfold chartModelBasisCoordSup
  have hne : (Finset.univ : Finset (Fin (Module.finrank ℝ E))).Nonempty := by
    refine Finset.univ_nonempty_iff.mpr ?_
    exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  obtain ⟨i₀, hi₀⟩ := hne
  have h_nn : (0 : ℝ) ≤ ‖((chartModelBasis E).coord i₀).toContinuousLinearMap‖ :=
    norm_nonneg _
  exact h_nn.trans (Finset.le_sup'
    (f := fun i => ‖((chartModelBasis E).coord i).toContinuousLinearMap‖) hi₀)

private lemma chartModelBasisVecSup_nonneg :
    0 ≤ chartModelBasisVecSup E := by
  classical
  unfold chartModelBasisVecSup
  have hne : (Finset.univ : Finset (Fin (Module.finrank ℝ E))).Nonempty := by
    refine Finset.univ_nonempty_iff.mpr ?_
    exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  obtain ⟨k₀, hk₀⟩ := hne
  have h_nn : (0 : ℝ) ≤ ‖(chartModelBasis E) k₀‖ := norm_nonneg _
  exact h_nn.trans (Finset.le_sup'
    (f := fun k => ‖(chartModelBasis E) k‖) hk₀)

private lemma norm_coord_le_chartModelBasisCoordSup
    (i : Fin (Module.finrank ℝ E)) :
    ‖((chartModelBasis E).coord i).toContinuousLinearMap‖ ≤
      chartModelBasisCoordSup E := by
  classical
  unfold chartModelBasisCoordSup
  exact Finset.le_sup'
    (f := fun i => ‖((chartModelBasis E).coord i).toContinuousLinearMap‖)
    (Finset.mem_univ _)

private lemma norm_basis_le_chartModelBasisVecSup
    (k : Fin (Module.finrank ℝ E)) :
    ‖(chartModelBasis E) k‖ ≤ chartModelBasisVecSup E := by
  classical
  unfold chartModelBasisVecSup
  exact Finset.le_sup'
    (f := fun k => ‖(chartModelBasis E) k‖)
    (Finset.mem_univ _)

/-! ## Per-summand operator-norm bound -/

/-- Operator-norm bound on a single summand of the triple sum defining
`christoffelCorrection`, at a point `b` of the tangent-trivialisation
neighbourhood, with all geometric / model-side constants exposed. -/
private lemma christoffelCorrection_summand_opNorm_le
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) (Y : E)
    (i j k : Fin (Module.finrank ℝ E))
    (C_J : ℝ) (hCJ : ‖chartJ (I := I) (M := M) α b‖ ≤ C_J)
    (hCJ_nn : 0 ≤ C_J)
    (C_Γ : ℝ) (hCΓ : |chartChristoffel (I := I) g α i j k (extChartAt I α b)| ≤ C_Γ)
    (hCΓ_nn : 0 ≤ C_Γ) :
    ‖(((chartModelBasis E).coord i).toContinuousLinearMap.comp
          (trivToE (I := I) α b)).smulRight
        (((chartModelBasis E).repr Y j *
            chartChristoffel (I := I) g α i j k (extChartAt I α b)) •
          (chartModelBasis E) k)‖ ≤
      chartModelBasisCoordSup E * C_J *
        (chartModelBasisCoordSup E * ‖Y‖ * C_Γ) *
        chartModelBasisVecSup E := by
  classical
  -- Abbreviations.
  set L_i : E →L[ℝ] ℝ := ((chartModelBasis E).coord i).toContinuousLinearMap
  set L_j : E →L[ℝ] ℝ := ((chartModelBasis E).coord j).toContinuousLinearMap
  set Γijk : ℝ := chartChristoffel (I := I) g α i j k (extChartAt I α b)
  -- Step 1: `‖smulRight L v‖ = ‖L‖ * ‖v‖`.
  rw [ContinuousLinearMap.norm_smulRight_apply]
  -- Step 2: `‖L_i.comp (trivToE α b)‖ ≤ ‖L_i‖ * ‖trivToE α b‖`.
  have hcomp_le :
      ‖L_i.comp (trivToE (I := I) α b)‖ ≤
        ‖L_i‖ * ‖trivToE (I := I) α b‖ :=
    ContinuousLinearMap.opNorm_comp_le L_i (trivToE (I := I) α b)
  -- `trivToE α b` is definitionally `chartJ α b`, hence the same norm.
  have h_triv_eq_chartJ :
      ‖trivToE (I := I) α b‖ = ‖chartJ (I := I) (M := M) α b‖ := rfl
  rw [h_triv_eq_chartJ] at hcomp_le
  -- Step 3: bound the scalar part `‖(b.repr Y j) * Γijk • e_k‖ = |(b.repr Y j) * Γijk| * ‖e_k‖`.
  have h_scalar_norm :
      ‖((chartModelBasis E).repr Y j * Γijk) • (chartModelBasis E) k‖ =
        |(chartModelBasis E).repr Y j * Γijk| * ‖(chartModelBasis E) k‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  rw [h_scalar_norm]
  -- Step 4: bound `|(b.repr Y j) * Γijk|` by `(‖L_j‖ * ‖Y‖) * C_Γ`.
  have h_repr_eq : (chartModelBasis E).repr Y j = L_j Y := rfl
  have h_repr_bound : |(chartModelBasis E).repr Y j| ≤ ‖L_j‖ * ‖Y‖ := by
    rw [h_repr_eq]
    have := L_j.le_opNorm Y
    have h_abs : ‖L_j Y‖ = |L_j Y| := Real.norm_eq_abs _
    rw [h_abs] at this
    exact this
  have h_abs_mul : |(chartModelBasis E).repr Y j * Γijk| =
      |(chartModelBasis E).repr Y j| * |Γijk| := abs_mul _ _
  have h_Lj_le : ‖L_j‖ ≤ chartModelBasisCoordSup E :=
    norm_coord_le_chartModelBasisCoordSup (E := E) j
  have h_Lj_nn : 0 ≤ ‖L_j‖ := norm_nonneg _
  have h_Y_nn : 0 ≤ ‖Y‖ := norm_nonneg _
  have h_abs_Γ_nn : 0 ≤ |Γijk| := abs_nonneg _
  -- `|b.repr Y j| * |Γijk| ≤ (‖L_j‖ * ‖Y‖) * C_Γ`.
  have h_scalar_bound :
      |(chartModelBasis E).repr Y j * Γijk| ≤
        chartModelBasisCoordSup E * ‖Y‖ * C_Γ := by
    rw [h_abs_mul]
    -- `|repr| * |Γ| ≤ (‖L_j‖ * ‖Y‖) * C_Γ`.
    have h1 : |(chartModelBasis E).repr Y j| * |Γijk| ≤
        (‖L_j‖ * ‖Y‖) * C_Γ := by
      have hpos : 0 ≤ ‖L_j‖ * ‖Y‖ := by positivity
      have h_mid : |(chartModelBasis E).repr Y j| * |Γijk| ≤
          (‖L_j‖ * ‖Y‖) * |Γijk| :=
        mul_le_mul_of_nonneg_right h_repr_bound h_abs_Γ_nn
      have h_end : (‖L_j‖ * ‖Y‖) * |Γijk| ≤ (‖L_j‖ * ‖Y‖) * C_Γ :=
        mul_le_mul_of_nonneg_left hCΓ hpos
      linarith
    -- Now upgrade `‖L_j‖` to `chartModelBasisCoordSup`.
    have hΓ_nn : 0 ≤ C_Γ := hCΓ_nn
    have h_step : (‖L_j‖ * ‖Y‖) * C_Γ ≤
        (chartModelBasisCoordSup E * ‖Y‖) * C_Γ := by
      have h_left : ‖L_j‖ * ‖Y‖ ≤ chartModelBasisCoordSup E * ‖Y‖ :=
        mul_le_mul_of_nonneg_right h_Lj_le h_Y_nn
      exact mul_le_mul_of_nonneg_right h_left hΓ_nn
    have h_eq : (chartModelBasisCoordSup E * ‖Y‖) * C_Γ =
        chartModelBasisCoordSup E * ‖Y‖ * C_Γ := by ring
    linarith
  -- Step 5: bound `‖e_k‖` by `chartModelBasisVecSup E`.
  have h_ek_le : ‖(chartModelBasis E) k‖ ≤ chartModelBasisVecSup E :=
    norm_basis_le_chartModelBasisVecSup (E := E) k
  have h_ek_nn : 0 ≤ ‖(chartModelBasis E) k‖ := norm_nonneg _
  -- Step 6: bound `‖L_i‖` by `chartModelBasisCoordSup E`.
  have h_Li_le : ‖L_i‖ ≤ chartModelBasisCoordSup E :=
    norm_coord_le_chartModelBasisCoordSup (E := E) i
  have h_Li_nn : 0 ≤ ‖L_i‖ := norm_nonneg _
  have h_J_nn : 0 ≤ ‖chartJ (I := I) (M := M) α b‖ := norm_nonneg _
  have h_coord_nn : 0 ≤ chartModelBasisCoordSup E := chartModelBasisCoordSup_nonneg
  have h_vec_nn : 0 ≤ chartModelBasisVecSup E := chartModelBasisVecSup_nonneg
  -- Combine: `‖L_i.comp triv‖ * (|.| * ‖e_k‖) ≤ (C_coord * C_J) * ((C_coord * ‖Y‖ * C_Γ) * C_vec)`.
  set A : ℝ := ‖L_i.comp (trivToE (I := I) α b)‖
  set B : ℝ := |(chartModelBasis E).repr Y j * Γijk| * ‖(chartModelBasis E) k‖
  -- Goal: `A * B ≤ C_coord * C_J * (C_coord * ‖Y‖ * C_Γ) * C_vec`.
  have hA_nn : 0 ≤ A := norm_nonneg _
  have hB_nn : 0 ≤ B := by
    refine mul_nonneg ?_ h_ek_nn
    exact abs_nonneg _
  -- `A ≤ ‖L_i‖ * ‖chartJ α b‖ ≤ C_coord * C_J`.
  have hA_le : A ≤ chartModelBasisCoordSup E * C_J := by
    refine hcomp_le.trans ?_
    have h_first : ‖L_i‖ * ‖chartJ (I := I) (M := M) α b‖ ≤
        chartModelBasisCoordSup E * ‖chartJ (I := I) (M := M) α b‖ :=
      mul_le_mul_of_nonneg_right h_Li_le h_J_nn
    have h_second :
        chartModelBasisCoordSup E * ‖chartJ (I := I) (M := M) α b‖ ≤
          chartModelBasisCoordSup E * C_J :=
      mul_le_mul_of_nonneg_left hCJ h_coord_nn
    linarith
  -- `B ≤ (C_coord * ‖Y‖ * C_Γ) * C_vec`.
  have hB_le : B ≤ (chartModelBasisCoordSup E * ‖Y‖ * C_Γ) *
      chartModelBasisVecSup E := by
    have h_first :
        |(chartModelBasis E).repr Y j * Γijk| * ‖(chartModelBasis E) k‖ ≤
          (chartModelBasisCoordSup E * ‖Y‖ * C_Γ) *
            ‖(chartModelBasis E) k‖ :=
      mul_le_mul_of_nonneg_right h_scalar_bound h_ek_nn
    have h_second :
        (chartModelBasisCoordSup E * ‖Y‖ * C_Γ) * ‖(chartModelBasis E) k‖ ≤
          (chartModelBasisCoordSup E * ‖Y‖ * C_Γ) *
            chartModelBasisVecSup E := by
      have h_left_nn : 0 ≤ chartModelBasisCoordSup E * ‖Y‖ * C_Γ := by positivity
      exact mul_le_mul_of_nonneg_left h_ek_le h_left_nn
    linarith
  -- Multiply: `A * B ≤ (C_coord * C_J) * ((C_coord * ‖Y‖ * C_Γ) * C_vec)`.
  have hRHS_nn : 0 ≤ (chartModelBasisCoordSup E * ‖Y‖ * C_Γ) *
      chartModelBasisVecSup E := by positivity
  have h_AB_le :
      A * B ≤ (chartModelBasisCoordSup E * C_J) *
        ((chartModelBasisCoordSup E * ‖Y‖ * C_Γ) * chartModelBasisVecSup E) := by
    have h_lhs : A * B ≤ (chartModelBasisCoordSup E * C_J) * B :=
      mul_le_mul_of_nonneg_right hA_le hB_nn
    have h_lhs2_nn : 0 ≤ chartModelBasisCoordSup E * C_J := by positivity
    have h_rhs : (chartModelBasisCoordSup E * C_J) * B ≤
        (chartModelBasisCoordSup E * C_J) *
          ((chartModelBasisCoordSup E * ‖Y‖ * C_Γ) * chartModelBasisVecSup E) :=
      mul_le_mul_of_nonneg_left hB_le h_lhs2_nn
    linarith
  -- Rearrange RHS into the form requested.
  have h_rearrange :
      (chartModelBasisCoordSup E * C_J) *
        ((chartModelBasisCoordSup E * ‖Y‖ * C_Γ) * chartModelBasisVecSup E) =
      chartModelBasisCoordSup E * C_J *
        (chartModelBasisCoordSup E * ‖Y‖ * C_Γ) *
        chartModelBasisVecSup E := by ring
  linarith

/-! ## Headline uniform op-norm bound -/

/-- **Uniform operator-norm bound for `christoffelCorrection g α b` on
`tsupport (chartAtlasPOU I M α)`.**

For a closed Riemannian manifold `(M, g)` with a locally constant chart
selection at the model, there exists a non-negative constant `C` depending
only on `g`, the chart at `α`, and the model space `E`, such that for every
`b` in the closed support of the canonical chart-atlas partition-of-unity
weight at `α`, the Christoffel-correction CLM satisfies

  `‖christoffelCorrection g α b Y‖ ≤ C * ‖Y‖`

for every `Y : E`. The constant `C` is independent of `b` and `Y`. -/
theorem christoffelCorrection_opNorm_isBounded_on_pouTsupport
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ Y : E, ‖christoffelCorrection (I := I) g α b Y‖ ≤ C * ‖Y‖ := by
  classical
  -- Notation for the compact base set.
  set K : Set M := tsupport (fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_def
  have hK_compact : IsCompact K := pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K ⊆ (chartAt H α).source :=
    pouTsupport_subset_chartAt_source (I := I) (M := M) α
  -- γ2.1: uniform bound on `‖chartJ α b‖`.
  obtain ⟨C_J, hCJ_pos, hCJ_bound⟩ :=
    chartJ_opNorm_isBounded_on_compact (I := I) (M := M) h_atlas α hK_compact hK_sub
  have hCJ_nn : 0 ≤ C_J := le_of_lt hCJ_pos
  -- Christoffel sup bound on the chart image.
  obtain ⟨C_Γ, hCΓ_nn, hCΓ_bound⟩ :=
    chartChristoffel_bdd_on_pou_tsupport (I := I) (M := M) g α
  -- Set the headline constant.
  set n : ℕ := Module.finrank ℝ E with hn_def
  set C_coord : ℝ := chartModelBasisCoordSup E with hC_coord_def
  set C_vec : ℝ := chartModelBasisVecSup E with hC_vec_def
  set C : ℝ := (n : ℝ) ^ 3 *
    (C_coord * C_J * (C_coord * C_Γ) * C_vec) with hC_def
  have hC_coord_nn : 0 ≤ C_coord := chartModelBasisCoordSup_nonneg
  have hC_vec_nn : 0 ≤ C_vec := chartModelBasisVecSup_nonneg
  have hC_nn : 0 ≤ C := by
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
    have hrest_nn : 0 ≤ C_coord * C_J * (C_coord * C_Γ) * C_vec := by positivity
    exact mul_nonneg this hrest_nn
  refine ⟨C, hC_nn, ?_⟩
  intro b hb Y
  -- Pointwise op-norm of the triple sum bounded by sum of op-norms.
  -- Unfold the definition.
  have hb_chartJ : ‖chartJ (I := I) (M := M) α b‖ ≤ C_J := hCJ_bound b hb
  -- Translate `b ∈ K` to `extChartAt I α b ∈ extChartAt I α '' K`.
  have hb_extImg : extChartAt I α b ∈
      (extChartAt I α) ''
        (tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) := by
    exact ⟨b, hb, rfl⟩
  have hb_Γ : ∀ i j k : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g α i j k (extChartAt I α b)| ≤ C_Γ := by
    intro i j k
    exact hCΓ_bound (extChartAt I α b) hb_extImg i j k
  -- Set the per-summand bound `D := C_coord * C_J * (C_coord * ‖Y‖ * C_Γ) * C_vec`.
  set D : ℝ := C_coord * C_J * (C_coord * ‖Y‖ * C_Γ) * C_vec with hD_def
  have hD_nn : 0 ≤ D := by
    have : 0 ≤ C_coord * ‖Y‖ * C_Γ := by positivity
    have : 0 ≤ C_coord * C_J := by positivity
    positivity
  -- For each summand `(i, j, k)`, the op-norm is ≤ D.
  have h_per : ∀ i j k : Fin (Module.finrank ℝ E),
      ‖(((chartModelBasis E).coord i).toContinuousLinearMap.comp
            (trivToE (I := I) α b)).smulRight
          (((chartModelBasis E).repr Y j *
              chartChristoffel (I := I) g α i j k (extChartAt I α b)) •
            (chartModelBasis E) k)‖ ≤ D := by
    intro i j k
    exact christoffelCorrection_summand_opNorm_le (I := I)
      g α b Y i j k C_J hb_chartJ hCJ_nn C_Γ (hb_Γ i j k) hCΓ_nn
  -- Triangle inequality on the triple sum.
  unfold christoffelCorrection
  -- Step a: opNorm of `∑_i (· · ·) ≤ ∑_i ‖· · ·‖`.
  have h_outer_norm :
      ‖∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              (((chartModelBasis E).coord i).toContinuousLinearMap.comp
                  (trivToE (I := I) α b)).smulRight
                (((chartModelBasis E).repr Y j *
                    chartChristoffel (I := I) g α i j k (extChartAt I α b)) •
                  (chartModelBasis E) k)‖ ≤
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E), D := by
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun k _ => ?_)
    exact h_per i j k
  -- Step b: collapse the triple sum-of-constant.
  have h_sum_const :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E), D = (n : ℝ) ^ 3 * D := by
    have h_inner :
        ∀ i j : Fin (Module.finrank ℝ E),
          (∑ _k : Fin (Module.finrank ℝ E), D) = (n : ℝ) * D := by
      intro i j
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul, hn_def]
    have h_middle :
        ∀ i : Fin (Module.finrank ℝ E),
          (∑ _j : Fin (Module.finrank ℝ E),
            (∑ _k : Fin (Module.finrank ℝ E), D)) = (n : ℝ) ^ 2 * D := by
      intro i
      calc (∑ _j : Fin (Module.finrank ℝ E),
              (∑ _k : Fin (Module.finrank ℝ E), D))
            = ∑ _j : Fin (Module.finrank ℝ E), (n : ℝ) * D := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              exact h_inner i j
          _ = (n : ℝ) * ((n : ℝ) * D) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
              simp [nsmul_eq_mul, hn_def]
          _ = (n : ℝ) ^ 2 * D := by ring
    calc (∑ i : Fin (Module.finrank ℝ E),
            (∑ _j : Fin (Module.finrank ℝ E),
              (∑ _k : Fin (Module.finrank ℝ E), D)))
          = ∑ i : Fin (Module.finrank ℝ E), (n : ℝ) ^ 2 * D := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            exact h_middle i
        _ = (n : ℝ) * ((n : ℝ) ^ 2 * D) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            simp [nsmul_eq_mul, hn_def]
        _ = (n : ℝ) ^ 3 * D := by ring
  rw [h_sum_const] at h_outer_norm
  -- Step c: rewrite `(n : ℝ)^3 * D = C * ‖Y‖`.
  have h_C_eq : (n : ℝ) ^ 3 * D = C * ‖Y‖ := by
    rw [hC_def, hD_def]
    ring
  rw [h_C_eq] at h_outer_norm
  exact h_outer_norm

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.christoffelCorrection_opNorm_isBounded_on_pouTsupport
end Sanity
