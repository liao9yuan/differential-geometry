import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartJUniformBoundLocallyConstant
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ChristoffelBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TrivProj.CovNormBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartTwistUniformBound
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.ChartLeviCivitaParallelCLMUnconditional
import DifferentialGeometry.Integral.Connection.LeviCivitaChartLocal
import DifferentialGeometry.Integral.Connection.ChartTensor0SCovariantDerivative
import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivative
import DifferentialGeometry.Tensor.RSTensor.TensorRSSpaceNormBridge
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Uniform operator-norm bounds for slot-correction infrastructure

Consolidated uniform operator-norm bounds used throughout the chart-spectral
machinery on a closed Riemannian manifold `(M, g)` with a locally constant
chart selection (`HasLocallyConstantChartAt H M`):

1. **Section-fibre norm comparison** — for a chart base point `α` and ranks
   `(r, s)`, the bundle-fibre norm `‖S.toSection b‖` of a smooth
   compactly-supported `(r, s)`-tensor section `S` is bounded squared by the
   pointwise tensor inner product on the closed support of the chart-atlas
   partition-of-unity weight at `α`:
   `‖S.toSection b‖² ≤ K_S · tensorInnerPointwise g r s b (S.toFun b) (S.toFun b)`.
2. **Christoffel-correction uniform op-norm bound** — the chart-local
   Christoffel-correction CLM `christoffelCorrection g α b Y` is uniformly
   operator-norm bounded over `b ∈ tsupport (chartAtlasPOU I M α)` by a
   constant (depending on `g` and the chart at `α`, independent of `b, Y`)
   times `‖Y‖`.
3. **Chart Levi-Civita parallel CLM op-norm bound** — the chart Levi-Civita
   parallel CLM `chartLeviCivitaParallelCLM g α b (chartBasisVecFiber α j)`
   has a uniform operator-norm bound on the closed support of the
   chart-atlas POU weight at `α`.
4. **Input / output slot-correction headline bounds** — the chart-frame
   input / output slot corrections satisfy
   `‖chartTensorRSInputSlotCorrection r s g α T (chartBasisVecFiber α j) b k‖
       ≤ M_F · ‖T b‖`
   (and the analogous output-slot bound), uniformly on
   `tsupport (chartAtlasPOU I M α)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Finset Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry
open DifferentialGeometry.Tensor
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Bundle-fibre norm identification

The `TensorRSSpace r s I b` normed-group instance is induced from the model
norm along `tensorRSSpace_continuousLinearEquiv`; hence `‖S.toSection b‖`
coincides definitionally with `‖TensorRSSpace.toModel (S.toSection b)‖ =
‖S.toFun b‖`. -/

private lemma section_norm_eq_toFun_norm
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) (b : M) :
    ‖S.toSection b‖ = ‖S.toFun b‖ := rfl

/-! ## The POU-`tsupport` lies in the chart source

We restate this auxiliary inclusion locally for use with the chart-twist
uniform op-norm bound, whose hypothesis is phrased on a compact subset of
`(chartAt H α).source`. -/

private lemma pouTsupport_subset_chartAt_source_secNorm (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      (chartAt H α).source := by
  intro b hb
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  rw [trivializationAt_baseSet_eq_chartAt_source (I := I)] at hb_base
  exact hb_base

/-! ## Headline: section-fibre norm squared bounded by the tensor inner product

The headline result discharges the `K_S` parameter of downstream
`tensorInnerPointwise`-quadratic bounds: there is a uniform `K_S ≥ 0` such
that for every smooth compactly-supported `(r, s)`-tensor section `S` and
every `b` in the closed support of the chart-`α` partition-of-unity weight,
`‖S.toSection b‖^2 ≤ K_S * tensorInnerPointwise g r s b (S.toFun b) (S.toFun b)`. -/

/-- **Section-fibre norm comparison by the pointwise tensor inner product.**

For a closed Riemannian manifold `(M, g)`, a chart base point `α`, and ranks
`(r, s)`, under the locality hypothesis `HasLocallyConstantChartAt H M` on
the chart-selection function, there is a non-negative constant `K_S` such
that for every smooth compactly-supported `(r, s)`-tensor section `S` and
every base point `b` in the closed support of the chart-atlas
partition-of-unity weight at `α`,
`‖S.toSection b‖² ≤ K_S · tensorInnerPointwise g r s b (S.toFun b) (S.toFun b)`.

The constant `K_S` depends only on `(g, r, s, α)` and on the locality
hypothesis; it is independent of `S`. -/
theorem norm_section_sq_le_const_mul_tensorInnerPointwise_on_pouTsupport
    (h_atlas : HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K_S : ℝ, 0 ≤ K_S ∧
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖S.toSection b‖ ^ 2 ≤
          K_S * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) := by
  classical
  -- Compact closed-support set `K := tsupport(ρ_α) ⊆ (chartAt H α).source`.
  set Kα : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hKα_def
  have hKα_compact : IsCompact Kα :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hKα_sub_source : Kα ⊆ (chartAt H α).source :=
    pouTsupport_subset_chartAt_source_secNorm (I := I) (M := M) α
  -- Step 1: chart-trivialisation-inverse norm bound on `Kα`.
  obtain ⟨K, hK_nn, hK_le⟩ :=
    chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_pouTsupport
      (I := I) (M := M) g r s α
  -- Step 2: uniform chart-twist op-norm bound on `Kα` (uses locality).
  obtain ⟨M_tw, hM_tw_pos, hM_tw_le⟩ :=
    chartRSTwist_pointwise_opNorm_isBounded_on_compact
      (I := I) (M := M) (E := E) h_atlas α hKα_compact hKα_sub_source r s
  -- Assemble `K_S := M_tw^2 * K`.
  refine ⟨M_tw ^ 2 * K, by positivity, ?_⟩
  intro S b hb
  -- `b ∈ baseSet` for the round-trip identity.
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  -- Abbreviate `Y := chartRSTwistInv α b r s (S.toFun b)`.
  set Y : TensorRSModel r s ℝ E :=
    chartRSTwistInv (I := I) (M := M) α b r s (S.toFun b) with hY_def
  -- Round-trip: `chartRSTwist α b r s Y = S.toFun b` on `baseSet`.
  have h_round : chartRSTwist (I := I) (M := M) α b r s Y = S.toFun b := by
    rw [hY_def]
    exact chartRSTwist_chartRSTwistInv (I := I) (M := M) α hb_base r s (S.toFun b)
  -- Chart-twist op-norm at `Y`: `‖chartRSTwist α b r s Y‖ ≤ M_tw * ‖Y‖`.
  have h_tw_Y : ‖chartRSTwist (I := I) (M := M) α b r s Y‖ ≤ M_tw * ‖Y‖ :=
    hM_tw_le b hb Y
  -- Rewrite using the round-trip on the LHS.
  rw [h_round] at h_tw_Y
  -- Inverse-twist norm bound at `S.toFun b`:
  -- `‖chartRSTwistInv α b r s (S.toFun b)‖^2 ≤ K * tensorInnerPointwise g r s b (S.toFun b) (S.toFun b)`.
  have h_inv : ‖Y‖ ^ 2 ≤
      K * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) := by
    rw [hY_def]
    exact hK_le hb (S.toFun b)
  -- Square the chart-twist bound: `‖S.toFun b‖^2 ≤ (M_tw * ‖Y‖)^2 = M_tw^2 * ‖Y‖^2`.
  have h_lhs_nn : 0 ≤ ‖S.toFun b‖ := norm_nonneg _
  have h_Y_nn : 0 ≤ ‖Y‖ := norm_nonneg _
  have h_M_tw_nn : 0 ≤ M_tw := le_of_lt hM_tw_pos
  have h_rhs_nn : 0 ≤ M_tw * ‖Y‖ := mul_nonneg h_M_tw_nn h_Y_nn
  have h_sq : ‖S.toFun b‖ ^ 2 ≤ (M_tw * ‖Y‖) ^ 2 := by
    have := mul_self_le_mul_self h_lhs_nn h_tw_Y
    have h_lhs_sq : ‖S.toFun b‖ * ‖S.toFun b‖ = ‖S.toFun b‖ ^ 2 := by rw [sq]
    have h_rhs_sq : (M_tw * ‖Y‖) * (M_tw * ‖Y‖) = (M_tw * ‖Y‖) ^ 2 := by rw [sq]
    linarith
  have h_expand : (M_tw * ‖Y‖) ^ 2 = M_tw ^ 2 * ‖Y‖ ^ 2 := by ring
  -- Chain: ‖S.toFun b‖^2 ≤ M_tw^2 * ‖Y‖^2 ≤ M_tw^2 * (K * tensorInnerPointwise ...).
  have h_chain : ‖S.toFun b‖ ^ 2 ≤
      M_tw ^ 2 * (K * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b)) := by
    have h_M_tw_sq_nn : 0 ≤ M_tw ^ 2 := sq_nonneg _
    have h_step1 : ‖S.toFun b‖ ^ 2 ≤ M_tw ^ 2 * ‖Y‖ ^ 2 := by
      calc ‖S.toFun b‖ ^ 2 ≤ (M_tw * ‖Y‖) ^ 2 := h_sq
        _ = M_tw ^ 2 * ‖Y‖ ^ 2 := h_expand
    have h_step2 : M_tw ^ 2 * ‖Y‖ ^ 2 ≤
        M_tw ^ 2 * (K * tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b)) :=
      mul_le_mul_of_nonneg_left h_inv h_M_tw_sq_nn
    exact h_step1.trans h_step2
  -- Reassociate `M_tw^2 * (K * X) = (M_tw^2 * K) * X`.
  have h_assoc :
      M_tw ^ 2 * (K * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b)) =
      M_tw ^ 2 * K * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) := by ring
  -- Apply the definitional identification `‖S.toSection b‖ = ‖S.toFun b‖`.
  rw [section_norm_eq_toFun_norm S b]
  linarith

/-! ## Compactness and chart-source containment of `tsupport (POU α)`

We restate compactness as a private alias to keep proof scripts mechanical;
the public `pouTsupport_isCompact` is also available transitively. -/

/-- The closed support of the canonical POU weight at `α` is contained in the
chart source at `α` by subordinacy of the chart-atlas partition of unity. -/
private theorem pouTsupport_subset_chartAt_source_chrCorr (α : M) :
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

/-! ## Headline uniform op-norm bound on `christoffelCorrection` -/

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
    pouTsupport_subset_chartAt_source_chrCorr (I := I) (M := M) α
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

/-! ## Chart Levi-Civita parallel CLM uniform op-norm bound

A finite-dimensional inner-product space is automatically complete; we
package it as a local instance so that the `chartLeviCivitaParallelCLM`
infrastructure (which requires `[CompleteSpace E]`) is usable here. -/

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ### Abbreviations -/

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

/-! ### Model-side basis sup -/

/-- The model-space basis vector norm sup. Local copy used by the chart
Levi-Civita parallel CLM bound below. -/
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

/-! ### Part B: uniform op-norm bound on
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

/-! ### Unconditional twin of the chart Levi-Civita parallel CLM op-norm bound

The unconditional headline removes the locality hypothesis `HasLocallyConstantChartAt`.
The operator norm is computed with respect to the Riemannian fibre norm on
`TangentSpace I b` (installed via the `RiemannianBundle` instance from `g`),
matching the convention of the unconditional Levi-Civita-parallel bound
`chartLeviCivitaParallelCLM_general_X_opNorm_isBounded_on_pouTsupport_unconditional`.

The chart-basis vector field is specialised from the general vector argument:
`chartBasisVecFiber α j b = trivFromE α b ((chartModelBasis E) j)`, whose
Riemannian fibre norm is bounded uniformly on the partition-of-unity tsupport by
`C_Jinv * C_e` via the unconditional `chartJinv` op-norm bound. -/

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Unconditional uniform operator-norm bound for the chart Levi-Civita
parallel CLM applied to a chart-basis vector field, on
`tsupport (chartAtlasPOU I M α)`.**

For a closed Riemannian manifold `(M, g)`, there exists a non-negative constant
`C` such that for every `b` in the closed support of the canonical chart-atlas
partition-of-unity weight at `α` and every model-basis index `j`,

  `‖chartLeviCivitaParallelCLM g α b (chartBasisVecFiber α j)‖ ≤ C`,

where the operator norm uses the Riemannian fibre norm on `TangentSpace I b`.
The constant `C` is independent of `b` and `j`. No locality hypothesis on the
chart selection is required. -/
theorem chartLeviCivitaParallelCLM_chartBasisVec_opNorm_isBounded_on_pouTsupport_unconditional
    (g : SmoothRiemannianMetric I M) (α : M) :
    letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
      g.toContinuousRiemannianMetric
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨cg.toRiemannianMetric⟩
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ pouTsupportSet (I := I) (M := M) α →
        ∀ (j : Fin (Module.finrank ℝ E)),
          ‖chartLeviCivitaParallelCLM (I := I) g α b
              (chartBasisVecFiber (I := I) α j)‖ ≤ C := by
  classical
  letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  -- Compact base set `K := tsupport(POU α) ⊆ baseSet`.
  set K : Set M := pouTsupportSet (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := pouTsupportSet_isCompact (I := I) (M := M) α
  have hK_base : K ⊆ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α
  -- Unconditional uniform bound on `chartLeviCivitaParallelCLM g α b X` (general `X`).
  obtain ⟨C_B, hC_B_nn, hC_B⟩ :=
    DifferentialGeometry.PDE.RicciFlow.HebeyBlock.chartLeviCivitaParallelCLM_general_X_opNorm_isBounded_on_pouTsupport_unconditional
      (I := I) (M := M) g α
  -- Unconditional uniform bound on `‖chartJinv α b‖` on `K` (Riemannian fibre norm).
  obtain ⟨C_Jinv, hCJinv_nn, hCJinv_bound⟩ :=
    DifferentialGeometry.PDE.RicciFlow.HebeyBlock.chartJinv_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g α hK_compact hK_base
  -- Maximum norm of model basis vectors.
  set C_e : ℝ := chartModelBasisVecSup' E with hCe_def
  have hCe_nn : 0 ≤ C_e := chartModelBasisVecSup'_nonneg
  -- The headline constant.
  set C : ℝ := C_B * (C_Jinv * C_e) with hC_def
  have hC_nn : 0 ≤ C := by positivity
  refine ⟨C, hC_nn, ?_⟩
  intro b hb j
  -- `chartBasisVecFiber α j b = trivFromE α b ((chartModelBasis E) j)`.
  have h_X_eq : (chartBasisVecFiber (I := I) α j b : TangentSpace I b) =
      trivFromE (I := I) α b ((chartModelBasis E) j) := rfl
  -- Riemannian fibre-norm bound on the chart-basis vector at `b`.
  have h_ej_le : ‖(chartModelBasis E) j‖ ≤ C_e :=
    norm_basis_le_chartModelBasisVecSup' (E := E) j
  have h_ej_nn : 0 ≤ ‖(chartModelBasis E) j‖ := norm_nonneg _
  have h_trivFromE_le : ‖trivFromE (I := I) α b‖ ≤ C_Jinv := hCJinv_bound b hb
  have h_trivFromE_nn : 0 ≤ ‖trivFromE (I := I) α b‖ := norm_nonneg _
  have h_Xb_le : ‖(chartBasisVecFiber (I := I) α j b : TangentSpace I b)‖ ≤
      C_Jinv * C_e := by
    rw [h_X_eq]
    calc ‖trivFromE (I := I) α b ((chartModelBasis E) j)‖
        ≤ ‖trivFromE (I := I) α b‖ * ‖(chartModelBasis E) j‖ :=
          (trivFromE (I := I) α b).le_opNorm _
      _ ≤ C_Jinv * C_e := by
          have h1 : ‖trivFromE (I := I) α b‖ * ‖(chartModelBasis E) j‖ ≤
              C_Jinv * ‖(chartModelBasis E) j‖ :=
            mul_le_mul_of_nonneg_right h_trivFromE_le h_ej_nn
          have h2 : C_Jinv * ‖(chartModelBasis E) j‖ ≤ C_Jinv * C_e :=
            mul_le_mul_of_nonneg_left h_ej_le hCJinv_nn
          linarith
  -- Apply the unconditional general-`X` bound at `X = chartBasisVecFiber α j`.
  have h_clm_le :
      ‖chartLeviCivitaParallelCLM (I := I) g α b (chartBasisVecFiber (I := I) α j)‖ ≤
        C_B * ‖(chartBasisVecFiber (I := I) α j) b‖ :=
    hC_B (b := b) hb (chartBasisVecFiber (I := I) α j)
  -- Chain: `≤ C_B * ‖X b‖ ≤ C_B * (C_Jinv * C_e) = C`.
  have h_chain : C_B * ‖(chartBasisVecFiber (I := I) α j) b‖ ≤ C := by
    rw [hC_def]
    exact mul_le_mul_of_nonneg_left h_Xb_le hC_B_nn
  exact h_clm_le.trans h_chain

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
is bounded uniformly on `tsupport (chartAtlasPOU I M α)` by the Levi-Civita
parallel CLM bound above.
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

/-! ### Slot-correction unconditional twins live downstream (Riemannian norm)

The locality-free uniform op-norm bounds for the chart-frame input / output
slot corrections are NOT provided here. Their proof would route through the
model-fibre operator norm of `chartLeviCivitaParallelCLM`
(`tensorSlotSubstCLM`'s factor product is the model `E →L[ℝ] E` operator norm
of the substituted CLMs), which factors through the model-to-model chart-
Jacobian operator norm `‖chartJ α b‖` / `‖chartJinv α b‖` — the discontinuous
quantity that no `HasLocallyConstantChartAt`-free uniform bound controls.

The genuinely unconditional formulation instead measures the slot corrections
in the Riemannian fibre norm on `TensorRSSpace`; that bound is proved
downstream once the Riemannian trivialisation op-norm comparisons are in scope.
It cannot be stated here because the supporting infrastructure imports this
file. -/

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
