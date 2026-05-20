import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivativeOpNorm
import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivativeAgreement
import DifferentialGeometry.Integral.Connection.LeviCivita
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartLeviCivitaParallelCLMOpNorm
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.GoodSetMeasure

/-!
# Pointwise op-norm bound for the second-application term in the
`(r, s)`-tensor connection-Laplacian frame trace

The frame-trace formula expresses `(Δ_∇ T)(x)` as a sum over `i` of two
terms: a *first-application* term and a *second-application* term
`cov_RS T x ((LeviCivita g) B_i x (B_i x))`. This file ships the
pointwise op-norm bound for the second-application term, in two stages:

* a bound on the inner Γ-correction `(LeviCivita g) X b (X b)` from the
  chart-α Levi-Civita formula and the uniform op-norm bounds on the
  trivialisations and the Christoffel correction;
* a bound on `cov_RS T b v` for any vector `v ∈ T_b M`, obtained from
  `chartTensorRSCovariantDerivative_opNorm_le_pou_tsupport` after a
  smooth extension of `v` and the chart-frame agreement
  `chartTensorRSCovariantDerivative_eq_abstract`. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## Stage 1: pointwise norm bound for `(LeviCivita g) X b (X b)`

For a smooth tangent vector field `X`, the bundled Levi-Civita value
`(LeviCivita g).toFun X b (X b)` agrees with the chart-α Levi-Civita
value at every `b` on the chart-α good set. The latter is the
trivialisation-pullback of a sum of two terms (the Fréchet-derivative
of the chart-representation of `X` and the Christoffel correction), each
of which admits a uniform op-norm bound on the partition-of-unity
tsupport via the previously shipped trivialisation and Christoffel-
correction bounds.

The resulting bound is

  `‖(LeviCivita g) X b (X b)‖
      ≤ C * ( ‖fderiv ℝ (chartE_section_repr α X ∘ symm)
                  (extChartAt I α b)‖ * ‖X b‖ + ‖X b‖^2 )`.

The constant `C` depends only on the chart at `α`, the locality
hypothesis, and the metric `g`. -/

/-- **Pointwise norm bound for the inner Γ-correction at `b`.** -/
theorem leviCivita_X_X_norm_bound_on_pouTsupport
    (h_atlas : HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
          ‖(LeviCivita (I := I) g).toFun X.toFun b (X.toFun b)‖ ≤
            C * (‖fderiv ℝ (chartE_section_repr (I := I) α X.toFun ∘
                  (extChartAt I α).symm) (extChartAt I α b)‖ * ‖X.toFun b‖
                + ‖X.toFun b‖ ^ 2) := by
  classical
  set K : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_def
  have hK_compact : IsCompact K := pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  -- Uniform bounds on `chartJ`, `chartJinv`, `christoffelCorrection`.
  obtain ⟨C_J, hCJ_pos, hCJ_bound⟩ :=
    chartJ_opNorm_isBounded_on_compact (I := I) (M := M) h_atlas α hK_compact hK_sub
  have hCJ_nn : 0 ≤ C_J := le_of_lt hCJ_pos
  obtain ⟨C_Jinv, hCJinv_pos, hCJinv_bound⟩ :=
    chartJinv_opNorm_isBounded_on_compact (I := I) (M := M)
      h_atlas α hK_compact hK_sub
  have hCJinv_nn : 0 ≤ C_Jinv := le_of_lt hCJinv_pos
  obtain ⟨C_χ, hCχ_nn, hCχ_bound⟩ :=
    christoffelCorrection_opNorm_isBounded_on_pouTsupport
      (I := I) (M := M) h_atlas g α
  -- Headline constant: `C_Jinv * max C_J (C_χ * C_J)` works, but we use the
  -- simpler form `C := C_Jinv * (C_J + C_χ * C_J)` which dominates both
  -- summands after one application of the triangle inequality.
  set C : ℝ := C_Jinv * (C_J + C_χ * C_J) with hC_def
  have hC_nn : 0 ≤ C := by
    have h₁ : 0 ≤ C_χ * C_J := mul_nonneg hCχ_nn hCJ_nn
    have h₂ : 0 ≤ C_J + C_χ * C_J := by linarith
    exact mul_nonneg hCJinv_nn h₂
  refine ⟨C, hC_nn, ?_⟩
  intro b hb X
  -- Membership in the chart-α good set, under boundaryless.
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := by
    have h_eq := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α
    rw [h_eq, extChartAt_source_eq_chartAt_source (I := I)]
    exact hK_sub hb
  -- Manifold-differentiability of `X` at `b`.
  set X_fn : Π y : M, TangentSpace I y := X.toFun with hX_fn_def
  have hX_at :
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun y : M => TotalSpace.mk' E
          (E := fun z : M => TangentSpace I z) y (X_fn y)) b :=
    (X.contMDiff b).mdifferentiableAt (by simp)
  -- Identify bundled LC with chart LC at `b`.
  have h_eq :
      (LeviCivita (I := I) g).toFun X_fn b (X_fn b) =
        chartLeviCivita (I := I) g α X_fn b (X_fn b) :=
    LeviCivita_chart_apply (I := I) g α hb_good hX_at (X_fn b)
  -- Chart LC formula at the good-set point.
  set N_dX : ℝ := ‖fderiv ℝ (chartE_section_repr (I := I) α X.toFun ∘
        (extChartAt I α).symm) (extChartAt I α b)‖ with hN_dX_def
  set N_X : ℝ := ‖X.toFun b‖ with hN_X_def
  have hN_X_nn : 0 ≤ N_X := norm_nonneg _
  have hN_dX_nn : 0 ≤ N_dX := norm_nonneg _
  have h_chart :
      chartLeviCivita (I := I) g α X.toFun b (X.toFun b) =
        trivFromE (I := I) α b
          (fderiv ℝ (chartE_section_repr (I := I) α X.toFun ∘
              (extChartAt I α).symm) (extChartAt I α b)
              (trivToE (I := I) α b (X.toFun b)) +
            christoffelCorrection (I := I) g α b
              (chartE_section_repr (I := I) α X.toFun b) (X.toFun b)) :=
    chartLeviCivita_apply (I := I) g α X.toFun hb_good (X.toFun b)
  -- Substitute.
  rw [h_eq, h_chart]
  -- Bound the trivFromE op-norm by C_Jinv.
  have h_trivFromE_le : ‖trivFromE (I := I) α b‖ ≤ C_Jinv := hCJinv_bound b hb
  -- Bound the trivToE op-norm by C_J.
  have h_trivToE_le : ‖trivToE (I := I) α b‖ ≤ C_J := hCJ_bound b hb
  -- chartE_section_repr α X.toFun b = trivToE α b (X.toFun b); its norm
  -- is ≤ C_J * N_X.
  have h_repr_norm : ‖chartE_section_repr (I := I) α X.toFun b‖ ≤ C_J * N_X := by
    have h_eq_repr : chartE_section_repr (I := I) α X.toFun b =
        trivToE (I := I) α b (X.toFun b) := rfl
    rw [h_eq_repr]
    have h_mul := mul_le_mul_of_nonneg_right h_trivToE_le hN_X_nn
    have := (trivToE (I := I) α b).le_opNorm (X.toFun b)
    linarith
  -- Bound the fderiv-applied-to-trivToE-X term.
  have h_step2 :
      ‖trivToE (I := I) α b (X.toFun b)‖ ≤ C_J * N_X := by
    have h_mul := mul_le_mul_of_nonneg_right h_trivToE_le hN_X_nn
    have := (trivToE (I := I) α b).le_opNorm (X.toFun b)
    linarith
  have h_fderiv_term :
      ‖fderiv ℝ (chartE_section_repr (I := I) α X.toFun ∘
          (extChartAt I α).symm) (extChartAt I α b)
          (trivToE (I := I) α b (X.toFun b))‖ ≤ N_dX * (C_J * N_X) := by
    have h_step1 :
        ‖fderiv ℝ (chartE_section_repr (I := I) α X.toFun ∘
            (extChartAt I α).symm) (extChartAt I α b)
            (trivToE (I := I) α b (X.toFun b))‖ ≤
          N_dX * ‖trivToE (I := I) α b (X.toFun b)‖ := by
      rw [hN_dX_def]
      exact ContinuousLinearMap.le_opNorm _ _
    have h_mul :
        N_dX * ‖trivToE (I := I) α b (X.toFun b)‖ ≤ N_dX * (C_J * N_X) :=
      mul_le_mul_of_nonneg_left h_step2 hN_dX_nn
    linarith
  -- Bound the Christoffel-correction term.
  have h_chris_term :
      ‖christoffelCorrection (I := I) g α b
          (chartE_section_repr (I := I) α X.toFun b) (X.toFun b)‖ ≤
        C_χ * (C_J * N_X) * N_X := by
    have h_step1 :
        ‖christoffelCorrection (I := I) g α b
            (chartE_section_repr (I := I) α X.toFun b) (X.toFun b)‖ ≤
          ‖christoffelCorrection (I := I) g α b
              (chartE_section_repr (I := I) α X.toFun b)‖ * N_X := by
      rw [hN_X_def]
      exact ContinuousLinearMap.le_opNorm _ _
    have h_step2 :
        ‖christoffelCorrection (I := I) g α b
            (chartE_section_repr (I := I) α X.toFun b)‖ ≤ C_χ * (C_J * N_X) :=
      le_trans (hCχ_bound (b := b) hb _)
        (mul_le_mul_of_nonneg_left h_repr_norm hCχ_nn)
    have h_step3 :
        ‖christoffelCorrection (I := I) g α b
            (chartE_section_repr (I := I) α X.toFun b)‖ * N_X ≤
          C_χ * (C_J * N_X) * N_X :=
      mul_le_mul_of_nonneg_right h_step2 hN_X_nn
    linarith
  -- Bound the sum inside trivFromE.
  set F_term : E :=
    fderiv ℝ (chartE_section_repr (I := I) α X.toFun ∘
        (extChartAt I α).symm) (extChartAt I α b)
        (trivToE (I := I) α b (X.toFun b)) with hF_term_def
  set G_term : E :=
    christoffelCorrection (I := I) g α b
        (chartE_section_repr (I := I) α X.toFun b) (X.toFun b) with hG_term_def
  have h_sum_norm : ‖F_term + G_term‖ ≤
      N_dX * (C_J * N_X) + C_χ * (C_J * N_X) * N_X := by
    have h_tri : ‖F_term + G_term‖ ≤ ‖F_term‖ + ‖G_term‖ := norm_add_le _ _
    linarith
  -- Apply trivFromE op-norm bound.
  have h_outer :
      ‖trivFromE (I := I) α b (F_term + G_term)‖ ≤
        ‖trivFromE (I := I) α b‖ * ‖F_term + G_term‖ :=
    (trivFromE (I := I) α b).le_opNorm _
  have h_outer_le :
      ‖trivFromE (I := I) α b (F_term + G_term)‖ ≤
        C_Jinv * (N_dX * (C_J * N_X) + C_χ * (C_J * N_X) * N_X) := by
    have h_a :
        ‖trivFromE (I := I) α b‖ * ‖F_term + G_term‖ ≤
          C_Jinv * ‖F_term + G_term‖ :=
      mul_le_mul_of_nonneg_right h_trivFromE_le (norm_nonneg _)
    have h_b :
        C_Jinv * ‖F_term + G_term‖ ≤
          C_Jinv * (N_dX * (C_J * N_X) + C_χ * (C_J * N_X) * N_X) :=
      mul_le_mul_of_nonneg_left h_sum_norm hCJinv_nn
    linarith
  -- Rearrange to the headline form C * (N_dX * N_X + N_X^2).
  have h_RHS_eq : C * (N_dX * N_X + N_X ^ 2) =
      C_Jinv * (C_J + C_χ * C_J) * N_dX * N_X +
        C_Jinv * (C_J + C_χ * C_J) * N_X ^ 2 := by
    rw [hC_def]; ring
  have h_lhs_eq :
      C_Jinv * (N_dX * (C_J * N_X) + C_χ * (C_J * N_X) * N_X) =
        C_Jinv * C_J * N_dX * N_X + C_Jinv * (C_χ * C_J) * N_X ^ 2 := by
    ring
  have h_cχJ_nn : 0 ≤ C_χ * C_J := mul_nonneg hCχ_nn hCJ_nn
  have h_NdXNX_nn : 0 ≤ N_dX * N_X := mul_nonneg hN_dX_nn hN_X_nn
  have h_NX2_nn : 0 ≤ N_X ^ 2 := pow_two_nonneg _
  have h_a1 : C_Jinv * C_J ≤ C_Jinv * (C_J + C_χ * C_J) :=
    mul_le_mul_of_nonneg_left (by linarith) hCJinv_nn
  have h_a2 : C_Jinv * (C_χ * C_J) ≤ C_Jinv * (C_J + C_χ * C_J) :=
    mul_le_mul_of_nonneg_left (by linarith) hCJinv_nn
  have h_term1_le :
      C_Jinv * C_J * N_dX * N_X ≤ C_Jinv * (C_J + C_χ * C_J) * N_dX * N_X := by
    have h_c : C_Jinv * C_J * N_dX * N_X = (C_Jinv * C_J) * (N_dX * N_X) := by ring
    have h_d : C_Jinv * (C_J + C_χ * C_J) * N_dX * N_X =
        C_Jinv * (C_J + C_χ * C_J) * (N_dX * N_X) := by ring
    rw [h_c, h_d]
    exact mul_le_mul_of_nonneg_right h_a1 h_NdXNX_nn
  have h_term2_le :
      C_Jinv * (C_χ * C_J) * N_X ^ 2 ≤ C_Jinv * (C_J + C_χ * C_J) * N_X ^ 2 :=
    mul_le_mul_of_nonneg_right h_a2 h_NX2_nn
  have h_combined :
      C_Jinv * (N_dX * (C_J * N_X) + C_χ * (C_J * N_X) * N_X) ≤
        C * (N_dX * N_X + N_X ^ 2) := by
    rw [h_lhs_eq, h_RHS_eq]; linarith
  exact le_trans h_outer_le h_combined

/-! ## Stage 2: headline op-norm bound for the second-application term

We apply `chartTensorRSCovariantDerivative_opNorm_le_pou_tsupport`
("H") to bound `‖chartTensorRSCovariantDerivative r s g α T Xext b‖` for
*any* raw vector field `Xext`, then use a smooth extension whose value
at `b` is precisely `(LeviCivita g) X b (X b)` and the chart-frame
agreement `chartTensorRSCovariantDerivative_eq_abstract` to identify
the chart-form value with the bundled
`cov_RS T b ((LeviCivita g) X b (X b))`. Substituting the inner-bound
from Stage 1 gives the headline. -/

/-- **Headline: uniform op-norm bound for the second-application term.**

There exists a non-negative constant `C` such that for every `b` in the
closed support of the canonical chart-atlas partition-of-unity weight at
`α`, every smooth `(r, s)`-tensor section `T`, and every smooth
tangent vector field `X`, the second-application term of the
connection-Laplacian frame trace satisfies

  `‖cov_RS T b ((LeviCivita g) X b (X b))‖
    ≤ C * (max (1 + ‖v_b‖) 1) ^ (max r s) *
      (‖fderiv ℝ (chart-pulled repr of T at α) (extChartAt I α b)‖ * ‖v_b‖
       + ‖T b‖)`

where `v_b := (LeviCivita g) X b (X b)`. The norm of `v_b` itself is
controlled by the Stage-1 bound

  `‖v_b‖ ≤ C_LC * ( ‖fderiv ℝ (chart-pulled repr of X at α)
      (extChartAt I α b)‖ * ‖X b‖ + ‖X b‖^2 )`.

The constant `C` depends only on `r`, `s`, the metric `g`, the chart
at `α`, and the locality hypothesis; it is independent of `T`, `X`,
and `b`. -/
theorem rawTensorConnLap_2ndApplication_opNorm_bound
    (h_atlas : HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ (T :
            letI _h_top : TopologicalSpace
                (TotalSpace (TensorRSModel r s ℝ E)
                  (fun x : M => TensorRSSpace r s I x)) :=
              tensorRSBundle_topology r s
            letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
                (fun x : M => TensorRSSpace r s I x) :=
              tensorRSBundle_fiber r s
            Cₛ^∞⟮I; TensorRSModel r s ℝ E,
              fun b => TensorRSSpace r s I b⟯)
          (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
          ‖(TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              T.toFun b
              ((LeviCivita (I := I) g).toFun X.toFun b (X.toFun b))‖ ≤
            C *
              (max (1 +
                ‖(LeviCivita (I := I) g).toFun X.toFun b (X.toFun b)‖) 1) ^
                  (max r s) *
              (‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α T.toFun ∘
                  (extChartAt I α).symm) (extChartAt I α b)‖ *
                  ‖(LeviCivita (I := I) g).toFun X.toFun b (X.toFun b)‖
                + ‖T.toFun b‖) := by
  classical
  -- Take the constant from `chartTensorRSCovariantDerivative_opNorm_le_pou_tsupport`.
  obtain ⟨C, hC_nn, hC_bound⟩ :=
    chartTensorRSCovariantDerivative_opNorm_le_pou_tsupport
      (I := I) (M := M) h_atlas g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro b hb T X
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  -- Abbreviation for the inner Γ-vector at `b`.
  set v : TangentSpace I b :=
    (LeviCivita (I := I) g).toFun X.toFun b (X.toFun b) with hv_def
  -- Smooth extension `Xext` with `Xext b = v`.
  obtain ⟨Xext, hXext_at_b⟩ :=
    ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
      (n := ⊤) b v
  -- POU tsupport ⊆ chartLeviCivitaGoodSet α (under [I.Boundaryless]).
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := by
    have hK_sub : tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆ (chartAt H α).source :=
      (chartAtlasPOU_isSubordinate I M) α
    have h_eq := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α
    rw [h_eq, extChartAt_source_eq_chartAt_source (I := I)]
    exact hK_sub hb
  -- Agreement: chart-form with `Xext` at `b` equals the bundled `cov_RS T b (Xext b)`.
  have h_agree :
      chartTensorRSCovariantDerivative (I := I) r s g α T.toFun Xext.toFun b =
        (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun T.toFun b (Xext.toFun b) :=
    chartTensorRSCovariantDerivative_eq_abstract (I := I) (M := M)
      g r s α T Xext (b := b) hb_good
  -- `Xext b = v`, also `Xext.toFun b = v` (same coercion).
  have hXext_toFun_b : Xext.toFun b = v := hXext_at_b
  rw [hXext_toFun_b] at h_agree
  -- The chart-form value at b only depends on Xext through Xext b.
  -- Apply the H bound to (T.toFun, Xext.toFun).
  have h_H :=
    hC_bound (b := b) hb T.toFun Xext.toFun
  -- Rewrite the H bound using ‖Xext b‖ = ‖v‖.
  rw [hXext_toFun_b] at h_H
  -- Use h_agree to rewrite LHS of h_H from chart-form to bundled form.
  rw [h_agree] at h_H
  exact h_H

end Connection
end Integral
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Integral.Connection.leviCivita_X_X_norm_bound_on_pouTsupport
#print axioms
  DifferentialGeometry.Integral.Connection.rawTensorConnLap_2ndApplication_opNorm_bound
end Sanity
