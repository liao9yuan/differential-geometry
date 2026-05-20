import DifferentialGeometry.Integral.Connection.TensorConnLaplacianChart
import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivativeOpNorm

/-!
# Pointwise op-norm bound for `rawTensorConnLap`

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, and a smooth
`(r, s)`-tensor section `T`, this file packages the pointwise op-norm bound for
the raw tensor connection Laplacian `rawTensorConnLap g r s T.toFun b` at every
point `b` lying in the intersection of the chart-α partition-of-unity tsupport
and the chart-α Levi-Civita good set.

The bound is the natural composition of two ingredients:

1. The chart-frame expansion `rawTensorConnLap_eq_chart` — at any
   `y ∈ chartLeviCivitaGoodSet α`,
   `rawTensorConnLap g r s T.toFun y` is a finite sum over
   `i : Fin (Module.finrank ℝ E)` of the difference between
   * the chart-frame second covariant derivative
     `chartTensorRSCovariantDerivative r s g α
        (covApply cov_RS B_i T.toFun) (smoothOrthoFrame g y i) y`, and
   * the second-application Γ-correction
     `cov_RS T.toFun y ((LeviCivita g) B_i y (B_i y))`,
   where `B_i = smoothOrthoFrame g y i`.

2. The headline op-norm bound
   `chartTensorRSCovariantDerivative_opNorm_le_pou_tsupport` controlling the
   chart-frame second covariant derivative pointwise on the chart-atlas
   partition-of-unity tsupport in terms of the chart-pulled Fréchet derivative
   of its tensor argument and the norm of its tangent argument.

Combining the two via the triangle inequality yields a pointwise op-norm bound
for `rawTensorConnLap g r s T.toFun b` of the form

  `‖rawTensorConnLap g r s T.toFun b‖ ≤
      C * ∑ i, (chart-frame data at b for the i-th second covariant derivative)
        + ∑ i, ‖(cov_RS T.toFun b) (LeviCivita g B_i b (B_i b))‖`,

where the constant `C` depends only on the chart at `α`, the locality
hypothesis, and the metric `g`; it is independent of `T` and `b`. The second
sum captures the residual second-application Γ-correction term; on its own
each summand is bounded by the operator norm of the abstract first covariant
derivative `cov_RS T.toFun b` applied to a specific tangent vector.

## Main result

* `rawTensorConnLap_pointwise_bound_on_pou_tsupport_goodSet` — the pointwise
  op-norm bound on the intersection of the chart-α POU tsupport and the
  chart-α Levi-Civita good set.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The pointwise per-frame-index chart-frame "data" expression appearing on
the right-hand side of the bound on the first contribution to
`rawTensorConnLap`. For a raw `(r, s)`-tensor section `T₀ : Π b, …`, a
chart-centre `α`, and a point `y`, the chart-frame data at the `i`-th frame
index is the non-negative real
`(max (1 + ‖B_i y‖) 1) ^ (max r s) *
    (‖fderiv ℝ (chart-pulled covApply cov_RS B_i T₀) (extChartAt I α y)‖
      * ‖B_i y‖ + ‖covApply cov_RS B_i T₀ y‖)`,
where `B_i = smoothOrthoFrame g y i`. -/
private noncomputable def chartFrameData
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : Π b : M, TensorRSSpace r s I b)
    (y : M) (i : Fin (Module.finrank ℝ E)) : ℝ :=
  (max (1 + ‖smoothOrthoFrame (I := I) g y i y‖) 1) ^ (max r s) *
    (‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g y i) T₀) ∘
        (extChartAt I α).symm) (extChartAt I α y)‖ *
      ‖smoothOrthoFrame (I := I) g y i y‖
      + ‖covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g y i) T₀ y‖)

private lemma chartFrameData_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : Π b : M, TensorRSSpace r s I b)
    (y : M) (i : Fin (Module.finrank ℝ E)) :
    0 ≤ chartFrameData (I := I) g r s α T₀ y i := by
  classical
  unfold chartFrameData
  have h1 : 0 ≤ max (1 + ‖smoothOrthoFrame (I := I) g y i y‖) 1 :=
    le_trans zero_le_one (le_max_right _ _)
  have h2 : 0 ≤ (max (1 + ‖smoothOrthoFrame (I := I) g y i y‖) 1) ^ (max r s) :=
    pow_nonneg h1 _
  have h3 : 0 ≤
      ‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g y i) T₀) ∘
          (extChartAt I α).symm) (extChartAt I α y)‖ *
        ‖smoothOrthoFrame (I := I) g y i y‖
        + ‖covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g y i) T₀ y‖ := by
    have h_a : 0 ≤
        ‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g y i) T₀) ∘
          (extChartAt I α).symm) (extChartAt I α y)‖ *
        ‖smoothOrthoFrame (I := I) g y i y‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have h_b : 0 ≤
        ‖covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g y i) T₀ y‖ := norm_nonneg _
    linarith
  exact mul_nonneg h2 h3

/-- **Pointwise op-norm bound for `rawTensorConnLap` on the intersection of the
chart-α POU tsupport and the chart-α Levi-Civita good set.**

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, and a
smooth `(r, s)`-tensor section `T`, there exists a non-negative constant `C`
such that at every point `b` lying simultaneously in the closed support of the
chart-α partition-of-unity weight and in the chart-α Levi-Civita good set, the
raw tensor connection Laplacian satisfies the pointwise op-norm bound

  `‖rawTensorConnLap g r s T.toFun b‖ ≤
      C * ∑ i, chartFrameData g r s α T b i +
        ∑ i, ‖(cov_RS T.toFun b) (LeviCivita g B_i b (B_i b))‖`,

where the first sum gives the chart-frame contribution at the `i`-th frame
index (governed by `chartTensorRSCovariantDerivative_opNorm_le_pou_tsupport`),
and the second sum collects the second-application Γ-correction terms
(`cov_RS T.toFun b` applied to the LeviCivita tangent-bundle derivative
`(LeviCivita g) B_i b (B_i b)`, where `B_i = smoothOrthoFrame g b i`).

The constant `C` depends only on `r`, `s`, the metric `g`, the chart at `α`,
and the locality hypothesis — not on `T` or `b`. -/
theorem rawTensorConnLap_pointwise_bound_on_pou_tsupport_goodSet
    (h_atlas : HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T :
      letI _h_top : TopologicalSpace
          (TotalSpace (TensorRSModel r s ℝ E)
            (fun x : M => TensorRSSpace r s I x)) :=
        tensorRSBundle_topology r s
      letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
          (fun x : M => TensorRSSpace r s I x) :=
        tensorRSBundle_fiber r s
      Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        fun b => TensorRSSpace r s I b⟯) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
        chartLeviCivitaGoodSet (I := I) α →
          ‖rawTensorConnLap (I := I) g r s T.toFun b‖ ≤
            C * (∑ i : Fin (Module.finrank ℝ E),
              chartFrameData (I := I) g r s α T.toFun b i) +
              ∑ i : Fin (Module.finrank ℝ E),
                ‖(TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g)).toFun T.toFun b
                  ((LeviCivita (I := I) g).toFun
                    (smoothOrthoFrame (I := I) g b i) b
                    (smoothOrthoFrame (I := I) g b i b))‖ := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  -- Extract the H bound's constant.
  obtain ⟨C_H, hC_H_nn, hC_H_bound⟩ :=
    chartTensorRSCovariantDerivative_opNorm_le_pou_tsupport
      (I := I) (M := M) h_atlas g r s α
  refine ⟨C_H, hC_H_nn, ?_⟩
  intro b hb
  obtain ⟨hb_pou, hb_good⟩ := hb
  -- Step 1: chart-frame expansion of `rawTensorConnLap g r s T.toFun b`.
  have h_chart_expand := rawTensorConnLap_eq_chart (I := I) (M := M) g r s α T hb_good
  -- Step 2: triangle inequality on the finite sum of differences.
  -- Each summand decomposes as `chart_piece_i - Γ_piece_i`, with norm
  -- ≤ ‖chart_piece_i‖ + ‖Γ_piece_i‖.
  set N : ℕ := Module.finrank ℝ E with hN_def
  set chartPiece : Fin N → ℝ := fun i =>
      ‖chartTensorRSCovariantDerivative (I := I) r s g α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g b i) T.toFun)
        (smoothOrthoFrame (I := I) g b i) b‖ with hChartPiece_def
  set ΓPiece : Fin N → ℝ := fun i =>
      ‖(TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun T.toFun b
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g b i) b
          (smoothOrthoFrame (I := I) g b i b))‖ with hΓPiece_def
  -- Bound the LHS via the chart expansion and the per-i triangle inequality.
  have h_lhs_le_sum :
      ‖rawTensorConnLap (I := I) g r s T.toFun b‖ ≤
        ∑ i : Fin N, (chartPiece i + ΓPiece i) := by
    rw [h_chart_expand]
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum ?_
    intro i _
    exact norm_sub_le _ _
  -- Step 3: per-i chart-piece bound via H.
  have h_chartPiece_le : ∀ i : Fin N,
      chartPiece i ≤ C_H * chartFrameData (I := I) g r s α T.toFun b i := by
    intro i
    rw [hChartPiece_def]
    have h_bound := hC_H_bound (b := b) hb_pou
      (T := covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g))
        (smoothOrthoFrame (I := I) g b i) T.toFun)
      (X := smoothOrthoFrame (I := I) g b i)
    -- `h_bound : ‖chart cov‖ ≤ C_H * (max (1 + ‖X b‖) 1)^(max r s) *
    --    (‖fderiv (chart-pulled covApply ...)‖ * ‖X b‖ + ‖covApply ... b‖)`.
    -- The RHS is exactly `C_H * chartFrameData g r s α T b i`.
    unfold chartFrameData
    have h_rewrite :
        C_H * (max (1 + ‖smoothOrthoFrame (I := I) g b i b‖) 1) ^ (max r s) *
          (‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g))
                (smoothOrthoFrame (I := I) g b i) T.toFun) ∘
              (extChartAt I α).symm) (extChartAt I α b)‖ *
            ‖smoothOrthoFrame (I := I) g b i b‖
            + ‖covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g))
                (smoothOrthoFrame (I := I) g b i) T.toFun b‖) =
          C_H * ((max (1 + ‖smoothOrthoFrame (I := I) g b i b‖) 1) ^ (max r s) *
            (‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
                (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g))
                  (smoothOrthoFrame (I := I) g b i) T.toFun) ∘
                (extChartAt I α).symm) (extChartAt I α b)‖ *
              ‖smoothOrthoFrame (I := I) g b i b‖
              + ‖covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g))
                  (smoothOrthoFrame (I := I) g b i) T.toFun b‖)) := by
      ring
    rw [h_rewrite] at h_bound
    exact h_bound
  -- Step 4: combine via sum-monotonicity.
  have h_sum_le :
      ∑ i : Fin N, (chartPiece i + ΓPiece i) ≤
        ∑ i : Fin N, (C_H * chartFrameData (I := I) g r s α T.toFun b i + ΓPiece i) := by
    refine Finset.sum_le_sum ?_
    intro i _
    have h_ΓPiece_nn : 0 ≤ ΓPiece i := norm_nonneg _
    have h := h_chartPiece_le i
    linarith
  -- Step 5: split the right-hand sum into chart + Γ parts and re-fold.
  have h_split :
      (∑ i : Fin N, (C_H * chartFrameData (I := I) g r s α T.toFun b i + ΓPiece i)) =
        C_H * (∑ i : Fin N, chartFrameData (I := I) g r s α T.toFun b i) +
          ∑ i : Fin N, ΓPiece i := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  -- Final combination.
  calc ‖rawTensorConnLap (I := I) g r s T.toFun b‖
      ≤ ∑ i : Fin N, (chartPiece i + ΓPiece i) := h_lhs_le_sum
    _ ≤ ∑ i : Fin N, (C_H * chartFrameData (I := I) g r s α T.toFun b i + ΓPiece i) :=
          h_sum_le
    _ = C_H * (∑ i : Fin N, chartFrameData (I := I) g r s α T.toFun b i) +
          ∑ i : Fin N, ΓPiece i := h_split

end Connection
end Integral
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Integral.Connection.rawTensorConnLap_pointwise_bound_on_pou_tsupport_goodSet
end Sanity
