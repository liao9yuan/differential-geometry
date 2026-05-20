import DifferentialGeometry.Integral.Connection.TensorConnLaplacianChart
import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivativeOpNorm
import DifferentialGeometry.Integral.Connection.RawTensorConnLap2ndApplicationOpNorm

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

/-! ## Combined chart-data-only pointwise bound

By bounding each `ΓPiece i = ‖cov_RS T b ((LeviCivita g) B_i b (B_i b))‖`
through `rawTensorConnLap_2ndApplication_opNorm_bound` (with the smooth
section `X := smoothOrthoFrame g α i`), we eliminate the residual abstract
`cov_RS` term in favour of a chart-data expression involving only
`T`, its chart-pulled Fréchet derivative, and the inner Γ-vector
`(LeviCivita g) B_i b (B_i b)`. The resulting bound is fully chart-based:
the right-hand side is a finite sum of chart-data quantities indexed by the
frame, with constants depending only on `r`, `s`, the metric `g`, the chart
at `α`, and the locality hypothesis. -/

/-- The pointwise per-frame-index "second-application chart-data" expression
appearing on the right-hand side of the bound on the second contribution to
`rawTensorConnLap`. For a raw `(r, s)`-tensor section `T₀`, a chart-centre
`α`, and a point `y`, the second-application chart-data at the `i`-th frame
index uses the inner Γ-vector
`v_i := (LeviCivita g) B_i y (B_i y)` (with `B_i = smoothOrthoFrame g y i`),
together with the chart-pulled Fréchet derivative of the chart-representation
of `T₀` itself. -/
private noncomputable def secondAppChartData
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : Π b : M, TensorRSSpace r s I b)
    (y : M) (i : Fin (Module.finrank ℝ E)) : ℝ :=
  (max (1 +
      ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g y i) y
        (smoothOrthoFrame (I := I) g y i y)‖) 1) ^ (max r s) *
    (‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α T₀ ∘
        (extChartAt I α).symm) (extChartAt I α y)‖ *
      ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g y i) y
        (smoothOrthoFrame (I := I) g y i y)‖
      + ‖T₀ y‖)

private lemma secondAppChartData_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : Π b : M, TensorRSSpace r s I b)
    (y : M) (i : Fin (Module.finrank ℝ E)) :
    0 ≤ secondAppChartData (I := I) g r s α T₀ y i := by
  classical
  unfold secondAppChartData
  have h1 : 0 ≤ max (1 +
      ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g y i) y
        (smoothOrthoFrame (I := I) g y i y)‖) 1 :=
    le_trans zero_le_one (le_max_right _ _)
  have h2 : 0 ≤ (max (1 +
      ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g y i) y
        (smoothOrthoFrame (I := I) g y i y)‖) 1) ^ (max r s) :=
    pow_nonneg h1 _
  have h3a : 0 ≤
      ‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α T₀ ∘
          (extChartAt I α).symm) (extChartAt I α y)‖ *
        ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g y i) y
          (smoothOrthoFrame (I := I) g y i y)‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h3b : 0 ≤ ‖T₀ y‖ := norm_nonneg _
  exact mul_nonneg h2 (by linarith)

/-- **Combined chart-data-only pointwise op-norm bound for `rawTensorConnLap`.**

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, and a
smooth `(r, s)`-tensor section `T`, there exists a non-negative constant `C`
such that at every point `b` lying simultaneously in the closed support of the
chart-α partition-of-unity weight and in the chart-α Levi-Civita good set, the
raw tensor connection Laplacian satisfies the pointwise op-norm bound

  `‖rawTensorConnLap g r s T.toFun b‖ ≤
      C * (∑ i, chartFrameData g r s α T b i
            + ∑ i, secondAppChartData g r s α T b i)`,

where `chartFrameData` captures the chart-pulled second covariant derivative
data (Fréchet derivative norm of the chart-representation of
`covApply cov_RS B_i T` and the value `‖cov_RS B_i T b‖`, scaled by
`(max (1 + ‖B_i b‖) 1)^(max r s)`), and `secondAppChartData` captures the
chart-pulled first-derivative data of `T` itself together with the inner
Γ-vector `(LeviCivita g) B_i b (B_i b)`. Both sums are finite (range
`Fin (Module.finrank ℝ E)`) and chart-data only — there is no remaining
abstract `cov_RS` term in the right-hand side beyond its appearance inside
`chartFrameData`.

The constant `C` depends only on `r`, `s`, the metric `g`, the chart at `α`,
and the locality hypothesis; it is independent of `T` and `b`. -/
theorem rawTensorConnLap_pointwise_bound_chart_data
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
            C * ((∑ i : Fin (Module.finrank ℝ E),
                chartFrameData (I := I) g r s α T.toFun b i) +
              ∑ i : Fin (Module.finrank ℝ E),
                secondAppChartData (I := I) g r s α T.toFun b i) := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  -- Step 1: J's bound.
  obtain ⟨C_J, hCJ_nn, hCJ_bound⟩ :=
    rawTensorConnLap_pointwise_bound_on_pou_tsupport_goodSet
      (I := I) (M := M) h_atlas g r s α T
  -- Step 2: I's bound.
  obtain ⟨C_I, hCI_nn, hCI_bound⟩ :=
    rawTensorConnLap_2ndApplication_opNorm_bound
      (I := I) (M := M) h_atlas g r s α
  -- Combined constant.
  set C : ℝ := max C_J C_I with hC_def
  have hC_nn : 0 ≤ C := le_max_of_le_left hCJ_nn
  have hCJ_le_C : C_J ≤ C := le_max_left _ _
  have hCI_le_C : C_I ≤ C := le_max_right _ _
  refine ⟨C, hC_nn, ?_⟩
  intro b hb
  obtain ⟨hb_pou, hb_good⟩ := hb
  -- J's bound at b.
  have hJ : ‖rawTensorConnLap (I := I) g r s T.toFun b‖ ≤
      C_J * (∑ i : Fin (Module.finrank ℝ E),
          chartFrameData (I := I) g r s α T.toFun b i) +
        ∑ i : Fin (Module.finrank ℝ E),
          ‖(TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun T.toFun b
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g b i) b
              (smoothOrthoFrame (I := I) g b i b))‖ :=
    hCJ_bound ⟨hb_pou, hb_good⟩
  -- Per-i I-bound for the second sum.
  set N : ℕ := Module.finrank ℝ E with hN_def
  -- Wrap each smoothOrthoFrame g b i as a ContMDiffSection.
  have hI_per_i : ∀ i : Fin N,
      ‖(TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun T.toFun b
          ((LeviCivita (I := I) g).toFun
            (smoothOrthoFrame (I := I) g b i) b
            (smoothOrthoFrame (I := I) g b i b))‖ ≤
        C_I * secondAppChartData (I := I) g r s α T.toFun b i := by
    intro i
    -- Package smoothOrthoFrame g b i as a smooth section.
    set Xi : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothOrthoFrame (I := I) g b i,
        smoothOrthoFrame_smooth (I := I) g b i⟩ with hXi_def
    -- Apply I with X = Xi.
    have h := hCI_bound (b := b) hb_pou T Xi
    -- Rearrange the RHS: I gives
    --   C_I * (max (1 + ‖v‖) 1)^(max r s) * (‖df‖ * ‖v‖ + ‖T b‖)
    -- where v = (LeviCivita g) Xi b (Xi b). Note Xi.toFun = smoothOrthoFrame g b i.
    have hXi_toFun : Xi.toFun = smoothOrthoFrame (I := I) g b i := rfl
    rw [hXi_toFun] at h
    -- The conclusion expression equals C_I * secondAppChartData ... i.
    unfold secondAppChartData
    -- After rewriting, h's RHS is exactly C_I * (the bracket from secondAppChartData).
    -- We just need to associate the multiplication: C_I * X * Y = C_I * (X * Y).
    have h_assoc :
        C_I *
          (max (1 +
            ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g b i) b
              (smoothOrthoFrame (I := I) g b i b)‖) 1) ^ (max r s) *
          (‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α T.toFun ∘
              (extChartAt I α).symm) (extChartAt I α b)‖ *
              ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g b i) b
                (smoothOrthoFrame (I := I) g b i b)‖
            + ‖T.toFun b‖) =
          C_I * ((max (1 +
            ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g b i) b
              (smoothOrthoFrame (I := I) g b i b)‖) 1) ^ (max r s) *
            (‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α T.toFun ∘
                (extChartAt I α).symm) (extChartAt I α b)‖ *
                ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g b i) b
                  (smoothOrthoFrame (I := I) g b i b)‖
              + ‖T.toFun b‖)) := by ring
    rw [h_assoc] at h
    exact h
  -- Sum the per-i I bounds.
  have h_sum_I :
      (∑ i : Fin N,
          ‖(TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun T.toFun b
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g b i) b
              (smoothOrthoFrame (I := I) g b i b))‖) ≤
        C_I * (∑ i : Fin N, secondAppChartData (I := I) g r s α T.toFun b i) := by
    have h_step : ∀ i : Fin N,
        ‖(TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun T.toFun b
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g b i) b
              (smoothOrthoFrame (I := I) g b i b))‖ ≤
          C_I * secondAppChartData (I := I) g r s α T.toFun b i := hI_per_i
    calc ∑ i : Fin N,
            ‖(TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun T.toFun b
              ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g b i) b
                (smoothOrthoFrame (I := I) g b i b))‖
          ≤ ∑ i : Fin N, C_I * secondAppChartData (I := I) g r s α T.toFun b i :=
            Finset.sum_le_sum (fun i _ => h_step i)
      _ = C_I * (∑ i : Fin N, secondAppChartData (I := I) g r s α T.toFun b i) := by
            rw [← Finset.mul_sum]
  -- Now combine: J's RHS ≤ C_J * (Σ chartFrameData) + C_I * (Σ secondAppChartData)
  --             ≤ C * ((Σ chartFrameData) + (Σ secondAppChartData)).
  set S1 : ℝ := ∑ i : Fin N, chartFrameData (I := I) g r s α T.toFun b i with hS1_def
  set S2 : ℝ := ∑ i : Fin N, secondAppChartData (I := I) g r s α T.toFun b i with hS2_def
  have hS1_nn : 0 ≤ S1 :=
    Finset.sum_nonneg (fun i _ => chartFrameData_nonneg g r s α T.toFun b i)
  have hS2_nn : 0 ≤ S2 :=
    Finset.sum_nonneg (fun i _ => secondAppChartData_nonneg g r s α T.toFun b i)
  -- J's bound rewritten.
  have hJ' : ‖rawTensorConnLap (I := I) g r s T.toFun b‖ ≤ C_J * S1 +
        ∑ i : Fin N,
          ‖(TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun T.toFun b
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g b i) b
              (smoothOrthoFrame (I := I) g b i b))‖ := hJ
  -- Final composition.
  have h_combined : C_J * S1 + C_I * S2 ≤ C * (S1 + S2) := by
    have hJ_le : C_J * S1 ≤ C * S1 := mul_le_mul_of_nonneg_right hCJ_le_C hS1_nn
    have hI_le : C_I * S2 ≤ C * S2 := mul_le_mul_of_nonneg_right hCI_le_C hS2_nn
    have h_distrib : C * (S1 + S2) = C * S1 + C * S2 := by ring
    linarith
  calc ‖rawTensorConnLap (I := I) g r s T.toFun b‖
      ≤ C_J * S1 +
          ∑ i : Fin N,
            ‖(TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun T.toFun b
              ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g b i) b
                (smoothOrthoFrame (I := I) g b i b))‖ := hJ'
    _ ≤ C_J * S1 + C_I * S2 := by linarith [h_sum_I]
    _ ≤ C * (S1 + S2) := h_combined

end Connection
end Integral
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Integral.Connection.rawTensorConnLap_pointwise_bound_on_pou_tsupport_goodSet
#print axioms
  DifferentialGeometry.Integral.Connection.rawTensorConnLap_pointwise_bound_chart_data
end Sanity
