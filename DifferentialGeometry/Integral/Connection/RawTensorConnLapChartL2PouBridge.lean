import DifferentialGeometry.Integral.Connection.TensorConnLaplacianL2Bound
import DifferentialGeometry.Analysis.Sobolev.Manifold.Rellich
import DifferentialGeometry.Analysis.Sobolev.Chart.CompletenessAux

/-!
# Manifold L² bound for the raw tensor connection Laplacian via a partition-
# of-unity-weighted chart-target aggregate

For a smooth closed Riemannian manifold `(M, g)` and a smooth compactly-
supported `(r, s)`-tensor section `T`, this file packages a quantitative
inequality bounding the manifold L²-norm-squared of the raw connection
Laplacian `rawTensorConnLap g r s T.toSection` by a constant multiple of a
chart-target aggregate built from the chart-pushed pointwise squared
model-fiber norm of the raw connection Laplacian, with the integrand on each
chart-target weighted by the *square* of the partition-of-unity weight
`ρ_α` pulled back through the inverse chart.

The POU-squared weight on the right-hand side localises the contribution from
each chart to the chart-α partition-of-unity support, which is the natural
support of the pointwise op-norm bound for the raw connection Laplacian. This
makes the aggregate definitionally compatible with the per-chart pointwise
bound `rawTensorConnLap_pointwise_bound_chart_data`, whose right-hand side is
only valid on the chart-α partition-of-unity tsupport.

The construction is unconditional in the sense that it makes no chart-coordinate
references at the statement level: the input is a smooth compactly-supported
tensor section, the connection Laplacian is the manifold-defined operator
`rawTensorConnLap`, the integration is against the canonical Riemannian volume
measure, and the right-hand-side aggregate is a finite sum of chart-target
integrals against the canonical Lebesgue measure on the Euclidean model space,
with each integrand weighted by `ρ_α((extChartAt I α).symm (toEuclidean.symm y))²`.

## Sign convention

Same as `RawTensorConnLapPointwiseBound`: geometer convention
`Δ_g = div ∘ grad`, spectrum in `(-∞, 0]` on closed manifolds.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open MeasureTheory
open scoped Manifold Topology ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The Euclidean ambient space of dimension `Module.finrank ℝ E`. -/
local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## The POU-weighted chart-target aggregate

We package the right-hand side of the POU-weighted L²-bound headline into a
single manifold-defined non-negative `ℝ≥0∞`-valued aggregate. This is a finite
sum, over the chart-atlas partition-of-unity support set
`chartAtlasPOU_finset I M`, of the chart-target Lebesgue integrals of
`ENNReal.ofReal` of the *POU²-weighted* chart-pushed squared model-fiber norm
of the raw connection Laplacian.

The POU² weight on the integrand localises the contribution to the
`(extChartAt I α)`-image of the chart-α partition-of-unity tsupport, which is
exactly the set on which the per-chart pointwise bound for the raw connection
Laplacian holds. -/

/-- **POU-weighted chart-target aggregate.** For a smooth Riemannian manifold
`(M, g)`, ranks `(r, s)`, and a smooth compactly-supported `(r, s)`-tensor
section `T : SmoothCcTensor g r s`, the POU-weighted chart-target aggregate is
the finite sum, over the chart-atlas partition-of-unity support set
`chartAtlasPOU_finset I M`, of the chart-target Lebesgue integrals of
`ENNReal.ofReal` of `ρ_α((extChartAt I α).symm (toEuclidean.symm y))² ·
(chart-pushed squared model-fiber norm)(y)`. -/
noncomputable def chartSobolevRawNormPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    ℝ≥0∞ :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
      ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
        ENNReal.ofReal
          (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
            (fun b : M =>
              rawTensorConnLap (I := I) g r s
                (fun z : M => T.toSection z) b)
            y)
      ∂(volume : Measure EuclN)

/-- Unfolding lemma for `chartSobolevRawNormPou`. -/
@[simp] lemma chartSobolevRawNormPou_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    chartSobolevRawNormPou (I := I) (M := M) g r s T =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
            ENNReal.ofReal
              (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                (fun b : M =>
                  rawTensorConnLap (I := I) g r s
                    (fun z : M => T.toSection z) b)
                y)
          ∂(volume : Measure EuclN) := rfl

/-! ## A density-only per-chart sup bound

For each `α ∈ chartAtlasPOU_finset I M`, the chart density `chartDensity g α`,
pulled back through the inverse chart on the toEuclidean image of
`tsupport ρ_α`, is uniformly bounded by a non-negative real `chartDensitySup α`.
This is the density-only counterpart of the `chartL2BridgeMα` constant
appearing in the POU×density bound. -/

variable (I M) in
/-- Predicate: the tsupport of `chartAtlasPOU α` is non-empty. -/
private noncomputable def chartAtlasPOU_tsupp_nonempty
    (α : M) : Prop :=
  (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)).Nonempty

variable (I M) in
/-- The per-chart `α : M` density sup bound, extracted via `Classical.choose`
from `exists_sup_chartDensity_on_pou_tsupport_image`. When `tsupport ρ_α` is
empty (i.e., `α ∉ chartAtlasPOU_finset`), the constant is defined to be `0`.

Naming this constant via a public `noncomputable def` (rather than via a local
`let` inside a proof) makes the value definitionally shareable across different
invocations of the POU-weighted bridge. -/
noncomputable def chartDensitySupPou
    (g : SmoothRiemannianMetric I M) (α : M) : ℝ :=
  open Classical in
  if h : chartAtlasPOU_tsupp_nonempty (I := I) (M := M) α then
    (exists_sup_chartDensity_on_pou_tsupport_image (I := I) (M := M)
      g α h).choose
  else 0

lemma chartDensitySupPou_nonneg
    (g : SmoothRiemannianMetric I M) (α : M) :
    0 ≤ chartDensitySupPou (I := I) (M := M) g α := by
  classical
  unfold chartDensitySupPou
  by_cases h : chartAtlasPOU_tsupp_nonempty (I := I) (M := M) α
  · rw [dif_pos h]
    exact le_of_lt
      (exists_sup_chartDensity_on_pou_tsupport_image (I := I) (M := M)
        g α h).choose_spec.1
  · rw [dif_neg h]

lemma chartDensitySupPou_le
    (g : SmoothRiemannianMetric I M) (α : M)
    (h_supp_ne :
      (tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)).Nonempty)
    {y : E}
    (hy_image :
      y ∈ (extChartAt I α) '' (tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))) :
    chartDensity g α ((extChartAt I α).symm y) ≤
      chartDensitySupPou (I := I) (M := M) g α := by
  classical
  have h_pred : chartAtlasPOU_tsupp_nonempty (I := I) (M := M) α := h_supp_ne
  have h := (exists_sup_chartDensity_on_pou_tsupport_image (I := I) (M := M)
    g α h_supp_ne).choose_spec.2 y hy_image
  unfold chartDensitySupPou
  rw [dif_pos h_pred]
  -- Convert `(extChartAt I α).symm y` (in `h`) vs whatever the goal looks like.
  -- Both reduce to the same Mathlib term; use `convert` for safety.
  convert h using 2

/-! ## The POU-weighted L² bridge constant -/

variable (I M) in
/-- The POU-weighted chart-target L² bridge's overall multiplicative constant,
defined as
`(card chartAtlasPOU_finset) · (euclideanHaarFactor E) ·
  ∑ α (chartDensitySupPou g α + 1)`.

The factor `(card chartAtlasPOU_finset)` comes from the pointwise Cauchy-
Schwarz inequality `‖raw ΔT‖² = (Σ_α ρ_α · ‖raw ΔT‖)² ≤ N · Σ_α ρ_α² · ‖raw ΔT‖²`
used to pass from the manifold L² of `‖raw ΔT‖²` to the POU²-weighted form.

The factor `(euclideanHaarFactor E)` is the Haar scale factor relating the
canonical Lebesgue measure on `EuclN` to the canonical Lebesgue measure on `E`.

Each per-α factor `(chartDensitySupPou g α + 1)` controls the chart-α density
on the (extChartAt α)-image of `tsupport ρ_α`. -/
noncomputable def chartSobolevRawNormPouBridgeConstant
    (g : SmoothRiemannianMetric I M) : ℝ :=
  ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) *
    ((euclideanHaarFactor E : ℝ) *
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartDensitySupPou (I := I) (M := M) g α + 1))

lemma chartSobolevRawNormPouBridgeConstant_nonneg
    (g : SmoothRiemannianMetric I M) :
    0 ≤ chartSobolevRawNormPouBridgeConstant (I := I) (M := M) g := by
  refine mul_nonneg (Nat.cast_nonneg _) (mul_nonneg ?_ ?_)
  · exact (euclideanHaarFactor_pos (E := E)).le
  · refine Finset.sum_nonneg ?_
    intro α _
    have := chartDensitySupPou_nonneg (I := I) (M := M) g α
    linarith

/-! ## File-local algebraic helpers

We record two elementary algebraic inequalities used in the pointwise
Cauchy–Schwarz step and in the indicator algebra. The first is the inequality
`(Σ_β a_β)² ≤ N · Σ_β a_β²` for a finite family `(a_β : ℝ)` indexed by a
finset of size `N`, with all `a_β ≥ 0` (we use this with `a_β = ρ_β`, summing
to one). -/

private lemma sum_finset_sq_le_card_mul_sum_sq
    {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 := by
  classical
  -- Reduce to the `Fintype` version `sum_sq_le_card_mul_sum_sq` by lifting to a
  -- finset-restricted Fintype on the subtype `{i // i ∈ s}`.
  -- Direct proof: `(Σ f i)² = (Σ 1·f i)²` and Cauchy-Schwarz `(Σ a_i · b_i)² ≤
  -- (Σ a_i²)·(Σ b_i²)` with `a_i = 1, b_i = f i`.
  by_cases hs : s.card = 0
  · -- s is empty: LHS = 0, RHS = 0.
    rw [Finset.card_eq_zero] at hs
    subst hs
    simp
  · -- General case via `Finset.inner_mul_le_norm_mul_norm`-style inequality.
    -- We compute directly: expand `(Σ f i)² = Σ_{i, j} f i · f j` and bound.
    -- `(Σ f i)² = Σ_i Σ_j f i · f j`.
    -- `s.card · Σ (f i)² - (Σ f i)² = (1/2) · Σ_i Σ_j (f i - f j)² ≥ 0`.
    have h_double_sum : ∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 =
        2 * ((s.card : ℝ) * (∑ i ∈ s, (f i) ^ 2) - (∑ i ∈ s, f i) ^ 2) := by
      -- ∑_i ∑_j (f i - f j)² = ∑_i ∑_j ((f i)² - 2(f i)(f j) + (f j)²)
      --   = card · Σ (f i)² - 2 (Σ f i)² + card · Σ (f j)²
      --   = 2 · (card · Σ (f i)² - (Σ f i)²).
      classical
      set S : ℝ := ∑ i ∈ s, f i with hS_def
      set Q : ℝ := ∑ i ∈ s, (f i) ^ 2 with hQ_def
      have h_inner : ∀ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 =
          (s.card : ℝ) * (f i) ^ 2 - 2 * (f i) * S + Q := by
        intro i hi
        have hexp : ∀ j, (f i - f j) ^ 2 =
            (f i) ^ 2 - 2 * (f i) * (f j) + (f j) ^ 2 := by
          intro j; ring
        calc ∑ j ∈ s, (f i - f j) ^ 2
            = ∑ j ∈ s, ((f i) ^ 2 - 2 * (f i) * (f j) + (f j) ^ 2) :=
              Finset.sum_congr rfl (fun j _ => hexp j)
          _ = (∑ _j ∈ s, (f i) ^ 2)
                - (∑ j ∈ s, 2 * (f i) * (f j)) + (∑ j ∈ s, (f j) ^ 2) := by
              rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          _ = (s.card : ℝ) * (f i) ^ 2 - 2 * (f i) * S + Q := by
              rw [Finset.sum_const]
              rw [show (∑ j ∈ s, 2 * (f i) * (f j)) = 2 * (f i) * S from by
                rw [show (fun j => 2 * (f i) * (f j)) =
                  (fun j => (2 * (f i)) * (f j)) from by funext j; ring]
                rw [← Finset.mul_sum, ← hS_def]]
              rw [← hQ_def, nsmul_eq_mul]
      calc ∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2
          = ∑ i ∈ s, ((s.card : ℝ) * (f i) ^ 2 - 2 * (f i) * S + Q) :=
            Finset.sum_congr rfl h_inner
        _ = (∑ i ∈ s, (s.card : ℝ) * (f i) ^ 2)
              - (∑ i ∈ s, 2 * (f i) * S) + (∑ i ∈ s, Q) := by
            rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        _ = (s.card : ℝ) * Q - 2 * S * S + (s.card : ℝ) * Q := by
            rw [show (∑ i ∈ s, (s.card : ℝ) * (f i) ^ 2) =
                (s.card : ℝ) * Q from by
              rw [← Finset.mul_sum, ← hQ_def]]
            rw [show (∑ i ∈ s, 2 * (f i) * S) = 2 * S * S from by
              rw [show (fun i => 2 * (f i) * S) = (fun i => (2 * S) * (f i)) from by
                funext i; ring]
              rw [← Finset.mul_sum, ← hS_def]]
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = 2 * ((s.card : ℝ) * Q - S ^ 2) := by ring
    have h_nn : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    rw [h_double_sum] at h_nn
    nlinarith

/-! ## Pointwise Cauchy–Schwarz: `‖raw‖² ≤ N · Σ_α ρ_α² · ‖raw‖²`

This is the key pointwise inequality used to pass from the manifold L² of
`‖raw ΔT‖²` to the POU²-weighted form. The proof uses `Σ_α ρ_α = 1` together
with the finset Cauchy–Schwarz inequality
`(Σ_α a_α)² ≤ (#atlas) · Σ_α a_α²`. -/

private lemma normSq_le_card_mul_sum_pou_sq_mul_normSq
    {r s : ℕ} (g : SmoothRiemannianMetric I M)
    (T₀ : Π b : M, TensorRSSpace r s I b) (x : M) :
    (‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2 : ℝ) ≤
      ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) *
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
            ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2 := by
  classical
  set v : ℝ := ‖rawTensorConnLap (I := I) g r s T₀ x‖ with hv_def
  set sset : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hs_def
  have hv_nn : 0 ≤ v := norm_nonneg _
  have hv_sq_nn : 0 ≤ v ^ 2 := sq_nonneg _
  -- POU sum equals one at `x`.
  have h_sum :=
    chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
  -- `v² = (Σ ρ_α · v)²` since `Σ ρ_α = 1`.
  have hv_sq_eq :
      v ^ 2 = (∑ α ∈ sset, (chartAtlasPOU I M α : M → ℝ) x * v) ^ 2 := by
    have heq : ∑ α ∈ sset, (chartAtlasPOU I M α : M → ℝ) x * v = v := by
      rw [← Finset.sum_mul, h_sum, one_mul]
    rw [heq]
  -- Apply finset Cauchy–Schwarz: `(Σ a_α)² ≤ N · Σ a_α²` with `a_α = ρ_α · v`.
  have hCS :=
    sum_finset_sq_le_card_mul_sum_sq sset (fun α => (chartAtlasPOU I M α : M → ℝ) x * v)
  -- Rewrite each `(ρ_α · v)² = ρ_α² · v²`.
  have h_factor_eq : ∑ α ∈ sset, ((chartAtlasPOU I M α : M → ℝ) x * v) ^ 2 =
      ∑ α ∈ sset, ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * v ^ 2 :=
    Finset.sum_congr rfl (fun α _ => by ring)
  rw [h_factor_eq] at hCS
  -- Combine: `v² = (Σ ρ_α · v)² ≤ N · Σ ρ_α² · v²`.
  calc (‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2 : ℝ)
      = v ^ 2 := rfl
    _ = (∑ α ∈ sset, (chartAtlasPOU I M α : M → ℝ) x * v) ^ 2 := hv_sq_eq
    _ ≤ (sset.card : ℝ) *
          ∑ α ∈ sset, ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * v ^ 2 := hCS

/-! ## Per-α reduction to a chart-target integral

For each `α ∈ chartAtlasPOU_finset I M`, the manifold integral of
`ρ_α² · ‖raw ΔT‖²` against `μ_g` equals the chart-target integral against
`volume`, weighted by `chartDensity g α` and the Haar factor `c_E`. -/

private lemma manifold_lintegral_pou_sq_normSq_eq_chartTarget
    {r s : ℕ} (g : SmoothRiemannianMetric I M)
    (T₀ : Π b : M, TensorRSSpace r s I b)
    (hraw_meas :
      Measurable (fun x : M => ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2))
    (α : M) :
    ∫⁻ x,
        ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
            ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      (euclideanHaarFactor E : ℝ≥0∞) *
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
                ‖rawTensorConnLap (I := I) g r s T₀
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
          ∂(volume : Measure EuclN) := by
  classical
  -- Set up the integrand `F : M → ℝ≥0∞`.
  set F : M → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
      ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2) with hF_def
  -- Measurability of `F`.
  have hρ_cont : Continuous (fun x : M => (chartAtlasPOU I M α : M → ℝ) x) :=
    ((chartAtlasPOU I M α)).contMDiff.continuous
  have hρ_meas : Measurable (fun x : M => (chartAtlasPOU I M α : M → ℝ) x) :=
    hρ_cont.measurable
  have hρ_sq_meas : Measurable (fun x : M => ((chartAtlasPOU I M α : M → ℝ) x) ^ 2) :=
    hρ_meas.pow_const 2
  have hF_meas : Measurable F := by
    rw [hF_def]
    exact ENNReal.measurable_ofReal.comp (hρ_sq_meas.mul hraw_meas)
  -- `F` is supported in `(chartAt H α).source`, since `ρ_α² = 0` outside
  -- `tsupport ρ_α ⊆ (chartAt H α).source`.
  have hF_supp : ∀ x : M, x ∉ (chartAt H α).source → F x = 0 := by
    intro x hx
    have hρ_zero : (chartAtlasPOU I M α : M → ℝ) x = 0 := by
      have hsub : tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ (chartAt H α).source :=
        chartAtlasPOU_isSubordinate (I := I) (M := M) α
      have hx_notsupp : x ∉ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := fun hc => hx (hsub hc)
      exact image_eq_zero_of_notMem_tsupport hx_notsupp
    change ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
      ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2) = 0
    rw [hρ_zero]
    simp
  -- Step 1: `∫_M F dμ_g = ∫_M F d(chartLocalMeasure g α)` via the support-in lemma.
  rw [show riemannianVolumeMeasure (I := I) (M := M) g =
      riemannianMeasure (I := I) g (chartAtlasPOU I M) from rfl]
  rw [riemannianMeasure_lintegral_eq_chartLocalMeasure_of_supportIn
      (I := I) (M := M) g α hF_meas hF_supp]
  -- Step 2: apply the chart bridge `chartLocalMeasure_lintegral_via_chartTargetEuclid`.
  rw [chartLocalMeasure_lintegral_via_chartTargetEuclid
      (I := I) (M := M) g α hF_meas]

/-! ## The bridge from the squared-norm integrand to `pushedNormSq`

On the chart-target image, `‖raw(symm y)‖²` equals
`tensorTrivProjPushedNormSq g r s α (fun b => raw b) y`. This is the same
identification used in `enorm_sq_apply_eq_ofReal_pushedNormSq` of the bridge
file, restated in real-valued (not ENNReal) form for use inside our
`ofReal`-of-product integrand. -/

private lemma normSq_apply_eq_pushedNormSq
    {r s : ℕ} (g : SmoothRiemannianMetric I M)
    (T₀ : Π b : M, TensorRSSpace r s I b)
    (α : M) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (‖rawTensorConnLap (I := I) g r s T₀
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2 : ℝ) =
      tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
        (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y := by
  classical
  rw [tensorTrivProjPushedNormSq_apply_of_mem
      (I := I) (M := M) g r s α
      (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) hy]
  -- The fiber norm equals the model norm via `TensorRSSpace.toModel`.
  rfl

/-! ## Per-chart density bound on `(extChartAt α).symm`-image of POU² support

On the chart target, the indicator `ρ_α(symm y)² ≠ 0` implies
`(extChartAt α).symm (toEuclidean.symm y) ∈ tsupport ρ_α`, which lifts to
`(toEuclidean.symm y) ∈ (extChartAt α) '' tsupport ρ_α`, where the density
bound `chartDensitySupPou g α` applies. Off this image, `ρ_α(symm y)² = 0`,
so the bound holds trivially. -/

private lemma density_pou_sq_le
    (g : SmoothRiemannianMetric I M) (α : M)
    (h_supp_ne :
      (tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)).Nonempty)
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartDensity g α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
      (((chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) ≤
      (chartDensitySupPou (I := I) (M := M) g α + 1) *
      (((chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) := by
  classical
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ) x with hρ_def
  set dens : ℝ := chartDensity g α x with hdens_def
  have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hρ_nn : 0 ≤ ρ := (chartAtlasPOU I M).nonneg α x
  have hρ_sq_nn : 0 ≤ ρ ^ 2 := sq_nonneg _
  -- Case split on whether `ρ = 0` at `x`.
  by_cases hρ_zero : ρ = 0
  · -- ρ = 0 → both sides are zero.
    rw [show ρ ^ 2 = 0 from by rw [hρ_zero]; ring]
    simp
  · -- ρ ≠ 0 → x ∈ supp ρ ⊆ tsupport ρ. Density bound applies.
    have hx_supp : x ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      subset_tsupport _ (Function.mem_support.mpr hρ_zero)
    have hy_image : (toEuclidean (E := E)).symm y ∈
        (extChartAt I α) '' (tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
      refine ⟨x, hx_supp, ?_⟩
      rw [hx_def]
      exact (extChartAt I α).right_inv hy_target
    have hdens_le : dens ≤ chartDensitySupPou (I := I) (M := M) g α := by
      rw [hdens_def, hx_def]
      exact chartDensitySupPou_le (I := I) (M := M) g α h_supp_ne hy_image
    have hbound : dens ≤ chartDensitySupPou (I := I) (M := M) g α + 1 := by
      linarith
    exact mul_le_mul_of_nonneg_right hbound hρ_sq_nn

/-! ## Per-chart bound: empty tsupport case

When `tsupport ρ_α` is empty (equivalently `α ∉ chartAtlasPOU_finset`), the
POU-squared weight `ρ_α²` is identically zero, so the chart-target integrand
is zero. -/

private lemma manifold_lintegral_pou_sq_normSq_eq_zero_of_empty
    {r s : ℕ} (g : SmoothRiemannianMetric I M)
    (T₀ : Π b : M, TensorRSSpace r s I b)
    (α : M)
    (h_supp_empty :
      ¬ (tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)).Nonempty) :
    (fun x : M => (chartAtlasPOU I M α : M → ℝ) x ^ 2 *
        ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2) = 0 := by
  classical
  rw [Set.not_nonempty_iff_eq_empty] at h_supp_empty
  funext x
  have hρ_zero : (chartAtlasPOU I M α : M → ℝ) x = 0 := by
    have hx_notsupp : x ∉ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      rw [h_supp_empty]; exact Set.notMem_empty x
    exact image_eq_zero_of_notMem_tsupport hx_notsupp
  rw [hρ_zero]; simp

/-! ## Headline

L² bound of the raw tensor connection Laplacian by the POU-weighted chart-
target aggregate `chartSobolevRawNormPou`. The constant
`chartSobolevRawNormPouBridgeConstant g` depends only on `g`, the chart atlas,
and the canonical partition of unity. -/

/-- **Manifold L² bound for the raw tensor connection Laplacian via the POU-
weighted chart-target aggregate.**

For a smooth closed Riemannian manifold `(M, g)`, every smooth compactly-
supported `(r, s)`-tensor section `T : SmoothCcTensor g r s` whose raw
connection Laplacian has a Borel-measurable pointwise squared norm satisfies
the inequality

  `∫⁻ x, (‖rawTensorConnLap g r s T.toSection x‖ₑ : ℝ≥0∞) ^ 2 ∂μ_g
        ≤ ENNReal.ofReal C *
            chartSobolevRawNormPou g r s T`,

with the named uniform constant
`C := chartSobolevRawNormPouBridgeConstant g`, which depends only on `g`, the
canonical chart atlas, and the canonical partition of unity.

The hypothesis `h_atlas` is the locally-constant chart predicate, retained in
the public signature for parity with the unweighted bridge
`rawTensorConnLap_L2NormSq_le_chartSobolevRawNorm`; it is not consumed by the
present proof (which uses only a density-only sup bound on the
`(extChartAt α)`-image of `tsupport ρ_α`, available unconditionally on a
compact manifold).

The measurability hypothesis is the natural one: the `(r, s)`-tensor bundle
does not currently carry an `IsContinuousRiemannianBundle` instance for
general `(r, s)`, so the pointwise squared norm of a smooth section is not
automatically measurable, and is supplied here as a public input. -/
theorem rawTensorConnLap_L2NormSq_le_chartSobolevRawNormPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g r s),
        Measurable
          (fun x : M =>
            ‖rawTensorConnLap (I := I) g r s
              (fun z : M => T.toSection z) x‖ ^ 2) →
          ∫⁻ x,
              (‖rawTensorConnLap (I := I) g r s
                  (fun z : M => T.toSection z) x‖ₑ : ℝ≥0∞) ^ 2
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
            ENNReal.ofReal
                (chartSobolevRawNormPouBridgeConstant (I := I) (M := M) g) *
              chartSobolevRawNormPou (I := I) (M := M) g r s T := by
  classical
  refine ⟨chartSobolevRawNormPouBridgeConstant (I := I) (M := M) g,
    chartSobolevRawNormPouBridgeConstant_nonneg (I := I) (M := M) g, ?_⟩
  intro T hraw_meas
  -- Abbreviations for the proof body.
  set T₀ : Π b : M, TensorRSSpace r s I b := fun z : M => T.toSection z with hT₀_def
  set Sfin : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hSfin_def
  set N : ℕ := Sfin.card with hN_def
  set cE : ℝ := (euclideanHaarFactor E : ℝ) with hcE_def
  have hcE_nn : 0 ≤ cE := (euclideanHaarFactor_pos (E := E)).le
  set Mα : M → ℝ := fun α => chartDensitySupPou (I := I) (M := M) g α with hMα_def
  have hMα_nn : ∀ α : M, 0 ≤ Mα α := fun α =>
    chartDensitySupPou_nonneg (I := I) (M := M) g α
  set C : ℝ := chartSobolevRawNormPouBridgeConstant (I := I) (M := M) g with hC_def
  -- `enorm² = ofReal ‖·‖²` rewrite.
  have henorm_sq :
      (fun x : M => (‖rawTensorConnLap (I := I) g r s T₀ x‖ₑ : ℝ≥0∞) ^ 2) =
        (fun x : M => ENNReal.ofReal (‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)) := by
    funext x
    have hen : ‖rawTensorConnLap (I := I) g r s T₀ x‖ₑ =
        ENNReal.ofReal ‖rawTensorConnLap (I := I) g r s T₀ x‖ :=
      (ofReal_norm _).symm
    rw [hen, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
  rw [henorm_sq]
  -- Step 1: pointwise Cauchy–Schwarz bound `‖raw‖² ≤ N · Σ_α ρ_α² · ‖raw‖²`.
  have h_pointwise : ∀ x : M,
      ENNReal.ofReal (‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2) ≤
        ENNReal.ofReal ((N : ℝ) *
          ∑ α ∈ Sfin,
            ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
              ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2) := by
    intro x
    have hle := normSq_le_card_mul_sum_pou_sq_mul_normSq
      (I := I) (M := M) g (r := r) (s := s) T₀ x
    refine ENNReal.ofReal_le_ofReal hle
  -- Step 2: integrate both sides.
  have h_int_le :
      ∫⁻ x, ENNReal.ofReal (‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ∫⁻ x, ENNReal.ofReal ((N : ℝ) *
            ∑ α ∈ Sfin,
              ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    MeasureTheory.lintegral_mono h_pointwise
  -- Step 3: split the RHS as `N · Σ_α ∫_M ρ_α² · ‖raw‖² dμ_g`.
  -- We work with the algebraic form first.
  have h_nn_each : ∀ x : M, ∀ α ∈ Sfin,
      0 ≤ ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
        ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2 := by
    intro x α _
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have h_nn_sum : ∀ x : M,
      0 ≤ ∑ α ∈ Sfin,
        ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
          ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2 := by
    intro x
    exact Finset.sum_nonneg (h_nn_each x)
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  -- Convert `ENNReal.ofReal (N · sum) = (ofReal N) · (ofReal sum)`.
  have h_ofReal_factor : ∀ x : M,
      ENNReal.ofReal ((N : ℝ) *
          ∑ α ∈ Sfin,
            ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
              ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2) =
        ENNReal.ofReal (N : ℝ) *
          ENNReal.ofReal (∑ α ∈ Sfin,
            ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
              ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2) := fun x =>
    ENNReal.ofReal_mul hN_nn
  -- Convert `ENNReal.ofReal (Σ a_α) = Σ ENNReal.ofReal a_α` (each term nonneg).
  have h_ofReal_sum : ∀ x : M,
      ENNReal.ofReal (∑ α ∈ Sfin,
          ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
            ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2) =
        ∑ α ∈ Sfin, ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
            ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2) := by
    intro x
    rw [ENNReal.ofReal_sum_of_nonneg (h_nn_each x)]
  have h_int_le' :
      ∫⁻ x, ENNReal.ofReal (‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal (N : ℝ) *
          ∑ α ∈ Sfin,
            ∫⁻ x, ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                  ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal ((N : ℝ) *
              ∑ α ∈ Sfin,
                ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                  ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := h_int_le
      _ = ∫⁻ x, ENNReal.ofReal (N : ℝ) *
              ENNReal.ofReal (∑ α ∈ Sfin,
                ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                  ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
            refine lintegral_congr ?_
            intro x; exact h_ofReal_factor x
      _ = ENNReal.ofReal (N : ℝ) *
            ∫⁻ x, ENNReal.ofReal (∑ α ∈ Sfin,
              ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
            rw [MeasureTheory.lintegral_const_mul']
            exact ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (N : ℝ) *
            ∫⁻ x, ∑ α ∈ Sfin, ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
            congr 1
            refine lintegral_congr ?_
            intro x; exact h_ofReal_sum x
      _ = ENNReal.ofReal (N : ℝ) *
            ∑ α ∈ Sfin,
              ∫⁻ x, ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                  ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
            congr 1
            exact lintegral_finset_sum _ (fun α _ => by
              have hρ_cont :
                  Continuous (fun x : M => (chartAtlasPOU I M α : M → ℝ) x) :=
                ((chartAtlasPOU I M α)).contMDiff.continuous
              have hρ_meas :
                  Measurable (fun x : M => (chartAtlasPOU I M α : M → ℝ) x) :=
                hρ_cont.measurable
              exact ENNReal.measurable_ofReal.comp
                ((hρ_meas.pow_const 2).mul hraw_meas))
  -- Step 4: for each `α ∈ Sfin`, push the chart-α integral to the chart-target.
  -- We bound each per-α manifold integral by the corresponding chart-target
  -- integrand `(M_α + 1) · ρ_α(symm y)² · pushedNormSq(y)` (with the Haar factor).
  have h_per_alpha : ∀ α ∈ Sfin,
      ∫⁻ x, ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
              ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal (cE * (Mα α + 1)) *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                  (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
            ∂(volume : Measure EuclN) := by
    intro α hα_mem
    -- Note: since `α ∈ Sfin`, `tsupport ρ_α` is non-empty.
    have h_supp_ne : (tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)).Nonempty := by
      rw [chartAtlasPOU_finset_mem] at hα_mem
      exact hα_mem.mono (subset_tsupport _)
    -- Apply the per-α chart-bridge reduction.
    rw [manifold_lintegral_pou_sq_normSq_eq_chartTarget
      (I := I) (M := M) g (r := r) (s := s) T₀ hraw_meas α]
    -- Now bound the chart-target integrand pointwise on `chartTargetEuclid α`.
    have hpt_bound : ∀ y, y ∈ chartTargetEuclid (I := I) (M := M) α →
        ENNReal.ofReal
            (chartDensity g α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
              ‖rawTensorConnLap (I := I) g r s T₀
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
          ≤ ENNReal.ofReal (Mα α + 1) *
              (ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)) := by
      intro y hy
      -- Pointwise: density(symm y) · ρ_α(symm y)² ≤ (Mα α + 1) · ρ_α(symm y)².
      have hdens_pou_sq_le := density_pou_sq_le
        (I := I) (M := M) g α h_supp_ne hy
      -- Convert to ENNReal.ofReal.
      have hdens_nn : 0 ≤ chartDensity g α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) :=
        Real.sqrt_nonneg _
      have hρ_sq_nn :
          0 ≤ ((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 :=
        sq_nonneg _
      have hnormSq_nn :
          0 ≤ ‖rawTensorConnLap (I := I) g r s T₀
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2 :=
        sq_nonneg _
      -- Identify ‖raw(symm y)‖² with pushedNormSq.
      have h_pushed := normSq_apply_eq_pushedNormSq
        (I := I) (M := M) (r := r) (s := s) g T₀ α hy
      -- Compute the ENNReal equivalent.
      -- LHS = ofReal(dens) * ofReal(ρ_α² * ‖raw‖²)
      --     = ofReal(dens * ρ_α² * ‖raw‖²)  [factor sign]
      --     = ofReal(dens * ρ_α²) * ofReal(‖raw‖²)  [split]
      --     ≤ ofReal((M_α + 1) * ρ_α²) * ofReal(pushedNormSq)
      --     = ofReal(M_α + 1) * ofReal(ρ_α²) * ofReal(pushedNormSq)
      have h_dens_pou_sq_nn : 0 ≤
          chartDensity g α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
            ((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 :=
        mul_nonneg hdens_nn hρ_sq_nn
      have h_ofReal_inner : ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
            ‖rawTensorConnLap (I := I) g r s T₀
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2) =
          ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
            ENNReal.ofReal
              (‖rawTensorConnLap (I := I) g r s T₀
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2) :=
        ENNReal.ofReal_mul hρ_sq_nn
      rw [h_ofReal_inner]
      -- Now: LHS = ofReal(dens) * (ofReal(ρ_α²) * ofReal(‖raw‖²))
      --         = (ofReal(dens) * ofReal(ρ_α²)) * ofReal(‖raw‖²)
      --         ≤ ofReal((M_α + 1) * ρ_α²) * ofReal(‖raw‖²)
      --         = ofReal(M_α + 1) * ofReal(ρ_α²) * ofReal(‖raw‖²)
      --         = ofReal(M_α + 1) * (ofReal(ρ_α²) * ofReal(pushedNormSq))
      have hkey :
          ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
            ≤ ENNReal.ofReal (Mα α + 1) *
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) := by
        have h_real := hdens_pou_sq_le
        have h_bound :
            chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
              ((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 ≤
            (Mα α + 1) *
              ((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 := by
          exact h_real
        have h_Mα1_nn : 0 ≤ Mα α + 1 := by have := hMα_nn α; linarith
        rw [← ENNReal.ofReal_mul hdens_nn,
            ← ENNReal.ofReal_mul h_Mα1_nn]
        exact ENNReal.ofReal_le_ofReal h_bound
      have h_pushed_eq :
          ENNReal.ofReal
            (‖rawTensorConnLap (I := I) g r s T₀
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2) =
          ENNReal.ofReal
            (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
              (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y) := by
        rw [h_pushed]
      calc ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            (ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (‖rawTensorConnLap (I := I) g r s T₀
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2))
          = (ENNReal.ofReal
                (chartDensity g α
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)) *
              ENNReal.ofReal
                (‖rawTensorConnLap (I := I) g r s T₀
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2) := by
            ring
        _ ≤ (ENNReal.ofReal (Mα α + 1) *
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)) *
              ENNReal.ofReal
                (‖rawTensorConnLap (I := I) g r s T₀
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2) := by
            exact mul_le_mul_left hkey _
        _ = ENNReal.ofReal (Mα α + 1) *
              (ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (‖rawTensorConnLap (I := I) g r s T₀
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)) := by
            ring
        _ = ENNReal.ofReal (Mα α + 1) *
              (ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)) := by
            rw [h_pushed_eq]
    -- Integrate the pointwise bound.
    have hset_int_le :
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
                ‖rawTensorConnLap (I := I) g r s T₀
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
            ∂(volume : Measure EuclN)
          ≤ ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal (Mα α + 1) *
                (ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y))
              ∂(volume : Measure EuclN) :=
      MeasureTheory.setLIntegral_mono_ae'
        (chartTargetEuclid_measurableSet (I := I) (M := M) α)
        (Filter.Eventually.of_forall hpt_bound)
    -- Pull out the constant factor `ofReal (Mα α + 1)`.
    have hpull :
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal (Mα α + 1) *
            (ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                  (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y))
            ∂(volume : Measure EuclN)
          = ENNReal.ofReal (Mα α + 1) *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
                ∂(volume : Measure EuclN) := by
      rw [MeasureTheory.lintegral_const_mul']
      exact ENNReal.ofReal_ne_top
    -- Combine and pull out the Haar factor `cE`.
    calc (euclideanHaarFactor E : ℝ≥0∞) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                  (chartDensity g α
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
                    ‖rawTensorConnLap (I := I) g r s T₀
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
              ∂(volume : Measure EuclN)
        ≤ (euclideanHaarFactor E : ℝ≥0∞) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal (Mα α + 1) *
                (ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y))
              ∂(volume : Measure EuclN) :=
        mul_le_mul_right hset_int_le _
      _ = (euclideanHaarFactor E : ℝ≥0∞) *
            (ENNReal.ofReal (Mα α + 1) *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
                ∂(volume : Measure EuclN)) := by rw [hpull]
      _ = ((euclideanHaarFactor E : ℝ≥0∞) * ENNReal.ofReal (Mα α + 1)) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
              ∂(volume : Measure EuclN) := by ring
      _ = ENNReal.ofReal (cE * (Mα α + 1)) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
              ∂(volume : Measure EuclN) := by
            congr 1
            rw [hcE_def]
            have hMα1_nn : 0 ≤ Mα α + 1 := by have := hMα_nn α; linarith
            rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
            congr 1
            rw [ENNReal.ofReal_coe_nnreal]
  -- Step 5: bound each `cE · (Mα + 1)` by `cE · Σ_β (Mβ + 1)`, then by `C/N`.
  -- We then combine the per-α bound and multiply by N.
  -- Final piece: bound the whole RHS by `ofReal C * chartSobolevRawNormPou`.
  set Sum_pou : Finset M → ℝ := fun s =>
    ∑ β ∈ s, (Mα β + 1) with hSum_pou_def
  set C_inner : ℝ := cE * Sum_pou Sfin with hC_inner_def
  have hC_inner_nn : 0 ≤ C_inner := by
    refine mul_nonneg hcE_nn ?_
    refine Finset.sum_nonneg ?_
    intro β _; have := hMα_nn β; linarith
  have hC_eq : C = (N : ℝ) * C_inner := by
    rw [hC_def, hN_def, hSfin_def, hC_inner_def, hSum_pou_def, hMα_def, hcE_def]
    rfl
  -- Each per-α coefficient is bounded by `C_inner`.
  have hper_term_le : ∀ α ∈ Sfin,
      cE * (Mα α + 1) ≤ C_inner := by
    intro α hα_mem
    have h_term_le : (Mα α + 1) ≤ Sum_pou Sfin := by
      have hsum_nn : ∀ β ∈ Sfin, 0 ≤ Mα β + 1 := by
        intro β _; have := hMα_nn β; linarith
      exact Finset.single_le_sum (f := fun β => Mα β + 1) hsum_nn hα_mem
    rw [hC_inner_def]
    exact mul_le_mul_of_nonneg_left h_term_le hcE_nn
  -- Combine: per-α bound becomes `ofReal C_inner * (chart-target integrand)`.
  have hper_alpha_C_inner : ∀ α ∈ Sfin,
      ENNReal.ofReal (cE * (Mα α + 1)) *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                  (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
            ∂(volume : Measure EuclN) ≤
        ENNReal.ofReal C_inner *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                  (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
            ∂(volume : Measure EuclN) := by
    intro α hα_mem
    refine mul_le_mul_left ?_ _
    exact ENNReal.ofReal_le_ofReal (hper_term_le α hα_mem)
  -- Compose Steps 4 and 5: sum over α and bound.
  -- First, combine the per-α bounds.
  have hsum_per_alpha_le :
      ∑ α ∈ Sfin,
          ∫⁻ x, ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                  ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g)
        ≤ ∑ α ∈ Sfin,
            ENNReal.ofReal C_inner *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
                ∂(volume : Measure EuclN) := by
    refine Finset.sum_le_sum ?_
    intro α hα_mem
    exact le_trans (h_per_alpha α hα_mem) (hper_alpha_C_inner α hα_mem)
  -- Pull the constant `ofReal C_inner` outside the sum.
  have hpull_sum :
      ∑ α ∈ Sfin,
          ENNReal.ofReal C_inner *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
              ∂(volume : Measure EuclN)
        = ENNReal.ofReal C_inner *
            ∑ α ∈ Sfin,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
                ∂(volume : Measure EuclN) := by
    rw [← Finset.mul_sum]
  -- Combine.
  have h_combined :
      ENNReal.ofReal (N : ℝ) *
        ∑ α ∈ Sfin,
          ∫⁻ x, ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal (N : ℝ) *
          (ENNReal.ofReal C_inner *
            chartSobolevRawNormPou (I := I) (M := M) g r s T) := by
    refine mul_le_mul_right ?_ _
    rw [chartSobolevRawNormPou_def]
    calc
      ∑ α ∈ Sfin,
          ∫⁻ x, ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)
        ≤ ∑ α ∈ Sfin,
            ENNReal.ofReal C_inner *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
                ∂(volume : Measure EuclN) := hsum_per_alpha_le
      _ = ENNReal.ofReal C_inner *
            ∑ α ∈ Sfin,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
                ∂(volume : Measure EuclN) := hpull_sum
  -- Finalise: chain `h_int_le' ≤ h_combined` and rewrite `N · C_inner = C`.
  have h_NC_eq : ENNReal.ofReal (N : ℝ) * ENNReal.ofReal C_inner =
      ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_mul hN_nn, ← hC_eq]
  have h_final_eq :
      ENNReal.ofReal (N : ℝ) *
        (ENNReal.ofReal C_inner *
          chartSobolevRawNormPou (I := I) (M := M) g r s T) =
        ENNReal.ofReal C *
          chartSobolevRawNormPou (I := I) (M := M) g r s T := by
    rw [← mul_assoc, h_NC_eq]
  exact le_trans h_int_le' (le_trans h_combined (le_of_eq h_final_eq))

/-! ## Notes on the bridge to a chart-pushed Sobolev norm of `T`

A natural follow-up headline is to bound `chartSobolevRawNormPou g r s T` by a
multiple of a Sobolev norm of the chart-pushed scalar components of `T`:

```
∃ C : ℝ, 0 ≤ C ∧ ∀ T,
  chartSobolevRawNormPou g r s T ≤
  ENNReal.ofReal C *
    ∑ α ∈ chartAtlasPOU_finset I M, ∑ Idx Jdx,
      wkpNorm 2 2
        (chartPushedRaw I α (tensorChartComponentRaw g r s T α Idx Jdx))
        (chartTargetEuclid α)
```

The mathematical content of this bound is the elliptic regularity / chart-
Sobolev embedding inequality that bounds the chart-pushed `L²` norm of the raw
connection Laplacian by the chart-`W^{2,2}` norm of the chart-pushed scalar
components of `T`. Implementing this requires bridging:

* the model-fiber norm `‖rawTensorConnLap g r s T x‖²` (a sum of squared
  components in any orthonormal frame) to a sum of squared second derivatives
  of the chart-pushed scalar components (modulo Christoffel-symbol corrections);
* the chart-frame data terms `chartFrameData` and `secondAppChartData` of
  `rawTensorConnLap_pointwise_bound_chart_data` to component-wise Sobolev
  quantities `wkpNorm 2 2 (chartPushedRaw I α (tensorChartComponentRaw …))`.

This bridge is the elliptic-regularity counterpart of the present
chart-pushforward `L²` bound and rests on a substantial body of analysis that
is not yet in place at the level of the raw tensor connection Laplacian (the
existing chart-component / second-derivative bounds are formulated for the
scalar Laplacian and the first-order chart-pushed derivatives of tensor
components; they do not yet combine into a public second-derivative chart-
component bound on the raw connection Laplacian's pointwise squared norm).
This file ships the L² decomposition headline and records the bridge as a
follow-up. -/

end Connection
end Integral
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Integral.Connection.rawTensorConnLap_L2NormSq_le_chartSobolevRawNormPou
end Sanity
