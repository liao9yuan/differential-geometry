import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.GradNormChartBoundPouWeighted
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorComponentGradientL2Atoms
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TrivProj.Bridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartTwistUniformBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.GradNormChartBound
import DifferentialGeometry.Analysis.Laplacian.MetricBounds

/-!
# Per-`α` `eLpNorm` bound on the metric self-inner-product square-root of the
gradient of the chart-frame scalar component

For a closed Riemannian manifold `(M, g)` admitting a locally constant chart
selection, a chart base point `α : M`, and ranks `(r, s)`, this file collects
the file-local elementary inequalities used to assemble the per-`α` `L²`
bound

```
eLpNorm (b ↦ √ g.inner b (∇ u_α b) (∇ u_α b)) 2 (riemannianVolumeMeasure g) ≤
  ENNReal.ofReal C * ‖S‖₊
```

where `u_α := tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx`, the
metric `g.inner` is the Riemannian fibre inner product on the tangent bundle,
and the constant `C` depends only on `(g, r, s, α)` and the locality
hypothesis.

## Strategy

The complete proof combines:

* the pointwise `ρ_α²`-weighted gradient bound
  (`g_inner_gradFun_le_pou_weighted_atoms_on_pouTsupport_h1`) and the
  vanishing of the gradient off `tsupport ρ_α`
  (`sqrt_g_inner_gradFun_tensorChartComponentScalar_eq_zero_outside_pouTsupport`),
  giving, after taking square roots,
  `√ g.inner b (∇u) (∇u) ≤ √A · |raw|_indicator
                          + √B · ρ · √Tcov_sum + √B · ρ · √Tchr_sum`
  globally on `M`;
* the per-`α` `L²`-bound on the raw indicator
  (`exists_integral_indicator_tsupp_raw_sq_le_const_mul_h1NormSq`, G4);
* the per-`α` `L²`-bound on the chart-covariant-derivative atom sum
  (`exists_eLpNorm_sq_pou_mul_sum_triv_chart_cov_le_const_mul_h1NormSq`, G2);
* the per-`α` per-direction `L²`-bound on the chart-Christoffel-correction
  atom (`exists_eLpNorm_sq_pou_mul_sqrt_sum_christoffel_correction_le_const_mul_h1NormSq`,
  G3), bridged to the `G1` per-direction trivialised Christoffel correction
  via the chart-twist inverse uniform operator-norm bound
  (`chartRSTwistInv_pointwise_opNorm_isBounded_on_compact`) combined with a
  square-of-sum bound;
* `AEStronglyMeasurable` of each summand from the atom measurability
  headlines (`aestronglyMeasurable_pou_mul_sqrt_sum_triv_chart_cov`,
  `aestronglyMeasurable_pou_mul_sqrt_sum_christoffel_correction`,
  `aestronglyMeasurable_indicator_tsupp_abs_raw`).

Three Minkowski applications (`eLpNorm_add_le`) glue the three `eLpNorm`
bounds into the headline.

This module currently ships the elementary algebraic ingredients used in the
final assembly. The remaining structural bridge between the trivialised
Christoffel correction sum `Tchr_k = ‖triv(−Σ inputs + Σ outputs)‖²` and the
non-trivialised slot-correction Euclidean square `(Σ ‖input‖² + Σ ‖output‖²)`,
followed by the three-way Minkowski assembly, will land in a follow-up step
in the same module.

## File-local helper lemmas

* `sqrt_add_le_sqrt_add_sqrt` — `√(a + b) ≤ √a + √b` for non-negative reals.
* `sqrt_add3_le_sum` — `√(a + b + c) ≤ √a + √b + √c` for non-negative reals.
* `coe_nnnorm_eq_ofReal_norm` — `(‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 2400000
set_option maxHeartbeats 2400000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Geometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Elementary `Real.sqrt` inequalities

`√(a + b) ≤ √a + √b` and `√(a + b + c) ≤ √a + √b + √c` for non-negative
reals. These are used in the headline-assembly step to split the pointwise
gradient bound into three summands after taking square roots, prior to the
three-way Minkowski application. -/

/-- For non-negative reals `a`, `b`, `√(a + b) ≤ √a + √b`. -/
lemma sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h_sum_nn : 0 ≤ a + b := add_nonneg ha hb
  have h_sa_nn : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
  have h_sb_nn : 0 ≤ Real.sqrt b := Real.sqrt_nonneg _
  have h_sum_sq_nn : 0 ≤ Real.sqrt a + Real.sqrt b := add_nonneg h_sa_nn h_sb_nn
  have h_lhs_sq : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt h_sum_nn
  have h_rhs_sq : (Real.sqrt a + Real.sqrt b) ^ 2 =
      a + b + 2 * (Real.sqrt a * Real.sqrt b) := by
    rw [add_pow_two, Real.sq_sqrt ha, Real.sq_sqrt hb]; ring
  have h_cross_nn : 0 ≤ 2 * (Real.sqrt a * Real.sqrt b) := by positivity
  have h_sq_le : Real.sqrt (a + b) ^ 2 ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    rw [h_lhs_sq, h_rhs_sq]; linarith
  exact (abs_le_of_sq_le_sq' h_sq_le h_sum_sq_nn).2

/-- For non-negative reals `a`, `b`, `c`, `√(a + b + c) ≤ √a + √b + √c`. -/
lemma sqrt_add3_le_sum {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a + b + c) ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c := by
  have h_ab_nn : 0 ≤ a + b := add_nonneg ha hb
  have h_step1 : Real.sqrt (a + b + c) ≤ Real.sqrt (a + b) + Real.sqrt c :=
    sqrt_add_le_sqrt_add_sqrt h_ab_nn hc
  have h_step2 : Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b :=
    sqrt_add_le_sqrt_add_sqrt ha hb
  linarith

/-! ## Coercion helper -/

/-- For any element of a `SeminormedAddCommGroup`,
`(‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖`. -/
lemma coe_nnnorm_eq_ofReal_norm {X : Type*} [SeminormedAddCommGroup X]
    (x : X) :
    (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
  rw [show ((‖x‖₊ : ℝ≥0∞)) = ‖x‖ₑ from (enorm_eq_nnnorm x).symm,
    ← ofReal_norm_eq_enorm x]

/-! ## Elementary `Finset`-norm bounds for the bridge step

The bridge inequality requires bounding `‖∑ x_i‖² ≤ n · ∑ ‖x_i‖²` (a special
case of the Cauchy-Schwarz / power-mean inequality on a finite sum of norms),
and combining two such bounds for the input- and output-slot families. The
helpers below package the two ingredients we need:

* `sum_norm_sq_le_card_mul_sum_norm_sq` — `‖∑ x_i‖² ≤ |s| · ∑ ‖x_i‖²` on any
  finite indexing set, for any `NormedAddCommGroup` family;
* `norm_sq_neg_sum_add_sum_le_two_mul` — `‖−∑ x_i + ∑ y_l‖² ≤ 2·(‖∑ x_i‖² +
  ‖∑ y_l‖²)`, the squared-triangle bound `(a + b)² ≤ 2(a² + b²)` applied to
  the two block sums. -/

/-- For a finite indexing set `s : Finset ι` and a `NormedAddCommGroup`-valued
family `x : ι → X`, the square of the norm of the sum is bounded by `|s|`
times the sum of squared norms:
`‖∑ i ∈ s, x i‖² ≤ |s| · ∑ i ∈ s, ‖x i‖²`. -/
lemma sum_norm_sq_le_card_mul_sum_norm_sq
    {ι : Type*} {X : Type*} [SeminormedAddCommGroup X]
    (s : Finset ι) (x : ι → X) :
    ‖∑ i ∈ s, x i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖x i‖ ^ 2 := by
  classical
  -- Step A: triangle inequality on the sum, then square both sides.
  have h_tri : ‖∑ i ∈ s, x i‖ ≤ ∑ i ∈ s, ‖x i‖ := norm_sum_le _ _
  have h_lhs_nn : 0 ≤ ‖∑ i ∈ s, x i‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ ∑ i ∈ s, ‖x i‖ :=
    Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have h_sq_tri : ‖∑ i ∈ s, x i‖ ^ 2 ≤ (∑ i ∈ s, ‖x i‖) ^ 2 := by
    have := mul_self_le_mul_self h_lhs_nn h_tri
    rw [← sq, ← sq] at this
    exact this
  -- Step B: power-mean inequality `(∑ a_i)² ≤ |s| · ∑ a_i²` for non-neg reals.
  -- Mathlib's `sq_sum_le_card_mul_sum_sq` (Cauchy-Schwarz with constant-1).
  have h_pmi : (∑ i ∈ s, ‖x i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖x i‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  exact h_sq_tri.trans h_pmi

/-- For a `NormedAddCommGroup`-valued family `x : Fin r → X` and `y : Fin s → X`,
the squared norm of `(−∑ x_i + ∑ y_l)` is bounded by twice the sum of squared
sub-block norms:
`‖−∑ i, x i + ∑ l, y l‖² ≤ 2·(‖∑ x_i‖² + ‖∑ y_l‖²)`. -/
lemma norm_sq_neg_sum_add_sum_le_two_mul
    {r' s' : ℕ} {X : Type*} [SeminormedAddCommGroup X]
    (x : Fin r' → X) (y : Fin s' → X) :
    ‖- (∑ i : Fin r', x i) + (∑ l : Fin s', y l)‖ ^ 2 ≤
      2 * (‖∑ i : Fin r', x i‖ ^ 2 + ‖∑ l : Fin s', y l‖ ^ 2) := by
  classical
  -- Triangle, then `(a + b)² ≤ 2(a² + b²)`.
  set u : X := ∑ i : Fin r', x i with hu_def
  set v : X := ∑ l : Fin s', y l with hv_def
  have h_tri : ‖- u + v‖ ≤ ‖u‖ + ‖v‖ := by
    calc ‖- u + v‖ ≤ ‖- u‖ + ‖v‖ := norm_add_le _ _
      _ = ‖u‖ + ‖v‖ := by rw [norm_neg]
  have h_lhs_nn : 0 ≤ ‖- u + v‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ ‖u‖ + ‖v‖ := by positivity
  have h_sq : ‖- u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    have := mul_self_le_mul_self h_lhs_nn h_tri
    rw [← sq, ← sq] at this
    exact this
  -- `(a + b)² ≤ 2(a² + b²)` for real `a, b`.
  have h_abc : (‖u‖ + ‖v‖) ^ 2 ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    have h_id : (‖u‖ + ‖v‖) ^ 2 + (‖u‖ - ‖v‖) ^ 2 = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
      ring
    have h_diff_nn : 0 ≤ (‖u‖ - ‖v‖) ^ 2 := sq_nonneg _
    linarith
  exact h_sq.trans h_abc

/-! ## Bridge inequality between `Tchr_k` (G1 form) and `Σ‖input‖² + Σ‖output‖²`

For the chart-frame Christoffel slot-correction sum at direction `k`, the G1
pointwise gradient bound presents the trivialisation-norm of the signed
input/output slot sum, namely
`‖triv.continuousLinearMapAt b (− Σ_i input_i + Σ_l output_l)‖²`. The G3
`L²`-atom bound, on the other hand, presents the Euclidean sum of squared
individual slot-correction norms, namely `Σ_i ‖input_i‖² + Σ_l ‖output_l‖²`.

This section ships the *pointwise* bridge inequality between the two,
controlling the G1 form by a constant multiple of the G3 form, uniformly on
the compact partition-of-unity support of the chart-`α` weight.

The derivation chains:
1. `triv.continuousLinearMapAt = chartRSTwistInv α b ∘ TensorRSSpace.toModel`
   (via `triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel`).
2. Uniform op-norm bound on `chartRSTwistInv α b r s` over the compact
   `tsupport ρ_α ⊆ (chartAt H α).source`
   (via `chartRSTwistInv_pointwise_opNorm_isBounded_on_compact`).
3. `‖TensorRSSpace.toModel X‖ = ‖X‖` definitionally (the induced norm on the
   bundle fibre is the pull-back of the model norm along the model-equiv).
4. The two `Finset`-norm helpers above. -/

/-- **Bridge inequality** between the G1 trivialisation-norm form `Tchr_k`
and the G3 slot-correction Euclidean square form. For each chart-basis
direction `k : Fin (Module.finrank ℝ E)`, every point `b ∈ tsupport ρ_α`, and
every smooth compactly-supported `(r, s)`-tensor section `S`:
```
‖triv.continuousLinearMapAt b
  (− ∑ i, chartTensorRSInputSlotCorrection ... b i
    + ∑ l, chartTensorRSOutputSlotCorrection ... b l)‖² ≤
  C_bridge · ( (∑ i, ‖chartTensorRSInputSlotCorrection ... b i‖²)
             + (∑ l, ‖chartTensorRSOutputSlotCorrection ... b l‖²) )
```
The non-negative constant `C_bridge` depends only on `(g, α, r, s)` and the
locality hypothesis; it is independent of `S`, of `b ∈ tsupport ρ_α`, and of
the direction `k`. -/
theorem norm_sq_triv_neg_sum_add_sum_le_const_mul_sum_norm_sq_on_pouTsupport
    (h_atlas : HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C_bridge : ℝ, 0 ≤ C_bridge ∧
      ∀ (S : SmoothCcTensor g r s) (k : Fin (Module.finrank ℝ E)) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖(trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (- (∑ i : Fin r,
              chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun b' => S.toSection b')
                (chartBasisVecFiber (I := I) α k) b i)
            + (∑ l : Fin s,
                chartTensorRSOutputSlotCorrection (I := I) r s g α
                  (fun b' => S.toSection b')
                  (chartBasisVecFiber (I := I) α k) b l))‖ ^ 2 ≤
          C_bridge *
            ((∑ i : Fin r,
                ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                    (fun b' => S.toSection b')
                    (chartBasisVecFiber (I := I) α k) b i‖ ^ 2) +
              (∑ l : Fin s,
                ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                    (fun b' => S.toSection b')
                    (chartBasisVecFiber (I := I) α k) b l‖ ^ 2)) := by
  classical
  -- Compact `K := tsupport ρ_α ⊆ (chartAt H α).source`.
  set K : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_def
  have hK_compact : IsCompact K :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K ⊆ (chartAt H α).source := by
    intro b hb
    exact chartAtlasPOU_isSubordinate (I := I) (M := M) α hb
  -- Uniform op-norm bound on `chartRSTwistInv α b r s` over `K`.
  obtain ⟨C₀, hC₀_pos, hC₀_le⟩ :=
    chartRSTwistInv_pointwise_opNorm_isBounded_on_compact
      (I := I) (M := M) h_atlas α hK_compact hK_sub r s
  -- The bridge constant: `C_bridge := 2 · (max r s + max r s) · C₀² = 4 · max r s · C₀²`,
  -- but to keep it simple we use `2 · (r + s) · C₀²`, which dominates both
  -- `2 r · C₀²` and `2 s · C₀²`.
  set C_bridge : ℝ := 2 * ((r : ℝ) + s) * C₀ ^ 2 with hC_bridge_def
  have hC_bridge_nn : 0 ≤ C_bridge := by
    rw [hC_bridge_def]; positivity
  refine ⟨C_bridge, hC_bridge_nn, ?_⟩
  intro S k b hb
  -- Convenient abbreviations for the slot-correction families.
  set a : Fin r → TensorRSSpace r s I b := fun i =>
    chartTensorRSInputSlotCorrection (I := I) r s g α
      (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α k) b i
    with ha_def
  set c : Fin s → TensorRSSpace r s I b := fun l =>
    chartTensorRSOutputSlotCorrection (I := I) r s g α
      (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α k) b l
    with hc_def
  set X : TensorRSSpace r s I b := - (∑ i : Fin r, a i) + (∑ l : Fin s, c l)
    with hX_def
  -- `b ∈ (chartAt H α).source`.
  have hb_chart : b ∈ (chartAt H α).source := hK_sub hb
  -- Step 1: the bridge identity equates `triv.continuousLinearMapAt b X` with
  -- `chartRSTwistInv α b r s (TensorRSSpace.toModel X)`.
  have h_bridge :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b X =
        chartRSTwistInv (I := I) (M := M) α b r s
          (TensorRSSpace.toModel (𝕜 := ℝ) X) :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
      (I := I) (M := M) r s α hb_chart X
  -- Step 2: op-norm bound on `chartRSTwistInv` at `b ∈ K`.
  have h_opNorm :
      ‖chartRSTwistInv (I := I) (M := M) α b r s
          (TensorRSSpace.toModel (𝕜 := ℝ) X)‖ ≤
        C₀ * ‖TensorRSSpace.toModel (𝕜 := ℝ) X‖ :=
    hC₀_le b hb (TensorRSSpace.toModel (𝕜 := ℝ) X)
  -- Step 3: norm-preservation for `TensorRSSpace.toModel`: definitional `rfl`.
  have h_norm_eq :
      ‖TensorRSSpace.toModel (𝕜 := ℝ) X‖ = ‖X‖ := rfl
  -- Combine 1+2+3 into `‖triv...X‖ ≤ C₀ · ‖X‖`.
  have h_step1 :
      ‖(trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b X‖ ≤
        C₀ * ‖X‖ := by
    rw [h_bridge]
    rw [h_norm_eq] at h_opNorm
    exact h_opNorm
  -- Square both sides: `‖triv...X‖² ≤ C₀² · ‖X‖²`.
  have h_triv_lhs_nn :
      0 ≤ ‖(trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b X‖ :=
    norm_nonneg _
  have h_C0_X_nn : 0 ≤ C₀ * ‖X‖ := mul_nonneg hC₀_pos.le (norm_nonneg _)
  have h_step1_sq :
      ‖(trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b X‖ ^ 2 ≤
        (C₀ * ‖X‖) ^ 2 := by
    have := mul_self_le_mul_self h_triv_lhs_nn h_step1
    rw [← sq, ← sq] at this
    exact this
  have h_sq_C₀X : (C₀ * ‖X‖) ^ 2 = C₀ ^ 2 * ‖X‖ ^ 2 := by ring
  rw [h_sq_C₀X] at h_step1_sq
  -- Step 4: `‖X‖² = ‖−Σa + Σc‖² ≤ 2 (‖Σa‖² + ‖Σc‖²) ≤ 2 r · Σ‖a_i‖² + 2 s · Σ‖c_l‖²`.
  have h_X_sq_split :
      ‖X‖ ^ 2 ≤
        2 * (‖∑ i : Fin r, a i‖ ^ 2 + ‖∑ l : Fin s, c l‖ ^ 2) :=
    norm_sq_neg_sum_add_sum_le_two_mul (r' := r) (s' := s) a c
  have h_sum_a_sq :
      ‖∑ i : Fin r, a i‖ ^ 2 ≤ (r : ℝ) * ∑ i : Fin r, ‖a i‖ ^ 2 := by
    have h := sum_norm_sq_le_card_mul_sum_norm_sq
      (s := (Finset.univ : Finset (Fin r))) a
    have hcard : ((Finset.univ : Finset (Fin r)).card : ℝ) = (r : ℝ) := by
      rw [Finset.card_univ, Fintype.card_fin]
    rw [hcard] at h
    exact h
  have h_sum_c_sq :
      ‖∑ l : Fin s, c l‖ ^ 2 ≤ (s : ℝ) * ∑ l : Fin s, ‖c l‖ ^ 2 := by
    have h := sum_norm_sq_le_card_mul_sum_norm_sq
      (s := (Finset.univ : Finset (Fin s))) c
    have hcard : ((Finset.univ : Finset (Fin s)).card : ℝ) = (s : ℝ) := by
      rw [Finset.card_univ, Fintype.card_fin]
    rw [hcard] at h
    exact h
  -- Combine: `‖X‖² ≤ 2r · Σ‖a_i‖² + 2s · Σ‖c_l‖²`.
  have h_a_sum_nn : 0 ≤ ∑ i : Fin r, ‖a i‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_c_sum_nn : 0 ≤ ∑ l : Fin s, ‖c l‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_X_sq_bound :
      ‖X‖ ^ 2 ≤ 2 * (r : ℝ) * (∑ i : Fin r, ‖a i‖ ^ 2) +
        2 * (s : ℝ) * (∑ l : Fin s, ‖c l‖ ^ 2) := by
    have h1 : 2 * (‖∑ i : Fin r, a i‖ ^ 2 + ‖∑ l : Fin s, c l‖ ^ 2) ≤
        2 * ((r : ℝ) * ∑ i : Fin r, ‖a i‖ ^ 2 + (s : ℝ) * ∑ l : Fin s, ‖c l‖ ^ 2) := by
      have h_add_le :
          ‖∑ i : Fin r, a i‖ ^ 2 + ‖∑ l : Fin s, c l‖ ^ 2 ≤
            (r : ℝ) * (∑ i : Fin r, ‖a i‖ ^ 2) +
            (s : ℝ) * (∑ l : Fin s, ‖c l‖ ^ 2) :=
        add_le_add h_sum_a_sq h_sum_c_sq
      have h_2_nn : (0 : ℝ) ≤ 2 := by norm_num
      exact mul_le_mul_of_nonneg_left h_add_le h_2_nn
    refine h_X_sq_split.trans ?_
    have h_rw :
        2 * ((r : ℝ) * ∑ i : Fin r, ‖a i‖ ^ 2 + (s : ℝ) * ∑ l : Fin s, ‖c l‖ ^ 2) =
          2 * (r : ℝ) * (∑ i : Fin r, ‖a i‖ ^ 2) +
            2 * (s : ℝ) * (∑ l : Fin s, ‖c l‖ ^ 2) := by ring
    rw [h_rw] at h1
    exact h1
  -- Step 5: dominate `2r · A + 2s · B ≤ 2(r+s) · (A + B)`.
  have h_r_le_rs : (r : ℝ) ≤ (r : ℝ) + s := by
    have : (0 : ℝ) ≤ (s : ℝ) := by positivity
    linarith
  have h_s_le_rs : (s : ℝ) ≤ (r : ℝ) + s := by
    have : (0 : ℝ) ≤ (r : ℝ) := by positivity
    linarith
  have h_r_2_le : 2 * (r : ℝ) ≤ 2 * ((r : ℝ) + s) := by linarith
  have h_s_2_le : 2 * (s : ℝ) ≤ 2 * ((r : ℝ) + s) := by linarith
  have h_2rs_nn : 0 ≤ 2 * ((r : ℝ) + s) := by positivity
  have h_X_sq_unified :
      ‖X‖ ^ 2 ≤ 2 * ((r : ℝ) + s) *
        ((∑ i : Fin r, ‖a i‖ ^ 2) + (∑ l : Fin s, ‖c l‖ ^ 2)) := by
    refine h_X_sq_bound.trans ?_
    have h1 : 2 * (r : ℝ) * (∑ i : Fin r, ‖a i‖ ^ 2) ≤
        2 * ((r : ℝ) + s) * (∑ i : Fin r, ‖a i‖ ^ 2) :=
      mul_le_mul_of_nonneg_right h_r_2_le h_a_sum_nn
    have h2 : 2 * (s : ℝ) * (∑ l : Fin s, ‖c l‖ ^ 2) ≤
        2 * ((r : ℝ) + s) * (∑ l : Fin s, ‖c l‖ ^ 2) :=
      mul_le_mul_of_nonneg_right h_s_2_le h_c_sum_nn
    have h_split :
        2 * ((r : ℝ) + s) *
          ((∑ i : Fin r, ‖a i‖ ^ 2) + (∑ l : Fin s, ‖c l‖ ^ 2)) =
        2 * ((r : ℝ) + s) * (∑ i : Fin r, ‖a i‖ ^ 2) +
          2 * ((r : ℝ) + s) * (∑ l : Fin s, ‖c l‖ ^ 2) := by ring
    rw [h_split]
    linarith
  -- Step 6: multiply by `C₀²` and combine with Step 3.
  have h_C0_sq_nn : 0 ≤ C₀ ^ 2 := by positivity
  have h_combined :
      C₀ ^ 2 * ‖X‖ ^ 2 ≤
        C₀ ^ 2 * (2 * ((r : ℝ) + s) *
          ((∑ i : Fin r, ‖a i‖ ^ 2) + (∑ l : Fin s, ‖c l‖ ^ 2))) :=
    mul_le_mul_of_nonneg_left h_X_sq_unified h_C0_sq_nn
  have h_assoc :
      C₀ ^ 2 * (2 * ((r : ℝ) + s) *
        ((∑ i : Fin r, ‖a i‖ ^ 2) + (∑ l : Fin s, ‖c l‖ ^ 2))) =
        C_bridge *
          ((∑ i : Fin r, ‖a i‖ ^ 2) + (∑ l : Fin s, ‖c l‖ ^ 2)) := by
    rw [hC_bridge_def]; ring
  rw [h_assoc] at h_combined
  -- Chain `h_step1_sq` (LHS ≤ C₀² · ‖X‖²) with `h_combined`.
  exact h_step1_sq.trans h_combined

/-! ## `H¹` variant of the bridge inequality -/

/-- **`H¹` variant.** Same as
`norm_sq_triv_neg_sum_add_sum_le_const_mul_sum_norm_sq_on_pouTsupport`,
formulated for the `H^1` wrapper `SmoothCcTensorH1`. Specialised by applying
the underlying `SmoothCcTensor` theorem to `S.toCcTensor`. -/
theorem norm_sq_triv_neg_sum_add_sum_le_const_mul_sum_norm_sq_on_pouTsupport_h1
    (h_atlas : HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C_bridge : ℝ, 0 ≤ C_bridge ∧
      ∀ (S : SmoothCcTensorH1 g r s) (k : Fin (Module.finrank ℝ E)) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖(trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (- (∑ i : Fin r,
              chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun b' => S.toCcTensor.toSection b')
                (chartBasisVecFiber (I := I) α k) b i)
            + (∑ l : Fin s,
                chartTensorRSOutputSlotCorrection (I := I) r s g α
                  (fun b' => S.toCcTensor.toSection b')
                  (chartBasisVecFiber (I := I) α k) b l))‖ ^ 2 ≤
          C_bridge *
            ((∑ i : Fin r,
                ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α k) b i‖ ^ 2) +
              (∑ l : Fin s,
                ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α k) b l‖ ^ 2)) := by
  obtain ⟨C_bridge, hC_nn, h⟩ :=
    norm_sq_triv_neg_sum_add_sum_le_const_mul_sum_norm_sq_on_pouTsupport
      (I := I) (M := M) h_atlas g r s α
  exact ⟨C_bridge, hC_nn, fun S k b hb => h S.toCcTensor k hb⟩

/-! ## Sub-additivity of `Real.sqrt` over a finite Fin-sum

We need `√(∑ k, a k) ≤ ∑ k, √(a k)` for non-negative reals, which we obtain
by induction on the cardinality via the two-term `sqrt_add_le_sqrt_add_sqrt`
helper above. -/

/-- For a non-negative real-valued family `a : Fin n → ℝ`, the square root of
the finite sum is bounded by the sum of square roots:
`√(∑ k, a k) ≤ ∑ k, √(a k)`. -/
lemma sqrt_sum_le_sum_sqrt_fin {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ k, 0 ≤ a k) :
    Real.sqrt (∑ k : Fin n, a k) ≤ ∑ k : Fin n, Real.sqrt (a k) := by
  classical
  -- Induction on `n` by `Finset.induction_on` over `Finset.univ : Finset (Fin n)`.
  -- We instead prove the more general statement on any `Finset`.
  suffices h : ∀ (s : Finset (Fin n)),
      Real.sqrt (∑ k ∈ s, a k) ≤ ∑ k ∈ s, Real.sqrt (a k) by
    simpa using h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert k₀ s' hk_notin ih =>
      rw [Finset.sum_insert hk_notin, Finset.sum_insert hk_notin]
      have h_a_nn : 0 ≤ a k₀ := ha k₀
      have h_sum_nn : 0 ≤ ∑ k ∈ s', a k :=
        Finset.sum_nonneg (fun k _ => ha k)
      have h_sqrt_add :=
        sqrt_add_le_sqrt_add_sqrt h_a_nn h_sum_nn
      have h_sqrt_ind : Real.sqrt (∑ k ∈ s', a k) ≤ ∑ k ∈ s', Real.sqrt (a k) := ih
      linarith

/-! ## The G5 headline assembly

We avoid the AE-strong-measurability hypotheses of three-term Minkowski
(`eLpNorm_add_le`) by working at the level of the squared `L²` seminorm,
which equals a `lintegral` of the squared `enorm` of the integrand. The
pointwise gradient bound is then a real-valued inequality, and the
`lintegral` is additive across the three non-negative summands. Each of
the three integrated pieces matches one of the atomic `L^2` headlines
(G2 / G3 / G4) used in squared form via Cauchy-Schwarz on `eLpNorm`.

This proof strategy mirrors the one used by `CovL2BoundFromH1.lean` (the
G2-atom `L^2`-bound) and avoids the need for explicit measurability of
the non-trivialised Christoffel slot-correction sum (only its `eLpNorm`
bound is consumed). -/

/-- **G5 headline: per-`α` `L²` bound on the metric self-inner-product
square-root of the gradient of the chart-frame scalar component.**

For a closed Riemannian manifold `(M, g)` admitting a locally constant chart
selection, ranks `(r, s)`, and a chart base point `α : M`, there is a
non-negative constant `C` (depending only on `(g, r, s, α)` and the locality
hypothesis) such that for every smooth compactly-supported `H^1` tensor
section `S : SmoothCcTensorH1 g r s` and every chart-frame multi-index
choice `(Idx, Jdx)`,
```
eLpNorm
    (fun b => √ g.inner b (∇u_α b) (∇u_α b)) 2 (riemannianVolumeMeasure g) ≤
  ENNReal.ofReal C * ‖S‖₊,
```
where `u_α := tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx`. The
constant `C` is independent of `S` and of `(Idx, Jdx)`. -/
theorem exists_eLpNorm_sqrt_g_inner_gradFun_tensorChartComponentScalar_le_const_mul_h1Norm
    (h_atlas : HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (fun b : M => Real.sqrt
            (g.inner b
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) b)
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) b))) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  -- ===== STRATEGY =====
  -- Avoid Minkowski (no AE-strong-measurability of the non-trivialised
  -- Christoffel slot-correction sum is shipped). Work directly on the squared
  -- L²-seminorm `(eLpNorm √Tinner 2 μ)² = ∫⁻ ofReal(Tinner)`, bound `Tinner`
  -- pointwise by `A · raw²·𝟙 + B · ρ² · Tcov + B · C_bridge · ρ² · TchrSumJ`,
  -- split the lintegral by additivity (ofReal of a non-negative sum), and
  -- bound each lintegral by squaring G4 / G2 / G3 via `sq_eLpNorm_two_eq_lintegral_enorm_sq`.
  -- Final constant: `C := √(A · C₄² + B · C₂² + B · C_bridge · ∑ j C₃_j²)`.
  -- ===== Step 1: extract atomic constants and bridge constant =====
  obtain ⟨A, B, hA_nn, hB_nn, h_G1⟩ :=
    g_inner_gradFun_le_pou_weighted_atoms_on_pouTsupport_h1
      (I := I) (M := M) g r s α
  obtain ⟨C_bridge, hC_bridge_nn, h_bridge⟩ :=
    norm_sq_triv_neg_sum_add_sum_le_const_mul_sum_norm_sq_on_pouTsupport_h1
      (I := I) (M := M) h_atlas g r s α
  obtain ⟨C₂, hC₂_nn, h_G2⟩ :=
    exists_eLpNorm_sq_pou_mul_sum_triv_chart_cov_le_const_mul_h1NormSq
      (I := I) (M := M) h_atlas g r s α
  obtain ⟨C₄, hC₄_nn, h_G4⟩ :=
    exists_integral_indicator_tsupp_raw_sq_le_const_mul_h1NormSq
      (I := I) (M := M) h_atlas g r s α
  -- Uniform input/output slot-correction operator-norm bounds on `tsupport ρ_α`.
  obtain ⟨M_F_in, hM_F_in_nn, hM_F_in_le⟩ :=
    chartTensorRSInputSlotCorrection_norm_le_const_on_pouTsupport
      (I := I) (M := M) h_atlas g r s α
  obtain ⟨M_F_out, hM_F_out_nn, hM_F_out_le⟩ :=
    chartTensorRSOutputSlotCorrection_norm_le_const_on_pouTsupport
      (I := I) (M := M) h_atlas g r s α
  set M_F : ℝ := max M_F_in M_F_out with hM_F_def
  have hM_F_nn : 0 ≤ M_F := le_max_of_le_left hM_F_in_nn
  -- Section-norm-square ≤ K_S · tensorInnerPointwise on `tsupport ρ_α`.
  obtain ⟨K_S, hK_S_nn, hK_S_bound⟩ :=
    norm_section_sq_le_const_mul_tensorInnerPointwise_on_pouTsupport
      (I := I) (M := M) h_atlas g r s α
  -- ===== Step 2: final constant =====
  -- The third-piece bound `B · C_bridge · ρ² · TchrSumJ` is dominated, on
  -- `tsupport ρ_α`, by `B · C_bridge · n · (r + s) · M_F² · K_S` times
  -- `tensorInnerPointwise b S S`, whose Bochner integral is bounded by
  -- `‖S‖²` (smooth-compact-support section, H¹-norm dominates L²-norm).
  set n : ℕ := Module.finrank ℝ E with hn_def
  set C₃ : ℝ := B * C_bridge * (n : ℝ) * ((r : ℝ) + (s : ℝ)) * M_F ^ 2 * K_S
    with hC₃_def
  have hC₃_nn : 0 ≤ C₃ := by
    rw [hC₃_def]; positivity
  set C_sq : ℝ :=
    A * C₄ ^ 2 + B * C₂ ^ 2 + C₃
    with hC_sq_def
  have hC_sq_nn : 0 ≤ C_sq := by
    rw [hC_sq_def]; positivity
  set C : ℝ := Real.sqrt C_sq with hC_def
  have hC_nn : 0 ≤ C := Real.sqrt_nonneg _
  refine ⟨C, hC_nn, ?_⟩
  intro S Idx Jdx
  -- ===== Step 3: concise abbreviations =====
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g
    with hμ_def
  set u : M → ℝ := tensorChartComponentScalar (I := I) (M := M)
      g r s S.toCcTensor α Idx Jdx with hu_def
  set ρ : M → ℝ := fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hρ_def
  -- Drop the abbreviations approach for the rawZ piece; we work directly.
  -- Inner integrand: `Tinner b := g.inner b (∇u b) (∇u b)`, non-negative.
  set Tinner : M → ℝ := fun b : M =>
      g.inner b (gradFun (I := I) g u b) (gradFun (I := I) g u b)
    with hTinner_def
  set TinnerSqrt : M → ℝ := fun b : M => Real.sqrt (Tinner b) with hTinnerSqrt_def
  have hTinner_nn : ∀ b, 0 ≤ Tinner b := fun b => by
    rw [hTinner_def]
    exact DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
      (I := I) (M := M) g b _
  -- The goal LHS already definitionally matches `TinnerSqrt` via `u = ...`.
  show eLpNorm TinnerSqrt 2 μ ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞)
  -- ===== Step 4: pointwise bound `Tinner ≤ A·raw²·𝟙 + B·ρ²·Tcov + B·C_bridge·ρ²·TchrSumJ` =====
  -- We bind some abbreviations for the three non-negative summands.
  set rawZ : M → ℝ := fun b : M =>
      scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M)
          g r s S.toCcTensor α Idx Jdx) (extChartAt I α b) with hrawZ_def
  set rawInd : M → ℝ := fun b : M =>
      (tsupport ρ).indicator rawZ b with hrawInd_def
  set Tcov : M → ℝ := fun b : M => ∑ k : Fin (Module.finrank ℝ E),
      ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (chartTensorRSCovariantDerivative (I := I) r s g α
          (fun b' => S.toCcTensor.toSection b')
          (chartBasisVecFiber (I := I) α k) b)‖ ^ 2
    with hTcov_def
  -- Per direction `j`: the chart Christoffel slot-correction Euclidean sum.
  set TchrPerJ : Fin (Module.finrank ℝ E) → M → ℝ := fun j b =>
    (∑ k : Fin r,
        ‖chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun b' => S.toCcTensor.toSection b')
            (chartBasisVecFiber (I := I) α j) b k‖ ^ 2) +
      (∑ l : Fin s,
        ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun b' => S.toCcTensor.toSection b')
            (chartBasisVecFiber (I := I) α j) b l‖ ^ 2)
    with hTchrPerJ_def
  set TchrSumJ : M → ℝ := fun b : M => ∑ j : Fin (Module.finrank ℝ E), TchrPerJ j b
    with hTchrSumJ_def
  -- The G1 trivialised Christoffel sum, per direction k:
  set TchrTriv : M → ℝ := fun b : M => ∑ k : Fin (Module.finrank ℝ E),
      ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (- (∑ i : Fin r,
            chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun b' => S.toCcTensor.toSection b')
              (chartBasisVecFiber (I := I) α k) b i)
          + (∑ l : Fin s,
              chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun b' => S.toCcTensor.toSection b')
                (chartBasisVecFiber (I := I) α k) b l))‖ ^ 2
    with hTchrTriv_def
  -- ===== Step 4: pointwise bound on `Tinner` =====
  -- On tsupport: use G1 + bridge per-k. Off tsupport: LHS = 0.
  have hρ_nn : ∀ b, 0 ≤ ρ b := fun b => by
    rw [hρ_def]; exact (chartAtlasPOU I M).nonneg α b
  have h_ptbound : ∀ b : M, Tinner b ≤
      A * (rawInd b) ^ 2 +
        B * (ρ b) ^ 2 * Tcov b +
        B * C_bridge * (ρ b) ^ 2 * TchrSumJ b := by
    intro b
    by_cases hb : b ∈ tsupport ρ
    · -- On tsupport: use G1, then bridge, then convert to TchrSumJ form.
      have h_G1_b := h_G1 S Idx Jdx b hb
      -- G1: `Tinner b ≤ A · rawZ² + B · ρ² · (Tcov + TchrTriv)`.
      have h_G1' : Tinner b ≤
          A * rawZ b ^ 2 + B * (ρ b) ^ 2 * (Tcov b + TchrTriv b) := h_G1_b
      -- Bridge bound on `TchrTriv b ≤ C_bridge · TchrSumJ b`.
      have h_TchrTriv_le : TchrTriv b ≤ C_bridge * TchrSumJ b := by
        rw [hTchrTriv_def, hTchrSumJ_def]
        have h1 : ∑ k : Fin (Module.finrank ℝ E),
            ‖(trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              (- (∑ i : Fin r,
                  chartTensorRSInputSlotCorrection (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α k) b i)
                + (∑ l : Fin s,
                    chartTensorRSOutputSlotCorrection (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (chartBasisVecFiber (I := I) α k) b l))‖ ^ 2 ≤
            ∑ k : Fin (Module.finrank ℝ E), C_bridge * TchrPerJ k b :=
          Finset.sum_le_sum (fun k _ => h_bridge S k hb)
        have h_mul_sum :
            ∑ k : Fin (Module.finrank ℝ E), C_bridge * TchrPerJ k b =
              C_bridge * ∑ k : Fin (Module.finrank ℝ E), TchrPerJ k b := by
          rw [← Finset.mul_sum]
        rw [h_mul_sum] at h1
        exact h1
      -- Combine algebraically.
      have h_Tcov_nn : 0 ≤ Tcov b := by
        rw [hTcov_def]
        exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have h_TchrSumJ_nn : 0 ≤ TchrSumJ b := by
        rw [hTchrSumJ_def]
        refine Finset.sum_nonneg (fun j _ => ?_)
        rw [hTchrPerJ_def]
        exact add_nonneg
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      have h_ρ_sq_nn : 0 ≤ (ρ b) ^ 2 := sq_nonneg _
      have h_Bρ_sq_nn : 0 ≤ B * (ρ b) ^ 2 := mul_nonneg hB_nn h_ρ_sq_nn
      -- On tsupport: `rawInd b = rawZ b`.
      have h_rawInd_eq : rawInd b = rawZ b := by
        show (tsupport ρ).indicator rawZ b = rawZ b
        exact Set.indicator_of_mem hb _
      have h_TchrTriv_step : B * (ρ b) ^ 2 * TchrTriv b ≤
          B * (ρ b) ^ 2 * (C_bridge * TchrSumJ b) :=
        mul_le_mul_of_nonneg_left h_TchrTriv_le h_Bρ_sq_nn
      calc Tinner b
          ≤ A * rawZ b ^ 2 + B * (ρ b) ^ 2 * (Tcov b + TchrTriv b) := h_G1'
        _ = A * rawZ b ^ 2 + B * (ρ b) ^ 2 * Tcov b +
              B * (ρ b) ^ 2 * TchrTriv b := by ring
        _ ≤ A * rawZ b ^ 2 + B * (ρ b) ^ 2 * Tcov b +
              B * (ρ b) ^ 2 * (C_bridge * TchrSumJ b) := by linarith
        _ = A * rawInd b ^ 2 + B * (ρ b) ^ 2 * Tcov b +
              B * C_bridge * (ρ b) ^ 2 * TchrSumJ b := by
              rw [h_rawInd_eq]; ring
    · -- Off tsupport: `Tinner b = 0` (gradient vanishes); RHS ≥ 0.
      -- Use the public sqrt-form vanishing lemma + `Real.sqrt_eq_zero`.
      have h_sqrt_zero :
          Real.sqrt (g.inner b
            (gradFun (I := I) g
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx) b)
            (gradFun (I := I) g
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx) b)) = 0 :=
        sqrt_g_inner_gradFun_tensorChartComponentScalar_eq_zero_outside_pouTsupport
          (I := I) (M := M) g r s S.toCcTensor α Idx Jdx hb
      have h_Tinner_zero : Tinner b = 0 := by
        rw [hTinner_def, hu_def]
        have h_nn := hTinner_nn b
        rw [hTinner_def, hu_def] at h_nn
        -- `√x = 0` and `0 ≤ x` implies `x = 0`.
        exact (Real.sqrt_eq_zero h_nn).mp h_sqrt_zero
      rw [h_Tinner_zero]
      -- rawInd b = 0 off tsupport (indicator).
      have h_rawInd_zero : rawInd b = 0 := by
        show (tsupport ρ).indicator rawZ b = 0
        exact Set.indicator_of_notMem hb _
      -- ρ b = 0 off tsupport.
      have h_ρ_zero : ρ b = 0 := by
        by_contra hne
        exact hb (subset_tsupport _ hne)
      rw [h_rawInd_zero, h_ρ_zero]
      simp
  -- ===== Step 5: convert squared `eLpNorm` to `lintegral` and bound it =====
  -- Goal: `(eLpNorm TinnerSqrt 2 μ)² ≤ ENNReal.ofReal (C_sq · ‖S‖²)`.
  -- Strategy: pointwise `(TinnerSqrt b)² = Tinner b ≥ 0`, then bound the
  -- lintegral of `ofReal (Tinner b)` by the lintegral of `ofReal` of the
  -- three-summand bound, splitting via `ENNReal.ofReal_add` (non-neg) and
  -- linearity of lintegral.
  have h_TinnerSqrt_sq : ∀ b, (TinnerSqrt b) ^ 2 = Tinner b := fun b => by
    rw [hTinnerSqrt_def, Real.sq_sqrt (hTinner_nn b)]
  -- ENNReal-valued pointwise bound on `‖TinnerSqrt b‖ₑ²`.
  have h_pt_enn : ∀ b, (‖TinnerSqrt b‖ₑ : ℝ≥0∞) ^ 2 ≤
      ENNReal.ofReal (A * (rawInd b) ^ 2) +
        ENNReal.ofReal (B * (ρ b) ^ 2 * Tcov b) +
        ENNReal.ofReal (B * C_bridge * (ρ b) ^ 2 * TchrSumJ b) := by
    intro b
    -- `‖x‖ₑ² = ofReal(x²)` for any real `x ≥ 0` via `Real.enorm_eq_ofReal_abs`.
    have h_lhs : (‖TinnerSqrt b‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (Tinner b) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
        sq_abs, h_TinnerSqrt_sq]
    rw [h_lhs]
    have h_t1_nn : 0 ≤ A * (rawInd b) ^ 2 := mul_nonneg hA_nn (sq_nonneg _)
    have h_Tcov_nn : 0 ≤ Tcov b := by
      rw [hTcov_def]
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have h_TchrSumJ_nn : 0 ≤ TchrSumJ b := by
      rw [hTchrSumJ_def]
      refine Finset.sum_nonneg (fun j _ => ?_)
      rw [hTchrPerJ_def]
      exact add_nonneg
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have h_t2_nn : 0 ≤ B * (ρ b) ^ 2 * Tcov b :=
      mul_nonneg (mul_nonneg hB_nn (sq_nonneg _)) h_Tcov_nn
    have h_t3_nn : 0 ≤ B * C_bridge * (ρ b) ^ 2 * TchrSumJ b :=
      mul_nonneg (mul_nonneg (mul_nonneg hB_nn hC_bridge_nn) (sq_nonneg _))
        h_TchrSumJ_nn
    -- `ofReal(a + b + c) = ofReal a + ofReal b + ofReal c` for non-neg.
    have h_add :
        ENNReal.ofReal (A * (rawInd b) ^ 2 + B * (ρ b) ^ 2 * Tcov b +
            B * C_bridge * (ρ b) ^ 2 * TchrSumJ b) =
          ENNReal.ofReal (A * (rawInd b) ^ 2) +
            ENNReal.ofReal (B * (ρ b) ^ 2 * Tcov b) +
            ENNReal.ofReal (B * C_bridge * (ρ b) ^ 2 * TchrSumJ b) := by
      rw [ENNReal.ofReal_add (add_nonneg h_t1_nn h_t2_nn) h_t3_nn,
          ENNReal.ofReal_add h_t1_nn h_t2_nn]
    rw [← h_add]
    exact ENNReal.ofReal_le_ofReal (h_ptbound b)
  -- Squared `eLpNorm` becomes a lintegral.
  have h_sq_to_lint :
      (eLpNorm TinnerSqrt 2 μ) ^ 2 =
        ∫⁻ b, (‖TinnerSqrt b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top]
    have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by
      show ENNReal.toReal 2 = 2; rfl
    rw [h2_toReal]
    have h_inner_eq : ∫⁻ b, (‖TinnerSqrt b‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
        ∫⁻ b, (‖TinnerSqrt b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards with b
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
    rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num
  -- Bound the squared eLpNorm.
  have h_sq_bound : (eLpNorm TinnerSqrt 2 μ) ^ 2 ≤
      ENNReal.ofReal (C_sq * ‖S‖ ^ 2) := by
    rw [h_sq_to_lint]
    -- Abbreviations for the three ENNReal-valued summands.
    set f1 : M → ℝ≥0∞ := fun b => ENNReal.ofReal (A * (rawInd b) ^ 2) with hf1_def
    set f2 : M → ℝ≥0∞ :=
      fun b => ENNReal.ofReal (B * (ρ b) ^ 2 * Tcov b) with hf2_def
    set f3 : M → ℝ≥0∞ :=
      fun b => ENNReal.ofReal (B * C_bridge * (ρ b) ^ 2 * TchrSumJ b) with hf3_def
    have h_lint_mono :
        ∫⁻ b, (‖TinnerSqrt b‖ₑ : ℝ≥0∞) ^ 2 ∂μ ≤
          ∫⁻ b, f1 b + f2 b + f3 b ∂μ := by
      refine lintegral_mono_ae ?_
      filter_upwards with b using h_pt_enn b
    refine h_lint_mono.trans ?_
    -- AE-strong-measurability of `f1` via atom 3 (`indicator_tsupp_abs_raw`).
    have h_atom3 :
        AEStronglyMeasurable
          (fun b : M =>
            (tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
              (fun b' : M => |scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx)
                (extChartAt I α b')|) b)
          μ :=
      aestronglyMeasurable_indicator_tsupp_abs_raw
        (I := I) (M := M) g r s α S Idx Jdx
    have h_rawInd_sq_eq :
        ∀ b, (rawInd b) ^ 2 =
          ((tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
            (fun b' : M => |scalarOnE (I := I) α
              (tensorChartComponentRaw (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx)
              (extChartAt I α b')|) b) ^ 2 := by
      intro b
      by_cases hb : b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
      · have h1 : rawInd b = rawZ b := by
          show (tsupport _).indicator rawZ b = rawZ b
          exact Set.indicator_of_mem hb _
        have h2 :
            (tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
              (fun b' : M => |scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx)
                (extChartAt I α b')|) b = |rawZ b| :=
          Set.indicator_of_mem hb _
        rw [h1, h2, sq_abs]
      · have h1 : rawInd b = 0 := by
          show (tsupport _).indicator rawZ b = 0
          exact Set.indicator_of_notMem hb _
        have h2 :
            (tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
              (fun b' : M => |scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx)
                (extChartAt I α b')|) b = 0 :=
          Set.indicator_of_notMem hb _
        rw [h1, h2]
    have h_f1_ae_str : AEStronglyMeasurable f1 μ := by
      have h_sq : AEStronglyMeasurable (fun b : M => (rawInd b) ^ 2) μ := by
        have : (fun b : M => (rawInd b) ^ 2) =
            (fun b : M =>
              ((tsupport (fun x : M =>
                  ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
                (fun b' : M => |scalarOnE (I := I) α
                  (tensorChartComponentRaw (I := I) (M := M)
                    g r s S.toCcTensor α Idx Jdx)
                  (extChartAt I α b')|) b) ^ 2) := by
          funext b; exact h_rawInd_sq_eq b
        rw [this]
        exact (continuous_pow 2).comp_aestronglyMeasurable h_atom3
      have h_A_sq : AEStronglyMeasurable (fun b : M => A * (rawInd b) ^ 2) μ :=
        h_sq.const_mul A
      exact (ENNReal.continuous_ofReal.comp_aestronglyMeasurable h_A_sq :
        AEStronglyMeasurable (fun b : M => ENNReal.ofReal (A * (rawInd b) ^ 2)) μ)
    have h_f1_aemeas : AEMeasurable f1 μ := h_f1_ae_str.aemeasurable
    -- AE-strong-measurability of `f2` via atom 1 (`pou_mul_sqrt_sum_triv_chart_cov`).
    have h_atom1 :
        AEStronglyMeasurable
          (fun b : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
              Real.sqrt
                (∑ k : Fin (Module.finrank ℝ E),
                  ‖(trivializationAt (TensorRSModel r s ℝ E)
                      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                        ℝ b
                    (chartTensorRSCovariantDerivative (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (chartBasisVecFiber (I := I) α k) b)‖ ^ 2))
          μ :=
      aestronglyMeasurable_pou_mul_sqrt_sum_triv_chart_cov
        (I := I) (M := M) g r s α S
    have h_Tcov_nn_pt : ∀ b, 0 ≤ Tcov b := fun b => by
      rw [hTcov_def]; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have h_rho_Tcov_sq_eq : ∀ b,
        (ρ b) ^ 2 * Tcov b =
          (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            Real.sqrt
              (∑ k : Fin (Module.finrank ℝ E),
                ‖(trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                      ℝ b
                  (chartTensorRSCovariantDerivative (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α k) b)‖ ^ 2)) ^ 2 := by
      intro b
      have h_sum_eq :
          (∑ k : Fin (Module.finrank ℝ E),
              ‖(trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toCcTensor.toSection b')
                  (chartBasisVecFiber (I := I) α k) b)‖ ^ 2) = Tcov b := by
        rw [hTcov_def]
      have h_Tcov_pt_nn : (0 : ℝ) ≤ Tcov b := h_Tcov_nn_pt b
      have h_eq_inside :
          Real.sqrt
              (∑ k : Fin (Module.finrank ℝ E),
                ‖(trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                      ℝ b
                  (chartTensorRSCovariantDerivative (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α k) b)‖ ^ 2) =
            Real.sqrt (Tcov b) := by
        rw [h_sum_eq]
      rw [h_eq_inside, mul_pow,
        show Real.sqrt (Tcov b) ^ 2 = Tcov b from Real.sq_sqrt h_Tcov_pt_nn]
    have h_f2_ae_str : AEStronglyMeasurable f2 μ := by
      have h_sq : AEStronglyMeasurable (fun b : M => (ρ b) ^ 2 * Tcov b) μ := by
        have hfun_eq :
            (fun b : M => (ρ b) ^ 2 * Tcov b) =
              (fun b : M =>
                (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                  Real.sqrt
                    (∑ k : Fin (Module.finrank ℝ E),
                      ‖(trivializationAt (TensorRSModel r s ℝ E)
                          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                            ℝ b
                        (chartTensorRSCovariantDerivative (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (chartBasisVecFiber (I := I) α k) b)‖ ^ 2)) ^ 2) := by
          funext b; exact h_rho_Tcov_sq_eq b
        rw [hfun_eq]
        exact (continuous_pow 2).comp_aestronglyMeasurable h_atom1
      have h_B_sq : AEStronglyMeasurable
          (fun b : M => B * ((ρ b) ^ 2 * Tcov b)) μ := h_sq.const_mul B
      have hrearr : (fun b : M => B * ((ρ b) ^ 2 * Tcov b)) =
          (fun b : M => B * (ρ b) ^ 2 * Tcov b) := by
        funext b; ring
      rw [hrearr] at h_B_sq
      exact ENNReal.continuous_ofReal.comp_aestronglyMeasurable h_B_sq
    have h_f2_aemeas : AEMeasurable f2 μ := h_f2_ae_str.aemeasurable
    -- Split the lintegral via `lintegral_add_left'` (twice).
    have h_split12 :
        ∫⁻ b, f1 b + f2 b + f3 b ∂μ =
          ∫⁻ b, f1 b ∂μ + ∫⁻ b, f2 b + f3 b ∂μ := by
      have hg_eq :
          (fun b : M => f1 b + f2 b + f3 b) =
            (fun b : M => f1 b + (f2 b + f3 b)) := by
        funext b; rw [add_assoc]
      rw [show (∫⁻ b, f1 b + f2 b + f3 b ∂μ) =
          ∫⁻ b, f1 b + (f2 b + f3 b) ∂μ from by rw [hg_eq]]
      exact lintegral_add_left' h_f1_aemeas _
    have h_split23 :
        ∫⁻ b, f2 b + f3 b ∂μ = ∫⁻ b, f2 b ∂μ + ∫⁻ b, f3 b ∂μ :=
      lintegral_add_left' h_f2_aemeas _
    rw [h_split12, h_split23]
    -- Bound the first lintegral via G4.
    -- G4 gives: `eLpNorm (rawInd) 2 μ ≤ ofReal C₄ · ‖S‖₊`.
    have h_G4_S : eLpNorm rawInd 2 μ ≤ ENNReal.ofReal C₄ * (‖S‖₊ : ℝ≥0∞) := by
      have := h_G4 S Idx Jdx
      -- `rawInd b = (tsupport ρ).indicator rawZ b` is the same function as in G4.
      have h_fun_eq :
          (fun b : M =>
            (tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
              (fun b' : M =>
                scalarOnE (I := I) α
                  (tensorChartComponentRaw (I := I) (M := M)
                    g r s S.toCcTensor α Idx Jdx)
                  (extChartAt I α b')) b) = rawInd := by
        funext b; rfl
      rw [h_fun_eq] at this
      exact this
    have h_f1_int : ∫⁻ b, f1 b ∂μ ≤ ENNReal.ofReal (A * C₄ ^ 2 * ‖S‖ ^ 2) := by
      -- Compute: `f1 b = ofReal A · ofReal((rawInd b)²) = ofReal A · ‖rawInd b‖ₑ²`.
      have h_f1_eq :
          ∀ b, f1 b = ENNReal.ofReal A * (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2 := by
        intro b
        have h_enn_sq : (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2 =
            ENNReal.ofReal ((rawInd b) ^ 2) := by
          rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
            sq_abs]
        show ENNReal.ofReal (A * (rawInd b) ^ 2) =
          ENNReal.ofReal A * (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2
        rw [h_enn_sq, ENNReal.ofReal_mul hA_nn]
      have h_int_eq :
          ∫⁻ b, f1 b ∂μ =
            ENNReal.ofReal A * ∫⁻ b, (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
        rw [show (∫⁻ b, f1 b ∂μ) =
            ∫⁻ b, ENNReal.ofReal A * (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2 ∂μ from by
          refine lintegral_congr ?_; intro b; exact h_f1_eq b]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      -- G4 squared: `∫⁻ ‖rawInd b‖ₑ² ≤ ofReal(C₄² · ‖S‖²)`.
      have h_G4_sq : (eLpNorm rawInd 2 μ) ^ 2 ≤
          ENNReal.ofReal (C₄ ^ 2 * ‖S‖ ^ 2) := by
        have h_pow_mono := pow_le_pow_left' h_G4_S 2
        have h_pow_rhs :
            (ENNReal.ofReal C₄ * (‖S‖₊ : ℝ≥0∞)) ^ 2 =
              ENNReal.ofReal (C₄ ^ 2 * ‖S‖ ^ 2) := by
          rw [mul_pow, ← ENNReal.ofReal_pow hC₄_nn,
            show ((‖S‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖S‖ ^ 2) from by
              rw [show ((‖S‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖S‖ from
                  coe_nnnorm_eq_ofReal_norm S,
                ← ENNReal.ofReal_pow (norm_nonneg _)],
            ← ENNReal.ofReal_mul (by positivity)]
        rw [h_pow_rhs] at h_pow_mono
        exact h_pow_mono
      have h_G4_sq_lint :
          ∫⁻ b, (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2 ∂μ ≤
            ENNReal.ofReal (C₄ ^ 2 * ‖S‖ ^ 2) := by
        have h_eLp_sq_eq : (eLpNorm rawInd 2 μ) ^ 2 =
            ∫⁻ b, (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
          have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
          have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top]
          have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by
            show ENNReal.toReal 2 = 2; rfl
          rw [h2_toReal]
          have h_inner_eq : ∫⁻ b, (‖rawInd b‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
              ∫⁻ b, (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
            refine lintegral_congr_ae ?_
            filter_upwards with b
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
              ENNReal.rpow_natCast]
          rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
          norm_num
        rw [← h_eLp_sq_eq]; exact h_G4_sq
      calc ∫⁻ b, f1 b ∂μ
          = ENNReal.ofReal A * ∫⁻ b, (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := h_int_eq
        _ ≤ ENNReal.ofReal A * ENNReal.ofReal (C₄ ^ 2 * ‖S‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h_G4_sq_lint (zero_le _)
        _ = ENNReal.ofReal (A * (C₄ ^ 2 * ‖S‖ ^ 2)) :=
            (ENNReal.ofReal_mul hA_nn).symm
        _ = ENNReal.ofReal (A * C₄ ^ 2 * ‖S‖ ^ 2) := by
            congr 1; ring
    -- Bound the second lintegral via G2.
    have h_G2_S := h_G2 S
    have h_f2_int : ∫⁻ b, f2 b ∂μ ≤ ENNReal.ofReal (B * C₂ ^ 2 * ‖S‖ ^ 2) := by
      -- `f2 b = ofReal B · ‖atom1(b)‖ₑ²` after the substitution `(ρ √Tcov)² = ρ² · Tcov`.
      set h2 : M → ℝ := fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              ‖(trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toCcTensor.toSection b')
                  (chartBasisVecFiber (I := I) α k) b)‖ ^ 2)
        with hh2_def
      have h_f2_eq :
          ∀ b, f2 b = ENNReal.ofReal B * (‖h2 b‖ₑ : ℝ≥0∞) ^ 2 := by
        intro b
        have h_rho_Tcov : (ρ b) ^ 2 * Tcov b = (h2 b) ^ 2 := h_rho_Tcov_sq_eq b
        have h_enn_sq : (‖h2 b‖ₑ : ℝ≥0∞) ^ 2 =
            ENNReal.ofReal ((h2 b) ^ 2) := by
          rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
            sq_abs]
        show ENNReal.ofReal (B * (ρ b) ^ 2 * Tcov b) =
          ENNReal.ofReal B * (‖h2 b‖ₑ : ℝ≥0∞) ^ 2
        rw [h_enn_sq, show B * (ρ b) ^ 2 * Tcov b = B * ((ρ b) ^ 2 * Tcov b)
          from by ring, h_rho_Tcov, ENNReal.ofReal_mul hB_nn]
      have h_int_eq :
          ∫⁻ b, f2 b ∂μ =
            ENNReal.ofReal B * ∫⁻ b, (‖h2 b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
        rw [show (∫⁻ b, f2 b ∂μ) =
            ∫⁻ b, ENNReal.ofReal B * (‖h2 b‖ₑ : ℝ≥0∞) ^ 2 ∂μ from by
          refine lintegral_congr ?_; intro b; exact h_f2_eq b]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      have h_G2_sq : (eLpNorm h2 2 μ) ^ 2 ≤
          ENNReal.ofReal (C₂ ^ 2 * ‖S‖ ^ 2) := by
        have h_pow_mono := pow_le_pow_left' h_G2_S 2
        have h_pow_rhs :
            (ENNReal.ofReal C₂ * (‖S‖₊ : ℝ≥0∞)) ^ 2 =
              ENNReal.ofReal (C₂ ^ 2 * ‖S‖ ^ 2) := by
          rw [mul_pow, ← ENNReal.ofReal_pow hC₂_nn,
            show ((‖S‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖S‖ ^ 2) from by
              rw [show ((‖S‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖S‖ from
                  coe_nnnorm_eq_ofReal_norm S,
                ← ENNReal.ofReal_pow (norm_nonneg _)],
            ← ENNReal.ofReal_mul (by positivity)]
        rw [h_pow_rhs] at h_pow_mono
        exact h_pow_mono
      have h_G2_sq_lint :
          ∫⁻ b, (‖h2 b‖ₑ : ℝ≥0∞) ^ 2 ∂μ ≤
            ENNReal.ofReal (C₂ ^ 2 * ‖S‖ ^ 2) := by
        have h_eLp_sq_eq : (eLpNorm h2 2 μ) ^ 2 =
            ∫⁻ b, (‖h2 b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
          have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
          have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top]
          have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by
            show ENNReal.toReal 2 = 2; rfl
          rw [h2_toReal]
          have h_inner_eq : ∫⁻ b, (‖h2 b‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
              ∫⁻ b, (‖h2 b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
            refine lintegral_congr_ae ?_
            filter_upwards with b
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
              ENNReal.rpow_natCast]
          rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
          norm_num
        rw [← h_eLp_sq_eq]; exact h_G2_sq
      calc ∫⁻ b, f2 b ∂μ
          = ENNReal.ofReal B * ∫⁻ b, (‖h2 b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := h_int_eq
        _ ≤ ENNReal.ofReal B * ENNReal.ofReal (C₂ ^ 2 * ‖S‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h_G2_sq_lint (zero_le _)
        _ = ENNReal.ofReal (B * (C₂ ^ 2 * ‖S‖ ^ 2)) :=
            (ENNReal.ofReal_mul hB_nn).symm
        _ = ENNReal.ofReal (B * C₂ ^ 2 * ‖S‖ ^ 2) := by
            congr 1; ring
    -- Bound the third lintegral via the slot-correction uniform bound
    -- and the section-vs-tensor-inner bound (no measurability needed thanks
    -- to `lintegral_mono` and `ofReal_integral_eq_lintegral_ofReal`).
    have h_f3_int : ∫⁻ b, f3 b ∂μ ≤ ENNReal.ofReal (C₃ * ‖S‖ ^ 2) := by
      -- Pointwise: `B · C_bridge · ρ² · TchrSumJ b ≤ C₃_pre · tensorInnerPointwise b S S`
      -- where `C₃_pre := B · C_bridge · n · (r+s) · M_F² · K_S`.  Off `tsupport ρ`,
      -- `ρ = 0` so the LHS vanishes; on `tsupport ρ`, use the chain of bounds.
      set TIP : M → ℝ := fun b : M =>
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toCcTensor.toFun b) (S.toCcTensor.toFun b) with hTIP_def
      have hTIP_nn : ∀ b, 0 ≤ TIP b := fun b =>
        tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
      -- The pointwise dominating constant in real form.
      set C₃' : ℝ := B * C_bridge * (n : ℝ) * ((r : ℝ) + (s : ℝ)) * M_F ^ 2 * K_S
        with hC₃'_def
      have hC₃'_nn : 0 ≤ C₃' := by rw [hC₃'_def]; positivity
      have hC₃'_eq : C₃' = C₃ := by rw [hC₃'_def, hC₃_def]
      have h_pt_f3 : ∀ b,
          B * C_bridge * (ρ b) ^ 2 * TchrSumJ b ≤ C₃' * TIP b := by
        intro b
        by_cases hb : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
        · -- On `tsupport ρ`: bound `TchrSumJ b` via slot-correction operator-norm
          -- bound, then `‖S.toSection b‖²` via the section-vs-tensor-inner bound.
          have h_rho_le_one : ρ b ≤ 1 := by
            rw [hρ_def]; exact (chartAtlasPOU I M).le_one α b
          have h_rho_nn_b : 0 ≤ ρ b := hρ_nn b
          have h_rho_sq_le_one : (ρ b) ^ 2 ≤ 1 := by
            have : ρ b ^ 2 = ρ b * ρ b := sq (ρ b)
            rw [this]
            calc ρ b * ρ b ≤ 1 * 1 :=
                  mul_le_mul h_rho_le_one h_rho_le_one h_rho_nn_b zero_le_one
              _ = 1 := by ring
          -- Per-slot bound (using the unified `M_F` for both input and output).
          have h_in_le : ∀ j : Fin (Module.finrank ℝ E), ∀ k : Fin r,
              ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                  (fun b' => S.toCcTensor.toSection b')
                  (chartBasisVecFiber (I := I) α j) b k‖ ≤
                M_F * ‖S.toCcTensor.toSection b‖ := by
            intro j k
            have h_orig := hM_F_in_le (fun b' => S.toCcTensor.toSection b')
              (b := b) hb j k
            have h_factor : M_F_in * ‖S.toCcTensor.toSection b‖ ≤
                M_F * ‖S.toCcTensor.toSection b‖ :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
            exact h_orig.trans h_factor
          have h_out_le : ∀ j : Fin (Module.finrank ℝ E), ∀ l : Fin s,
              ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                  (fun b' => S.toCcTensor.toSection b')
                  (chartBasisVecFiber (I := I) α j) b l‖ ≤
                M_F * ‖S.toCcTensor.toSection b‖ := by
            intro j l
            have h_orig := hM_F_out_le (fun b' => S.toCcTensor.toSection b')
              (b := b) hb j l
            have h_factor : M_F_out * ‖S.toCcTensor.toSection b‖ ≤
                M_F * ‖S.toCcTensor.toSection b‖ :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
            exact h_orig.trans h_factor
          -- Per-j: `TchrPerJ j b ≤ (r + s) · M_F² · ‖S.toCcTensor.toSection b‖²`.
          have h_norm_sec_nn : 0 ≤ ‖S.toCcTensor.toSection b‖ := norm_nonneg _
          have h_MF_sec_nn : 0 ≤ M_F * ‖S.toCcTensor.toSection b‖ :=
            mul_nonneg hM_F_nn h_norm_sec_nn
          have h_perj : ∀ j : Fin (Module.finrank ℝ E),
              TchrPerJ j b ≤
                ((r : ℝ) + (s : ℝ)) * M_F ^ 2 * ‖S.toCcTensor.toSection b‖ ^ 2 := by
            intro j
            rw [hTchrPerJ_def]
            have h_in_sq : ∀ k : Fin r,
                ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α j) b k‖ ^ 2 ≤
                  (M_F * ‖S.toCcTensor.toSection b‖) ^ 2 := by
              intro k
              exact pow_le_pow_left₀ (norm_nonneg _) (h_in_le j k) 2
            have h_out_sq : ∀ l : Fin s,
                ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α j) b l‖ ^ 2 ≤
                  (M_F * ‖S.toCcTensor.toSection b‖) ^ 2 := by
              intro l
              exact pow_le_pow_left₀ (norm_nonneg _) (h_out_le j l) 2
            have h_sum_in_le :
                (∑ k : Fin r,
                  ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (chartBasisVecFiber (I := I) α j) b k‖ ^ 2) ≤
                  (r : ℝ) * (M_F * ‖S.toCcTensor.toSection b‖) ^ 2 := by
              calc (∑ k : Fin r,
                  ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (chartBasisVecFiber (I := I) α j) b k‖ ^ 2)
                  ≤ ∑ _k : Fin r, (M_F * ‖S.toCcTensor.toSection b‖) ^ 2 :=
                    Finset.sum_le_sum (fun k _ => h_in_sq k)
                _ = (r : ℝ) * (M_F * ‖S.toCcTensor.toSection b‖) ^ 2 := by
                    rw [Finset.sum_const, Finset.card_univ,
                      Fintype.card_fin]
                    ring
            have h_sum_out_le :
                (∑ l : Fin s,
                  ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (chartBasisVecFiber (I := I) α j) b l‖ ^ 2) ≤
                  (s : ℝ) * (M_F * ‖S.toCcTensor.toSection b‖) ^ 2 := by
              calc (∑ l : Fin s,
                  ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (chartBasisVecFiber (I := I) α j) b l‖ ^ 2)
                  ≤ ∑ _l : Fin s, (M_F * ‖S.toCcTensor.toSection b‖) ^ 2 :=
                    Finset.sum_le_sum (fun l _ => h_out_sq l)
                _ = (s : ℝ) * (M_F * ‖S.toCcTensor.toSection b‖) ^ 2 := by
                    rw [Finset.sum_const, Finset.card_univ,
                      Fintype.card_fin]
                    ring
            have h_combined :
                (∑ k : Fin r,
                  ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (chartBasisVecFiber (I := I) α j) b k‖ ^ 2) +
                  (∑ l : Fin s,
                  ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (chartBasisVecFiber (I := I) α j) b l‖ ^ 2) ≤
                ((r : ℝ) + (s : ℝ)) *
                  (M_F * ‖S.toCcTensor.toSection b‖) ^ 2 := by
              have := add_le_add h_sum_in_le h_sum_out_le
              linarith
            have h_mul_eq :
                ((r : ℝ) + (s : ℝ)) *
                  (M_F * ‖S.toCcTensor.toSection b‖) ^ 2 =
                ((r : ℝ) + (s : ℝ)) * M_F ^ 2 *
                  ‖S.toCcTensor.toSection b‖ ^ 2 := by
              rw [mul_pow]; ring
            rw [← h_mul_eq]
            exact h_combined
          -- Sum over `j` (there are `n = Module.finrank ℝ E` of them).
          have h_sumJ_le :
              TchrSumJ b ≤
                (n : ℝ) * ((r : ℝ) + (s : ℝ)) * M_F ^ 2 *
                  ‖S.toCcTensor.toSection b‖ ^ 2 := by
            rw [hTchrSumJ_def]
            calc (∑ j : Fin (Module.finrank ℝ E), TchrPerJ j b)
                ≤ ∑ _j : Fin (Module.finrank ℝ E),
                    (((r : ℝ) + (s : ℝ)) * M_F ^ 2 *
                      ‖S.toCcTensor.toSection b‖ ^ 2) :=
                  Finset.sum_le_sum (fun j _ => h_perj j)
              _ = (n : ℝ) * ((r : ℝ) + (s : ℝ)) * M_F ^ 2 *
                    ‖S.toCcTensor.toSection b‖ ^ 2 := by
                  rw [Finset.sum_const, Finset.card_univ,
                    Fintype.card_fin]
                  rw [hn_def]
                  push_cast
                  ring
          -- Apply `‖S.toSection b‖² ≤ K_S · tensorInnerPointwise b S S`.
          have h_secSq_le : ‖S.toCcTensor.toSection b‖ ^ 2 ≤ K_S * TIP b := by
            rw [hTIP_def]
            exact hK_S_bound S.toCcTensor hb
          have h_pre1 : (n : ℝ) * ((r : ℝ) + (s : ℝ)) * M_F ^ 2 ≥ 0 := by
            positivity
          have h_sumJ_le' :
              TchrSumJ b ≤ (n : ℝ) * ((r : ℝ) + (s : ℝ)) * M_F ^ 2 *
                (K_S * TIP b) := by
            calc TchrSumJ b
                ≤ (n : ℝ) * ((r : ℝ) + (s : ℝ)) * M_F ^ 2 *
                    ‖S.toCcTensor.toSection b‖ ^ 2 := h_sumJ_le
              _ ≤ (n : ℝ) * ((r : ℝ) + (s : ℝ)) * M_F ^ 2 *
                    (K_S * TIP b) :=
                  mul_le_mul_of_nonneg_left h_secSq_le h_pre1
          have h_BCB_nn : 0 ≤ B * C_bridge := mul_nonneg hB_nn hC_bridge_nn
          have h_BCB_rho_sq_nn : 0 ≤ B * C_bridge * (ρ b) ^ 2 :=
            mul_nonneg h_BCB_nn (sq_nonneg _)
          have h_BCB_rho_sq_le : B * C_bridge * (ρ b) ^ 2 ≤ B * C_bridge := by
            have : B * C_bridge * (ρ b) ^ 2 ≤ B * C_bridge * 1 :=
              mul_le_mul_of_nonneg_left h_rho_sq_le_one h_BCB_nn
            linarith
          have h_TchrSumJ_nn_b : 0 ≤ TchrSumJ b := by
            rw [hTchrSumJ_def]
            refine Finset.sum_nonneg (fun j _ => ?_)
            rw [hTchrPerJ_def]
            exact add_nonneg
              (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
              (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
          calc B * C_bridge * (ρ b) ^ 2 * TchrSumJ b
              ≤ B * C_bridge * TchrSumJ b :=
                mul_le_mul_of_nonneg_right h_BCB_rho_sq_le h_TchrSumJ_nn_b
            _ ≤ B * C_bridge * ((n : ℝ) * ((r : ℝ) + (s : ℝ)) * M_F ^ 2 *
                  (K_S * TIP b)) :=
                mul_le_mul_of_nonneg_left h_sumJ_le' h_BCB_nn
            _ = C₃' * TIP b := by rw [hC₃'_def]; ring
        · -- Off tsupport: `ρ b = 0`, LHS vanishes; RHS ≥ 0.
          have h_ρ_zero : ρ b = 0 := by
            by_contra hne
            exact hb (subset_tsupport _ hne)
          have hRHS_nn : 0 ≤ C₃' * TIP b := mul_nonneg hC₃'_nn (hTIP_nn b)
          rw [h_ρ_zero]; simpa using hRHS_nn
      -- Conclude the lintegral bound via `lintegral_mono` and the Bochner integral.
      have h_pt_enn3 : ∀ b, f3 b ≤ ENNReal.ofReal (C₃' * TIP b) := by
        intro b
        rw [hf3_def]
        exact ENNReal.ofReal_le_ofReal (h_pt_f3 b)
      have h_mono : ∫⁻ b, f3 b ∂μ ≤
          ∫⁻ b, ENNReal.ofReal (C₃' * TIP b) ∂μ :=
        lintegral_mono h_pt_enn3
      -- The dominating function is integrable; rewrite the lintegral as `ofReal ∫`.
      have h_TIP_int : Integrable TIP μ := by
        rw [hμ_def, hTIP_def]
        exact SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
          S.toCcTensor S.toCcTensor
      have h_CTIP_int : Integrable (fun b => C₃' * TIP b) μ :=
        h_TIP_int.const_mul C₃'
      have h_CTIP_ae_nn : 0 ≤ᵐ[μ] (fun b => C₃' * TIP b) :=
        Filter.Eventually.of_forall (fun b => mul_nonneg hC₃'_nn (hTIP_nn b))
      have h_lint_to_int :
          ∫⁻ b, ENNReal.ofReal (C₃' * TIP b) ∂μ =
            ENNReal.ofReal (∫ b, C₃' * TIP b ∂μ) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_CTIP_int h_CTIP_ae_nn).symm
      -- The integral of `tensorInnerPointwise b S S` is bounded by `‖S‖²`.
      have h_int_TIP_le : ∫ b, TIP b ∂μ ≤ ‖S‖ ^ 2 := by
        -- `∫ TIP = tensorL2Inner g r s S S = ‖S.toCcTensor‖² ≤ ‖S‖²`.
        have h_l2_eq : ∫ b, TIP b ∂μ = ‖S.toCcTensor‖ ^ 2 := by
          rw [hTIP_def, hμ_def]
          have h_eq : ∫ b,
              tensorInnerPointwise (I := I) (M := M) g r s b
                (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
            tensorL2Inner (I := I) (M := M) g r s
              S.toCcTensor.toFun S.toCcTensor.toFun := rfl
          rw [h_eq, ← SmoothCcTensor.norm_sq_eq_inner_self
            (I := I) (M := M) S.toCcTensor]
        rw [h_l2_eq]
        exact SmoothCcTensorH1.l2NormSq_le_h1NormSq S
      have h_int_CTIP_le : ∫ b, C₃' * TIP b ∂μ ≤ C₃' * ‖S‖ ^ 2 := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left h_int_TIP_le hC₃'_nn
      calc ∫⁻ b, f3 b ∂μ
          ≤ ∫⁻ b, ENNReal.ofReal (C₃' * TIP b) ∂μ := h_mono
        _ = ENNReal.ofReal (∫ b, C₃' * TIP b ∂μ) := h_lint_to_int
        _ ≤ ENNReal.ofReal (C₃' * ‖S‖ ^ 2) :=
            ENNReal.ofReal_le_ofReal h_int_CTIP_le
        _ = ENNReal.ofReal (C₃ * ‖S‖ ^ 2) := by rw [hC₃'_eq]
    -- Combine the three lintegrals.
    have h_sum_le :
        ∫⁻ b, f1 b ∂μ + (∫⁻ b, f2 b ∂μ + ∫⁻ b, f3 b ∂μ) ≤
          ENNReal.ofReal (A * C₄ ^ 2 * ‖S‖ ^ 2) +
            (ENNReal.ofReal (B * C₂ ^ 2 * ‖S‖ ^ 2) +
              ENNReal.ofReal (C₃ * ‖S‖ ^ 2)) := by
      refine add_le_add h_f1_int ?_
      exact add_le_add h_f2_int h_f3_int
    refine h_sum_le.trans ?_
    -- Sum the three `ofReal` constants.
    have hA_sq_nn : 0 ≤ A * C₄ ^ 2 * ‖S‖ ^ 2 :=
      mul_nonneg (mul_nonneg hA_nn (sq_nonneg _)) (sq_nonneg _)
    have hB_sq_nn : 0 ≤ B * C₂ ^ 2 * ‖S‖ ^ 2 :=
      mul_nonneg (mul_nonneg hB_nn (sq_nonneg _)) (sq_nonneg _)
    have hC3_sq_nn : 0 ≤ C₃ * ‖S‖ ^ 2 :=
      mul_nonneg hC₃_nn (sq_nonneg _)
    have h_sum_pos : 0 ≤ B * C₂ ^ 2 * ‖S‖ ^ 2 + C₃ * ‖S‖ ^ 2 :=
      add_nonneg hB_sq_nn hC3_sq_nn
    rw [← ENNReal.ofReal_add hB_sq_nn hC3_sq_nn,
      ← ENNReal.ofReal_add hA_sq_nn h_sum_pos]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hC_sq_def]
    ring_nf
    -- Both sides simplify to `(A · C₄² + B · C₂² + C₃) · ‖S‖²`.
    linarith
  -- ===== Step 6: take square roots =====
  have h_sq_nn : 0 ≤ C_sq * ‖S‖ ^ 2 := mul_nonneg hC_sq_nn (sq_nonneg _)
  have h_eLpNorm_le : eLpNorm TinnerSqrt 2 μ ≤
      ENNReal.ofReal (Real.sqrt (C_sq * ‖S‖ ^ 2)) := by
    have h_pow : eLpNorm TinnerSqrt 2 μ =
        ((eLpNorm TinnerSqrt 2 μ) ^ 2) ^ ((1 : ℝ) / 2) := by
      rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
      norm_num
    rw [h_pow]
    refine (ENNReal.rpow_le_rpow h_sq_bound (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans ?_
    -- Show `(ENNReal.ofReal X) ^ (1/2) ≤ ENNReal.ofReal (√X)` for `X ≥ 0`.
    -- Direct: by `Real.mul_self_sqrt`, `X = √X · √X`, so `ENNReal.ofReal X =
    -- (ENNReal.ofReal √X)²`. Then take `1/2`-power.
    have h_X_decomp : ENNReal.ofReal (C_sq * ‖S‖ ^ 2) =
        ENNReal.ofReal (Real.sqrt (C_sq * ‖S‖ ^ 2)) ^ 2 := by
      have h_sq_eq : Real.sqrt (C_sq * ‖S‖ ^ 2) *
          Real.sqrt (C_sq * ‖S‖ ^ 2) = C_sq * ‖S‖ ^ 2 := Real.mul_self_sqrt h_sq_nn
      rw [show ENNReal.ofReal (Real.sqrt (C_sq * ‖S‖ ^ 2)) ^ 2 =
          ENNReal.ofReal (Real.sqrt (C_sq * ‖S‖ ^ 2)) *
            ENNReal.ofReal (Real.sqrt (C_sq * ‖S‖ ^ 2)) from sq _,
        ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), h_sq_eq]
    rw [h_X_decomp]
    rw [← ENNReal.rpow_natCast (ENNReal.ofReal (Real.sqrt (C_sq * ‖S‖ ^ 2))) 2,
      ← ENNReal.rpow_mul]
    -- After cast `(↑2 : ℝ) = 2`, target reduces to `^ 1 = ^ 1`.
    rw [show ((2 : ℕ) : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
  refine h_eLpNorm_le.trans ?_
  -- Final: rewrite `√(C_sq · ‖S‖²) = √C_sq · ‖S‖ = C · ‖S‖`.
  have hS_nn : 0 ≤ ‖S‖ := norm_nonneg _
  have h_sqrt_fact : Real.sqrt (C_sq * ‖S‖ ^ 2) = C * ‖S‖ := by
    rw [hC_def, Real.sqrt_mul hC_sq_nn,
      show ‖S‖ ^ 2 = ‖S‖ * ‖S‖ from by ring, Real.sqrt_mul_self hS_nn]
  rw [h_sqrt_fact, ENNReal.ofReal_mul hC_nn,
    show ENNReal.ofReal ‖S‖ = (‖S‖₊ : ℝ≥0∞) from
      (coe_nnnorm_eq_ofReal_norm S).symm]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

/-! ## Axiom audit -/

section Sanity
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sqrt_add_le_sqrt_add_sqrt
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sqrt_add3_le_sum
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coe_nnnorm_eq_ofReal_norm
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sum_norm_sq_le_card_mul_sum_norm_sq
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.norm_sq_neg_sum_add_sum_le_two_mul
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.norm_sq_triv_neg_sum_add_sum_le_const_mul_sum_norm_sq_on_pouTsupport
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.norm_sq_triv_neg_sum_add_sum_le_const_mul_sum_norm_sq_on_pouTsupport_h1
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sqrt_sum_le_sum_sqrt_fin
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_sqrt_g_inner_gradFun_tensorChartComponentScalar_le_const_mul_h1Norm
end Sanity
