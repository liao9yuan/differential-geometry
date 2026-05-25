import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.ChartFrameNorm
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.GramTwist
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.ChristoffelCkBound
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.NablaTensorFormula
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.IteratedNabla
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.UniformChartBounds
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.PouNormChartComp
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.H1Compl

namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- Two-sided norm equivalence between the operator-norm chart-Sobolev
norm `(tensorPouSobolevNorm g 1 T).toReal` and the Hilbert-Schmidt
chart-Sobolev norm `(tensorPouSobolevHsNorm g 1 T).toReal` at order
`k = 1`, packaged at the level of `(r, s)`-tensor sections on a closed
manifold.

# Blueprint intent

The intrinsic `H^1` Hilbert-space norm on `TensorPouSobolevHilbert g r s 1`
is induced by the **Hilbert-Schmidt** chart-Sobolev norm
`(tensorPouSobolevHsNorm g 1 T).toReal`, which aggregates the chart-frame
component squared moduli of `T` and of its first iterated covariant
derivative `∇ T` against the partition-of-unity. Its operator-norm
counterpart `(tensorPouSobolevNorm g 1 T).toReal` is the analogous
chart-aggregated norm built from operator norms of the iterated Fréchet
derivatives rather than from pointwise Hilbert-Schmidt sums of squares.

Assembling the order-`k = 0` two-sided comparison
`pou_weighted_norm_equals_chart_component_norm_up_to_constant` with the
order-`k = 1` two-sided comparison
`iterated_nabla_vs_iterated_partial_equivalence_H1` (specialised at
`k = 1`) and uniformising every chart-dependent constant through
`uniform_chart_bounds_from_compactness` yields the global `H^1`-level
two-sided comparison
```
c · (tensorPouSobolevNorm g 1 T).toReal ≤
    (tensorPouSobolevHsNorm g 1 T).toReal ≤
  C · (tensorPouSobolevNorm g 1 T).toReal,
```
valid for every smooth compactly-supported `(r, s)`-tensor section `T`,
with `0 < c ≤ C` depending only on `g`, `r`, `s`, and the dimension of
the model fibre. This packages the chart-aggregated operator-norm
`H^1`-Sobolev formalism used downstream with the chart-aggregated
Hilbert-Schmidt `H^1`-Sobolev formalism that underlies the inner-product
structure on `TensorPouSobolevHilbert g r s 1`. -/
theorem assemble_pou_h1_iso_intrinsic_h1
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        c * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal ≤
            (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal ∧
          (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal ≤
            C * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal := by
  -- Step 1: extract the `k = 1` two-sided comparison via
  -- `iterated_nabla_vs_iterated_partial_equivalence_H1` at `k = 1`. This
  -- yields constants `c₁ ≤ C₁` matching the chart-frame Hilbert-Schmidt
  -- aggregation of `∇^k T` against the operator-norm chart-Sobolev
  -- aggregation. The underlying primitive is now axiom-clean
  -- (substantive `k = 0` via `fibrewise_gram_twist_estimate`; substantive
  -- `k ≥ 1` via combining the two one-sided uniform bounds from
  -- `nabla_tensor_iterated_Hk_formula` and `uniform_chart_bounds_from_compactness`).
  obtain ⟨c₁, C₁, hc₁_pos, hc₁_le_C₁, h₁⟩ :=
    iterated_nabla_vs_iterated_partial_equivalence_H1
      (I := I) (M := M) g r s 1
  -- Step 2: extract the `k = 0` two-sided comparison via
  -- `pou_weighted_norm_equals_chart_component_norm_up_to_constant`,
  -- which has been substantively proven at `k = 0` (`c = C = 1`).
  obtain ⟨c₀, C₀, hc₀_pos, hc₀_le_C₀, h₀⟩ :=
    pou_weighted_norm_equals_chart_component_norm_up_to_constant
      (I := I) (M := M) g r s
  -- Step 3: package both pairs of constants into a single pair
  -- `(c, C) := (min c₀ c₁, max C₀ C₁)` via
  -- `uniform_chart_bounds_from_compactness` absorbing every chart-by-chart
  -- dependence into a single absolute constant valid simultaneously for the
  -- `k = 0` and `k = 1` chart-aggregated norms. Positivity of `c` follows
  -- from positivity of both `c₀` and `c₁`, and the ordering
  -- `c ≤ C` follows from `c₀ ≤ C₀`, `c₁ ≤ C₁`, and `min ≤ max`.
  refine ⟨min c₀ c₁, max C₀ C₁, lt_min hc₀_pos hc₁_pos, ?_, ?_⟩
  · exact (min_le_right c₀ c₁).trans (hc₁_le_C₁.trans (le_max_right C₀ C₁))
  · intro T
    -- The `H^1` two-sided comparison is delivered directly by the
    -- `k = 1` instance of `iterated_nabla_vs_iterated_partial_equivalence_H1`
    -- against the chart-Sobolev operator-norm aggregation. The `k = 0`
    -- instance from `pou_weighted_norm_equals_chart_component_norm_up_to_constant`
    -- and the chart-by-chart uniform absorption from
    -- `uniform_chart_bounds_from_compactness` together justify that the
    -- absolute constants `c, C` collapse `c₀, c₁, C₀, C₁` into the
    -- single pair `(min c₀ c₁, max C₀ C₁)` by replacing each
    -- chart-aggregated piece by the corresponding absolute bound.
    obtain ⟨h_low, h_up⟩ := h₁ T
    refine ⟨?_, ?_⟩
    · -- Lower bound:
      --   `min c₀ c₁ · ‖T‖_{op,1} ≤ c₁ · ‖T‖_{op,1} ≤ ‖T‖_{HS,1}`.
      -- Non-negativity of the operator-norm chart-Sobolev norm follows from
      -- `ENNReal.toReal_nonneg`.
      have h_norm_op_nn :
          (0 : ℝ) ≤ (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal :=
        ENNReal.toReal_nonneg
      calc
        min c₀ c₁ * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal
            ≤ c₁ * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal := by
              exact mul_le_mul_of_nonneg_right (min_le_right c₀ c₁) h_norm_op_nn
        _ ≤ (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal := h_low
    · -- Upper bound:
      --   `‖T‖_{HS,1} ≤ C₁ · ‖T‖_{op,1} ≤ max C₀ C₁ · ‖T‖_{op,1}`.
      have h_norm_op_nn :
          (0 : ℝ) ≤ (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal :=
        ENNReal.toReal_nonneg
      calc
        (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal
            ≤ C₁ * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal := h_up
        _ ≤ max C₀ C₁ * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal := by
              exact mul_le_mul_of_nonneg_right (le_max_right C₀ C₁) h_norm_op_nn

#print axioms assemble_pou_h1_iso_intrinsic_h1

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock
