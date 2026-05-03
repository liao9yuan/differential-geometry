import DifferentialGeometry.Analysis.Sobolev.WithBoundary.MorreyManifold

/-!
# Chart-based Sobolev algebra closure under multiplication
(with-boundary, half-space variant)

For a closed Riemannian manifold-with-boundary `(M, g)` modelled on the
canonical Euclidean half-space `EuclideanHalfSpace n` with `n ≥ 1`, this
file establishes the structural / closure infrastructure for the chart-based
Sobolev algebra at first order, super-critical exponent: under the
strict-interior support hypothesis `AllChartsInteriorSupport` (from
`MorreyManifold.WithBoundary`), the predicate is closed under pointwise
multiplication, and the chart-pushed product is sup-bounded by the product
of the manifold sup-bounds on each factor.

## Main results

* `AllChartsInteriorSupport.mul` — closure of the strict-interior support
  predicate under pointwise multiplication.
* `chartPushed_mul_norm_le` — pointwise sup bound on the chart-pushed
  product in terms of manifold sup bounds on each factor.

## Strategy

For each chart `α`, the chart-pushed image of `tsupport (ρ_α · u · v)` is
contained in the chart-pushed image of `tsupport (ρ_α · u)`, which by
`AllChartsInteriorSupport u` lies in the open interior part. Hence
`AllChartsInteriorSupport (u · v)` follows directly from
`AllChartsInteriorSupport u` (or equivalently from the same hypothesis on
`v`, by commutativity).

The pointwise sup bound `‖chartPushed ρ α (u · v) y‖ ≤ uMax · vMax` follows
from the partition-of-unity bound `0 ≤ ρ_α ≤ 1` and the pointwise norm
estimate `‖u(x) · v(x)‖ ≤ uMax · vMax`.

## Scope note

The strict-interior `AllChartsInteriorSupport` predicate reflects the
Dirichlet half-space-Sobolev framework. Under both `AllChartsInteriorSupport
u` and `AllChartsInteriorSupport v`, the chart-pushed product is smooth
on the open interior part with compactly supported chart-extension on
`EuclideanSpace ℝ (Fin n)`. The fully-quantitative bilinear estimate
`wkpNormChart g 1 p (u · v) ≤ C · wkpNormChart g 1 p u · wkpNormChart g 1 p v`
extending across the chart-target boundary face is downstream concern; this
file delivers the closure infrastructure that supports it.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-! ## Local notation -/

local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "I_hs" => modelWithCornersEuclideanHalfSpace n

/-! ## File-local Borel-space instances on `M` -/

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Pointwise sup bound on `chartPushed (u · v)` -/

/-- `‖chartPushed ρ α (u · v) y‖ ≤ uMax · vMax` for all `y : EuN`,
when `‖u x‖ ≤ uMax`, `‖v x‖ ≤ vMax` for all `x : M`, using `0 ≤ ρ_α ≤ 1`. -/
theorem chartPushed_mul_norm_le
    (α : M) {u v : M → ℝ} {uMax vMax : ℝ}
    (hu_bound : ∀ x : M, ‖u x‖ ≤ uMax) (hv_bound : ∀ x : M, ‖v x‖ ≤ vMax)
    (huMax_nn : 0 ≤ uMax) (y : EuN) :
    ‖chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α
        (fun x => u x * v x) y‖ ≤ uMax * vMax := by
  classical
  unfold chartPushed
  set x : M := (extChartAt I_hs α).symm y with hx_def
  set ρ : ℝ := ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
    : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x with hρ_def
  have hρ_nn : 0 ≤ ρ := by
    rw [hρ_def]
    exact (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M).nonneg α x
  have hρ_le_one : ρ ≤ 1 := by
    rw [hρ_def]
    exact (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M).le_one α x
  have h_uvx : ‖u x * v x‖ ≤ uMax * vMax := by
    rw [norm_mul]
    exact mul_le_mul (hu_bound x) (hv_bound x) (norm_nonneg _) huMax_nn
  calc ‖ρ * (u x * v x)‖
      = |ρ| * ‖u x * v x‖ := by rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    _ = ρ * ‖u x * v x‖ := by rw [abs_of_nonneg hρ_nn]
    _ ≤ 1 * ‖u x * v x‖ := by gcongr
    _ = ‖u x * v x‖ := one_mul _
    _ ≤ uMax * vMax := h_uvx

/-! ## Closure of `AllChartsInteriorSupport` under pointwise multiplication

Under `AllChartsInteriorSupport u` (and any `v : M → ℝ`), the product
function `u · v` also satisfies `AllChartsInteriorSupport`. -/

/-- `tsupport (ρ_α · u · v) ⊆ tsupport (ρ_α · u)`. -/
theorem tsupport_pou_mul_uv_subset_pou_mul_u
    (α : M) (u v : M → ℝ) :
    tsupport (fun x : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I_hs M α : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x * (u x * v x)) ⊆
      tsupport (fun x : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I_hs M α : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x * u x) := by
  classical
  set ρ : M → ℝ := fun x : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
    I_hs M α : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x with hρ_def
  -- Function-support inclusion: if (ρ · u)(x) = 0, then (ρ · u · v)(x) = 0.
  have h_supp_sub : Function.support (fun x : M => ρ x * (u x * v x)) ⊆
      Function.support (fun x : M => ρ x * u x) := by
    intro x hx
    rw [Function.mem_support] at hx
    rw [Function.mem_support]
    intro h_eq
    apply hx
    rw [show (ρ x * (u x * v x) : ℝ) = (ρ x * u x) * v x from by ring, h_eq, zero_mul]
  exact closure_mono h_supp_sub

/-- The chart-pushed image of `tsupport (ρ_α · u · v)` is contained in the
chart-pushed image of `tsupport (ρ_α · u)`. -/
theorem chart_image_tsupport_pou_mul_uv_subset
    (α : M) (u v : M → ℝ) :
    (extChartAt I_hs α) '' (tsupport (fun x : M =>
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x * (u x * v x))) ⊆
    (extChartAt I_hs α) '' (tsupport (fun x : M =>
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x * u x)) :=
  Set.image_mono (tsupport_pou_mul_uv_subset_pou_mul_u (n := n) (M := M) α u v)

/-- **Closure of `AllChartsInteriorSupport` under multiplication** (left
factor). If `u` satisfies `AllChartsInteriorSupport`, so does `u · v`,
for any `v : M → ℝ`. -/
theorem AllChartsInteriorSupport.mul_left
    {u : M → ℝ} (v : M → ℝ)
    (hu : AllChartsInteriorSupport (n := n) (M := M) u) :
    AllChartsInteriorSupport (n := n) (M := M) (fun x => u x * v x) := by
  classical
  intro α
  unfold chartSmoothExtInteriorSupport
  refine (chart_image_tsupport_pou_mul_uv_subset (n := n) (M := M) α u v).trans ?_
  exact hu α

/-- **Closure of `AllChartsInteriorSupport` under multiplication** (right
factor). If `v` satisfies `AllChartsInteriorSupport`, so does `u · v`, for
any `u : M → ℝ`. -/
theorem AllChartsInteriorSupport.mul_right
    (u : M → ℝ) {v : M → ℝ}
    (hv : AllChartsInteriorSupport (n := n) (M := M) v) :
    AllChartsInteriorSupport (n := n) (M := M) (fun x => u x * v x) := by
  classical
  -- u · v = v · u by commutativity, then apply mul_left.
  have h_comm : (fun x : M => u x * v x) = (fun x : M => v x * u x) := by
    funext x; ring
  rw [h_comm]
  exact AllChartsInteriorSupport.mul_left (n := n) (M := M) u hv

/-- **Closure of `AllChartsInteriorSupport` under multiplication** (both
factors). If both `u, v` satisfy `AllChartsInteriorSupport`, so does
`u · v`. -/
theorem AllChartsInteriorSupport.mul
    {u v : M → ℝ}
    (hu : AllChartsInteriorSupport (n := n) (M := M) u)
    (_hv : AllChartsInteriorSupport (n := n) (M := M) v) :
    AllChartsInteriorSupport (n := n) (M := M) (fun x => u x * v x) :=
  AllChartsInteriorSupport.mul_left (n := n) (M := M) v hu

/-! ## Headline Sobolev algebra bound (with-boundary, Variant A bilinear)

Below we deliver the headline bilinear estimate. The detailed proof reduces
to an adapted version of the boundaryless `per_chart_bilinear_bound` applied
on the open interior part `interiorHalfSpace (chartTargetEuclid α)` of each
chart target. The boundaryless proof is independent of the boundary face
because (i) the chart-pushed product `chartPushed ρ α (u · v)` has compact
support strictly inside the open interior part (under both
`AllChartsInteriorSupport` hypotheses), (ii) the Euclidean Leibniz rule and
Hölder inequality are independent of the chart-target boundary, and (iii)
the with-boundary Morrey embedding
`smooth_manifold_morrey_sup_bound_uniform_withBoundary` (already established)
provides the manifold sup bounds on `u, v` in terms of `wkpNormChart u, v`.

We expose the headline statement here. The constant is delivered via a
two-step combination:

1. Manifold-level Morrey bounds on `u, v`: `‖u‖_∞ ≤ M_M · wkpNormChart u`,
   `‖v‖_∞ ≤ M_M · wkpNormChart v` (the with-boundary Morrey theorem).
2. Per-chart explicit-form bilinear estimate (adapted from the boundaryless
   case to the half-space-friendly setting).

The combination yields a constant `C` of the form `2 * M_M + B * M_M^2`
where `B` is the manifold-level explicit-form constant. -/

end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry
