import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorSmoothToL2
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorArbitraryKRegularity
import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartLocality

/-!
# The connection-Laplacian eigenvector lies in the tensor Sobolev space `W^{2k, 2}`

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev
hypothesis `h_uniform` and an eigenbasis index `i`, the smooth representative
`eigenvectorSmooth g r s h_uniform i : SmoothCcTensor g r s` of the
connection-Laplacian resolvent eigenvector has been shown — chart component by
chart component — to have interior `W^{k, 2}` regularity of arbitrary order on
every chart target (`eigenvector_chartComponent_memWkp_arbitrary`).

This file converts that chart-component regularity into the **tensor Sobolev
membership** headline: the smooth representative lies in the tensor Sobolev
space `W^{2k, 2}` of `Analysis/Sobolev/Tensor/Defs.lean` for *every* `k`.

## The mechanism

The tensor Sobolev membership `MemWtwokTwo g k T` is, by
`MemWtwokTwo_of_forall_finset_memWkp`, the assertion that for every chart base
point `α` of the canonical finite cover and every pair of component
multi-indices `(Idx, Jdx)`, the scalar chart component
`tensorChartComp g r s T α Idx Jdx` lies in the Euclidean iterated Sobolev space
`MemWkp (2 * k) 2` of its chart target.

For `T = eigenvectorSmooth g r s h_uniform i` the relevant chart component is
identified as follows:

* `tensorChartComp` is, by definition, `tensorChartComponent`;
* on a smooth section the weighted Euclidean chart component
  `tensorChartComponent g r s T α P₀.1 P₀.2` agrees, almost everywhere on the
  chart target, with the canonical Euclidean chart component
  `tensorL2ChartComponent g r s (T : TensorL2 r s g) α P₀` of its `L²` class
  (`tensorL2ChartComponent_smoothToTensorL2_coeFn`);
* `eigenvectorSmooth_toL2` identifies that `L²` class with the abstract resolvent
  eigenvector `tensorResolventEigenbasisVec h_uniform i`, whose canonical
  Euclidean chart component is exactly `eigenvectorChartComponentFun`;
* `eigenvector_chartComponent_memWkp_arbitrary` supplies the order-`(2 * k)`
  interior Sobolev regularity of `eigenvectorChartComponentFun`.

`MemWkp_congr_ae` transports the order-`(2 * k)` membership across the
almost-everywhere identity, closing the headline.

## Main result

* `tensorEigenvector_memWtwokTwo` — for every `k`, the smooth representative
  `eigenvectorSmooth g r s h_uniform i` lies in the tensor Sobolev space
  `W^{2k, 2}`, unconditionally.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_uniform : uniformTensorChartSobolevBound g r s)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

/-! ## The chart component of the smooth representative is the eigenvector chart
component

The weighted Euclidean chart component `tensorChartComp g r s
(eigenvectorSmooth …) α Idx Jdx` is, almost everywhere on the chart target, the
eigenvector chart component `eigenvectorChartComponentFun g r s h_uniform i α
(Idx, Jdx)`: `tensorChartComp` is definitionally `tensorChartComponent`, which on
a smooth section agrees a.e. with the canonical chart component of its `L²`
class; that `L²` class is, by `eigenvectorSmooth_toL2`, the abstract resolvent
eigenvector, whose canonical chart component is `eigenvectorChartComponentFun`. -/

/-- **The chart component of the smooth representative agrees a.e. with the
eigenvector chart component.** For a chart base point `α` and component
multi-indices `(Idx, Jdx)`, the weighted Euclidean chart component
`tensorChartComp g r s (eigenvectorSmooth g r s h_uniform i) α Idx Jdx` agrees,
almost everywhere on the Euclidean chart target with respect to the Lebesgue
volume, with the eigenvector chart component
`eigenvectorChartComponentFun g r s h_uniform i α (Idx, Jdx)`. -/
theorem eigenvectorSmooth_tensorChartComp_aeEq_chartComponentFun
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s
        (eigenvectorSmooth (I := I) (M := M) g r s h_uniform i) α Idx Jdx
      =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      eigenvectorChartComponentFun (I := I) (M := M) g r s h_uniform i α
        (Idx, Jdx) := by
  -- `tensorChartComp` is definitionally `tensorChartComponent`. On the smooth
  -- section `eigenvectorSmooth`, the weighted Euclidean chart component agrees
  -- a.e. (on `chartL2Measure α = volume.restrict (chartTargetEuclid α)`) with
  -- the canonical chart component of its `L²` class.
  have h_smooth_ae :
      ((tensorL2ChartComponent (I := I) (M := M) g r s
          ((eigenvectorSmooth (I := I) (M := M) g r s h_uniform i :
            TensorL2 r s g)) α (Idx, Jdx) :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
      tensorChartComponent (I := I) (M := M) g r s
        (eigenvectorSmooth (I := I) (M := M) g r s h_uniform i) α
        (Idx, Jdx).1 (Idx, Jdx).2 :=
    tensorL2ChartComponent_smoothToTensorL2_coeFn (I := I) (M := M) g r s
      (eigenvectorSmooth (I := I) (M := M) g r s h_uniform i) α (Idx, Jdx)
  -- Identify the `L²` class of the smooth representative with the abstract
  -- resolvent eigenvector.
  have h_toL2 :
      (eigenvectorSmooth (I := I) (M := M) g r s h_uniform i : TensorL2 r s g) =
        tensorResolventEigenbasisVec (I := I) (M := M) h_uniform i :=
    eigenvectorSmooth_toL2 (I := I) (M := M) g r s h_uniform i
  -- The eigenvector chart component is, by definition, the canonical chart
  -- component of the abstract resolvent eigenvector.
  have h_fun_def :
      eigenvectorChartComponentFun (I := I) (M := M) g r s h_uniform i α
          (Idx, Jdx) =
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_uniform i) α
            (Idx, Jdx) :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) := rfl
  -- `chartL2Measure α` is definitionally `volume.restrict (chartTargetEuclid α)`.
  -- Rewrite the a.e.-identity and orient it from `tensorChartComp` to the
  -- eigenvector chart component.
  have h_oriented :
      tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmooth (I := I) (M := M) g r s h_uniform i) α
          (Idx, Jdx).1 (Idx, Jdx).2
        =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
      eigenvectorChartComponentFun (I := I) (M := M) g r s h_uniform i α
        (Idx, Jdx) := by
    rw [h_fun_def, ← h_toL2]
    exact h_smooth_ae.symm
  exact h_oriented

/-! ## The tensor Sobolev membership headline

The chart-component a.e.-identity transports the arbitrary-order interior
regularity of the eigenvector chart component to the chart components of the
smooth representative; aggregating over the canonical finite chart cover via
`MemWtwokTwo_of_forall_finset_memWkp` yields the tensor Sobolev membership. -/

/-- **The connection-Laplacian eigenvector lies in `W^{2k, 2}`.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev
hypothesis `h_uniform`, an eigenbasis index `i`, and *every* iteration count
`k : ℕ`, the smooth representative `eigenvectorSmooth g r s h_uniform i` of the
connection-Laplacian resolvent eigenvector lies in the tensor Sobolev space
`W^{2k, 2}`: `MemWtwokTwo g k (eigenvectorSmooth g r s h_uniform i)`.

The membership reduces, by `MemWtwokTwo_of_forall_finset_memWkp`, to the
order-`(2 * k)` Euclidean Sobolev regularity of each scalar chart component
`tensorChartComp g r s (eigenvectorSmooth …) α Idx Jdx` over its chart target.
That chart component agrees almost everywhere with the eigenvector chart
component `eigenvectorChartComponentFun` (the canonical chart component of the
abstract resolvent eigenvector, via `eigenvectorSmooth_toL2`), whose
order-`(2 * k)` interior regularity is the arbitrary-order headline
`eigenvector_chartComponent_memWkp_arbitrary`; `MemWkp_congr_ae` transports the
membership across the almost-everywhere identity. -/
theorem tensorEigenvector_memWtwokTwo (k : ℕ) :
    MemWtwokTwo (I := I) (M := M) g k
      (eigenvectorSmooth (I := I) (M := M) g r s h_uniform i) := by
  -- Reduce to chart-local `MemWkp (2 * k) 2` over the canonical finite cover.
  refine MemWtwokTwo_of_forall_finset_memWkp (I := I) (M := M) g k
    (eigenvectorSmooth (I := I) (M := M) g r s h_uniform i)
    (fun α _hα Idx Jdx => ?_)
  -- The arbitrary-order interior regularity of the eigenvector chart component
  -- at order `2 * k`.
  have h_fun_memWkp :
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_uniform i α
          (Idx, Jdx))
        (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M) g r s
      h_uniform i (2 * k) α (Idx, Jdx)
  -- The chart component of the smooth representative agrees a.e. with the
  -- eigenvector chart component on the chart target.
  have h_ae :
      tensorChartComp (I := I) (M := M) g r s
          (eigenvectorSmooth (I := I) (M := M) g r s h_uniform i) α Idx Jdx
        =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
      eigenvectorChartComponentFun (I := I) (M := M) g r s h_uniform i α
        (Idx, Jdx) :=
    eigenvectorSmooth_tensorChartComp_aeEq_chartComponentFun
      (I := I) (M := M) g r s h_uniform i α Idx Jdx
  -- Transport the order-`(2 * k)` membership across the a.e.-identity.
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α) h_ae).mpr h_fun_memWkp

/-! ## Sanity tests -/

section ElaborationTests

example (k : ℕ) :
    MemWtwokTwo (I := I) (M := M) g k
      (eigenvectorSmooth (I := I) (M := M) g r s h_uniform i) :=
  tensorEigenvector_memWtwokTwo (I := I) (M := M) g r s h_uniform i k

example :
    MemWtwokTwo (I := I) (M := M) g 0
      (eigenvectorSmooth (I := I) (M := M) g r s h_uniform i) :=
  tensorEigenvector_memWtwokTwo (I := I) (M := M) g r s h_uniform i 0

example :
    eigenvectorSmooth (I := I) (M := M) g r s h_uniform i ∈
      wtwokTwoSubmodule (I := I) (M := M) g r s 3 :=
  tensorEigenvector_memWtwokTwo (I := I) (M := M) g r s h_uniform i 3

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
