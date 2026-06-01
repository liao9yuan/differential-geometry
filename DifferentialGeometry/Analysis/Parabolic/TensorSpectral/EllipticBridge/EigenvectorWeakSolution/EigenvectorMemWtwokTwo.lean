import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorSmoothToL2
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorArbitraryKRegularity
import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartLocality

/-!
# The connection-Laplacian eigenvector lies in the tensor Sobolev space `W^{2k, 2}`

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)` and an eigenbasis
index `i`, the chart-locality-free smooth representative
`eigenvectorSmooth g r s i : SmoothCcTensor g r s` of the
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

For `T = eigenvectorSmooth g r s i` the relevant chart component is
identified as follows:

* `tensorChartComp` is, by definition, `tensorChartComponent`;
* on a smooth section the weighted Euclidean chart component
  `tensorChartComponent g r s T α P₀.1 P₀.2` agrees, almost everywhere on the
  chart target, with the canonical Euclidean chart component
  `tensorL2ChartComponent g r s (T : TensorL2 r s g) α P₀` of its `L²` class
  (`tensorL2ChartComponent_smoothToTensorL2_coeFn`);
* `eigenvectorSmooth_toL2` identifies that `L²` class with the
  intrinsic resolvent eigenvector `tensorResolventEigenbasisVec`, whose
  canonical Euclidean chart component is exactly
  `eigenvectorChartComponentFun`;
* `eigenvector_chartComponent_memWkp_arbitrary` supplies the
  order-`(2 * k)` interior Sobolev regularity of
  `eigenvectorChartComponentFun`.

`MemWkp_congr_ae` transports the order-`(2 * k)` membership across the
almost-everywhere identity, closing the headline.

## Main result

* `tensorEigenvector_memWtwokTwo` — for every `k`, the smooth
  representative `eigenvectorSmooth g r s i` lies in the tensor
  Sobolev space `W^{2k, 2}`, unconditionally.

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
  (i : TensorEigenIdx (I := I) (M := M) g r s)

/-! ## The chart-locality-free tensor Sobolev membership

The chart-component a.e.-identity transports the arbitrary-order interior
regularity of the eigenvector chart component to the chart components of the
smooth representative; aggregating over the canonical finite chart cover via
`MemWtwokTwo_of_forall_finset_memWkp` yields the tensor Sobolev membership.

The development is keyed onto the intrinsic compact-operator eigenbasis
`tensorResolventEigenbasisVec`, with no uniform-Sobolev hypothesis. It
consumes the chart-locality-free smooth representative
`eigenvectorSmooth` (whose `L²` class is
`tensorResolventEigenbasisVec … i` via
`eigenvectorSmooth_toL2`) and the chart-locality-free
arbitrary-order interior regularity
`eigenvector_chartComponent_memWkp_arbitrary` of the intrinsic
eigenvector chart component `eigenvectorChartComponentFun`. -/

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- The chart component of the chart-locality-free smooth representative agrees
a.e. with the intrinsic eigenvector chart component. -/
theorem eigenvectorSmooth_tensorChartComp_aeEq_chartComponentFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s
        (eigenvectorSmooth (I := I) (M := M) g r s i) α Idx Jdx
      =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      eigenvectorChartComponentFun (I := I) (M := M) g r s i α
        (Idx, Jdx) := by
  -- `tensorChartComp` is definitionally `tensorChartComponent`. On the smooth
  -- section `eigenvectorSmooth`, the weighted Euclidean chart
  -- component agrees a.e. (on `chartL2Measure α = volume.restrict
  -- (chartTargetEuclid α)`) with the canonical chart component of its `L²` class.
  have h_smooth_ae :
      ((tensorL2ChartComponent (I := I) (M := M) g r s
          ((eigenvectorSmooth (I := I) (M := M) g r s i :
            TensorL2 r s g)) α (Idx, Jdx) :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
      tensorChartComponent (I := I) (M := M) g r s
        (eigenvectorSmooth (I := I) (M := M) g r s i) α
        (Idx, Jdx).1 (Idx, Jdx).2 :=
    tensorL2ChartComponent_smoothToTensorL2_coeFn (I := I) (M := M) g r s
      (eigenvectorSmooth (I := I) (M := M) g r s i) α (Idx, Jdx)
  -- Identify the `L²` class of the smooth representative with the intrinsic
  -- resolvent eigenvector.
  have h_toL2 :
      (eigenvectorSmooth (I := I) (M := M) g r s i :
          TensorL2 r s g) =
        tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i :=
    eigenvectorSmooth_toL2 (I := I) (M := M) g r s i
  -- The intrinsic eigenvector chart component is, by definition, the canonical
  -- chart component of the intrinsic resolvent eigenvector.
  have h_fun_def :
      eigenvectorChartComponentFun (I := I) (M := M) g r s i α
          (Idx, Jdx) =
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) α
            (Idx, Jdx) :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) := rfl
  -- `chartL2Measure α` is definitionally `volume.restrict (chartTargetEuclid α)`.
  -- Rewrite the a.e.-identity and orient it from `tensorChartComp` to the
  -- eigenvector chart component.
  have h_oriented :
      tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmooth (I := I) (M := M) g r s i) α
          (Idx, Jdx).1 (Idx, Jdx).2
        =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
      eigenvectorChartComponentFun (I := I) (M := M) g r s i α
        (Idx, Jdx) := by
    rw [h_fun_def, ← h_toL2]
    exact h_smooth_ae.symm
  exact h_oriented

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The connection-Laplacian eigenvector lies in `W^{2k, 2}`** (chart-locality
free). For every iteration count `k`, the chart-locality-free smooth
representative `eigenvectorSmooth g r s i` lies in the tensor
Sobolev space `W^{2k, 2}`, unconditionally. -/
theorem tensorEigenvector_memWtwokTwo
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (k : ℕ) :
    MemWtwokTwo (I := I) (M := M) g k
      (eigenvectorSmooth (I := I) (M := M) g r s i) := by
  -- Reduce to chart-local `MemWkp (2 * k) 2` over the canonical finite cover.
  refine MemWtwokTwo_of_forall_finset_memWkp (I := I) (M := M) g k
    (eigenvectorSmooth (I := I) (M := M) g r s i)
    (fun α _hα Idx Jdx => ?_)
  -- The arbitrary-order interior regularity of the intrinsic eigenvector chart
  -- component at order `2 * k`.
  have h_fun_memWkp :
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α
          (Idx, Jdx))
        (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M)
      g r s i (2 * k) α (Idx, Jdx)
  -- The chart component of the smooth representative agrees a.e. with the
  -- intrinsic eigenvector chart component on the chart target.
  have h_ae :
      tensorChartComp (I := I) (M := M) g r s
          (eigenvectorSmooth (I := I) (M := M) g r s i) α Idx Jdx
        =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
      eigenvectorChartComponentFun (I := I) (M := M) g r s i α
        (Idx, Jdx) :=
    eigenvectorSmooth_tensorChartComp_aeEq_chartComponentFun
      (I := I) (M := M) g r s i α Idx Jdx
  -- Transport the order-`(2 * k)` membership across the a.e.-identity.
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α) h_ae).mpr h_fun_memWkp

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
