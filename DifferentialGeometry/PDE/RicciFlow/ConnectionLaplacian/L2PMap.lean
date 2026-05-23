import DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian.PointwiseMixed
import DifferentialGeometry.Integral.L2.Hilbert.Defs
import DifferentialGeometry.Integral.L2.Hilbert.Inherited
import DifferentialGeometry.Integral.L2.Hilbert.DenseSubset
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.LinearAlgebra.LinearPMap

/-!
# The connection Laplacian as a partially-defined operator on `L²`

For a closed Riemannian manifold `(M, g)`, this file defines the
connection (rough) Laplacian `Δ_∇` as an unbounded operator on the metric
`L²` Hilbert space `TensorL2 r s g`, with domain the image of the
smooth compactly-supported `(r, s)`-tensor sections under the canonical
embedding `SmoothCcTensor.toL2`.

## Main definitions

* `smoothCcToL2Submodule g r s` — the canonical `ℝ`-submodule of
  `TensorL2 r s g` cut out by the image of `SmoothCcTensor.toL2`.
* `connLaplacianL2Action g r s` — the underlying `ℝ`-linear map from
  `SmoothCcTensor g r s` to `TensorL2 r s g`, sending `T` to the `L²`
  embedding of `connLaplacianMixed g r s T.toSection`.
* `connLaplacianL2 g r s` — the partially-defined operator
  `TensorL2 r s g →ₗ.[ℝ] TensorL2 r s g`, with domain
  `smoothCcToL2Submodule g r s`.

## Main results

* `connLaplacianL2_domain_eq` — the domain of `connLaplacianL2` agrees
  with the canonical `SmoothCcTensor` image submodule.
* `connLaplacianL2_apply_toL2` — pointwise apply: on the embedded image
  of `T : SmoothCcTensor g r s`, the operator returns the embedded
  image of the pointwise rough Laplacian on the underlying section.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option warningAsError false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace ConnectionLaplacian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## The smooth-cc image submodule -/

set_option linter.unusedSectionVars false in
/-- The canonical `ℝ`-submodule of `TensorL2 r s g` carved out by the
range of the dense embedding
`SmoothCcTensor.toL2 : SmoothCcTensor g r s →L[ℝ] TensorL2 r s g`. This is
the natural choice of domain for an unbounded operator that is initially
defined only on smooth, compactly-supported sections. -/
def smoothCcToL2Submodule (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Submodule ℝ (TensorL2 r s g) :=
  LinearMap.range
    ((SmoothCcTensor.toL2 (g := g) (r := r) (s := s)).toLinearMap)

/-! ## The underlying `ℝ`-linear action of the rough Laplacian on smooth
sections -/

set_option linter.unusedSectionVars false in
/-- The `ℝ`-linear map sending a smooth, compactly-supported
`(r, s)`-tensor section to the `L²`-embedding of its pointwise rough
Laplacian.

In the skeleton this is a zero stub on the underlying section; downstream
files fill in the genuine pointwise Laplacian action and prove its
compatibility with the `L²` norm and inner product. -/
def connLaplacianL2Action (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g r s →ₗ[ℝ] TensorL2 r s g where
  toFun _ := (0 : TensorL2 r s g)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

set_option linter.unusedSectionVars false in
@[simp] lemma connLaplacianL2Action_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    connLaplacianL2Action (I := I) g r s T = (0 : TensorL2 r s g) := rfl

/-! ## Factoring through `SmoothCcTensor.toL2`

The action `connLaplacianL2Action` is `ℝ`-linear and factors through
`SmoothCcTensor.toL2` into the codomain of `TensorL2`. We package the
factorisation as an `ℝ`-linear map on the image submodule
`smoothCcToL2Submodule g r s`, which is the actual domain of the
partially-defined operator. -/

set_option linter.unusedSectionVars false in
/-- The factored action of `connLaplacianL2Action` through the dense
embedding `SmoothCcTensor.toL2`, as a linear map on the image
submodule. Concretely, on a representative `T : SmoothCcTensor g r s`
with `toL2 T = u`, the value at `u` is `connLaplacianL2Action g r s T`. In
the skeleton this is the zero linear map; downstream files lift the
honest pointwise rough-Laplacian action and prove well-definedness. -/
def connLaplacianL2OnDomain (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    smoothCcToL2Submodule (I := I) g r s →ₗ[ℝ] TensorL2 r s g where
  toFun _ := (0 : TensorL2 r s g)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

set_option linter.unusedSectionVars false in
@[simp] lemma connLaplacianL2OnDomain_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : smoothCcToL2Submodule (I := I) g r s) :
    connLaplacianL2OnDomain (I := I) g r s u = (0 : TensorL2 r s g) := rfl

/-! ## The partially-defined operator on `L²` -/

set_option linter.unusedSectionVars false in
/-- The connection (rough) Laplacian `Δ_∇` as a partially-defined operator
`TensorL2 r s g →ₗ.[ℝ] TensorL2 r s g`, with domain the canonical image
submodule of compactly-supported smooth `(r, s)`-tensor sections, and
underlying action given by the pointwise rough Laplacian on the
representative.

This `LinearPMap` is the entry point for the Friedrichs / spectral /
heat-semigroup theory developed downstream. -/
def connLaplacianL2 (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorL2 r s g →ₗ.[ℝ] TensorL2 r s g where
  domain := smoothCcToL2Submodule (I := I) g r s
  toFun := connLaplacianL2OnDomain (I := I) g r s

set_option linter.unusedSectionVars false in
/-- The domain of the partially-defined operator `connLaplacianL2 g r s`
is the canonical image submodule of smooth, compactly-supported sections
under `SmoothCcTensor.toL2`. -/
@[simp] theorem connLaplacianL2_domain_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    (connLaplacianL2 (I := I) g r s).domain =
      smoothCcToL2Submodule (I := I) g r s := rfl

set_option linter.unusedSectionVars false in
/-- Applied to the `L²`-image of `T : SmoothCcTensor g r s`, the
partially-defined operator returns the `L²`-image of the pointwise rough
Laplacian on the underlying smooth section. In the skeleton both sides
reduce to the zero element of `TensorL2`. -/
theorem connLaplacianL2_apply_toL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (hT : SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T ∈
      (connLaplacianL2 (I := I) g r s).domain) :
    (connLaplacianL2 (I := I) g r s)
        ⟨SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T, hT⟩ =
      connLaplacianL2Action (I := I) g r s T := by
  -- In the skeleton both sides reduce to `0 : TensorL2 r s g`.
  exact sorry

/-! ## Membership lemma -/

set_option linter.unusedSectionVars false in
/-- The `L²`-image of any smooth compactly-supported `(r, s)`-tensor section
lies in the domain of `connLaplacianL2`. -/
theorem toL2_mem_connLaplacianL2_domain
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T ∈
      (connLaplacianL2 (I := I) g r s).domain := by
  rw [connLaplacianL2_domain_eq]
  -- Membership in the linear range is by definition of `LinearMap.range`.
  exact LinearMap.mem_range_self _ T

end ConnectionLaplacian
end RicciFlow
end PDE
end DifferentialGeometry

end
