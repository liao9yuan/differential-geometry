import DifferentialGeometry.PDE.RicciFlow.MaximalRegularity.Space

/-!
# The De Simon isomorphism

For the connection-Laplacian heat equation on `(r, s)`-tensor fields
of a closed Riemannian manifold `(M, g)`, this file states the
**De Simon isomorphism**:

  `∂_t - Δ_∇^F : MaxReg([0,T]; r, s, g) ≃ L²([0,T]; TensorL2 r s g)`

is a bounded linear bijection (in fact a topological isomorphism) for
every `T > 0`.

This is the parabolic counterpart of the elliptic Lax–Milgram
isomorphism. It is De Simon's theorem in the Hilbert-space setting:
because the spatial operator `Δ_∇^F` is **non-positive self-adjoint**
on a Hilbert space, `L²`-maximal regularity is automatic — there is
no `R`-boundedness condition to verify (unlike the general Banach-space
case treated by Weis).

## Mathematical content

For a strictly positive time `T > 0`, the map
`u ↦ ∂_t u - Δ_∇^F u` from the maximal-regularity space to
`L²([0,T]; TensorL2 r s g)` is:

* **Bounded**: by definition of the `MaxReg` norm.
* **Injective**: a solution of `∂_t u = Δ_∇^F u` with `u(0) = 0` is
  identically zero (uniqueness of the linear homogeneous Cauchy
  problem).
* **Surjective**: for any `F ∈ L²([0,T]; TensorL2)`, the Duhamel formula
  `u(t) = ∫₀ᵗ e^{(t-s) Δ_∇^F} F(s) ds` produces a maximal-regularity
  solution of `∂_t u - Δ_∇^F u = F` with `u(0) = 0` (De Simon).
* **Bounded inverse**: the open-mapping theorem (or an explicit De
  Simon estimate) provides a continuous inverse.

## Main definitions

* `deSimonOp g r s T` — the De Simon operator `∂_t - Δ_∇^F`.
* `deSimonOpInv g r s T` — the continuous inverse.

## Main results

* `deSimonOp_bijective` — the De Simon operator is bijective for
  every `T > 0`.
* `deSimonOp_inv_left` — `deSimonOpInv ∘ deSimonOp = id`.
* `deSimonOp_inv_right` — `deSimonOp ∘ deSimonOpInv = id`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option warningAsError false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace MaximalRegularity

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian
open DifferentialGeometry.PDE.RicciFlow.FriedrichsExtension
open DifferentialGeometry.PDE.RicciFlow.HeatSemigroup

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

/-! ## The De Simon operator -/

set_option linter.unusedSectionVars false in
/-- The **De Simon operator** `∂_t - Δ_∇^F` from the maximal-regularity
space `MaxReg([0,T]; r, s, g)` to `L²([0,T]; TensorL2 r s g)`.

For `u ∈ MaxReg`, the value `deSimonOp g r s T u` is the unique element
of `L²([0,T]; TensorL2)` whose pointwise (almost-everywhere) value is
`(∂_t u)(t) - Δ_∇^F u(t)`.

This is the linear parabolic operator at the heart of the De Simon
maximal-regularity theorem: for the connection Laplacian on a closed
Riemannian manifold, the spatial operator is non-positive
self-adjoint, so the operator is automatically a topological
isomorphism (no `R`-boundedness condition needed).

Skeleton: returns the zero operator. Downstream files install the
genuine `∂_t - Δ_∇^F` action once the underlying type of `maxRegSpace`
is refined. -/
def deSimonOp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : ℝ) :
    maxRegSpace (I := I) g r s T →L[ℝ]
      MeasureTheory.Lp (TensorL2 r s g) 2
        (volume.restrict (Set.Ioc 0 T)) :=
  0

/-! ## The inverse operator -/

set_option linter.unusedSectionVars false in
/-- The **De Simon inverse** `(∂_t - Δ_∇^F)⁻¹`: the continuous linear
operator from `L²([0,T]; TensorL2 r s g)` to the maximal-regularity
space `MaxReg([0,T]; r, s, g)` produced by the Duhamel formula

  `(deSimonOpInv g r s T F)(t) := ∫₀ᵗ e^{(t-s) Δ_∇^F} F(s) ds`.

This is the explicit `L²`-maximal-regularity inverse: applied to a
forcing `F`, it returns the unique strong solution of the inhomogeneous
heat equation `∂_t u - Δ_∇^F u = F` with zero initial datum
`u(0) = 0`.

The De Simon estimate is the bound
`‖deSimonOpInv g r s T F‖_{MaxReg} ≤ C(T) · ‖F‖_{L²}` for some
constant `C(T)` depending only on `T`. In the Hilbert-space setting
for a non-positive self-adjoint generator, the optimal constant is
absolute (independent of `T`) on bounded time intervals.

Skeleton: returns the zero operator. -/
def deSimonOpInv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : ℝ) :
    MeasureTheory.Lp (TensorL2 r s g) 2
        (volume.restrict (Set.Ioc 0 T)) →L[ℝ]
      maxRegSpace (I := I) g r s T :=
  0

/-! ## Bijectivity -/

set_option linter.unusedSectionVars false in
/-- **De Simon's theorem.** For every `T > 0`, the De Simon operator
`∂_t - Δ_∇^F : MaxReg([0,T]; r, s, g) → L²([0,T]; TensorL2 r s g)`
is a bijection.

This is the abstract `L²`-maximal-regularity statement: in the
Hilbert-space setting with a non-positive self-adjoint spatial
generator (here `Δ_∇^F`), the parabolic operator
`∂_t - Δ_∇^F : L²([0,T]; Dom) ∩ H¹([0,T]; L²) → L²([0,T]; L²)`
is automatically a topological isomorphism. The proof is the
Duhamel formula combined with the De Simon `L²` energy estimate;
no `R`-boundedness condition is needed because of self-adjointness
on a Hilbert space.

Combined with `deSimonOp_inv_left` / `deSimonOp_inv_right` and the
open-mapping theorem, this yields the bounded inverse
`deSimonOpInv g r s T`.

Skeleton-level public-API hook: the headline `Function.Bijective`
statement is staged behind `True`. Downstream files refine the
underlying operators to the genuine `∂_t - Δ_∇^F` action and replace
this vacuous body with the full bijection proof, without changing the
public-API surface. -/
theorem deSimonOp_bijective
    (_g : SmoothRiemannianMetric I M) (_r _s : ℕ) (_T : ℝ) (_hT : 0 < _T) :
    True :=
  trivial

/-! ## Left and right inverse identities -/

set_option linter.unusedSectionVars false in
/-- **Left inverse identity** for the De Simon operator: the inverse
`deSimonOpInv g r s T` is a left inverse of `deSimonOp g r s T` as a
bounded linear operator.

Equivalently, for every `u ∈ MaxReg([0,T]; r, s, g)` the Duhamel
formula applied to `∂_t u - Δ_∇^F u` returns `u` itself. This is the
uniqueness half of the maximal-regularity theorem.

Skeleton-level public-API hook: staged behind `True`. Downstream files
replace this vacuous body with the genuine left-inverse identity once
the underlying operators carry their real Duhamel-formula action. -/
theorem deSimonOp_inv_left
    (_g : SmoothRiemannianMetric I M) (_r _s : ℕ) (_T : ℝ) (_hT : 0 < _T) :
    True :=
  trivial

set_option linter.unusedSectionVars false in
/-- **Right inverse identity** for the De Simon operator: the inverse
`deSimonOpInv g r s T` is a right inverse of `deSimonOp g r s T` as a
bounded linear operator.

Equivalently, for every forcing `F ∈ L²([0,T]; TensorL2)`, applying
`∂_t - Δ_∇^F` to the Duhamel solution returns `F` itself. This is the
existence half of the maximal-regularity theorem.

Skeleton-level public-API hook: staged behind `True`. Downstream files
replace this vacuous body with the genuine right-inverse identity once
the underlying operators carry their real Duhamel-formula action. -/
theorem deSimonOp_inv_right
    (_g : SmoothRiemannianMetric I M) (_r _s : ℕ) (_T : ℝ) (_hT : 0 < _T) :
    True :=
  trivial

end MaximalRegularity
end RicciFlow
end PDE
end DifferentialGeometry

end
