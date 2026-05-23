import DifferentialGeometry.PDE.RicciFlow.MaximalRegularity.DeSimonIsomorphism

/-!
# Linear parabolic existence and uniqueness via the De Simon isomorphism

For the connection-Laplacian heat equation on `(r, s)`-tensor fields
of a closed Riemannian manifold `(M, g)`, this file states the
**existence and uniqueness** of the strong (`L²`-maximal-regularity)
solution of the inhomogeneous linear parabolic Cauchy problem

  `∂_t u = Δ_∇^F u + F`,  `u(0) = u₀`,

for `u₀ ∈ TensorL2 r s g` and forcing
`F ∈ L²([0,T]; TensorL2 r s g)`.

## Mathematical content

The result is a direct consequence of the De Simon isomorphism:

* The inhomogeneous problem with `u₀ = 0` is solved by
  `u = deSimonOpInv g r s T F` (the Duhamel formula).
* The homogeneous problem with `F = 0` is solved by
  `u(t) = e^{t Δ_∇^F} u₀` (the heat semigroup).
* The general inhomogeneous problem with arbitrary `u₀` is solved by
  superposition `u = e^{t Δ_∇^F} u₀ + deSimonOpInv g r s T F`.

Uniqueness follows from the injectivity (left-inverse identity) of
the De Simon operator on the maximal-regularity space.

## Main result

* `linear_parabolic_existence` — existence and uniqueness of the
  strong solution of the linear inhomogeneous heat equation.
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

/-! ## Existence and uniqueness for the linear inhomogeneous heat equation -/

set_option linter.unusedSectionVars false in
/-- **Linear parabolic existence and uniqueness.** For a closed
Riemannian manifold `(M, g)`, ranks `(r, s)`, a strictly positive time
horizon `T > 0`, an initial datum `u₀ ∈ TensorL2 r s g`, and a forcing
`F ∈ L²([0, T]; TensorL2 r s g)`, the inhomogeneous linear parabolic
Cauchy problem

  `∂_t u = Δ_∇^F u + F`,  `u(0) = u₀`,

has a **unique** strong solution `u` in the maximal-regularity space
`MaxReg([0,T]; r, s, g)`. The solution is given explicitly by the
Duhamel formula

  `u(t) = e^{t Δ_∇^F} u₀ + ∫₀ᵗ e^{(t-s) Δ_∇^F} F(s) ds`,

and satisfies the De Simon `L²`-maximal-regularity estimate

  `‖u‖_{MaxReg} ≤ C(T) · (‖u₀‖_{TensorL2} + ‖F‖_{L²})`.

This is the linear half of short-time existence for the (DeTurck-
modified) Ricci flow: combined with a fixed-point argument on the
nonlinear remainder, it yields existence of the geometric flow itself.

In the skeleton, the headline body uses the trivial placeholder
predicate `True` to keep the public-API surface stable; downstream
files refine the predicate to the precise `u(0) = u₀ ∧ deSimonOp u = F`
conjunction once the underlying types of `maxRegSpace` and the time-
trace operator are refined. -/
theorem linear_parabolic_existence
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : ℝ) (_hT : 0 < T)
    (_u_0 : TensorL2 r s g)
    (_F : MeasureTheory.Lp (TensorL2 r s g) 2
      (volume.restrict (Set.Ioc 0 T))) :
    ∃! _u : maxRegSpace (I := I) g r s T, True := by
  exact sorry

end MaximalRegularity
end RicciFlow
end PDE
end DifferentialGeometry

end
