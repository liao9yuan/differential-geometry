import DifferentialGeometry.PDE.RicciFlow.FriedrichsExtension.SelfAdjoint
import DifferentialGeometry.PDE.RicciFlow.FriedrichsExtension.Construction
import DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian.L2PMap
import DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian.NegSemiBounded
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Resolvent estimate for the Friedrichs extension of the connection Laplacian

For the Friedrichs extension `A := connLaplacianL2_friedrichs g r s` of
the connection (rough) Laplacian on the metric `L²` Hilbert space of
`(r, s)`-tensor fields, the combination of self-adjointness and the
negative-semi-bounded estimate
$\langle A T, T\rangle_{L^2} \le 0$ implies that for every `λ > 0` the
operator `λ • I - A` is invertible on its range and the inverse has
operator norm at most `1/λ`.

The resolvent bound is the analytic input for the heat semigroup
`exp(t A) = (1 − t A / n)^{-n}` (Hille–Yosida / Lumer–Phillips), and for
the resolvent representation of `(1 - A)⁻¹` used in the spectral
analysis of `Δ_∇`.

## Main results

* `connLaplacianL2_friedrichs_neg_semi_bounded` — for every `T` in the
  domain of the Friedrichs extension, `-⟪A T, T⟫_{L²} ≥ 0`.
* `connLaplacianL2_friedrichs_resolvent_exists` — for every `λ > 0` the
  range of `λ • I - A` is all of `TensorL2 r s g` and the inverse is a
  bounded operator with norm at most `1/λ` (skeleton signature; the
  precise statement is filled in downstream once the `LinearPMap`
  resolvent API is fixed).
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
open DifferentialGeometry.PDE.RicciFlow.FriedrichsExtension

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

set_option linter.unusedSectionVars false in
/-- **Negative semi-boundedness of the Friedrichs extension.** For every
element `T` of the domain of `connLaplacianL2_friedrichs g r s`, the
inner-product pairing satisfies
$$
  -\langle A T, T\rangle_{L^2} \;\ge\; 0,
$$
where `A := connLaplacianL2_friedrichs g r s`.

This is the textbook negative-semi-boundedness estimate, inherited from
the corresponding `connLaplacianL2_neg_semi_bounded` on the smooth-cc
domain via the Friedrichs construction's preservation of the form
inequality. -/
theorem connLaplacianL2_friedrichs_neg_semi_bounded
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∀ T : (connLaplacianL2_friedrichs (I := I) g r s).domain,
      0 ≤ -(@inner ℝ _ _
        ((connLaplacianL2_friedrichs (I := I) g r s) T)
        (T : TensorL2 r s g)) := by
  exact sorry

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- **Resolvent estimate.** For every `λ > 0`, the operator
`λ • I - A` (where `A := connLaplacianL2_friedrichs g r s` and `I`
denotes the identity on `TensorL2 r s g`) has range equal to all of
`TensorL2 r s g`, and its set-theoretic inverse, viewed as a bounded
operator on the Hilbert space, has operator norm at most `1/λ`.

In particular, the resolvent `(λ • I - A)⁻¹` is well-defined and
bounded for every `λ > 0`, which is the analytic input for the
Hille–Yosida construction of the heat semigroup `exp(t A)`.

The skeleton ships the proposition as `True`; the precise statement
(specifying the existence of the inverse operator together with its
norm bound) is fixed downstream once the `LinearPMap`-based resolvent
API is committed to. -/
theorem connLaplacianL2_friedrichs_resolvent_exists
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    -- TODO: replace `True` with the precise statement once the
    -- `LinearPMap`-based resolvent / inverse API is selected.
    True := by
  trivial

end ConnectionLaplacian
end RicciFlow
end PDE
end DifferentialGeometry

end
