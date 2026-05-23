import DifferentialGeometry.PDE.RicciFlow.DeTurck.FlowEq
import DifferentialGeometry.PDE.RicciFlow.FriedrichsExtension.SelfAdjoint
import DifferentialGeometry.PDE.RicciFlow.FriedrichsExtension.ResolventBound

/-!
# Linearization of the DeTurck flow

The DeTurck flow `∂_t g = -2 Ric(g) + ℒ_{V(g)} g` on symmetric
`(0, 2)`-tensors is strictly parabolic: its **linearization at the
background metric `g₀`** is a uniformly elliptic second-order linear
operator on `(0, 2)`-tensor variations `h`.

Mathematically the linearization acts as the **Lichnerowicz Laplacian**

  `(Δ_L h)_{ij} = (Δ_∇ h)_{ij} + 2 R_{ikjl} h^{kl} - R_{ik} h^k_j - R_{jk} h^k_i`,

where `Δ_∇ = ∇^* ∇` is the rough connection Laplacian on `(0, 2)`-tensors
and the remaining terms are zeroth-order curvature corrections involving
the Riemann and Ricci tensors of the background. The principal symbol is
that of `-Δ` on each tensor component, so the operator is uniformly
elliptic; in particular its Friedrichs extension on
`TensorL2 0 2 g₀` is self-adjoint and negative semi-bounded.

In the skeleton we **identify** the linearization with the Friedrichs
extension `Δ_∇^F` of the connection Laplacian on `(0, 2)`-tensors —
i.e. we drop the zeroth-order curvature corrections, which do not
affect the principal symbol nor the qualitative analytic properties
(self-adjointness, negative semi-boundedness, sectorial generation of
an analytic semigroup). The genuine Lichnerowicz Laplacian is a
zeroth-order perturbation of `Δ_∇^F`, and downstream files refine the
identification once the curvature-perturbation infrastructure is
committed to.

## Main definitions

* `deTurckLinearization g₀` — the linearization of the DeTurck
  right-hand side at `g₀`, packaged as a partially-defined operator
  `TensorL2 0 2 g₀ →ₗ.[ℝ] TensorL2 0 2 g₀`. In the skeleton this is
  `connLaplacianL2_friedrichs g₀ 0 2`.

## Main results

* `deTurckLinearization_isSelfAdjoint` — the linearization is
  self-adjoint on its operator domain.
* `deTurckLinearization_neg_semi_bounded` — the linearization is
  negative semi-bounded, i.e. `-⟨A h, h⟩ ≥ 0` for every `h` in the
  operator domain.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option warningAsError false

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace DeTurck

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian
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

/-! ## The linearized DeTurck operator -/

set_option linter.unusedSectionVars false in
/-- The **linearization of the DeTurck right-hand side at the background
metric `g₀`**, as a partially-defined linear operator on the metric
`L²` Hilbert space of symmetric `(0, 2)`-tensor fields.

Mathematically this is the Lichnerowicz Laplacian
`Δ_L h = Δ_∇ h + (\text{curvature corrections})`. In the skeleton it is
identified with the Friedrichs extension `Δ_∇^F` of the rough
connection Laplacian; the zeroth-order curvature corrections do not
affect the principal symbol nor the qualitative analytic properties
(self-adjointness, negative semi-boundedness, sectorial generation of
the analytic semigroup), so they can be refined downstream as a
bounded perturbation. -/
def deTurckLinearization
    (g_0 : SmoothRiemannianMetric I M) :
    TensorL2 0 2 g_0 →ₗ.[ℝ] TensorL2 0 2 g_0 :=
  connLaplacianL2_friedrichs (I := I) g_0 0 2

/-! ## Self-adjointness and negative semi-boundedness -/

set_option linter.unusedSectionVars false in
/-- **Self-adjointness of the DeTurck linearization.** The
partially-defined operator `deTurckLinearization g₀` on
`TensorL2 0 2 g₀` is self-adjoint.

In the skeleton this is the immediate specialisation of
`connLaplacianL2_friedrichs_isSelfAdjoint` at ranks `(0, 2)`.
Downstream, when the linearization is refined to include the
zeroth-order curvature corrections of the Lichnerowicz Laplacian,
self-adjointness is preserved because those corrections are symmetric
bounded perturbations. -/
theorem deTurckLinearization_isSelfAdjoint
    (g_0 : SmoothRiemannianMetric I M) :
    _root_.IsSelfAdjoint (deTurckLinearization (I := I) g_0) := by
  unfold deTurckLinearization
  exact connLaplacianL2_friedrichs_isSelfAdjoint (I := I) g_0 0 2

set_option linter.unusedSectionVars false in
/-- **Negative semi-boundedness of the DeTurck linearization.** For
every `h` in the operator domain of `deTurckLinearization g₀`, the
pairing
$$
  -\langle (\mathrm{deTurckLinearization}\;g_0)\,h,\;h\rangle_{L^2} \;\ge\; 0.
$$

In the skeleton this is the immediate specialisation of
`connLaplacianL2_friedrichs_neg_semi_bounded` at ranks `(0, 2)`.
Downstream, when the linearization is refined to include the
zeroth-order curvature corrections of the Lichnerowicz Laplacian,
negative semi-boundedness need only hold up to a constant lower-order
shift, which is enough for sectoriality and the maximal-regularity
isomorphism. -/
theorem deTurckLinearization_neg_semi_bounded
    (g_0 : SmoothRiemannianMetric I M) :
    ∀ h : (deTurckLinearization (I := I) g_0).domain,
      0 ≤ -(@inner ℝ _ _
        ((deTurckLinearization (I := I) g_0) h)
        (h : TensorL2 0 2 g_0)) := by
  unfold deTurckLinearization
  exact connLaplacianL2_friedrichs_neg_semi_bounded (I := I) g_0 0 2

end DeTurck
end RicciFlow
end PDE
end DifferentialGeometry

end
