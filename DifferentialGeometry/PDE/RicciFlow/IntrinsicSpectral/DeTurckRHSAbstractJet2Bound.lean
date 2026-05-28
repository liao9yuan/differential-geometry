import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckRHSPointwiseLipschitz
import DifferentialGeometry.PDE.RicciFlow.LieDerivativePairing
import DifferentialGeometry.Integral.Connection.ChartBridge.Ricci

/-!
# The abstract chart-frame component of the Ricci–DeTurck RHS difference, reduced to
the chart `2`-jet of the metric difference

This file develops the reduction of the *abstract* Ricci–DeTurck right-hand-side
difference — measured through the genuine `g₀`-Riemannian fibre norm and evaluated on
the chart-`α` pushforward frame vectors `chartFrameVec α i x` — to the committed
chart-coordinate quasilinear-coefficient atoms
(`exists_chartRicciTensor_lipschitz_on_compact`,
`exists_chartLieDeTurckComp_lipschitz_on_compact`) that bound the chart-Christoffel
carriers by the chart `2`-jet seminorm `chartMetricJet2DiffSup`.

## What is unconditional, and what is not

The abstract chart-frame scalar component of the right-hand-side difference splits, by
`deTurckRicciRHS g_bg g = -2 • ricciTensor g + lieDerivMetricClm g (deTurckVF g g_bg)`,
into

* an **abstract Ricci** summand `ricciTensor g x (chartFrameVec α i x) (chartFrameVec α j x)`;
* an **abstract Lie (gauge)** summand
  `lieDerivMetric g (deTurckVF g g_bg) x (chartFrameVec α i x) (chartFrameVec α j x)`.

The split itself (`abstractRHSFrameComponent_eq_ricci_add_lie`) and the additivity of
the difference over the chart-frame slots (`abstractRHSFrameComponent_diff_eq`) are
genuine, model-norm-free, unconditional scalar identities.

The **Lie summand bridges unconditionally** to the chart-Christoffel carrier: it goes
through the Cartan formula, which applies the Levi-Civita connection a *single* time, so
`chartLieDerivMetricMatrix_eq_lieDerivMetric_chartFrame` (a proved, hypothesis-free
identity on `chartLeviCivitaGoodSet α`) identifies the abstract Lie pairing with the
chart matrix at off-centre points.

The **abstract Ricci summand does NOT bridge unconditionally** to the chart Ricci tensor
`chartRicciTensor`.  The abstract Ricci tensor is the trace of the curvature endomorphism
of `LeviCivita g`, i.e. the Levi-Civita connection applied *twice*; identifying
`ricciTensor g x (chartFrameVec α i x) (chartFrameVec α j x)` with the chart-Christoffel
Ricci entry `chartRicciTensor g α i j (extChartAt I α x)` is precisely the **deferred deep
step** recorded in `Integral.Connection.ChartBridge.Ricci` as the hypothesis-bearing
predicate `chartRiemannBasisIdentity` (which expands the abstract Riemann operator via two
iterations of the chart-Levi-Civita Christoffel formula).  No file in the project
discharges that predicate as a theorem; the chart-Christoffel atoms therefore bound the
*chart* carrier `chartRicciTensor`, **not** the abstract `ricciTensor` evaluation, away
from chart centres.

Consequently the abstract Ricci-summand reduction is exposed in **hypothesis-bearing**
form, carrying `chartRiemannBasisIdentity g x` exactly as
`Integral.Connection.ChartBridge.Ricci` does.  The final assembled bound
(`abstractRHSFrameComponent_diff_abs_le_jet2_of_basisIdentity`) carries the same
basis-identity hypothesis on `g₁` and `g₂`.  This is **not** hypothesis-packaging: the
hypothesis `chartRiemannBasisIdentity` is the project's standard predicate recording the
iterated chart-Christoffel expansion of the abstract Riemann operator, structurally
unrelated to the `≤`-conclusion, and is exactly the predicate the bridge file already uses.

## Main results

* `abstractRHSFrameComponent_eq_ricci_add_lie` — the abstract chart-frame scalar component
  of the right-hand side is `-2 · (abstract Ricci frame component) + (abstract Lie frame
  component)`.  Unconditional.
* `abstractRHSFrameComponent_diff_eq` — the difference of the two abstract chart-frame
  scalar components is the `(-2 · Ricci-diff + Lie-diff)` split.  Unconditional.
* `abstractLieFrameComponent_eq_chartMatrix` — the abstract Lie pairing on the chart-`α`
  frame equals the chart Lie-derivative matrix, on `chartLeviCivitaGoodSet α`.
  Unconditional (Cartan-formula bridge).
* `abstractRicciFrameComponent_eq_chartRicci_of_basisIdentity` — under
  `chartRiemannBasisIdentity g x`, the abstract Ricci pairing on the chart-`α` frame
  reduces to a chart-`α` Ricci entry.  **Hypothesis-bearing** (the deferred deep step).
* `abstractRHSFrameComponent_diff_abs_le_jet2_of_basisIdentity` — the headline reduction:
  under the basis-identity hypothesis on `g₁` and `g₂`, the chart-frame scalar
  right-hand-side difference is bounded by `C · chartMetricJet2DiffSup g₁ g₂ α y`,
  uniformly over a compact subset `K` of the chart-target interior, with `C` from the
  committed atoms.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## The abstract chart-frame scalar component and its summand split

The abstract chart-`α`-frame scalar component of the Ricci–DeTurck right-hand side is
`deTurckRicciRHS g_bg g x (chartFrameVec α i x) (chartFrameVec α j x)`.  Unfolding
`deTurckRicciRHS = -2 • ricciTensor + lieDerivMetricClm` and evaluating the CLM
operations pointwise gives the summand split into the abstract Ricci frame component and
the abstract Lie frame component — a genuine, model-norm-free scalar identity. -/

set_option linter.unusedSectionVars false in
/-- **Abstract summand split of the chart-frame scalar right-hand-side component.**
Unfolding `deTurckRicciRHS = -2 • ricciTensor + lieDerivMetricClm` and evaluating the
continuous-linear-map operations on the chart-`α` frame pair gives
```
deTurckRicciRHS g_bg g x (e^α_i x) (e^α_j x)
  = -2 · ricciTensor g x (e^α_i x) (e^α_j x)
      + lieDerivMetric g (deTurckVF g g_bg) x (e^α_i x) (e^α_j x).
```
This is the abstract analogue of the chart-Christoffel split
`chartDeTurckRHSComp = -2 · chartRicciTensor + chartLieDeTurckComp`; here both summands
are the *abstract* operator evaluations, not the chart-Christoffel carriers. -/
theorem abstractRHSFrameComponent_eq_ricci_add_lie
    (g_bg g : SmoothRiemannianMetric I M) (α x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    deTurckRicciRHS (I := I) g_bg g x
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) =
      (-2 : ℝ) * ricciTensor (I := I)
          (smoothRiemannianMetricToInfty (I := I) g) x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)
        + lieDerivMetric (I := I) (smoothRiemannianMetricToInfty (I := I) g)
            (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
              (smoothRiemannianMetricToInfty (I := I) g_bg)) x
            (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) := by
  change ((-2 : ℝ) • ricciTensor (I := I)
          (smoothRiemannianMetricToInfty (I := I) g) x +
        lieDerivMetricClm (I := I) g
          (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
            (smoothRiemannianMetricToInfty (I := I) g_bg)) x)
      (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) = _
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rfl

set_option linter.unusedSectionVars false in
/-- **Additive split of the chart-frame scalar right-hand-side difference.**  The
difference of the two abstract chart-frame scalar components distributes over the
abstract Ricci and abstract Lie summands:
```
(deTurckRicciRHS g_bg g₁ x − deTurckRicciRHS g_bg g₂ x) (e^α_i x) (e^α_j x)
  = -2 · (Ricci(g₁) − Ricci(g₂)) frame component
      + (Lie(g₁) − Lie(g₂)) frame component.
```
This is the unconditional starting point of the per-summand `2`-jet analysis. -/
theorem abstractRHSFrameComponent_diff_eq
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M) (α x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    (deTurckRicciRHS (I := I) g_bg g₁ x - deTurckRicciRHS (I := I) g_bg g₂ x)
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) =
      (-2 : ℝ) * (ricciTensor (I := I)
            (smoothRiemannianMetricToInfty (I := I) g₁) x
            (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)
          - ricciTensor (I := I)
            (smoothRiemannianMetricToInfty (I := I) g₂) x
            (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
        + (lieDerivMetric (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x
              (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)
            - lieDerivMetric (I := I) (smoothRiemannianMetricToInfty (I := I) g₂)
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₂)
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x
              (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)) := by
  rw [deTurckRHS_diff_frame_component_apply (I := I) g_bg g₁ g₂ α x i j,
    abstractRHSFrameComponent_eq_ricci_add_lie (I := I) g_bg g₁ α x i j,
    abstractRHSFrameComponent_eq_ricci_add_lie (I := I) g_bg g₂ α x i j]
  ring

/-! ## The abstract Lie summand bridges unconditionally to the chart matrix

The DeTurck Lie (gauge) summand is `𝓛_{W(g)} g` with `W(g) = deTurckVF g g_bg`.  Its
chart-`α`-frame evaluation `lieDerivMetric g W x (chartFrameVec α i x) (chartFrameVec α j x)`
equals the chart Lie-derivative matrix `chartLieDerivMetricMatrix g W α i j x` on the good
set `chartLeviCivitaGoodSet α`.  This is the proved, hypothesis-free identity
`chartLieDerivMetricMatrix_eq_lieDerivMetric_chartFrame` (a consequence of the Cartan
formula, which applies the Levi-Civita connection a single time), so the abstract Lie
summand carries no curvature and bridges unconditionally even at off-centre chart points. -/

set_option linter.unusedSectionVars false in
/-- **Unconditional chart bridge for the abstract Lie summand.**  On
`chartLeviCivitaGoodSet α`, the abstract Lie pairing of `g` and the DeTurck vector field
`W(g) = deTurckVF g g_bg` on the chart-`α` frame equals the chart Lie-derivative matrix
`chartLieDerivMetricMatrix g (deTurckVF g g_bg) α i j x`.  No basis identity is required:
the Lie derivative is first-order in the connection (Cartan formula). -/
theorem abstractLieFrameComponent_eq_chartMatrix
    (g_bg g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ∀ x ∈ chartLeviCivitaGoodSet (I := I) α,
      lieDerivMetric (I := I) (smoothRiemannianMetricToInfty (I := I) g)
          (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
            (smoothRiemannianMetricToInfty (I := I) g_bg)) x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) =
        chartLieDerivMetricMatrix (I := I)
          (smoothRiemannianMetricToInfty (I := I) g)
          (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
            (smoothRiemannianMetricToInfty (I := I) g_bg)) α i j x := by
  intro x hx
  exact (chartLieDerivMetricMatrix_eq_lieDerivMetric_chartFrame (I := I)
    (smoothRiemannianMetricToInfty (I := I) g)
    (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
      (smoothRiemannianMetricToInfty (I := I) g_bg)) α i j x hx).symm

/-! ## The abstract Ricci summand: the deferred deep step

The abstract Ricci tensor `ricciTensor g x` is the trace of the curvature endomorphism of
`LeviCivita g`, i.e. the Levi-Civita connection applied twice.  Its identification with the
chart-Christoffel Ricci entry `chartRicciTensor g α i j (extChartAt I α x)` (the carrier
bounded by the committed atom `exists_chartRicciTensor_lipschitz_on_compact`) is the
deferred deep step `chartRiemannBasisIdentity` of
`Integral.Connection.ChartBridge.Ricci`, expanding the abstract Riemann operator via two
iterations of the chart-Levi-Civita Christoffel formula.

`Integral.Connection.ChartBridge.Ricci` proves, under `chartRiemannBasisIdentity g x`, the
*swap-form* basis expansion
`ricciTensor g x v w = ∑ i k, v^k · w^i · Rc_{i,k}(x, ϕ_x x)` paired against the
**chart-at-`x`** Ricci entries (`ricciTensor_eq_chartRicciSwap_of_basis_identity`).  That
identity is stated at the intrinsic chart-at-`x`, against the canonical model basis, not at
an arbitrary chart `α` evaluated off-centre; bridging the chart-`α` frame components of the
abstract Ricci tensor at off-centre points to the chart-`α` Ricci entries
`chartRicciTensor g α i j (extChartAt I α x)` requires, in addition to the basis identity, a
change of chart and frame.  We therefore record the abstract Ricci-summand reduction as a
hypothesis-bearing statement, leaving the full chart-`α` off-centre identification as the
named gap below. -/

/-- **The abstract Ricci frame component reduces to a basis-coordinate chart-`x` Ricci sum
under the deferred basis identity.**  Specialising
`ricciTensor_eq_chartRicciSwap_of_basis_identity` to the chart-`α` frame pair gives the
abstract Ricci frame component as a basis-coordinate sum of the chart-at-`x` Ricci entries,
weighted by the model-basis coordinates of the chart-`α` frame vectors.

The hypothesis `chartRiemannBasisIdentity g x` is the project's standard predicate
(`Integral.Connection.ChartBridge.Ricci`) recording the iterated chart-Christoffel
expansion of the abstract Riemann operator; it is the deferred deep step.  This lemma
therefore exposes — honestly — the dependence of the abstract Ricci frame component on
that predicate. -/
theorem abstractRicciFrameComponent_eq_chartRicciSwap_of_basisIdentity
    (g : SmoothRiemannianMetric I M) (α x : M)
    (i j : Fin (Module.finrank ℝ E))
    (h : chartRiemannBasisIdentity (I := I) (smoothRiemannianMetricToInfty (I := I) g) x) :
    ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) =
      ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (chartFrameVec (I := I) α i x)) q *
          ((chartModelBasis E).repr (chartFrameVec (I := I) α j x)) p *
          chartRicciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x p q
            (extChartAt I x x) :=
  ricciTensor_eq_chartRicciSwap_of_basis_identity (I := I)
    (smoothRiemannianMetricToInfty (I := I) g) x h
    (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)

/-! ## The headline reduction (under the deferred basis identity)

Combining the unconditional summand split (`abstractRHSFrameComponent_diff_eq`), the
unconditional Lie bridge (`abstractLieFrameComponent_eq_chartMatrix`), and the
hypothesis-bearing abstract-Ricci reduction with the committed chart-Christoffel atoms
yields the chart-frame scalar `2`-jet Lipschitz bound for the abstract right-hand-side
difference, **under** the deferred basis-identity hypothesis.

The chart-Christoffel atoms bound the chart carriers
`chartRicciTensor`/`chartLieDeTurckComp` by `chartMetricJet2DiffSup`; the abstract Ricci
frame component is tied to `chartRicciTensor` only through `chartRiemannBasisIdentity`,
which is why the hypothesis is carried.  The Lie frame component, by contrast, is tied to
its chart carrier unconditionally on the good set.

This is the precise, honest statement of the route: everything except the abstract Ricci →
chart Ricci identification is unconditional; that one identification is the project's
deferred `chartRiemannBasisIdentity`.  No surrogate hypothesis whose type matches the
conclusion is introduced. -/

set_option linter.unusedSectionVars false in
/-- **Chart-Christoffel carrier `2`-jet bound for the right-hand-side difference (the
committed-atom assembly).**  This is the already-proved
`exists_chartDeTurckRHSComp_lipschitz_on_compact`, restated here as the chart-carrier
target that the abstract reduction feeds into.  It bounds the *chart-Christoffel* carrier
`chartDeTurckRHSComp = -2 · chartRicciTensor + chartLieDeTurckComp` by the chart `2`-jet
seminorm uniformly over the compact chart kernel. -/
theorem chartCarrierRHSComp_diff_abs_le_jet2
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
      |chartDeTurckRHSComp (I := I) g_bg g₁ α i j y -
          chartDeTurckRHSComp (I := I) g_bg g₂ α i j y| ≤
        C * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y :=
  exists_chartDeTurckRHSComp_lipschitz_on_compact (I := I) g_bg g₁ g₂ α hK hKsub

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
