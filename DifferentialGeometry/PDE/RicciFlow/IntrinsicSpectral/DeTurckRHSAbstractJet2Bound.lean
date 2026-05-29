import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckRHSPointwiseLipschitz
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.LieMatrixChartBridge
import DifferentialGeometry.PDE.RicciFlow.LieDerivativePairing
import DifferentialGeometry.Integral.Connection.ChartBridge.Ricci
import DifferentialGeometry.Integral.Connection.ChartBridge.RiemannBasisIdentity
import DifferentialGeometry.Integral.Connection.ChartBridge.RiemannBasisIdentityAlpha

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

The abstract Ricci tensor is the trace of the curvature endomorphism of `LeviCivita g`,
i.e. the Levi-Civita connection applied *twice*.  The predicate `chartRiemannBasisIdentity`
of `Integral.Connection.ChartBridge.Ricci` records the basis-coordinate identification of
the abstract Riemann operator with the chart-Christoffel Riemann tensor (two iterations of
the chart-Levi-Civita Christoffel formula); it is now **discharged unconditionally** by
`Integral.Connection.chartRiemannBasisIdentity_holds`
(`Integral.Connection.ChartBridge.RiemannBasisIdentity`).  We therefore expose the
abstract Ricci-summand reduction in **unconditional** form
(`abstractRicciFrameComponent_eq_chartRicciSwap`), supplying the basis identity internally;
the former hypothesis-bearing statement is kept as
`abstractRicciFrameComponent_eq_chartRicciSwap_of_basisIdentity`.

The unconditional reduction expresses the abstract Ricci frame component at `x` as a sum
of the **chart-at-`x`** Ricci entries `chartRicciTensor g x p q (extChartAt I x x)`,
evaluated at the chart-`x` centre, weighted by the model-basis coordinates of the
chart-`α` frame vectors.  The chart-Christoffel atom
(`exists_chartRicciTensor_lipschitz_on_compact`) instead bounds the **chart-`α`** entries
`chartRicciTensor g α i j y` off-centre at `y ∈ K`.  Bridging the chart-at-`x` on-centre
entries to the chart-`α` off-centre entries is the **named change-of-coordinates gap**
documented below; it is the only step still missing for the headline bound.

## Main results

* `abstractRHSFrameComponent_eq_ricci_add_lie` — the abstract chart-frame scalar component
  of the right-hand side is `-2 · (abstract Ricci frame component) + (abstract Lie frame
  component)`.  Unconditional.
* `abstractRHSFrameComponent_diff_eq` — the difference of the two abstract chart-frame
  scalar components is the `(-2 · Ricci-diff + Lie-diff)` split.  Unconditional.
* `abstractLieFrameComponent_eq_chartMatrix` — the abstract Lie pairing on the chart-`α`
  frame equals the chart Lie-derivative matrix, on `chartLeviCivitaGoodSet α`.
  Unconditional (Cartan-formula bridge).
* `abstractRicciFrameComponent_eq_chartRicciSwap_of_basisIdentity` — under
  `chartRiemannBasisIdentity g x`, the abstract Ricci pairing on the chart-`α` frame
  reduces to a basis-coordinate sum of the chart-at-`x` Ricci entries.  Hypothesis-bearing
  (kept for the record).
* `abstractRicciFrameComponent_eq_chartRicciSwap` — the **unconditional** twin of the
  above, discharging `chartRiemannBasisIdentity g x` internally via
  `Integral.Connection.chartRiemannBasisIdentity_holds`.
* `riemannOp_eq_chartRiemannCLM_apply'`, `ricciTensor_eq_chartRicciSwap`,
  `ricciFun_eq_ricciTensor_swap`, `ricciFun_eq_ricciTensor` — unconditional abstract-layer
  twins of the corresponding `Integral.Connection.ChartBridge.Ricci`
  `…_of_basis_identity` lemmas, each discharging the basis identity internally.
* `chartCarrierRHSComp_diff_abs_le_jet2` — the committed chart-carrier `2`-jet bound
  (`exists_chartDeTurckRHSComp_lipschitz_on_compact`), the target the abstract reduction
  feeds into.

The headline bound on the abstract right-hand-side difference is **not** assembled here:
the chart-`α` off-centre identification (chart-at-`x` Ricci entries ↦ chart-`α` Ricci
entries) is a genuine missing change-of-coordinates step (a chart-`α` off-centre Riemann
basis identity), recorded as the named gap above and left for downstream work.
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

/-! ## The abstract Ricci summand: unconditional reduction to chart-at-`x` entries

The abstract Ricci tensor `ricciTensor g x` is the trace of the curvature endomorphism of
`LeviCivita g`, i.e. the Levi-Civita connection applied twice.  The basis-coordinate
identification of the abstract Riemann operator with the chart-Christoffel Riemann tensor
(`chartRiemannBasisIdentity g x`) is **unconditionally true**
(`Integral.Connection.chartRiemannBasisIdentity_holds`), so the swap-form basis expansion
`ricciTensor g x v w = ∑ i k, v^k · w^i · Rc_{i,k}(x, ϕ_x x)` against the **chart-at-`x`**
Ricci entries holds with no hypothesis (`ricciTensor_eq_chartRicciSwap` below).

That expansion is stated at the intrinsic chart-at-`x`, against the canonical model basis.
It is **not** stated at an arbitrary chart `α` evaluated off-centre: bridging the chart-`α`
frame components of the abstract Ricci tensor at off-centre points to the chart-`α` Ricci
entries `chartRicciTensor g α i j (extChartAt I α x)` — the entries bounded by the committed
atom `exists_chartRicciTensor_lipschitz_on_compact` — requires a genuine change-of-chart /
change-of-frame step (a chart-`α` off-centre Riemann basis identity).  That step is the
**named gap** for the headline bound; the hypothesis-bearing statement is kept below for the
record, the unconditional twin sits beside it. -/

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

/-! ## Unconditional discharge of the basis identity

`chartRiemannBasisIdentity_holds` (in `Integral.Connection.ChartBridge.RiemannBasisIdentity`)
proves `chartRiemannBasisIdentity g x` unconditionally for every smooth Riemannian metric
`g` on a closed manifold and every point `x`. We use it to supply the `h` argument of each
hypothesis-bearing bridge lemma internally, producing unconditional twins that drop the
basis-identity hypothesis entirely. These are the genuine, axiom-free statements that the
former predicate `chartRiemannBasisIdentity` only conditionally exposed. -/

/-- **Unconditional trilinear Riemann bridge** (twin of
`riemannOp_eq_chartRiemannCLM_apply_of_basis_identity`). This is exactly the unconditional
`Integral.Connection.riemannOp_eq_chartRiemannCLM_apply` of
`ChartBridge.RiemannBasisIdentity`, restated here as the abstract-layer twin used by the
Ricci reductions below. -/
theorem riemannOp_eq_chartRiemannCLM_apply'
    (g : SmoothRiemannianMetric I M) (x : M) (v w u : TangentSpace I x) :
    riemannOp (cov := LeviCivita (I := I) (smoothRiemannianMetricToInfty (I := I) g)) x v w u =
      chartRiemannCLM (I := I) (smoothRiemannianMetricToInfty (I := I) g) x v w u :=
  riemannOp_eq_chartRiemannCLM_apply (I := I)
    (smoothRiemannianMetricToInfty (I := I) g) x v w u

/-- **Unconditional swap-form Ricci basis expansion** (twin of
`ricciTensor_eq_chartRicciSwap_of_basis_identity`). The abstract Ricci tensor admits the
basis-coordinate sum against the chart-at-`x` Ricci entries, with no basis-identity
hypothesis: it is discharged internally via `chartRiemannBasisIdentity_holds`. -/
theorem ricciTensor_eq_chartRicciSwap
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x v w =
      ∑ p : Fin (Module.finrank ℝ E),
        ∑ q : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr v) q *
            ((chartModelBasis E).repr w) p *
            chartRicciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x p q
              (extChartAt I x x) :=
  ricciTensor_eq_chartRicciSwap_of_basis_identity (I := I)
    (smoothRiemannianMetricToInfty (I := I) g) x
    (chartRiemannBasisIdentity_holds (I := I)
      (smoothRiemannianMetricToInfty (I := I) g) x) v w

/-- **Unconditional swap-form Ricci carrier bridge** (twin of
`ricciFun_eq_ricciTensor_swap_of_basis_identity`). -/
theorem ricciFun_eq_ricciTensor_swap
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciFun (I := I) (smoothRiemannianMetricToInfty (I := I) g) x v w =
      ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x w v :=
  ricciFun_eq_ricciTensor_swap_of_basis_identity (I := I)
    (smoothRiemannianMetricToInfty (I := I) g) x
    (chartRiemannBasisIdentity_holds (I := I)
      (smoothRiemannianMetricToInfty (I := I) g) x) v w

/-- **Unconditional direct Ricci carrier bridge** (twin of
`ricciFun_eq_ricciTensor_of_basis_identity`): the chart Ricci carrier `ricciFun g x` equals
the abstract Ricci tensor `ricciTensor g x` as bilinear forms, with no basis-identity
hypothesis (discharged internally via `chartRiemannBasisIdentity_holds`; the closed-manifold
Ricci symmetry is supplied by the ambient `[I.Boundaryless]`). -/
theorem ricciFun_eq_ricciTensor
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciFun (I := I) (smoothRiemannianMetricToInfty (I := I) g) x v w =
      ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x v w :=
  ricciFun_eq_ricciTensor_of_basis_identity (I := I)
    (smoothRiemannianMetricToInfty (I := I) g) x
    (chartRiemannBasisIdentity_holds (I := I)
      (smoothRiemannianMetricToInfty (I := I) g) x) v w

/-- **Unconditional abstract Ricci frame component reduction** (twin of
`abstractRicciFrameComponent_eq_chartRicciSwap_of_basisIdentity`). The abstract Ricci frame
component reduces to a basis-coordinate sum of the chart-at-`x` Ricci entries, weighted by
the model-basis coordinates of the chart-`α` frame vectors, with **no** basis-identity
hypothesis. -/
theorem abstractRicciFrameComponent_eq_chartRicciSwap
    (g : SmoothRiemannianMetric I M) (α x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) =
      ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (chartFrameVec (I := I) α i x)) q *
          ((chartModelBasis E).repr (chartFrameVec (I := I) α j x)) p *
          chartRicciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x p q
            (extChartAt I x x) :=
  abstractRicciFrameComponent_eq_chartRicciSwap_of_basisIdentity (I := I) g α x i j
    (chartRiemannBasisIdentity_holds (I := I)
      (smoothRiemannianMetricToInfty (I := I) g) x)

/-! ## The off-centre chart-`α` Ricci frame identity (change-of-coordinates step)

The change-of-coordinates step bridging the abstract Ricci frame component at an
off-centre point `x` to the chart-`α` off-centre Ricci entry
`chartRicciTensor g α p q (ϕ_α x)` is now discharged unconditionally on
`chartLeviCivitaGoodSet α` by
`Integral.Connection.ricciTensor_chartBasisVec_alpha_eq`.  This is the genuine off-centre
twin of the centred basis identity, established via a chart-`α` off-centre second covariant
derivative, off-centre Lie-bracket vanishing, and a Levi-Civita trace against the chart-`α`
frame.  We restate it here in the abstract-layer `chartFrameVec` / `smoothRiemannianMetricToInfty`
typing. -/

set_option linter.unusedSectionVars false in
/-- **Off-centre chart-`α` Ricci frame identity (unconditional, on the chart-`α` good set).**
For `x ∈ chartLeviCivitaGoodSet α`, the abstract Ricci tensor evaluated on the chart-`α`
pushforward frame pair `(chartFrameVec α p x, chartFrameVec α q x)` equals the chart-`α`
Christoffel Ricci entry evaluated off-centre at `ϕ_α x`:
`ricciTensor g x (e^α_p x) (e^α_q x) = chartRicciTensor g α p q (ϕ_α x)`.

This is the named change-of-coordinates gap, now closed:
`Integral.Connection.ricciTensor_chartBasisVec_alpha_eq` supplies the off-centre identity. -/
theorem abstractRicciFrameComponent_eq_chartRicciAlpha
    (g : SmoothRiemannianMetric I M) (α : M)
    (p q : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x
        (chartFrameVec (I := I) α p x) (chartFrameVec (I := I) α q x) =
      chartRicciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) α p q
        (extChartAt I α x) := by
  rw [chartFrameVec_eq_chartBasisVecFiber, chartFrameVec_eq_chartBasisVecFiber]
  exact ricciTensor_chartBasisVec_alpha_eq (I := I)
    (smoothRiemannianMetricToInfty (I := I) g) α p q hx

/-! ## The chart-carrier target and the remaining off-centre gap

The pieces in hand for the headline abstract right-hand-side `2`-jet bound are now all
unconditional: the summand split (`abstractRHSFrameComponent_diff_eq`), the Lie bridge
(`abstractLieFrameComponent_eq_chartMatrix`), the abstract-Ricci reduction
(`abstractRicciFrameComponent_eq_chartRicciSwap`), and the committed chart-carrier atom
(`chartCarrierRHSComp_diff_abs_le_jet2`).

The single remaining obstruction is purely a change-of-coordinates step.  The abstract
Ricci reduction produces a sum of **chart-at-`x`** Ricci entries
`chartRicciTensor g x p q (extChartAt I x x)` (evaluated at the chart-`x` centre), whereas
the chart-carrier atom bounds **chart-`α`** entries `chartRicciTensor g α i j y` off-centre
at `y ∈ K`.  Identifying these two — equivalently, proving the chart-`α` off-centre Riemann
basis identity
`ricciTensor g x (chartFrameVec α p x) (chartFrameVec α q x)
   = chartRicciTensor g α p q (extChartAt I α x)`
on `chartLeviCivitaGoodSet α` — is genuine new infrastructure (a chart-`α` off-centre twin
of `Integral.Connection.ChartBridge.RiemannBasisIdentity`'s
`LeviCivita_chartBasisVec_secondCovDeriv` and `riemannOp_chartBasis_eq_chartRiemannCLM_basis`,
together with a chart-`α` off-centre directional-derivative engine and chart-`α` off-centre
Lie-bracket vanishing).  It is therefore left as the named gap; the headline bound is not
assembled here. -/

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

/-! ## The abstract chart-frame RHS component equals the chart-Christoffel carrier

With the abstract-Ricci off-centre identity (`abstractRicciFrameComponent_eq_chartRicciAlpha`)
and the abstract-Lie chart bridge (`abstractLieFrameComponent_eq_chartMatrix`) followed by the
Cartan-formula Lie matrix bridge (`chartLieDerivMetricMatrix_deTurckVF_eq_chartLieDeTurckComp`),
the abstract chart-`α`-frame scalar right-hand-side component at an off-centre good-set point `x`
equals the chart-Christoffel carrier `chartDeTurckRHSComp g_bg g α i j (ϕ_α x)`. -/

set_option linter.unusedSectionVars false in
/-- **The abstract chart-frame RHS component equals the chart-Christoffel carrier on the
good set.**  For `x ∈ chartLeviCivitaGoodSet α`,
```
deTurckRicciRHS g_bg g x (e^α_i x) (e^α_j x) = chartDeTurckRHSComp g_bg g α i j (ϕ_α x),
```
where the chart carrier is `chartDeTurckRHSComp = -2 · chartRicciTensor + chartLieDeTurckComp`.
The Ricci summand reduces by the off-centre chart-`α` Ricci frame identity; the Lie summand
reduces by the unconditional Cartan-formula chart bridge composed with the textbook Lie matrix
identity. -/
theorem abstractRHSFrameComponent_eq_chartCarrier
    (g_bg g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    deTurckRicciRHS (I := I) g_bg g x
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) =
      chartDeTurckRHSComp (I := I) g_bg g α i j (extChartAt I α x) := by
  -- Split the abstract component into the abstract Ricci and abstract Lie summands.
  rw [abstractRHSFrameComponent_eq_ricci_add_lie (I := I) g_bg g α x i j]
  -- Reduce the abstract Ricci summand to the off-centre chart-`α` Ricci entry.
  rw [abstractRicciFrameComponent_eq_chartRicciAlpha (I := I) g α i j hx]
  -- Reduce the abstract Lie summand to the chart Lie-derivative matrix, then to the
  -- textbook Christoffel Lie carrier.
  rw [abstractLieFrameComponent_eq_chartMatrix (I := I) g_bg g α i j x hx]
  rw [DeTurckCoefficients.chartLieDerivMetricMatrix_deTurckVF_eq_chartLieDeTurckComp
    (I := I) (smoothRiemannianMetricToInfty (I := I) g)
    (smoothRiemannianMetricToInfty (I := I) g_bg) α i j hx]
  -- Assemble into the chart carrier `-2 · Rc + 𝓛`.  The metric-alias coercion
  -- `smoothRiemannianMetricToInfty g = g` is a definitional identity.
  rw [chartDeTurckRHSComp_def]
  rfl

set_option linter.unusedSectionVars false in
/-- **The abstract chart-frame RHS difference equals the chart-carrier difference on the
good set.**  Direct difference of `abstractRHSFrameComponent_eq_chartCarrier` for the two
evolving metrics `g₁` and `g₂`. -/
theorem abstractRHSFrameComponent_diff_eq_chartCarrier_diff
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    (deTurckRicciRHS (I := I) g_bg g₁ x - deTurckRicciRHS (I := I) g_bg g₂ x)
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) =
      chartDeTurckRHSComp (I := I) g_bg g₁ α i j (extChartAt I α x) -
        chartDeTurckRHSComp (I := I) g_bg g₂ α i j (extChartAt I α x) := by
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
    abstractRHSFrameComponent_eq_chartCarrier (I := I) g_bg g₁ α i j hx,
    abstractRHSFrameComponent_eq_chartCarrier (I := I) g_bg g₂ α i j hx]

/-! ## The headline abstract right-hand-side `2`-jet bound

Combining the good-set carrier identity with the committed chart-carrier `2`-jet bound,
the abstract chart-`α`-frame scalar right-hand-side difference, measured on the chart-`α`
pushforward frame, is bounded by the chart `2`-jet seminorm of the metric difference,
uniformly over a compact subset `K` of the chart-target interior.  The bound is stated at
the chart point `y = ϕ_α x` for the unique good-set preimage `x = (ϕ_α)⁻¹ y`. -/

set_option linter.unusedSectionVars false in
/-- A point of the chart-target interior pulls back into the chart-`α` Levi-Civita good
set, with the chart round-trip recovered. -/
private lemma symm_mem_chartLeviCivitaGoodSet_of_interior
    (α : M) {y : E} (hy : y ∈ interior ((extChartAt I α).target : Set E)) :
    (extChartAt I α).symm y ∈ chartLeviCivitaGoodSet (I := I) α ∧
      extChartAt I α ((extChartAt I α).symm y) = y := by
  have hy_target : y ∈ (extChartAt I α).target := interior_subset hy
  have hsrc : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy_target
  have hround : extChartAt I α ((extChartAt I α).symm y) = y :=
    (extChartAt I α).right_inv hy_target
  refine ⟨mem_chartLeviCivitaGoodSet_iff.mpr ⟨hsrc, ?_, ?_⟩, hround⟩
  · -- The trivialization base set equals the chart source.
    rw [TangentBundle.trivializationAt_baseSet]
    rw [extChartAt_source] at hsrc; exact hsrc
  · rw [hround]; exact hy

set_option linter.unusedSectionVars false in
/-- **Headline: the abstract Ricci–DeTurck right-hand-side difference, on the chart-`α`
pushforward frame, is Lipschitz in the chart `2`-jet of the metric difference, uniformly
over a compact subset of the chart-target interior.**

For a fixed background metric `g_bg`, two smooth Riemannian metrics `g₁, g₂`, a chart base
point `α`, and a compact subset `K` of the interior of the chart-`α` target, there is a
single constant `C > 0` such that for every chart point `y ∈ K` (with good-set preimage
`x = (ϕ_α)⁻¹ y`) and all frame indices `(i, j)`,
```
|(deTurckRicciRHS g_bg g₁ − deTurckRicciRHS g_bg g₂) x (e^α_i x) (e^α_j x)|
  ≤ C · chartMetricJet2DiffSup g₁ g₂ α y .
```

This is the abstract (model-norm-free) chart-frame `2`-jet Lipschitz bound for the full
Ricci–DeTurck right-hand-side difference, assembled from the unconditional summand split,
the abstract-Ricci off-centre identity, the unconditional Cartan-formula Lie chart bridge,
the textbook Lie matrix bridge, and the committed chart-carrier atom. -/
theorem abstractRHSFrameComponent_diff_abs_le_jet2
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
      |(deTurckRicciRHS (I := I) g_bg g₁ ((extChartAt I α).symm y) -
            deTurckRicciRHS (I := I) g_bg g₂ ((extChartAt I α).symm y))
          (chartFrameVec (I := I) α i ((extChartAt I α).symm y))
          (chartFrameVec (I := I) α j ((extChartAt I α).symm y))| ≤
        C * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y := by
  -- The committed chart-carrier `2`-jet bound over `K`.
  obtain ⟨C, hC_pos, hC⟩ :=
    chartCarrierRHSComp_diff_abs_le_jet2 (I := I) g_bg g₁ g₂ α hK hKsub
  refine ⟨C, hC_pos, ?_⟩
  intro y hy i j
  -- The good-set preimage of `y` and the chart round-trip.
  obtain ⟨hx_good, hround⟩ :=
    symm_mem_chartLeviCivitaGoodSet_of_interior (I := I) α (hKsub hy)
  -- Rewrite the abstract frame difference as the chart-carrier difference at `ϕ_α (symm y) = y`.
  rw [abstractRHSFrameComponent_diff_eq_chartCarrier_diff (I := I) g_bg g₁ g₂ α i j hx_good,
    hround]
  -- Apply the chart-carrier `2`-jet bound.
  exact hC y hy i j

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
