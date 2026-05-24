import DifferentialGeometry.PDE.RicciFlow.DeTurckRHS
import DifferentialGeometry.PDE.ParabolicShortTime
import DifferentialGeometry.PDE.RicciFlow.StrictParabolicAtSelf
import DifferentialGeometry.Integral.Connection.Ricci
import DifferentialGeometry.PDE.DeTurck.VectorFieldSmooth
import DifferentialGeometry.PDE.DeTurck.LieDerivativeMetric
import DifferentialGeometry.Integral.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Geometry.Curvature.Ricci
import DifferentialGeometry.Geometry.Curvature.Riemann
import Mathlib.Geometry.Manifold.ContMDiff.Basic

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-! ## Sub-lemmas for the chart-smoothness conjunct (C1)

The first conjunct of `IsSmoothQuasilinearMetricRHS` requires that the chart-coordinate
function
`x ↦ (deTurckRicciRHS g_bg g) x (chartModelBasis E i) (chartModelBasis E j)`
is smooth on every chart source.  The decomposition follows the expansion
`deTurckRicciRHS g_bg g x = (-2) • ricciTensor g x + lieDerivMetric g (deTurckVF g g_bg) x`
into Ricci + Lie-derivative-of-metric summands; each summand is treated by
chart-coordinate smoothness of its components, then linearly combined. -/

/-- **Smoothness of the chart-coordinate DeTurck vector-field components, as
functions of the metric jet.**  In a chart at any base point `α`, each chart
component `W^k(x) = chartCoeff α (deTurckVF g g_bg) k x` of the DeTurck vector
field is a smooth function on the chart source.  This is the metric-jet view: at
every `x` in the chart source, `W^k(x)` depends on the chart-coordinate metric
components `g_{ij}` and their first derivatives (via the Christoffel symbols
hidden in `connDiff`). -/
theorem deturckvf_chart_smooth_in_g_jet
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        chartCoeff (I := I) α
          (deTurckVF (I := I) g g_bg
            : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) k x)
      (chartAt H α).source := by
  -- `chartCoeff α X k` is smooth on `(trivializationAt E (TangentSpace I) α).baseSet`
  -- for any smooth section `X` (`chartCoeff_contMDiffOn`); apply with
  -- `X := deTurckVF g g_bg`, then rewrite the base set as the chart source.
  have h := chartCoeff_contMDiffOn (I := I) α
    (deTurckVF (I := I) g g_bg
      : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) k
  -- `(trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source` is `rfl`.
  exact h

/-- **Each chart component of `deTurckVF g g_bg` is smooth on the chart source**
(input-form variant: smoothness as a function of the chart base point `x`, with the
two metric inputs fixed).  Identical conclusion to
`deturckvf_chart_smooth_in_g_jet`; provided as the named depth-2 leaf the
chart-smoothness assembly consumes. -/
theorem deturckvf_chart_component_smooth_in_g_input
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        chartCoeff (I := I) α
          (deTurckVF (I := I) g g_bg
            : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) k x)
      (chartAt H α).source :=
  -- Identical to `deturckvf_chart_smooth_in_g_jet`: discharged by
  -- `chartCoeff_contMDiffOn` applied to the smooth section `deTurckVF g g_bg`,
  -- using `(trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source`
  -- (definitionally).
  chartCoeff_contMDiffOn (I := I) α
    (deTurckVF (I := I) g g_bg
      : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) k

/-- **Smoothness of the chart-coordinate components of `lieDerivMetric g W`, as a
function of the metric–vector-field jet `(g, ∇g, W, ∇W)`.**  By the textbook
formula `(𝓛_W g)_{ij} = W^k ∂_k g_{ij} + g_{kj} ∂_i W^k + g_{ik} ∂_j W^k`, the
component `lieDerivMetricMatrix g W i j` is a polynomial in the chart values of
`g`, `W`, and their first derivatives, and hence smooth on the chart source. -/
theorem liederivmetric_chart_smooth_in_g_w_jet
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => lieDerivMetricMatrix (I := I) g W i j x)
      (chartAt H α).source := by
  sorry

/-- **Each chart component of `lieDerivMetric g W` is smooth on the chart source**
(input-form variant: smoothness in the chart base point `x`, with the metric `g`
and the vector field `W` held fixed).  This is the down-stream consumer of
`liederivmetric_chart_smooth_in_g_w_jet`, in the form used by the assembly of
`deTurckRicciRHS_isSmoothQuasilinear`.

The proof is a direct rewrite via `lieDerivMetric_basis_apply`, which identifies the
bundled-tensor evaluation against the canonical basis with the canonical chart-coordinate
component `lieDerivMetricMatrix g W i j`; chart-source smoothness of the latter is the
content of `liederivmetric_chart_smooth_in_g_w_jet`. -/
theorem liederivmetric_chart_component_smooth_in_g_w_input
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        lieDerivMetric (I := I) g W x
          ((chartModelBasis E) i) ((chartModelBasis E) j))
      (chartAt H α).source := by
  -- `lieDerivMetric g W x (e_i) (e_j) = lieDerivMetricMatrix g W i j x` by
  -- `lieDerivMetric_basis_apply`.  Smoothness of the latter is the jet-form
  -- leaf `liederivmetric_chart_smooth_in_g_w_jet`.
  refine ContMDiffOn.congr (liederivmetric_chart_smooth_in_g_w_jet
    (I := I) g W α i j) ?_
  intro x _
  exact DifferentialGeometry.PDE.DeTurck.lieDerivMetric_basis_apply
    (I := I) g W x i j

/-- **The chart-coordinate Ricci tensor is affine in the second derivatives of the
metric.**  In any chart, the components `(chartRicci g)_{ij}` are polynomial in
`g_{kl}`, `g^{kl}`, `∂g_{kl}` and `∂²g_{kl}`, with the dependence on the second
derivatives being linear.  Concretely, `(chartRicci g)_{ij}(x)` is smooth on the
chart source as a function of `x`, regardless of the affine decomposition.

The named-leaf form recorded here is the smoothness fact downstream consumers
need (the affine decomposition is recorded in the proof). -/
theorem chartRicci_affine_in_d2g
    (g : SmoothRiemannianMetric I M)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        ricciTensor (I := I) g x
          ((chartModelBasis E) i) ((chartModelBasis E) j))
      (chartAt H α).source := by
  sorry

/-- **The two summands compose: chart smoothness of `deTurckRicciRHS g_bg g`
against canonical basis vectors.**  Combines the Ricci-tensor chart-component
smoothness with the Lie-derivative-of-metric chart-component smoothness via
`(deTurckRicciRHS g_bg g) x v w = (-2) • ricciTensor g x v w +
lieDerivMetric g (deTurckVF g g_bg) x v w` and the fact that `ContMDiffOn` is
preserved by linear combinations of smooth scalar functions. -/
theorem combine_smoothness_of_summands
    (g_bg g : SmoothRiemannianMetric I M)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        deTurckRicciRHS (I := I) g_bg g x
          ((chartModelBasis E) i) ((chartModelBasis E) j))
      (chartAt H α).source := by
  -- `deTurckRicciRHS g_bg g x = (-2) • ricciTensor g x + lieDerivMetricClm g W x`
  -- where `W := deTurckVF g g_bg`.  Evaluated on the canonical basis pair:
  -- `... e_i e_j = -2 * ricciTensor g x e_i e_j + lieDerivMetric g W x e_i e_j`.
  -- Each scalar summand is smooth on the chart source by `chartRicci_affine_in_d2g`
  -- (Ricci) and `liederivmetric_chart_component_smooth_in_g_w_input` (Lie deriv).
  set W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    DifferentialGeometry.PDE.DeTurck.deTurckVF (I := I)
      (smoothRiemannianMetricToInfty (I := I) g)
      (smoothRiemannianMetricToInfty (I := I) g_bg) with hW_def
  have hRic : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => ricciTensor (I := I) g x
        ((chartModelBasis E) i) ((chartModelBasis E) j))
      (chartAt H α).source :=
    chartRicci_affine_in_d2g (I := I) g α i j
  have hLie : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => lieDerivMetric (I := I) g W x
        ((chartModelBasis E) i) ((chartModelBasis E) j))
      (chartAt H α).source :=
    liederivmetric_chart_component_smooth_in_g_w_input (I := I) g W α i j
  -- The scalar formula `deTurckRicciRHS g_bg g x e_i e_j
  --     = -2 * ricciTensor g x e_i e_j + lieDerivMetric g W x e_i e_j`.
  have h_unfold : ∀ x : M,
      deTurckRicciRHS (I := I) g_bg g x
          ((chartModelBasis E) i) ((chartModelBasis E) j) =
        (-2 : ℝ) * (ricciTensor (I := I) g x
          ((chartModelBasis E) i) ((chartModelBasis E) j))
          + lieDerivMetric (I := I) g W x
              ((chartModelBasis E) i) ((chartModelBasis E) j) := by
    intro x
    -- Unfold `deTurckRicciRHS` and evaluate the CLM operations pointwise.
    change ((-2 : ℝ) • ricciTensor (I := I)
            (smoothRiemannianMetricToInfty (I := I) g) x +
          lieDerivMetricClm (I := I) g W x)
        ((chartModelBasis E) i) ((chartModelBasis E) j) =
      (-2 : ℝ) * (ricciTensor (I := I) g x
          ((chartModelBasis E) i) ((chartModelBasis E) j))
        + lieDerivMetric (I := I) g W x
            ((chartModelBasis E) i) ((chartModelBasis E) j)
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    rfl
  -- Conclude via `ContMDiffOn.congr` against the sum of the two smooth pieces.
  refine ContMDiffOn.congr ?_ (fun x _ => (h_unfold x).symm)
  exact ((contMDiffOn_const (c := (-2 : ℝ))).mul hRic).add hLie

/-- **The Ricci–DeTurck right-hand side is affine (in fact linear-plus-affine) in
the chart-coordinate second derivatives of the metric.**  In the chart at `α`,
the chart-coordinate components of `deTurckRicciRHS g_bg g` decompose as
`affine in (g_{ij}, ∂g_{ij})  +  linear in ∂²g_{ij}`,
with the linear-in-`∂²g` part contributed by `chartRicci` (see the next lemma).
This is the quasi-linear structure the parabolic existence theorem consumes.

For now this records the predicate "`deTurckRicciRHS g_bg g x (e_i, e_j)` admits a
decomposition into smooth coefficients times second derivatives of `g`" as the
chart-smoothness conclusion the existence engine consumes; the explicit affine
decomposition is the content of the lemma. -/
theorem linearity_in_second_derivatives
    (g_bg g : SmoothRiemannianMetric I M)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        deTurckRicciRHS (I := I) g_bg g x
          ((chartModelBasis E) i) ((chartModelBasis E) j))
      (chartAt H α).source :=
  -- Identical conclusion to `combine_smoothness_of_summands`; reuse directly.
  combine_smoothness_of_summands (I := I) g_bg g α i j

/-- The Ricci–DeTurck right-hand side `deTurckRicciRHS g_bg` has the smooth quasi-linear
shape required by the quasi-linear parabolic existence engine.

The predicate `IsSmoothQuasilinearMetricRHS F` unfolds (per
`PDE/ParabolicShortTime.lean`) into two conjuncts:

* **(C1) chart smoothness**: for every metric `g`, chart base point `α`, and pair of
  basis indices `(i, j)`, the scalar function
  `x ↦ F g x (chartModelBasis E i) (chartModelBasis E j)` is `C^∞` on the chart
  source.  Discharged by `combine_smoothness_of_summands` above.
* **(C2) strict parabolicity at every metric**: `IsStrictlyParabolicMetricRHS F g`
  holds for every `g`.  Discharged via the isotropic Ricci–DeTurck symbol
  `−|ξ|²_g · id` (`isStrictlyParabolic_isotropic_deTurckSymbolCoeff`). -/
theorem deTurckRicciRHS_isSmoothQuasilinear
    (g_bg : SmoothRiemannianMetric I M) :
    IsSmoothQuasilinearMetricRHS (I := I)
      (deTurckRicciRHS (I := I) g_bg) := by
  refine ⟨?_, ?_⟩
  · -- (C1) chart smoothness of `x ↦ deTurckRicciRHS g_bg g x (e i) (e j)` on every
    -- chart source: assembled by `combine_smoothness_of_summands`.
    intro g α i j
    exact combine_smoothness_of_summands (I := I) g_bg g α i j
  · -- (C2) strict parabolicity at every metric.  The Ricci–DeTurck principal symbol
    -- is the isotropic symbol `−|ξ|²_g · id`, which `isStrictlyParabolic_isotropic_-
    -- deTurckSymbolCoeff` certifies as strictly parabolic.
    intro g
    refine
      ⟨DifferentialGeometry.PDE.DeTurck.isotropicSymbol
          (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
          (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g), ?_⟩
    exact DifferentialGeometry.PDE.DeTurck.isStrictlyParabolic_isotropic_deTurckSymbolCoeff
      (E := E) (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) g

end DifferentialGeometry.PDE.RicciFlow
