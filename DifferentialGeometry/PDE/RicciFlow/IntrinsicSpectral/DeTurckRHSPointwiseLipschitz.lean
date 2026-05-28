import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.FiberNormRiemannianBridge
import DifferentialGeometry.PDE.RicciFlow.SmoothQuasilinear
import DifferentialGeometry.PDE.RicciFlow.DeTurckRHSSection

/-!
# Pointwise Riemannian local-Lipschitz bound for the DeTurck reaction RHS difference

This file develops the genuinely *intrinsic* (Riemannian-fibre-norm) control of
the difference of two evaluations of the Ricci–DeTurck right-hand side
`deTurckRicciRHS g_bg g₁ x − deTurckRicciRHS g_bg g₂ x`, viewed as a covariant
`(0,2)`-tensor fibre element and measured in the `g₀`-induced Riemannian fibre
norm `‖·‖_{g₀,x}` coming from `Tensor0SBundle.tensorRS_riemannianBundle g₀ 0 2`.

## Rank convention

The DeTurck right-hand side `deTurckRicciRHS g_bg g x : TangentSpace I x →L[ℝ]
TangentSpace I x →L[ℝ] ℝ` is a continuous bilinear form, i.e. a covariant
`(0,2)`-tensor, living in the fibre `TensorRSSpace 0 2 I x` (see
`PDE/RicciFlow/DeTurckRHSSection.lean`).  Its Riemannian fibre norm is taken in
the `(0,2)`-tensor bundle Riemannian metric induced by the tangent metric
`g₀.toContinuousRiemannianMetric`.

## Model-norm-free discipline

Throughout, the *only* norms used on tensor fibres are either
* the Riemannian fibre norm `‖·‖_g` of `tensorRS_riemannianBundle`, or
* the chart-frame **scalar** component `deTurckRicciRHS g_bg g x (eᵢ x) (eⱼ x)`
  paired against the chart-`α`-pushforward frame vectors `chartFrameVec α i x`
  (a genuine smooth local frame).

The canonical model-space operator norm `‖TensorRSSpace.toModel T‖` is NOT used
at base points away from a chart centre: away from chart centres it is the
chart-selection-dependent trivialization-image norm, which is provably
*unbounded* on a non-parallelizable manifold (e.g. `S²`).  All trivialization
op-norm bounds consumed here are the *unconditional* ones, restricted to a
single chart source, exactly as in `FiberNormRiemannianBridge.lean`.

## Main results

* `deTurckRHS_diff_frame_component` — the chart-`α`-frame scalar component of the
  RHS difference is the difference of chart-frame components, hence smooth on the
  chart source (a genuine, true, model-norm-free identity).
* `deTurckRHS_diff_riemannianNorm_le_modelNorm_pointwise` — at each base point,
  the Riemannian fibre norm of the RHS difference is controlled by its model
  *space* norm at that chart centre (the per-point reverse bridge).

The full quantitative local-Lipschitz constant is recorded as a precise
`-- BLOCKED:` obstruction below: see the discussion at
`deTurck_rhs_pointwise_riemannian_lipschitz_obstruction`.
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
open DifferentialGeometry.Tensor
open DifferentialGeometry.PDE.RicciFlow.HebeyBlock
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Chart-frame scalar component of the RHS difference -/

set_option linter.unusedSectionVars false in
/-- **The chart-`α`-frame scalar component of the RHS difference is the
difference of the chart-frame components.**  This is the model-norm-free scalar
identity at the heart of the per-summand Lipschitz analysis: evaluating the
bilinear-form difference on the chart-`α`-pushforward frame vectors
`chartFrameVec α i x` distributes over the subtraction. -/
theorem deTurckRHS_diff_frame_component_apply
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M) (α x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    (deTurckRicciRHS (I := I) g_bg g₁ x - deTurckRicciRHS (I := I) g_bg g₂ x)
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) =
      deTurckRicciRHS (I := I) g_bg g₁ x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)
      - deTurckRicciRHS (I := I) g_bg g₂ x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) := by
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]

set_option linter.unusedSectionVars false in
/-- **The chart-`α`-frame scalar component of the RHS difference is `C^∞` on the
chart source.**  Both summands are `C^∞` by `combine_smoothness_of_summands`
(the quasi-linear chart-smoothness of the DeTurck right-hand side), and `C^∞` is
closed under subtraction.  This is the true, model-norm-free smoothness fact
underlying the per-summand Lipschitz estimates. -/
theorem deTurckRHS_diff_frame_component_contMDiffOn
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        (deTurckRicciRHS (I := I) g_bg g₁ x - deTurckRicciRHS (I := I) g_bg g₂ x)
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
      (chartAt H α).source := by
  have h₁ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => deTurckRicciRHS (I := I) g_bg g₁ x
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
      (chartAt H α).source :=
    combine_smoothness_of_summands (I := I) g_bg g₁ α i j
  have h₂ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => deTurckRicciRHS (I := I) g_bg g₂ x
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
      (chartAt H α).source :=
    combine_smoothness_of_summands (I := I) g_bg g₂ α i j
  refine (h₁.sub h₂).congr (fun x _ => ?_)
  exact deTurckRHS_diff_frame_component_apply (I := I) g_bg g₁ g₂ α x i j

/-! ## Per-point reverse bridge for the RHS difference

At a single base point `x₀`, the Riemannian fibre norm of the RHS difference,
identified as the `(0,2)`-tensor fibre element via `bilinFormToModelₗᵢ`, is
controlled by its model-space norm at the chart centre — using the per-point
reverse bridge `gNorm_le_modelNorm_pointwise` (which is itself derived purely
from the unconditional chart-fibre trivialization op-norm bound at the chart
centre, where `toModel` is the *intrinsic* identification). -/

set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Per-point reverse bridge applied to the RHS difference.**  At each base
point `x₀`, there is `D > 0` (depending on `g₀` and `x₀`) with
`‖T‖_{g₀,x₀} ≤ D · ‖toModel T‖` for every `(0,2)`-tensor fibre element `T` at
`x₀`; in particular this controls the Riemannian fibre norm of the RHS
difference packaged through `bilinFormToModelₗᵢ`.

The constant is the per-point reverse-bridge constant; making it *uniform* over
the compact base is the content of the blocked step below. -/
theorem deTurckRHS_diff_gNorm_le_modelNorm_pointwise
    (g₀ : SmoothRiemannianMetric I M) (x₀ : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2
    ∃ D : ℝ, 0 < D ∧ ∀ T : TensorRSSpace 0 2 I x₀,
      ‖T‖ ≤ D * ‖TensorRSSpace.toModel (𝕜 := ℝ) (I := I) T‖ :=
  gNorm_le_modelNorm_pointwise (I := I) (M := M) g₀ 0 2 x₀

/-! ## The quantitative pointwise Riemannian local-Lipschitz bound: obstruction

The target deliverable is a constant `C(R) ≥ 0` with, for all `x : M`,

  `‖deTurckRicciRHS g_bg g₁ x − deTurckRicciRHS g_bg g₂ x‖_{g₀,x}`
      `≤ C(R) · ‖(g₁ − g₂)(x)‖_{g₀,x}`

for `g₁, g₂` in a ball of radius `R` around a base metric `g₀`, with both norms
the Riemannian fibre norm.

Two genuinely *mathematical* (not merely engineering) obstructions block this
exact statement:

`-- BLOCKED:`

**(O1) Jet-versus-value obstruction (statement-level falsity).**
`deTurckRicciRHS g_bg g x` depends on the **2-jet** of `g` at `x`: the Ricci
summand is *affine in the second chart-derivatives* `∂²g` (this is the explicit
content of `chartRicci_affine_in_d2g` in `SmoothQuasilinear.lean`), and the
Lie-derivative summand `𝓛_{deTurckVF g g_bg} g` depends on `∂g` and `∂²g` of `g`
(via the Christoffel symbols inside `deTurckVF`).  Therefore the difference
`deTurckRicciRHS g_bg g₁ x − deTurckRicciRHS g_bg g₂ x` depends on
`∂²(g₁ − g₂)(x)` and `∂(g₁ − g₂)(x)`, which are **not** controlled by the
pointwise fibre value `‖(g₁ − g₂)(x)‖_{g₀,x}` (the `0`-jet).  Concretely: fix
`x`, let `g₂ = g₁ + ε·χ·H` where `χ` is a bump with `χ(x) = 0` but
`∂²χ(x) ≠ 0`; then `(g₁ − g₂)(x) = 0` while the second-order part of the RHS
difference at `x` is `≠ 0`.  Hence **no** constant `C` can satisfy the displayed
inequality with the `0`-jet `‖(g₁ − g₂)(x)‖_{g₀,x}` on the right-hand side, for
any `C⁰`/`L^∞` ball condition.

The *true* pointwise statement bounds the LHS by `C(R)` times the **2-jet
seminorm** of `g₁ − g₂` at `x` (value + first + second chart-derivatives).  The
displayed value-only inequality holds only when the admissibility/ball condition
controls the full `2`-jet pointwise (e.g. a `C²` ball with the right-hand side
being the `2`-jet seminorm) — in which case the right-hand side is no longer the
fibre value `‖(g₁ − g₂)(x)‖_{g₀,x}` but the jet seminorm.  The downstream
quasilinear-parabolic existence engine
(`quasilinear_metric_parabolic_shortTime_exists`, `PDE/ParabolicShortTime.lean`)
consumes a Lipschitz constant in the `Hᵏ` (Sobolev) norm — which *does* control
the jet — not a pointwise-value Lipschitz bound, confirming the value-only form
is the wrong target.

**(O2) Uniform model↔Riemannian comparison (model-norm wall).**
Even granting the `2`-jet right-hand side, the natural route translates the
chart-frame scalar component Lipschitz bound (true and model-norm-free, see
`deTurckRHS_diff_frame_component_contMDiffOn`) into the Riemannian fibre norm via
a model↔`g` comparison.  The per-point bridge
`gNorm_le_modelNorm_pointwise` gives the comparison constant only at a single
base point; making it **uniform over the compact base** requires a uniform bound
on `b ↦ ‖TensorRSSpace.toModel T‖` away from chart centres.  But
`TensorRSSpace.toModel` at `b ≠` (chart centre) is the chart-selection-dependent
trivialization-image norm, which is provably **unbounded** on a
non-parallelizable manifold (this is exactly the `HasLocallyConstantChartAt`
phenomenon, false on `S²`).  The correct model-norm-free uniformisation must
therefore proceed through the partition-of-unity / chart-frame-component
assembly (`uniform_chart_bounds_from_compactness`,
`chart_frame_component_norm_bound`), which delivers a uniform constant in the
`Hᵏ` (integrated) norm — not pointwise — again landing on the jet/Sobolev side
rather than the pointwise-fibre-value side.

**Conclusion.**  The exact stated lemma is mathematically false as written
(obstruction O1).  The mathematically correct and model-norm-free deliverable is
either (a) a *jet-seminorm* pointwise bound, or (b) an `Hᵏ`-Lipschitz bound; both
are substantially larger pieces of infrastructure tied to the parabolic
existence engine, and (b) is what the downstream consumer actually requires.
The true, model-norm-free building blocks established above
(`deTurckRHS_diff_frame_component_apply`,
`deTurckRHS_diff_frame_component_contMDiffOn`,
`deTurckRHS_diff_gNorm_le_modelNorm_pointwise`) are the per-summand inputs to
either correct formulation. -/
theorem deTurck_rhs_pointwise_riemannian_lipschitz_obstruction : True := trivial

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end

/-! ## Axiom audit -/

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
#print axioms deTurckRHS_diff_frame_component_apply

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
#print axioms deTurckRHS_diff_frame_component_contMDiffOn

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
#print axioms deTurckRHS_diff_gNorm_le_modelNorm_pointwise
