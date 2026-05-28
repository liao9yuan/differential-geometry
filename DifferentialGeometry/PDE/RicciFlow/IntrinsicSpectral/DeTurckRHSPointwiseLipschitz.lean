import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.FiberNormRiemannianBridge
import DifferentialGeometry.PDE.RicciFlow.SmoothQuasilinear
import DifferentialGeometry.PDE.RicciFlow.DeTurckRHSSection
import DifferentialGeometry.Integral.Connection.TensorExtension
import DifferentialGeometry.Integral.Connection.IteratedTensorCovDeriv

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
open DifferentialGeometry.PDE.RicciFlow
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

/-! ## The intrinsic `2`-jet seminorm of a metric difference

The correct right-hand side of the pointwise Lipschitz bound is the **`2`-jet
seminorm** of the metric perturbation `g₁ − g₂`, measured in `g₀`-induced
Riemannian fibre norms.  The metric difference is the smooth covariant
`(0,2)`-tensor field `b ↦ g₁.inner b − g₂.inner b`; its `0`-jet is the fibre
value, its `1`-jet adds the first covariant derivative
`∇^{g₀}(g₁ − g₂)` (a `(0,3)`-tensor), and its `2`-jet adds the second covariant
derivative `∇^{g₀,2}(g₁ − g₂)` (a `(0,4)`-tensor).  This subsection gives the
intrinsic `(0,2)` and `(0,3)` building blocks (the value and first-order terms);
all fibre norms used are Riemannian, so no trivialization-image (chart-selection)
norm enters and the construction needs no parallelizability witness. -/

/-- The metric difference `g₁ − g₂`, as a `(0,2)`-tensor field
`b ↦ g₁.inner b − g₂.inner b`.  This is
`metricTensor02 g₁ − metricTensor02 g₂` and is the object whose `2`-jet
controls the Ricci–DeTurck right-hand-side difference. -/
def metricDiff02 (g₁ g₂ : SmoothRiemannianMetric I M) :
    Π b : M, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ :=
  fun b => metricTensor02 (I := I) g₁ b - metricTensor02 (I := I) g₂ b

@[simp] theorem metricDiff02_apply
    (g₁ g₂ : SmoothRiemannianMetric I M) (b : M) (v w : TangentSpace I b) :
    metricDiff02 (I := I) g₁ g₂ b v w =
      g₁.inner b v w - g₂.inner b v w := by
  change (metricTensor02 (I := I) g₁ b - metricTensor02 (I := I) g₂ b) v w =
    g₁.inner b v w - g₂.inner b v w
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
  rfl

/-- The first covariant derivative `∇^{g₀}(g₁ − g₂)` of the metric difference,
computed with the Levi-Civita connection of the base metric `g₀`.  This is a
`(0,3)`-tensor fibre element at each point: `T_b M →L[ℝ] (T_b M →L[ℝ] T_b M
→L[ℝ] ℝ)`, the directional covariant derivative of the `(0,2)`-tensor field
`metricDiff02 g₁ g₂`. -/
def metricDiff02Cov (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (b : M) :
    TangentSpace I b →L[ℝ]
      (TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) :=
  (tensor02Cov (LeviCivita (I := I) g₀)).toFun
    (metricDiff02 (I := I) g₁ g₂) b

/-- The first covariant derivative is additive in the metric difference: it
distributes over the `(0,2)`-tensor subtraction defining `metricDiff02`.  This
is the connection additivity axiom of `tensor02Cov` specialised to the metric
difference, valid since both metric sections are smooth (hence differentiable). -/
theorem metricDiff02Cov_eq_sub
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (b : M) :
    metricDiff02Cov (I := I) g₀ g₁ g₂ b =
      (tensor02Cov (LeviCivita (I := I) g₀)).toFun
          (metricTensor02 (I := I) g₁) b
        - (tensor02Cov (LeviCivita (I := I) g₀)).toFun
          (metricTensor02 (I := I) g₂) b := by
  classical
  -- The `(0,2)`-tensor covariant derivative is additive on differentiable sections
  -- (`add` axiom of `IsCovariantDerivativeOn`); both metric sections are smooth.
  set cov := tensor02Cov (LeviCivita (I := I) g₀) with hcov_def
  have hcovOn := cov.isCovariantDerivativeOnUniv
  have hT₁ : MDiffAtTensor02 (metricTensor02 (I := I) g₁) b :=
    metricTensor02_mdiff (I := I) g₁ b
  have hT₂ : MDiffAtTensor02 (metricTensor02 (I := I) g₂) b :=
    metricTensor02_mdiff (I := I) g₂ b
  -- `MDiffAtTensor02 T b` is exactly section-differentiability `MDiffAt (T% T) b`
  -- for the `(0,2)`-tensor bundle, so the section-arithmetic lemmas apply.
  have hT₂neg : MDiffAtTensor02 (-(metricTensor02 (I := I) g₂)) b :=
    mdifferentiableAt_neg_section hT₂
  -- Step 1: `cov (-T₂) b = - cov T₂ b`, from additivity and `cov 0 = 0`.
  have hneg : cov.toFun (-(metricTensor02 (I := I) g₂)) b =
      - cov.toFun (metricTensor02 (I := I) g₂) b := by
    have hsum : cov.toFun (metricTensor02 (I := I) g₂
          + (-(metricTensor02 (I := I) g₂))) b =
        cov.toFun (metricTensor02 (I := I) g₂) b
          + cov.toFun (-(metricTensor02 (I := I) g₂)) b :=
      hcovOn.add hT₂ hT₂neg (Set.mem_univ b)
    rw [add_neg_cancel] at hsum
    have hzero : cov.toFun (0 : Π x : M,
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b = 0 :=
      hcovOn.zero (Set.mem_univ b)
    rw [hzero] at hsum
    -- `0 = cov T₂ b + cov (-T₂) b`, so `cov (-T₂) b = - cov T₂ b`.
    exact eq_neg_of_add_eq_zero_right hsum.symm
  -- Step 2: `cov (T₁ - T₂) b = cov T₁ b + cov (-T₂) b = cov T₁ b - cov T₂ b`.
  have hadd : cov.toFun (metricTensor02 (I := I) g₁
        + (-(metricTensor02 (I := I) g₂))) b =
      cov.toFun (metricTensor02 (I := I) g₁) b
        + cov.toFun (-(metricTensor02 (I := I) g₂)) b :=
    hcovOn.add hT₁ hT₂neg (Set.mem_univ b)
  -- `metricDiff02 = metricTensor02 g₁ + (-(metricTensor02 g₂))` as a section.
  have hdiff_eq : metricDiff02 (I := I) g₁ g₂ =
      metricTensor02 (I := I) g₁ + (-(metricTensor02 (I := I) g₂)) := by
    funext c
    simp only [metricDiff02, metricTensor02, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]
  calc metricDiff02Cov (I := I) g₀ g₁ g₂ b
      = cov.toFun (metricDiff02 (I := I) g₁ g₂) b := rfl
    _ = cov.toFun (metricTensor02 (I := I) g₁
          + (-(metricTensor02 (I := I) g₂))) b := by rw [hdiff_eq]
    _ = cov.toFun (metricTensor02 (I := I) g₁) b
          + cov.toFun (-(metricTensor02 (I := I) g₂)) b := hadd
    _ = cov.toFun (metricTensor02 (I := I) g₁) b
          - cov.toFun (metricTensor02 (I := I) g₂) b := by rw [hneg]; abel

/-! ## The intrinsic `2`-jet (second covariant derivative) of a metric difference

The `2`-jet term needs the **second** covariant derivative of a `(0,2)`-tensor
field, i.e. the iterated operator `tensor02CovIterate (LeviCivita g₀)`, valued in
the `(0,4)`-tensor bundle.  It is additive on differentiable `(0,2)`-tensor
sections, so on the metric difference it splits as the difference of the two
metric second covariant derivatives — exactly the structure of
`metricDiff02Cov_eq_sub`.  The supporting differentiability fact is that the first
covariant derivative `tensor02Cov (LeviCivita g₀)` of a *smooth* metric tensor is
itself a differentiable `(0,3)`-tensor section (from the inherited smoothness of
the induced `(0,2)`-tensor covariant derivative). -/

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- The first covariant derivative `tensor02Cov (LeviCivita g₀) (metricTensor02 g)`
of a smooth metric tensor is a differentiable `(0,3)`-tensor section at every
point.  This is the inherited `C^∞` smoothness of the induced `(0,2)`-tensor
covariant derivative (`tensor02Cov_isContMDiff`, applicable since the metric
section is smooth and `LeviCivita g₀` is a `C^∞` covariant derivative). -/
theorem metricTensor02Cov_mdiffAtTensor03
    (g₀ g : SmoothRiemannianMetric I M) (x : M) :
    MDiffAtTensor03 (I := I)
      ((tensor02Cov (LeviCivita (I := I) g₀)).toFun (metricTensor02 (I := I) g)) x := by
  classical
  -- The metric section is `C^∞` as a `(0,2)`-tensor total-space section.
  have hmetric : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (metricTensor02 (I := I) g b)) := g.contMDiff
  -- `tensor02Cov (LeviCivita g₀)` inherits `C^∞`-class smoothness.
  haveI hcov : CovariantDerivative.ContMDiffCovariantDerivative
      (tensor02Cov (LeviCivita (I := I) g₀)) ∞ :=
    tensor02Cov_isContMDiff (LeviCivita (I := I) g₀)
  -- The smoothness field consumes a `CMDiff[univ] (∞+1)` section and produces a
  -- `ContMDiffOn ... univ` of the covariant-derivative total-space section.
  have h_le : (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) + 1 := by rw [ENat.coe_top_add_one]
  have hmetric₁ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((∞ : WithTop ℕ∞) + 1)
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (metricTensor02 (I := I) g b)) Set.univ :=
    contMDiffOn_univ.mpr (hmetric.of_le h_le)
  have hcovOn := hcov.contMDiff
  have hsmooth :=
    hcovOn.contMDiff (σ := metricTensor02 (I := I) g) hmetric₁
  -- `hsmooth` is `ContMDiffOn` of the `(0,3)`-valued covariant-derivative section on
  -- `univ`; turn it into a global `ContMDiff` and extract `MDifferentiableAt` at `x`,
  -- which is exactly `MDiffAtTensor03`.
  exact (contMDiffOn_univ.mp hsmooth x).mdifferentiableAt (by simp)

/-- The second covariant derivative `∇^{g₀,2}(g₁ − g₂)` of the metric difference,
computed with the Levi-Civita connection of the base metric `g₀`.  This is the
iterated covariant derivative `tensor02CovIterate (LeviCivita g₀)` applied to the
`(0,2)`-tensor field `metricDiff02 g₁ g₂`, a `(0,4)`-tensor fibre element at each
point. -/
def metricDiff02CovIterate (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (b : M) :
    TangentSpace I b →L[ℝ]
      (TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) :=
  tensor02CovIterate (LeviCivita (I := I) g₀) (metricDiff02 (I := I) g₁ g₂) b

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- The second covariant derivative is additive in the metric difference: it
distributes over the `(0,2)`-tensor subtraction defining `metricDiff02`.  The
inner `(0,2)`-tensor covariant derivative is additive (the `add` axiom of
`tensor02Cov`), so it carries the subtraction inside; the outer `(0,3)`-tensor
covariant derivative is then additive on the two differentiable `(0,3)`-tensor
sections (`tensor03Cov_sub`), so the iterate splits as a difference.  This is the
`2`-jet analogue of `metricDiff02Cov_eq_sub`. -/
theorem metricDiff02CovIterate_eq_sub
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (b : M) :
    metricDiff02CovIterate (I := I) g₀ g₁ g₂ b =
      tensor02CovIterate (LeviCivita (I := I) g₀) (metricTensor02 (I := I) g₁) b
        - tensor02CovIterate (LeviCivita (I := I) g₀) (metricTensor02 (I := I) g₂) b := by
  classical
  set cov := LeviCivita (I := I) g₀ with hcov_def
  -- Inner `(0,2)`-tensor covariant derivative carries the subtraction inside (additivity
  -- of `tensor02Cov` on the two smooth metric sections), as a *section* equality.
  have hinner_eq : (tensor02Cov cov).toFun (metricDiff02 (I := I) g₁ g₂) =
      (tensor02Cov cov).toFun (metricTensor02 (I := I) g₁)
        - (tensor02Cov cov).toFun (metricTensor02 (I := I) g₂) := by
    funext c
    have h := metricDiff02Cov_eq_sub (I := I) g₀ g₁ g₂ c
    -- `metricDiff02Cov g₀ g₁ g₂ c = (tensor02Cov cov).toFun (metricDiff02 g₁ g₂) c` by def.
    have hlhs : metricDiff02Cov (I := I) g₀ g₁ g₂ c =
        (tensor02Cov cov).toFun (metricDiff02 (I := I) g₁ g₂) c := rfl
    rw [hlhs] at h
    rw [h]
    rfl
  -- The two metric first covariant derivatives are differentiable `(0,3)`-sections.
  have hS₁ : MDiffAtTensor03 (I := I)
      ((tensor02Cov cov).toFun (metricTensor02 (I := I) g₁)) b :=
    metricTensor02Cov_mdiffAtTensor03 (I := I) g₀ g₁ b
  have hS₂ : MDiffAtTensor03 (I := I)
      ((tensor02Cov cov).toFun (metricTensor02 (I := I) g₂)) b :=
    metricTensor02Cov_mdiffAtTensor03 (I := I) g₀ g₂ b
  calc metricDiff02CovIterate (I := I) g₀ g₁ g₂ b
      = (tensor03Cov cov).toFun
          ((tensor02Cov cov).toFun (metricDiff02 (I := I) g₁ g₂)) b := rfl
    _ = (tensor03Cov cov).toFun
          ((tensor02Cov cov).toFun (metricTensor02 (I := I) g₁)
            - (tensor02Cov cov).toFun (metricTensor02 (I := I) g₂)) b := by
        rw [hinner_eq]
    _ = (tensor03Cov cov).toFun
          ((tensor02Cov cov).toFun (metricTensor02 (I := I) g₁)) b
        - (tensor03Cov cov).toFun
          ((tensor02Cov cov).toFun (metricTensor02 (I := I) g₂)) b :=
        tensor03Cov_sub cov hS₁ hS₂
    _ = tensor02CovIterate cov (metricTensor02 (I := I) g₁) b
        - tensor02CovIterate cov (metricTensor02 (I := I) g₂) b := rfl

/-! ## Smoothness of the metric-difference jets as bundle sections

For the continuity of the intrinsic `2`-jet seminorm we need the three jet
sections (`(0,2)`, `(0,3)`, `(0,4)`) of the metric difference to be smooth
sections of their tensor bundles.  The `0`-jet is the metric-difference section,
smooth from the metric smoothness; the `1`-jet is the induced `(0,2)`-tensor
covariant derivative of a smooth section, smooth from `tensor02Cov_isContMDiff`;
the `2`-jet is the further `(0,3)`-tensor covariant derivative, whose smoothness we
build here by the same operator-to-bundle bridge used for the lower orders. -/

/-- Smoothness of the trilinear pairing scalar `b ↦ S b (Y b) (Z b) (W b)` for a
smooth `(0,3)`-tensor section `S` and smooth tangent sections `Y, Z, W`.  Three
applications of `ContMDiff.clm_bundle_apply` peel the slots off. -/
private theorem tensor03_pairing_contMDiff
    {S : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b)))
    {Y Z W : Π x : M, TangentSpace I x}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (Y b)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (Z b)))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (W b))) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => S b (Y b) (Z b) (W b)) := by
  -- `b ↦ S b (Y b)` : smooth `(0,2)`-section.
  have h1 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b (Y b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
      (b := fun b : M => b) (ϕ := fun b => S b) (v := fun b => Y b) hS hY
  -- `b ↦ S b (Y b) (Z b)` : smooth cotangent section.
  have h2 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) b (S b (Y b) (Z b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
      (b := fun b : M => b) (ϕ := fun b => S b (Y b)) (v := fun b => Z b) h1 hZ
  -- `b ↦ S b (Y b) (Z b) (W b)` : smooth scalar (trivial-bundle ℝ target).
  have h3 : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun b : M => TotalSpace.mk' ℝ (E := fun _ : M => ℝ) b (S b (Y b) (Z b) (W b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun _ : M => ℝ)
      (b := fun b : M => b) (ϕ := fun b => S b (Y b) (Z b)) (v := fun b => W b) h2 hW
  intro x
  exact (contMDiffAt_section (F := ℝ) (E := fun _ : M => ℝ) x).mp (h3 x)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- Smoothness of the four-slot scalar
`b ↦ ((tensor03Cov cov).toFun S b (Y b)) (Z b) (W b) (U b)` for a smooth
`(0,3)`-tensor section `S`, a `C^∞` tangent covariant derivative `cov`, and smooth
tangent sections.  The value expands via `tensor03CovAt_apply_of_diff_extend` into
the `tensor03Scalar` formula, each summand of which is smooth. -/
private theorem tensor03Cov_quad_apply_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {S : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b)))
    (Y Z W U : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => ((((tensor03Cov cov).toFun S x (Y x)) (Z x)) (W x)) (U x)) := by
  -- Expand the value as the `tensor03Scalar` formula.
  have h_eq : ∀ x : M,
      ((((tensor03Cov cov).toFun S x (Y x)) (Z x)) (W x)) (U x) =
        extDerivFun (I := I) (fun b => S b (Z b) (W b) (U b)) x (Y x)
          - S x (cov.toFun Z x (Y x)) (W x) (U x)
          - S x (Z x) (cov.toFun W x (Y x)) (U x)
          - S x (Z x) (W x) (cov.toFun U x (Y x)) := by
    intro x
    have hSx : MDiffAtTensor03 S x := (hS x).mdifferentiableAt (by simp)
    have hYx := (Y.contMDiff x).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    have hZx := (Z.contMDiff x).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    have hWx := (W.contMDiff x).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    have hUx := (U.contMDiff x).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    have h := tensor03CovAt_apply_of_diff_extend cov hSx hYx hZx hWx hUx
    rw [tensor03Cov_toFun, tensor03CovFun_apply, h]
    rfl
  -- (i) `b ↦ S b (Z b) (W b) (U b)` smooth scalar.
  have h_pair : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => S b (Z b) (W b) (U b)) :=
    tensor03_pairing_contMDiff hS Z.contMDiff W.contMDiff U.contMDiff
  -- (ii) `extDerivFun (...)` smooth cotangent section, applied to `Y` gives smooth scalar.
  have h_extDeriv : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] (Bundle.Trivial M ℝ) x)
        x (extDerivFun (I := I) (fun b => S b (Z b) (W b) (U b)) x)) :=
    cotangentCov_extDerivFun_smooth h_pair
  have h_extDeriv_Y : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => extDerivFun (I := I) (fun b => S b (Z b) (W b) (U b)) x (Y x)) := by
    have hap : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun x => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) x
          (extDerivFun (I := I) (fun b => S b (Z b) (W b) (U b)) x (Y x))) :=
      ContMDiff.clm_bundle_apply
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => (Bundle.Trivial M ℝ) x)
        (b := fun x : M => x)
        (ϕ := fun x => extDerivFun (I := I) (fun b => S b (Z b) (W b) (U b)) x)
        (v := fun x => Y x) h_extDeriv Y.contMDiff
    intro x
    exact (contMDiffAt_section (F := ℝ) (E := Bundle.Trivial M ℝ) x).mp (hap x)
  -- (iii)-(v) the three Christoffel-cross terms: `cov.toFun · x (Y x)` smooth tangent section,
  -- paired against `S` with the other two slots.
  have h_covApp : ∀ (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x => TotalSpace.mk' E (E := TangentSpace I) x (cov.toFun (fun y => V y) x (Y x))) := by
    intro V
    have hcovV : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun x => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) x
          (cov.toFun (fun y => V y) x)) :=
      cotangentCov_covApply_smooth cov V.contMDiff
    exact ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x)
      (b := fun x : M => x) (ϕ := fun x => cov.toFun (fun y => V y) x)
      (v := fun x => Y x) hcovV Y.contMDiff
  have h_t1 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => S x (cov.toFun Z x (Y x)) (W x) (U x)) :=
    tensor03_pairing_contMDiff hS (h_covApp Z) W.contMDiff U.contMDiff
  have h_t2 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => S x (Z x) (cov.toFun W x (Y x)) (U x)) :=
    tensor03_pairing_contMDiff hS Z.contMDiff (h_covApp W) U.contMDiff
  have h_t3 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => S x (Z x) (W x) (cov.toFun U x (Y x))) :=
    tensor03_pairing_contMDiff hS Z.contMDiff W.contMDiff (h_covApp U)
  have h_combined : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => extDerivFun (I := I) (fun b => S b (Z b) (W b) (U b)) x (Y x)
        - S x (cov.toFun Z x (Y x)) (W x) (U x)
        - S x (Z x) (cov.toFun W x (Y x)) (U x)
        - S x (Z x) (W x) (cov.toFun U x (Y x))) :=
    ((h_extDeriv_Y.sub h_t1).sub h_t2).sub h_t3
  exact h_combined.congr (fun x => h_eq x)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **Smoothness of the `(0,3)`-tensor covariant derivative output.** For a smooth
`(0,3)`-tensor section `S` and a `C^∞` tangent covariant derivative `cov`, the
covariant derivative `tensor03Cov cov S` is a smooth `(0,4)`-tensor section.  The
argument mirrors `tensor02Cov_isContMDiff`: three iterated applications of the
operator-to-bundle bridge `cotangentCov_clmSection_smooth_aux` reduce the target to
the four-slot scalar `tensor03Cov_quad_apply_smooth`. -/
private theorem tensor03Cov_output_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {S : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))) ∞
      (fun x : M => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))
        (E := fun x : M => TangentSpace I x →L[ℝ]
          (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))) x
        ((tensor03Cov cov).toFun S x)) := by
  -- Outermost bridge: reduce to `Y`-applied `(0,3)`-section smoothness.
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ]
      (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))
    (φ := fun x => (tensor03Cov cov).toFun S x)
  intro Y
  -- Middle bridge: reduce to `(Y, Z)`-applied `(0,2)`-section smoothness.
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ))
    (φ := fun x => (tensor03Cov cov).toFun S x (Y x))
  intro Z
  -- Inner bridge: reduce to `(Y, Z, W)`-applied cotangent-section smoothness.
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x => (tensor03Cov cov).toFun S x (Y x) (Z x))
  intro W
  -- Innermost bridge: reduce to the four-slot scalar.
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x => (tensor03Cov cov).toFun S x (Y x) (Z x) (W x))
  intro U
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => ((((tensor03Cov cov).toFun S x (Y x)) (Z x)) (W x)) (U x)) :=
    tensor03Cov_quad_apply_smooth cov hS Y Z W U
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change ((((tensor03Cov cov).toFun S y (Y y)) (Z y)) (W y)) (U y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x
      ⟨y, ((((tensor03Cov cov).toFun S y (Y y)) (Z y)) (W y)) (U y)⟩).2
  rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The metric `2`-jet (second covariant derivative) is a smooth `(0,4)`-tensor
section.**  The first covariant derivative of a smooth metric is a smooth
`(0,3)`-section (`tensor02Cov_isContMDiff`), and its further `(0,3)`-tensor
covariant derivative is smooth by `tensor03Cov_output_contMDiff`. -/
theorem tensor02CovIterate_metric_contMDiff
    (g₀ g : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))) ∞
      (fun x : M => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))
        (E := fun x : M => TangentSpace I x →L[ℝ]
          (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))) x
        (tensor02CovIterate (LeviCivita (I := I) g₀) (metricTensor02 (I := I) g) x)) := by
  haveI hcov : CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivita (I := I) g₀) ∞ := inferInstance
  -- The first covariant derivative `tensor02Cov (LeviCivita g₀) (metricTensor02 g)` is a smooth
  -- `(0,3)`-section.
  have h_metric : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (metricTensor02 (I := I) g b)) := g.contMDiff
  have h_le : (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) + 1 := by rw [ENat.coe_top_add_one]
  have h_metric₁ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((∞ : WithTop ℕ∞) + 1)
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (metricTensor02 (I := I) g b)) Set.univ :=
    contMDiffOn_univ.mpr (h_metric.of_le h_le)
  have hS₃ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        ((tensor02Cov (LeviCivita (I := I) g₀)).toFun (metricTensor02 (I := I) g) x)) :=
    contMDiffOn_univ.mp
      ((tensor02Cov_isContMDiff (LeviCivita (I := I) g₀)).contMDiff.contMDiff
        (σ := metricTensor02 (I := I) g) h_metric₁)
  -- The further `(0,3)`-tensor covariant derivative is a smooth `(0,4)`-section.
  exact tensor03Cov_output_contMDiff (LeviCivita (I := I) g₀) hS₃

/-! ## Continuity of the intrinsic fibre op-norm of a smooth tensor section

The Riemannian fibre norms in the `2`-jet seminorm are realised through the
const-`1` fibre isometries (`biForm₂ToModelₗᵢ`, `triFormToModelₗᵢ`,
`quadFormToModelₗᵢ`), which are norm-preserving and act on the *fixed* fibre `E`
(since `TangentSpace I x = E`); hence the fibre norm equals the operator norm of
the curried multilinear form `σ x`.  For a continuous total-space section `σ` of a
vector bundle that is a *continuous Riemannian bundle*, the real-valued map
`x ↦ ‖σ x‖` is continuous: it equals the square root of the (continuous) fibre
inner product `⟪σ x, σ x⟫`.  We use this with the operator-norm comparison built
into the chart-fibre Riemannian metric. -/

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **Continuity of a fibre norm of a continuous section of a continuous Riemannian
bundle.**  For a continuous total-space section `σ` of a vector bundle whose fibres
carry an inner product depending continuously on the base point, the real-valued
map `x ↦ ‖σ x‖` is continuous (it is the square root of the continuous fibre inner
product `⟪σ x, σ x⟫`). -/
private theorem continuous_riemannian_fiber_norm_of_continuous_section
    {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]
    {V₀ : M → Type*} [∀ x, NormedAddCommGroup (V₀ x)] [∀ x, InnerProductSpace ℝ (V₀ x)]
    [TopologicalSpace (TotalSpace F₀ V₀)] [FiberBundle F₀ V₀] [VectorBundle ℝ F₀ V₀]
    [IsContinuousRiemannianBundle F₀ V₀]
    {σ : Π x : M, V₀ x}
    (hσ : Continuous (fun x : M => TotalSpace.mk' F₀ (E := V₀) x (σ x))) :
    Continuous (fun x : M => ‖σ x‖) := by
  have h_inner : Continuous (fun x : M => (inner ℝ (σ x) (σ x) : ℝ)) :=
    Continuous.inner_bundle (F := F₀) (E := V₀) hσ hσ
  have h_eq : (fun x : M => ‖σ x‖) = fun x : M => Real.sqrt (inner ℝ (σ x) (σ x)) := by
    funext x
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [h_eq]
  exact Real.continuous_sqrt.comp h_inner

/-! ## The intrinsic `2`-jet seminorm of the metric difference

The `2`-jet seminorm of `g₁ − g₂` at `x` is the sum of the three Riemannian fibre
norms of its `0`-, `1`-, and `2`-jets, realised through the const-`1` fibre
isometries `biForm₂ToModelₗᵢ` (bilinear, `0`-jet), `triFormToModelₗᵢ` (tri,
`1`-jet) and `quadFormToModelₗᵢ` (quad, `2`-jet).  Because these isometries act on
the fixed model fibre `E` (via `TangentSpace I x = E`) and preserve the norm, each
summand is the operator norm of the corresponding curried multilinear form. -/

/-- The intrinsic `2`-jet seminorm of the metric difference `g₁ − g₂` at `x`,
measured with the base metric `g₀`'s Levi-Civita connection: the sum of the
Riemannian fibre norms of the `0`-jet (`metricDiff02`), the `1`-jet
(`metricDiff02Cov`, the first covariant derivative) and the `2`-jet
(`metricDiff02CovIterate`, the iterated/second covariant derivative), each
realised through the const-`1` fibre isometry of the appropriate arity. -/
def metricDiff2JetNorm (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) : ℝ :=
  ‖biForm₂ToModelₗᵢ (TangentSpace I x) (metricDiff02 (I := I) g₁ g₂ x)‖
    + ‖triFormToModelₗᵢ (TangentSpace I x) (metricDiff02Cov (I := I) g₀ g₁ g₂ x)‖
    + ‖quadFormToModelₗᵢ (TangentSpace I x) (metricDiff02CovIterate (I := I) g₀ g₁ g₂ x)‖

/-- The intrinsic `2`-jet seminorm equals the sum of the operator norms of the
three jet tensors (the isometries are norm-preserving). -/
theorem metricDiff2JetNorm_eq_opNorm_sum
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    metricDiff2JetNorm (I := I) g₀ g₁ g₂ x =
      ‖metricDiff02 (I := I) g₁ g₂ x‖
        + ‖metricDiff02Cov (I := I) g₀ g₁ g₂ x‖
        + ‖metricDiff02CovIterate (I := I) g₀ g₁ g₂ x‖ := by
  unfold metricDiff2JetNorm
  rw [(biForm₂ToModelₗᵢ (TangentSpace I x)).norm_map,
    (triFormToModelₗᵢ (TangentSpace I x)).norm_map,
    (quadFormToModelₗᵢ (TangentSpace I x)).norm_map]

/-- The intrinsic `2`-jet seminorm is non-negative. -/
theorem metricDiff2JetNorm_nonneg
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    0 ≤ metricDiff2JetNorm (I := I) g₀ g₁ g₂ x := by
  unfold metricDiff2JetNorm
  positivity

/-! ## The quantitative pointwise Riemannian `2`-jet-Lipschitz bound

The mathematically correct target — confirmed against the dependence of
`deTurckRicciRHS g_bg g x` on the **`2`-jet** of `g` (the Ricci summand is affine
in the second chart-derivatives `∂²g`, `chartRicci_affine_in_d2g`; the Lie
summand `𝓛_{deTurckVF g g_bg} g` carries `∂g` and `∂²g` via the Christoffel
symbols of `deTurckVF`) — is, for `g₁, g₂` in an `R`-ball around `g₀` and all
`x : M`,

  `‖deTurckRicciRHS g_bg g₁ x − deTurckRicciRHS g_bg g₂ x‖_{g₀,x}`
    `≤ C(R) · ( ‖(g₁−g₂)(x)‖_{g₀,x} + ‖∇^{g₀}(g₁−g₂)(x)‖ + ‖∇^{g₀,2}(g₁−g₂)(x)‖ )`

with all fibre norms Riemannian and `C(R)` coming from the (continuous,
compact-bounded) coefficient functions of the quasilinear chart formulas.  The
value-only inequality (`0`-jet right-hand side) is *false*: with `g₂ = g₁ +
ε·χ·H`, `χ(x) = 0`, `∂²χ(x) ≠ 0` one has `(g₁−g₂)(x) = 0` while the second-order
part of the RHS difference at `x` is nonzero.

The full intrinsic `2`-jet seminorm of the metric difference is now available and
HLCC-free, with all fibre norms Riemannian (realised through the const-`1` fibre
isometries `biForm₂ToModelₗᵢ` / `triFormToModelₗᵢ` / `quadFormToModelₗᵢ`):

* the `0`-jet term `‖(g₁−g₂)(x)‖_{g₀,x}` is the `(0,2)` fibre norm of
  `metricDiff02 g₁ g₂ x`;
* the `1`-jet term `‖∇^{g₀}(g₁−g₂)(x)‖` is the fibre norm of the `(0,3)`-tensor
  `metricDiff02Cov g₀ g₁ g₂ x` (`metricDiff02Cov_eq_sub` expresses it as the
  difference of the two metric covariant derivatives);
* the `2`-jet term `‖∇^{g₀,2}(g₁−g₂)(x)‖` is the fibre norm of the `(0,4)`-tensor
  `metricDiff02CovIterate g₀ g₁ g₂ x` (the iterated covariant derivative,
  `metricDiff02CovIterate_eq_sub` expresses it as a difference; smoothness of the
  two metric `2`-jets is `tensor02CovIterate_metric_contMDiff`).

`metricDiff2JetNorm` packages the sum of the three Riemannian fibre norms, with
non-negativity (`metricDiff2JetNorm_nonneg`).

The remaining genuinely missing piece before the displayed inequality can be
discharged with a finite `C(R)` is the analytic core:

`-- BLOCKED:`

**(A) Quasilinear-coefficient apparatus (the analytic core).**  Each chart-frame
scalar component `rhsDiff(x)(eᵢ, eⱼ)` must be exhibited as an explicit smooth
function of the chart `2`-jet `(g, ∂g, ∂²g)` of `g`, *affine* in `∂²g` (from the
Ricci summand, `chartRicci_affine_in_d2g`) and quasilinear in `(g, ∂g, ∂²g)`
(from the Christoffel-built Lie summand), with all coefficients (entries of the
inverse Gram matrix, Christoffel symbols and their derivatives) continuous in `g`
and hence — over the compact `R`-ball of admissible `2`-jets — uniformly bounded.
The difference `rhsDiff(x)(eᵢ, eⱼ)` is then, by a mean-value estimate on this
smooth jet-function, Lipschitz in the chart `2`-jet of `g₁ − g₂` with the
displayed constant.  This explicit coefficient expansion (inverse-Gram
perturbation, Christoffel and Christoffel-derivative bounds tied to
`christoffel_Ck_bound_from_metric_Ck1`, and the affine-in-`∂²g` decomposition
extracted from `chartRicciSecondOrderPrincipalSymbol` and its first-order
remainder) is several thousand lines of new infrastructure that does not yet
exist as a *pointwise* (rather than integrated `Hᵏ`) statement. -/
theorem deTurck_rhs_pointwise_riemannian_jetLipschitz_target : True := trivial

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
