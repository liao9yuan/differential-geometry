import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.JinvContinuity
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.InnerLowerBound
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian
import DifferentialGeometry.Tensor.RSTensor.TangentRiemannian
import DifferentialGeometry.Integral.L2.PointwiseInner.Defs
import DifferentialGeometry.Integral.L2.PointwiseInner.DualMetric
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Module.Multilinear.Topology
import Mathlib.Topology.FiberBundle.Trivialization
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Chart-local continuity blocks for the `(r, s)`-tensor inner product

For a smooth manifold `M` modelled on `(E, H)` with model `I` and a smooth
Riemannian metric `g`, this file packages a partial proof tree towards
pointwise basepoint continuity of the `(r, s)`-tensor inner product. The
deliverables are the early building blocks (Steps 2 and 3 in the
dispatch's framing); they appear as named theorems usable directly by
downstream chart-local arguments.

## Delivered results

* `chartJ_apply_chartBasisVecFiber_continuousOn` — the forward chart-Jacobian
  applied to a chart-`α` basis fibre is the constant model basis vector, and
  hence trivially continuous on the chart-`α` base set.
* `metric_inner_chartBasisFibers_continuousOn` — the metric pairing of two
  chart-`α` basis fibres is continuous on the chart-`α` base set; this is
  the `ContinuousOn` projection of `chartGramMatrix_entry_contMDiffOn`.
* `separableFormAt_chartBasisFibers_eval_continuousOn` — the separable
  `(0, r)`-form built on chart-`α` basis fibres, evaluated on another
  chart-`α` basis-fibre tuple, is continuous on the chart-`α` base set;
  reduces to a finite product of `metric_inner_chartBasisFibers_continuousOn`
  terms.

## Bundle-section continuity (Steps 5 to 7)

We deliver three additional building blocks that work entirely with
continuous bundle sections (total-space-valued) and never extract an
`M → E` function from such a section.

* `triv_symm_apply_const_continuousOn_baseSet` — for any fixed model
  vector `v : E`, the symm-image section
  `b ↦ TotalSpace.mk' E b ((triv α).symm b v)` is continuous on the
  chart-`α` base set. This follows from `Trivialization.continuousOn_symm`
  composed with the continuous map `b ↦ (b, v)`.
* `chartBasisVec_continuousOn_baseSet` — the chart-`α` basis section
  `chartBasisVec α k` is continuous on the chart-`α` base set. Special
  case of the above with `v = (chartModelBasis E) k`.
* `metric_inner_section_const_continuousOn` — for any two continuous
  bundle sections produced as `(triv α).symm b · v` images, the metric
  pairing `g.inner b (X b) (Y b)` is continuous on the chart-`α` base set.
  Delivered through `ContinuousOn.inner_bundle` with the diamond between
  the project's `tangentSpace_normedAddCommGroup`/`tangentSpace_normedSpace`
  and Mathlib's `RiemannianBundle (TangentSpace I)`-derived instances
  resolved by a local `attribute [-instance]` scope, mirroring the
  `Continuous`-variant in `Tensor/RSTensor/TangentRiemannian.lean`.

## Remaining technical gap

The headline target `tensorInnerPointwise_continuousOn_baseSet` for fixed
model tensors `T₀, T₁ : TensorRSModel r s ℝ E` is not delivered here. Any
expansion of the bilinear form in a fixed basis of the model fibre
introduces evaluations of the form `g.inner b X(b) v` for `X` a
continuous bundle section and `v : E` a constant model vector. The
constant section `b ↦ TotalSpace.mk' E b v` is not a continuous bundle
section in general (its trivialised projection is
`b ↦ tangentCoordChange I b α b v`, whose `b`-continuity is not delivered
by `continuousOn_tangentCoordChange`), so `ContinuousOn.inner_bundle` is
not directly applicable. Closing the gap requires operator-norm
continuity of the bare `b ↦ (triv α).symmL ℝ b ∈ E →L[ℝ] E` on the base
set, of which only the wrapped form (continuous at the centre by
`chartJinv_wrapped_continuousAt`) is currently delivered. The bundle-
section continuity facts shipped below are precisely the building blocks
any closure of the gap will need.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Step 2: forward chart-Jacobian on chart-`α` basis fibres -/

/-- The forward chart-Jacobian `chartJ α b` applied to the chart-`α` basis
fibre `chartBasisVecFiber α i b` is the constant model basis vector
`chartModelBasis E i` on the chart-`α` base set; hence trivially continuous
in `b`. -/
theorem chartJ_apply_chartBasisVecFiber_continuousOn
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M => chartJ (I := I) (M := M) α b
        (chartBasisVecFiber (I := I) α i b))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have heq : ∀ b ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      chartJ (I := I) (M := M) α b
          (chartBasisVecFiber (I := I) α i b) = (chartModelBasis E) i := by
    intro b hb
    unfold chartJ chartBasisVecFiber
    exact (trivializationAt E (TangentSpace I) α).continuousLinearMapAt_symmL hb
      ((chartModelBasis E) i)
  refine ContinuousOn.congr ?_ (fun b hb => heq b hb)
  exact continuousOn_const

/-! ## Step 3: metric pairing on chart-`α` basis-fibre pairs -/

/-- The metric pairing of two chart-`α` basis fibres is continuous on the
chart-`α` base set. This is the `ContinuousOn` projection of the chart-Gram
matrix entry smoothness `chartGramMatrix_entry_contMDiffOn`. -/
theorem metric_inner_chartBasisFibers_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M =>
        g.inner b
          (chartBasisVecFiber (I := I) α i b)
          (chartBasisVecFiber (I := I) α j b))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have hsmooth : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => chartGramMatrix g α b i j)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartGramMatrix_entry_contMDiffOn (I := I) g α i j
  have hcont : ContinuousOn (fun b : M => chartGramMatrix g α b i j)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    hsmooth.continuousOn
  refine hcont.congr ?_
  intro b _
  exact (chartGramMatrix_apply g α b i j).symm

/-! ## Step 4: separable `(0, r)`-form evaluated at chart-basis-fibre tuples -/

/-- The separable `(0, r)`-form built on chart-`α` basis fibres, evaluated
on another chart-`α` basis-fibre tuple, is continuous on the chart-`α` base
set. This is a finite product of metric inner products on chart-`α` basis
fibres, each continuous on the base set by
`metric_inner_chartBasisFibers_continuousOn`. -/
theorem separableFormAt_chartBasisFibers_eval_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M) (r : ℕ)
    (Idx Jdx : Fin r → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M =>
        separableFormAt (I := I) (M := M) g b r
          (fun k : Fin r => chartBasisVecFiber (I := I) α (Idx k) b)
          (fun k : Fin r => chartBasisVecFiber (I := I) α (Jdx k) b))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have heq : ∀ b : M,
      separableFormAt (I := I) (M := M) g b r
          (fun k : Fin r => chartBasisVecFiber (I := I) α (Idx k) b)
          (fun k : Fin r => chartBasisVecFiber (I := I) α (Jdx k) b) =
        ∏ k : Fin r, g.inner b
          (chartBasisVecFiber (I := I) α (Idx k) b)
          (chartBasisVecFiber (I := I) α (Jdx k) b) := by
    intro b
    rw [separableFormAt_apply]
  refine ContinuousOn.congr ?_ (fun b _ => heq b)
  refine continuousOn_finset_prod _ (fun k _ => ?_)
  exact metric_inner_chartBasisFibers_continuousOn (I := I) (M := M) g α
    (Idx k) (Jdx k)

/-! ## Step 5: continuous bundle sections produced by the trivialisation symm -/

/-- For any fixed model vector `v : E`, the symm-image section
`b ↦ TotalSpace.mk' E b ((triv α).symm b v)` is continuous on the
chart-`α` base set, as a total-space-valued function. This follows from
`Trivialization.continuousOn_symm` composed with the continuous map
`b ↦ (b, v) : M → M × E`. -/
theorem triv_symm_apply_const_continuousOn_baseSet
    (α : M) (v : E) :
    ContinuousOn
      (fun b : M => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) b
        ((trivializationAt E (TangentSpace I) α).symm b v))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  -- The total-space-valued symm map is continuous on `baseSet ×ˢ univ`.
  have hsymm :
      ContinuousOn
        (fun z : M × E => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          z.1 ((trivializationAt E (TangentSpace I) α).symm z.1 z.2))
        ((trivializationAt E (TangentSpace I) α).baseSet ×ˢ Set.univ) :=
    (trivializationAt E (TangentSpace I) α).continuousOn_symm
  -- Compose with `b ↦ (b, v) : M → M × E`.
  have hcomp : Continuous (fun b : M => (b, v)) :=
    continuous_id.prodMk continuous_const
  have hmaps :
      Set.MapsTo (fun b : M => (b, v))
        (trivializationAt E (TangentSpace I) α).baseSet
        ((trivializationAt E (TangentSpace I) α).baseSet ×ˢ Set.univ) := by
    intro b hb
    exact ⟨hb, Set.mem_univ _⟩
  exact hsymm.comp hcomp.continuousOn hmaps

/-- The chart-`α` basis section `chartBasisVec α k` is continuous on the
chart-`α` base set, as a total-space-valued function. Special case of
`triv_symm_apply_const_continuousOn_baseSet` with `v = (chartModelBasis E) k`,
unfolding the definition `chartBasisVec α k b = TotalSpace.mk' E b
((triv α).symm b ((chartModelBasis E) k))`. -/
theorem chartBasisVec_continuousOn_baseSet
    (α : M) (k : Fin (Module.finrank ℝ E)) :
    ContinuousOn (chartBasisVec (I := I) α k)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  unfold chartBasisVec chartBasisVecFiber
  exact triv_symm_apply_const_continuousOn_baseSet (I := I) (M := M) α
    ((chartModelBasis E) k)

/-! ## Step 6: diamond-cleaned `ContinuousOn` of the metric inner product

The Mathlib lemma `ContinuousOn.inner_bundle` requires an
`IsContinuousRiemannianBundle E (TangentSpace I)` instance on the
tangent bundle. The project's `SmoothRiemannianMetric I M` provides this
through Mathlib's `RiemannianBundle` mechanism, but installing the
mechanism on the tangent bundle creates a diamond with the project's
default `tangentSpace_normedAddCommGroup` / `tangentSpace_normedSpace`
instances. We resolve the diamond locally on a private auxiliary lemma
using `attribute [-instance]`, mirroring the `Continuous`-variant
`Tensor/RSTensor/TangentRiemannian.lean::continuous_g_inner_aux`. The
scalar `M → ℝ` conclusion is independent of the disabled instances and
survives outside the local scope. -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private lemma continuousOn_g_inner_aux
    (g : SmoothRiemannianMetric I M)
    {v w : ∀ x : M, TangentSpace I x} {s : Set M}
    (hv : ContinuousOn (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (v x)) s)
    (hw : ContinuousOn (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (w x)) s) :
    ContinuousOn (fun b : M => g.inner b (v b) (w b)) s := by
  -- Install Mathlib's `RiemannianBundle` derived from `g`. Going through
  -- `toContinuousRiemannianMetric` makes the `IsContinuousRiemannianBundle`
  -- instance discoverable by typeclass inference.
  letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  have h := ContinuousOn.inner_bundle (F := E) (B := M)
    (E := (TangentSpace I : M → Type _)) (b := fun x => x) (v := v) (w := w)
    (s := s) hv hw
  refine h.congr ?_
  intro b _
  rfl

/-- Public `ContinuousOn` version: the metric pairing of two continuous
bundle sections (total-space-valued) is continuous on any set on which
both sections are continuous. The result is a scalar `M → ℝ` function and
is independent of the diamond-handling internals. -/
theorem metric_inner_sections_continuousOn
    (g : SmoothRiemannianMetric I M)
    {v w : ∀ x : M, TangentSpace I x} {s : Set M}
    (hv : ContinuousOn (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (v x)) s)
    (hw : ContinuousOn (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (w x)) s) :
    ContinuousOn (fun b : M => g.inner b (v b) (w b)) s :=
  continuousOn_g_inner_aux (I := I) (M := M) g hv hw

/-! ## Step 7: metric inner of a chart-basis fibre and a symm-image fibre

The metric pairing
`g.inner b (chartBasisVecFiber α k b) ((triv α).symm b v)`
is continuous on the chart-`α` base set, for any fixed `k` and `v : E`.
This combines Step 5 (continuity of each section) with Step 6. -/

/-- The metric pairing of the chart-`α` basis fibre and the symm-image of a
constant model vector is continuous on the chart-`α` base set. -/
theorem metric_inner_chartBasisFiber_trivSymm_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) (v : E) :
    ContinuousOn
      (fun b : M =>
        g.inner b
          (chartBasisVecFiber (I := I) α k b)
          ((trivializationAt E (TangentSpace I) α).symm b v))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have hX : ContinuousOn (chartBasisVec (I := I) α k)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartBasisVec_continuousOn_baseSet (I := I) (M := M) α k
  have hY : ContinuousOn
      (fun b : M => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) b
        ((trivializationAt E (TangentSpace I) α).symm b v))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    triv_symm_apply_const_continuousOn_baseSet (I := I) (M := M) α v
  -- The chart-basis section `chartBasisVec α k` has fibre value
  -- `chartBasisVecFiber α k b`. Unfold and apply Step 6.
  have h := metric_inner_sections_continuousOn (I := I) (M := M) (E := E) g
    (v := fun b => chartBasisVecFiber (I := I) α k b)
    (w := fun b => (trivializationAt E (TangentSpace I) α).symm b v)
    (s := (trivializationAt E (TangentSpace I) α).baseSet) hX hY
  exact h

/-- The metric pairing of two symm-image fibres of constant model vectors
is continuous on the chart-`α` base set. -/
theorem metric_inner_trivSymm_trivSymm_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M) (v w : E) :
    ContinuousOn
      (fun b : M =>
        g.inner b
          ((trivializationAt E (TangentSpace I) α).symm b v)
          ((trivializationAt E (TangentSpace I) α).symm b w))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have hX : ContinuousOn
      (fun b : M => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) b
        ((trivializationAt E (TangentSpace I) α).symm b v))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    triv_symm_apply_const_continuousOn_baseSet (I := I) (M := M) α v
  have hY : ContinuousOn
      (fun b : M => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) b
        ((trivializationAt E (TangentSpace I) α).symm b w))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    triv_symm_apply_const_continuousOn_baseSet (I := I) (M := M) α w
  exact metric_inner_sections_continuousOn (I := I) (M := M) (E := E) g
    (v := fun b => (trivializationAt E (TangentSpace I) α).symm b v)
    (w := fun b => (trivializationAt E (TangentSpace I) α).symm b w)
    (s := (trivializationAt E (TangentSpace I) α).baseSet) hX hY

/-! ## Headline pointwise norm comparison on `tsupport(POU_α)`

The uniform positive lower bound `chartTensorInnerPointwise_rs_model g r s α b T T ≥ ε`
for `‖T‖ = 1` (delivered upstream as `exists_chartTensorInnerPointwise_rs_model_lower_bound_on_pouTsupport`)
rescales by bilinearity to the homogeneous-degree-two estimate
`‖T‖² ≤ ε⁻¹ · chartTensorInnerPointwise_rs_model g r s α b T T`
for every `T`, valid uniformly on the closed support of the chart-atlas
partition-of-unity weight at `α`. Composing with the bridge identity
`chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise` produces a parallel
bundle-form comparison through the chart-`(α, b)`-twist. -/

section HeadlineNormComparison

variable [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]

/-- Rescaling form of the uniform lower bound: on `tsupport(POU_α)`,
`‖T‖² ≤ ε⁻¹ · chartTensorInnerPointwise_rs_model g r s α b T T` for every
`T : TensorRSModel r s ℝ E`, with the same `ε > 0` produced by the unit-sphere
lower bound. The case `T = 0` is handled separately; the non-zero case rescales
by `‖T‖` and uses bilinearity of the chart-frame quadratic form together with
the unit-sphere bound on the unit vector `‖T‖⁻¹ • T`. -/
lemma sq_norm_le_inv_eps_mul_chartTensorInnerPointwise_rs_model_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {ε : ℝ} (hε : 0 < ε)
    (h_lb : ∀ b : M, b ∈ tsupport (fun x : M =>
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
      ∀ T : TensorRSModel r s ℝ E, ‖T‖ = 1 →
        ε ≤ chartTensorInnerPointwise_rs_model (I := I) (M := M)
          g r s α b T T) :
    ∀ b : M, b ∈ tsupport (fun x : M =>
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
      ∀ T : TensorRSModel r s ℝ E,
        ‖T‖ ^ 2 ≤ ε⁻¹ *
          chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T T := by
  classical
  intro b hb T
  -- `tsupport ⊆ baseSet`: gives non-negativity of the diagonal.
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  have hQ_nn : 0 ≤ chartTensorInnerPointwise_rs_model
      (I := I) (M := M) g r s α b T T :=
    chartTensorInnerPointwise_rs_model_nonneg
      (I := I) (M := M) g r s α hb_base T
  by_cases hT0 : T = 0
  · -- The zero tensor: both sides are zero.
    subst hT0
    -- `‖(0 : TensorRSModel r s ℝ E)‖ = 0` and the quadratic form vanishes.
    have h_left : ‖(0 : TensorRSModel r s ℝ E)‖ ^ 2 = 0 := by
      simp
    have h_right : chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r s α b (0 : TensorRSModel r s ℝ E)
          (0 : TensorRSModel r s ℝ E) = 0 := by
      -- Rewrite the first `0` as `(0 : ℝ) • (0 : TensorRSModel r s ℝ E)` and
      -- pull the scalar out using `_smul_left`.
      have h_zero_smul :
          chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r s α b
              ((0 : ℝ) • (0 : TensorRSModel r s ℝ E))
              (0 : TensorRSModel r s ℝ E) =
          (0 : ℝ) *
            chartTensorInnerPointwise_rs_model
              (I := I) (M := M) g r s α b
                (0 : TensorRSModel r s ℝ E) (0 : TensorRSModel r s ℝ E) :=
        chartTensorInnerPointwise_rs_model_smul_left
          (I := I) (M := M) g r s α b 0 (0 : TensorRSModel r s ℝ E)
          (0 : TensorRSModel r s ℝ E)
      have h_eq : (0 : TensorRSModel r s ℝ E) =
          ((0 : ℝ) • (0 : TensorRSModel r s ℝ E)) := by rw [zero_smul]
      calc chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r s α b
              (0 : TensorRSModel r s ℝ E) (0 : TensorRSModel r s ℝ E)
          = chartTensorInnerPointwise_rs_model
              (I := I) (M := M) g r s α b
                ((0 : ℝ) • (0 : TensorRSModel r s ℝ E))
                (0 : TensorRSModel r s ℝ E) := by rw [← h_eq]
        _ = (0 : ℝ) *
            chartTensorInnerPointwise_rs_model
              (I := I) (M := M) g r s α b
                (0 : TensorRSModel r s ℝ E) (0 : TensorRSModel r s ℝ E) :=
              h_zero_smul
        _ = 0 := by ring
    rw [h_left, h_right, mul_zero]
  · -- Non-zero tensor: rescale by `‖T‖` and apply the unit-sphere bound.
    have hT_ne : ‖T‖ ≠ 0 := norm_ne_zero_iff.mpr hT0
    have hT_pos : 0 < ‖T‖ := (norm_pos_iff).mpr hT0
    -- The unit-norm rescaling `T' := ‖T‖⁻¹ • T` has norm one. Use the explicit
    -- `NormedSpace`-derived `NormSMulClass` instance to compute the norm.
    letI : NormSMulClass ℝ (TensorRSModel r s ℝ E) :=
      NormedSpace.toNormSMulClass
    set T' : TensorRSModel r s ℝ E := ‖T‖⁻¹ • T with hT'_def
    have hT'_norm : ‖T'‖ = 1 := by
      rw [hT'_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hT_pos]
      field_simp
    -- The lower bound at `T'`.
    have h_T' : ε ≤ chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r s α b T' T' :=
      h_lb b hb T' hT'_norm
    -- Bilinearity: `chartTensorInnerPointwise_rs_model g r s α b T' T' =
    --   (‖T‖⁻¹ * ‖T‖⁻¹) * chartTensorInnerPointwise_rs_model g r s α b T T`.
    have h_bilin :
        chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T' T' =
          (‖T‖⁻¹ * ‖T‖⁻¹) *
            chartTensorInnerPointwise_rs_model
              (I := I) (M := M) g r s α b T T := by
      rw [hT'_def]
      rw [chartTensorInnerPointwise_rs_model_smul_left
        (I := I) (M := M) g r s α b ‖T‖⁻¹ T (‖T‖⁻¹ • T)]
      rw [chartTensorInnerPointwise_rs_model_smul_right
        (I := I) (M := M) g r s α b ‖T‖⁻¹ T T]
      ring
    rw [h_bilin] at h_T'
    -- Multiply both sides by `‖T‖²`. Both factors are non-negative.
    have h_sq_pos : 0 < ‖T‖ ^ 2 := by positivity
    have h_mul : ε * ‖T‖ ^ 2 ≤
        ((‖T‖⁻¹ * ‖T‖⁻¹) *
          chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r s α b T T) * ‖T‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h_T' (le_of_lt h_sq_pos)
    -- Simplify the RHS to `chartTensorInnerPointwise_rs_model g r s α b T T`.
    have h_rhs :
        ((‖T‖⁻¹ * ‖T‖⁻¹) *
          chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r s α b T T) * ‖T‖ ^ 2 =
          chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r s α b T T := by
      have h_sq_eq : ‖T‖ ^ 2 = ‖T‖ * ‖T‖ := by ring
      rw [h_sq_eq]
      field_simp
    rw [h_rhs] at h_mul
    -- From `ε * ‖T‖² ≤ Q`, divide by `ε > 0` to obtain `‖T‖² ≤ ε⁻¹ * Q`.
    -- Use `(le_div_iff₀ hε)` to rewrite the target.
    rw [show ε⁻¹ * chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r s α b T T =
        chartTensorInnerPointwise_rs_model
          (I := I) (M := M) g r s α b T T / ε by
      rw [div_eq_inv_mul]]
    exact (le_div_iff₀ hε).mpr (by linarith [h_mul])

/-- **Headline pointwise norm comparison (chart-frame form).**

For a closed Riemannian manifold `(M, g)`, a chart base point `α`, and ranks
`(r, s)`, there is a non-negative constant `K` such that the Euclidean square
norm of a model `(r, s)`-tensor is bounded above by `K` times the chart-frame
diagonal quadratic form, uniformly on the closed support of the chart-atlas
partition-of-unity weight at `α`. -/
theorem chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r s ℝ E,
          ‖T‖ ^ 2 ≤ K * chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r s α b T T := by
  classical
  -- Extract the uniform positive lower bound on the unit sphere.
  obtain ⟨ε, hε_pos, h_lb⟩ :=
    exists_chartTensorInnerPointwise_rs_model_lower_bound_on_pouTsupport
      (I := I) (M := M) g r s α
  refine ⟨ε⁻¹, le_of_lt (inv_pos.mpr hε_pos), ?_⟩
  -- Apply the rescaling lemma.
  exact sq_norm_le_inv_eps_mul_chartTensorInnerPointwise_rs_model_on_pouTsupport
    (I := I) (M := M) g r s α hε_pos h_lb

/-- **Headline pointwise norm comparison (bundle-inner form, via the twist).**

The model-tensor Euclidean square norm is bounded by `K` times the
bundle-fibre `(r, s)`-inner product on the chart-`(α, b)`-twisted tensor,
uniformly on `tsupport(POU_α)`. This is the chart-frame form composed with
the bridge identity `chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise`. -/
theorem chartTrivializationNorm_le_const_mul_tensorInnerPointwise_chartRSTwist_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r s ℝ E,
          ‖T‖ ^ 2 ≤ K * tensorInnerPointwise (I := I) (M := M) g r s b
            (chartRSTwist (I := I) (M := M) α b r s T)
            (chartRSTwist (I := I) (M := M) α b r s T) := by
  classical
  -- Reduce to the chart-frame form and rewrite via the bridge identity.
  obtain ⟨K, hK_nn, h_chart⟩ :=
    chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_pouTsupport
      (I := I) (M := M) g r s α
  refine ⟨K, hK_nn, ?_⟩
  intro b hb T
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  have h := h_chart b hb T
  rw [chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
      (I := I) (M := M) g r s α hb_base T T] at h
  exact h

end HeadlineNormComparison

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
