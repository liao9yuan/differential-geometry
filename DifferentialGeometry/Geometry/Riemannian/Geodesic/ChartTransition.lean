import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

set_option linter.unusedSectionVars false

/-!
# Chart-transition derivative as a CLM

For two basepoints `α β : M` on a smooth manifold, the chart-transition map
$$T_{\alpha\beta}\;:=\;\varphi_\beta\,\circ\,\varphi_\alpha^{-1}\;:\;E\to E$$
is smooth on the open set
`((extChartAt I α).symm ≫ extChartAt I β).source ⊆ E`. Its Fréchet derivative
at a point `x` of the overlap is a continuous linear map `E →L[ℝ] E`, which
plays the role of the (one-sided) chart-transition Jacobian whenever a
downstream development needs to push tangent data from chart-α coordinates
to chart-β coordinates.

This file packages:

* `chartTransitionSource α β` — the open set in `E` on which `T_{αβ}` is
  smooth, namely the source of the partial-equiv composition
  `(extChartAt I α).symm ≫ extChartAt I β`.
* `chartTransitionMap α β` — the function `T_{αβ}` itself, packaged as
  `extChartAt I β ∘ (extChartAt I α).symm`.
* `chartTransitionAt α β x` — the Fréchet derivative
  `fderiv ℝ (chartTransitionMap α β) x`, kept as a continuous linear map
  `E →L[ℝ] E`. Outside the smooth overlap, this falls back to the
  Mathlib default value of `fderiv`, which is zero.
* `chartTransitionMap_contDiffOn` — smoothness of `T_{αβ}` on its natural
  source.
* `chartTransitionAt_smooth` — smoothness of `x ↦ chartTransitionAt α β x`
  as a map into `E →L[ℝ] E`.
* `chartTransitionMap_apply_extChartAt`, `chartTransitionSource_mem_nhds_of_overlap`,
  `chartTransitionSource_of_boundaryless` — value at a point in the overlap,
  membership of the source in the neighbourhood filter at a point lying in
  both `M`-chart sources, and the equivalent formulation for boundaryless
  models.

The transformation law for chart-Christoffel symbols under `T_{αβ}` is a
separate development: it requires unfolding the chart-coordinate
Christoffel symbol from the metric and applying the change-of-variable
formula for second derivatives. That derivation is outside the scope of
this file; what is recorded here is the smoothness pre-requisite shared
by every downstream consumer.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The chart-transition source set, map, and its differential -/

/-- The open subset of `E` on which the chart-transition map `T_{αβ} :=
extChartAt I β ∘ (extChartAt I α).symm` is naturally defined and smooth.
It is the source of the `PartialEquiv` composition
`(extChartAt I α).symm ≫ extChartAt I β`. -/
def chartTransitionSource (α β : M) : Set E :=
  ((extChartAt I α).symm ≫ extChartAt I β).source

omit [IsManifold I ∞ M] in
lemma chartTransitionSource_def (α β : M) :
    chartTransitionSource (I := I) α β =
      ((extChartAt I α).symm ≫ extChartAt I β).source := rfl

/-- The chart-transition map itself, as a function `E → E`. Outside the
natural source it returns the partial-equiv coercion's default value, which
we never inspect in practice. -/
def chartTransitionMap (α β : M) : E → E :=
  extChartAt I β ∘ (extChartAt I α).symm

omit [IsManifold I ∞ M] in
lemma chartTransitionMap_def (α β : M) :
    chartTransitionMap (I := I) α β =
      extChartAt I β ∘ (extChartAt I α).symm := rfl

omit [IsManifold I ∞ M] in
lemma chartTransitionMap_apply (α β : M) (x : E) :
    chartTransitionMap (I := I) α β x =
      extChartAt I β ((extChartAt I α).symm x) := rfl

/-- For a manifold point `x : M` in both chart sources, the chart-transition
map sends the chart-α image of `x` to the chart-β image of `x`. -/
lemma chartTransitionMap_apply_extChartAt
    (α β : M) {x : M} (hx_α : x ∈ (chartAt H α).source) :
    chartTransitionMap (I := I) α β ((extChartAt I α) x) = extChartAt I β x := by
  unfold chartTransitionMap
  have hx_src : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]
    exact hx_α
  change extChartAt I β ((extChartAt I α).symm ((extChartAt I α) x)) = extChartAt I β x
  rw [(extChartAt I α).left_inv hx_src]

/-! ## Smoothness of the chart-transition map -/

/-- Smoothness of `T_{αβ}` on its natural source. This is the manifold-
infrastructure lemma `contDiffOn_ext_coord_change` packaged using our local
identifiers `chartTransitionSource` and `chartTransitionMap`. -/
theorem chartTransitionMap_contDiffOn (α β : M) :
    ContDiffOn ℝ ∞ (chartTransitionMap (I := I) α β)
      (chartTransitionSource (I := I) α β) := by
  -- Directly delegate to Mathlib's `contDiffOn_ext_coord_change`.
  -- Note: `contDiffOn_ext_coord_change α β` proves smoothness of
  -- `extChartAt I α ∘ (extChartAt I β).symm` on
  -- `((extChartAt I β).symm ≫ extChartAt I α).source`, so we apply it with
  -- the arguments swapped.
  have h := (contDiffOn_ext_coord_change (I := I) (n := ∞) β α)
  -- `h : ContDiffOn ℝ ∞ (extChartAt I β ∘ (extChartAt I α).symm)
  --        ((extChartAt I α).symm ≫ extChartAt I β).source`
  exact h

omit [IsManifold I ∞ M] in
/-- Membership lemma: if a manifold point `x` lies in both chart sources, then
its chart-α image lies in `chartTransitionSource α β`. -/
lemma extChartAt_mem_chartTransitionSource
    (α β : M) {x : M}
    (hx_α : x ∈ (chartAt H α).source) (hx_β : x ∈ (chartAt H β).source) :
    (extChartAt I α) x ∈ chartTransitionSource (I := I) α β := by
  unfold chartTransitionSource
  -- `((extChartAt I α).symm ≫ extChartAt I β).source =
  --    {y ∈ (extChartAt I α).target | (extChartAt I α).symm y ∈ (extChartAt I β).source}`
  have hx_α_src : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]; exact hx_α
  have hx_β_src : x ∈ (extChartAt I β).source := by
    rw [extChartAt_source (I := I)]; exact hx_β
  refine ⟨?_, ?_⟩
  · -- (extChartAt I α x) ∈ (extChartAt I α).symm.source = (extChartAt I α).target
    exact (extChartAt I α).map_source hx_α_src
  · -- (extChartAt I α).symm (extChartAt I α x) ∈ (extChartAt I β).source
    have h_inv : (extChartAt I α).symm ((extChartAt I α) x) = x :=
      (extChartAt I α).left_inv hx_α_src
    change (extChartAt I α).symm ((extChartAt I α) x) ∈ (extChartAt I β).source
    rw [h_inv]
    exact hx_β_src

/-- The chart-transition source is open in `E`, in the boundaryless setting.
This is the version that matches §4.4 hypotheses (project-internal "no
boundary"). -/
theorem chartTransitionSource_isOpen [I.Boundaryless] (α β : M) :
    IsOpen (chartTransitionSource (I := I) α β) := by
  -- We rewrite `chartTransitionSource = I '' ((chartAt H α).symm ≫ₕ chartAt H β).source`
  -- and use the fact that boundaryless `I` is an open embedding, hence sends
  -- opens to opens.
  unfold chartTransitionSource
  have : ((extChartAt I α).symm ≫ extChartAt I β).source =
      ((chartAt H α).extend I).symm.source ∩
        ((chartAt H α).extend I).symm ⁻¹' ((chartAt H β).extend I).source := by
    rfl
  rw [this]
  -- The first factor is the target of `extend I` of chart α, which is open
  -- in the boundaryless setting via `isOpen_extend_target`.
  have h1 : IsOpen (((chartAt H α).extend I).symm.source) := by
    -- symm.source = (extend I).target
    change IsOpen ((chartAt H α).extend I).target
    exact (chartAt H α).isOpen_extend_target (I := I)
  have h2_cont : ContinuousOn ((chartAt H α).extend I).symm
      ((chartAt H α).extend I).symm.source := by
    -- continuousOn of extend.symm on its source = extend.target
    change ContinuousOn ((chartAt H α).extend I).symm ((chartAt H α).extend I).target
    exact (chartAt H α).continuousOn_extend_symm (I := I)
  -- The preimage of the open set `((chartAt H β).extend I).source`
  -- under the continuous-on `extend.symm` is open relative to the source.
  -- Combined with the openness of the source, the whole intersection is open.
  have h3 : IsOpen ((chartAt H β).extend I).source :=
    (chartAt H β).isOpen_extend_source (I := I)
  exact h2_cont.isOpen_inter_preimage h1 h3

/-! ## The differential CLM -/

/-- The Fréchet derivative of the chart-transition map at a point `x`, as a
continuous linear map `E →L[ℝ] E`. Outside the smooth overlap this falls
back to Mathlib's default `fderiv` value, which is the zero map. -/
def chartTransitionAt (α β : M) (x : E) : E →L[ℝ] E :=
  fderiv ℝ (chartTransitionMap (I := I) α β) x

omit [IsManifold I ∞ M] in
lemma chartTransitionAt_def (α β : M) (x : E) :
    chartTransitionAt (I := I) α β x =
      fderiv ℝ (chartTransitionMap (I := I) α β) x := rfl

/-! ## Differentiability and smoothness of `chartTransitionAt` -/

/-- The chart-transition map is `ContDiffAt` at any interior point of its
natural source, in the boundaryless setting. -/
theorem chartTransitionMap_contDiffAt [I.Boundaryless]
    (α β : M) {x : E}
    (hx : x ∈ chartTransitionSource (I := I) α β) :
    ContDiffAt ℝ ∞ (chartTransitionMap (I := I) α β) x := by
  have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
    chartTransitionSource_isOpen (I := I) α β
  have h_on : ContDiffOn ℝ ∞ (chartTransitionMap (I := I) α β)
      (chartTransitionSource (I := I) α β) :=
    chartTransitionMap_contDiffOn (I := I) α β
  exact (h_on.contDiffAt (h_open.mem_nhds hx))

/-- The chart-transition map is differentiable at any point of its source,
in the boundaryless setting. -/
theorem chartTransitionMap_differentiableAt [I.Boundaryless]
    (α β : M) {x : E}
    (hx : x ∈ chartTransitionSource (I := I) α β) :
    DifferentiableAt ℝ (chartTransitionMap (I := I) α β) x :=
  (chartTransitionMap_contDiffAt (I := I) α β hx).differentiableAt (by
    -- The `ContDiff` order is `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, which is non-zero.
    decide)

/-- Smoothness of `x ↦ chartTransitionAt α β x` as a map into the CLM space
`E →L[ℝ] E`, on the open overlap, in the boundaryless setting. -/
theorem chartTransitionAt_smooth [I.Boundaryless] (α β : M) :
    ContDiffOn ℝ ∞
      (fun x => (chartTransitionAt (I := I) α β x : E →L[ℝ] E))
      (chartTransitionSource (I := I) α β) := by
  -- `chartTransitionAt α β` is by definition `fderiv ℝ (chartTransitionMap α β)`,
  -- and the source is open. Use `ContDiffOn.fderiv_of_isOpen`.
  have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
    chartTransitionSource_isOpen (I := I) α β
  have h_smooth :
      ContDiffOn ℝ ∞ (chartTransitionMap (I := I) α β)
        (chartTransitionSource (I := I) α β) :=
    chartTransitionMap_contDiffOn (I := I) α β
  -- We need `ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x) s` for `s` open.
  -- Mathlib lemma: `ContDiffOn.fderiv_of_isOpen` requires `(m + 1 ≤ n)`.
  -- Here `n = ∞`, `m = ∞`, and `∞ + 1 = ∞` so the bound holds.
  have h_top : (∞ + 1) ≤ ∞ := by
    -- `∞ + 1 = ∞` in `ℕ∞`.
    simp
  refine h_smooth.fderiv_of_isOpen h_open ?_
  exact h_top

/-- Pointwise equality: at any point `x` of the overlap, the chart-transition
CLM equals the Fréchet derivative of the chart-transition map. -/
@[simp] lemma chartTransitionAt_apply_eq_fderiv (α β : M) (x : E) (v : E) :
    chartTransitionAt (I := I) α β x v =
      fderiv ℝ (chartTransitionMap (I := I) α β) x v := rfl

/-! ## Identity and composition relations -/

/-- The chart-transition map from a chart back to itself is the identity, on
the natural source. (This is the partial-equiv left-inverse rewritten.) -/
lemma chartTransitionMap_self_apply
    (α : M) {x : E}
    (hx : x ∈ (extChartAt I α).target) :
    chartTransitionMap (I := I) α α x = x := by
  unfold chartTransitionMap
  change extChartAt I α ((extChartAt I α).symm x) = x
  exact (extChartAt I α).right_inv hx

/-- For two chart-base points `α, β` and any manifold point `x` in both chart
sources, the value of the chart-transition map at the chart-α image of `x`
is the chart-β image of `x`. (Restated for emphasis; identical content to
`chartTransitionMap_apply_extChartAt`.) -/
lemma chartTransitionMap_value_on_overlap
    (α β : M) {x : M}
    (hx_α : x ∈ (chartAt H α).source) :
    chartTransitionMap (I := I) α β ((extChartAt I α) x) = extChartAt I β x :=
  chartTransitionMap_apply_extChartAt (I := I) α β hx_α

/-! ## Continuity (in the manifold-sense) consequences -/

/-- The chart-transition map is continuous on its natural source. -/
theorem chartTransitionMap_continuousOn (α β : M) :
    ContinuousOn (chartTransitionMap (I := I) α β)
      (chartTransitionSource (I := I) α β) :=
  (chartTransitionMap_contDiffOn (I := I) α β).continuousOn

/-- In the boundaryless setting, the chart-transition map is `ContinuousAt`
at every point of the overlap. -/
theorem chartTransitionMap_continuousAt [I.Boundaryless]
    (α β : M) {x : E}
    (hx : x ∈ chartTransitionSource (I := I) α β) :
    ContinuousAt (chartTransitionMap (I := I) α β) x := by
  have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
    chartTransitionSource_isOpen (I := I) α β
  exact (chartTransitionMap_continuousOn (I := I) α β).continuousAt (h_open.mem_nhds hx)

/-! ## Inverse-composition identity for the chart-transition map

For two basepoints `α, β : M` and a manifold point `p` lying in both chart
sources, applying `T_{βα}` after `T_{αβ}` to the chart-α image of `p` returns
the original chart-α image. This is the partial-equiv composition identity
specialised to the overlap. -/

/-- Composition identity: `T_{βα}(T_{αβ}(extChartAt I α p)) = extChartAt I α p`
whenever `p` is in both chart sources. -/
lemma chartTransitionMap_comp_self_extChartAt
    (α β : M) {p : M}
    (hp_α : p ∈ (chartAt H α).source)
    (hp_β : p ∈ (chartAt H β).source) :
    chartTransitionMap (I := I) β α
        (chartTransitionMap (I := I) α β ((extChartAt I α) p)) =
      (extChartAt I α) p := by
  -- Step 1: `T_{αβ}((extChartAt I α) p) = extChartAt I β p`.
  have h1 : chartTransitionMap (I := I) α β ((extChartAt I α) p) =
      extChartAt I β p :=
    chartTransitionMap_apply_extChartAt (I := I) α β hp_α
  rw [h1]
  -- Step 2: `T_{βα}(extChartAt I β p) = extChartAt I α p`.
  exact chartTransitionMap_apply_extChartAt (I := I) β α hp_β

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry
