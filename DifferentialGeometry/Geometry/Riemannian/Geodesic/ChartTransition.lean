import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.MetricCompatibility
import DifferentialGeometry.Integral.Measure.Invariance
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

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

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

/-- Pointwise inverse identity on the source: for every `y` in the source of the
chart-transition `T_{αβ}`, applying `T_{βα}` afterwards returns `y`. -/
lemma chartTransitionMap_comp_self_of_mem_source
    (α β : M) {y : E} (hy : y ∈ chartTransitionSource (I := I) α β) :
    chartTransitionMap (I := I) β α (chartTransitionMap (I := I) α β y) = y := by
  -- `hy : y ∈ (extChartAt I α).target ∧ (extChartAt I α).symm y ∈ (extChartAt I β).source`.
  obtain ⟨hy_tgt, hy_pre⟩ := hy
  -- `(extChartAt I α).symm y ∈ (extChartAt I β).source`.
  have hy_pre' : (extChartAt I α).symm y ∈ (extChartAt I β).source := hy_pre
  -- `T_{αβ} y = extChartAt I β ((extChartAt I α).symm y)`.
  -- `T_{βα} (T_{αβ} y) = extChartAt I α ((extChartAt I β).symm (T_{αβ} y))`.
  change extChartAt I α
      ((extChartAt I β).symm (extChartAt I β ((extChartAt I α).symm y))) = y
  rw [(extChartAt I β).left_inv hy_pre']
  exact (extChartAt I α).right_inv hy_tgt

/-! ## Mutual-inverse identity for the chart-transition Jacobians

Differentiating the pointwise inverse identity `T_{βα} ∘ T_{αβ} = id` on the
open source gives, by the chain rule, that the Fréchet derivative of `T_{βα}` at
`T_{αβ} y` composed with the Fréchet derivative of `T_{αβ} y` is the identity
continuous linear map. This is the chart-Jacobian statement that the two
chart-transition maps are mutually inverse to first order. -/

/-- The chart-transition map `T_{αβ}` sends the source `chartTransitionSource α β`
into the source `chartTransitionSource β α`. -/
lemma chartTransitionMap_mapsTo_source [I.Boundaryless]
    (α β : M) :
    Set.MapsTo (chartTransitionMap (I := I) α β)
      (chartTransitionSource (I := I) α β)
      (chartTransitionSource (I := I) β α) := by
  intro y hy
  obtain ⟨hy_tgt, hy_pre⟩ := hy
  have hy_pre' : (extChartAt I α).symm y ∈ (extChartAt I β).source := hy_pre
  -- We must show `T_{αβ} y ∈ (extChartAt I β).target` and
  -- `(extChartAt I β).symm (T_{αβ} y) ∈ (extChartAt I α).source`.
  refine ⟨?_, ?_⟩
  · -- `T_{αβ} y = extChartAt I β ((extChartAt I α).symm y) ∈ (extChartAt I β).target`.
    change extChartAt I β ((extChartAt I α).symm y) ∈ (extChartAt I β).target
    exact (extChartAt I β).map_source hy_pre'
  · -- `(extChartAt I β).symm (T_{αβ} y) = (extChartAt I α).symm y ∈ (extChartAt I α).source`.
    change (extChartAt I β).symm
        (extChartAt I β ((extChartAt I α).symm y)) ∈ (extChartAt I α).source
    rw [(extChartAt I β).left_inv hy_pre']
    exact (extChartAt I α).map_target hy_tgt

/-- **Mutual-inverse Jacobian identity.** For `y` in the chart-transition source,
the chart-transition CLM at `T_{αβ} y` for the reverse transition composed with
the chart-transition CLM at `y` for the forward transition is the identity:
`(chartTransitionAt β α (T_{αβ} y)) ∘ (chartTransitionAt α β y) = id`. -/
theorem chartTransitionAt_comp_chartTransitionAt [I.Boundaryless]
    (α β : M) {y : E} (hy : y ∈ chartTransitionSource (I := I) α β) :
    (chartTransitionAt (I := I) β α (chartTransitionMap (I := I) α β y)).comp
        (chartTransitionAt (I := I) α β y) =
      ContinuousLinearMap.id ℝ E := by
  classical
  -- The composite `T_{βα} ∘ T_{αβ}` agrees with `id` on a neighbourhood of `y`.
  have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
    chartTransitionSource_isOpen (I := I) α β
  have h_nhds : chartTransitionSource (I := I) α β ∈ nhds y :=
    h_open.mem_nhds hy
  -- Eventual equality of the composite with `id`.
  have h_eq : (chartTransitionMap (I := I) β α ∘ chartTransitionMap (I := I) α β)
      =ᶠ[nhds y] id := by
    filter_upwards [h_nhds] with z hz
    simp only [Function.comp_apply, id_eq]
    exact chartTransitionMap_comp_self_of_mem_source (I := I) α β hz
  -- Differentiability ingredients.
  have hdiff_f : DifferentiableAt ℝ (chartTransitionMap (I := I) α β) y :=
    chartTransitionMap_differentiableAt (I := I) α β hy
  have hy' : chartTransitionMap (I := I) α β y ∈ chartTransitionSource (I := I) β α :=
    chartTransitionMap_mapsTo_source (I := I) α β hy
  have hdiff_g : DifferentiableAt ℝ (chartTransitionMap (I := I) β α)
      (chartTransitionMap (I := I) α β y) :=
    chartTransitionMap_differentiableAt (I := I) β α hy'
  -- `fderiv` of the composite at `y` equals `fderiv id y = id` by eventual eq.
  have h_fderiv_comp :
      fderiv ℝ (chartTransitionMap (I := I) β α ∘ chartTransitionMap (I := I) α β) y =
        (fderiv ℝ (chartTransitionMap (I := I) β α)
            (chartTransitionMap (I := I) α β y)).comp
          (fderiv ℝ (chartTransitionMap (I := I) α β) y) :=
    fderiv_comp y hdiff_g hdiff_f
  have h_fderiv_id : fderiv ℝ (id : E → E) y = ContinuousLinearMap.id ℝ E :=
    fderiv_id
  have h_chain : fderiv ℝ
      (chartTransitionMap (I := I) β α ∘ chartTransitionMap (I := I) α β) y =
      ContinuousLinearMap.id ℝ E := by
    rw [h_eq.fderiv_eq, h_fderiv_id]
  -- Combine.
  rw [chartTransitionAt_def, chartTransitionAt_def]
  rw [← h_fderiv_comp, h_chain]

/-- **Mutual-inverse Jacobian identity, other order.** For `y` in the source of
`T_{αβ}`, the forward CLM at `y` composed *after* the reverse CLM at `T_{αβ} y`
is the identity: `(chartTransitionAt α β y) ∘ (chartTransitionAt β α (T_{αβ} y)) = id`. -/
theorem chartTransitionAt_comp_chartTransitionAt' [I.Boundaryless]
    (α β : M) {y : E} (hy : y ∈ chartTransitionSource (I := I) α β) :
    (chartTransitionAt (I := I) α β y).comp
        (chartTransitionAt (I := I) β α (chartTransitionMap (I := I) α β y)) =
      ContinuousLinearMap.id ℝ E := by
  -- Apply the identity with roles of `α, β` swapped at the point `T_{αβ} y`,
  -- which lies in the source of `T_{βα}`, and whose image under `T_{βα}` is `y`.
  have hy' : chartTransitionMap (I := I) α β y ∈ chartTransitionSource (I := I) β α :=
    chartTransitionMap_mapsTo_source (I := I) α β hy
  have hback : chartTransitionMap (I := I) β α (chartTransitionMap (I := I) α β y) = y :=
    chartTransitionMap_comp_self_of_mem_source (I := I) α β hy
  have h := chartTransitionAt_comp_chartTransitionAt (I := I) β α hy'
  rw [hback] at h
  exact h

/-! ## Matrix view of `chartTransitionAt` and bridge to `tangentCoordChange`

The transformation law for chart-Christoffel symbols under the chart-transition
map `T_{αβ}` is built in stages below. The first ingredient is the matrix entry
of the chart-transition Fréchet derivative in the canonical model basis, and the
identification of this Jacobian with Mathlib's `tangentCoordChange` on the chart
overlap. -/

/-- The `(i, a)`-entry of the chart-transition Fréchet derivative
`chartTransitionAt α β x : E →L[ℝ] E` in the canonical model-space basis
`chartModelBasis E`: the `i`-th coordinate of `(chartTransitionAt α β x)(e_a)`. -/
def chartTransitionJacEntry (α β : M) (x : E)
    (i a : Fin (Module.finrank ℝ E)) : ℝ :=
  (chartModelBasis E).repr
    (chartTransitionAt (I := I) α β x ((chartModelBasis E) a)) i

@[simp] lemma chartTransitionJacEntry_def (α β : M) (x : E)
    (i a : Fin (Module.finrank ℝ E)) :
    chartTransitionJacEntry (I := I) α β x i a =
      (chartModelBasis E).repr
        (chartTransitionAt (I := I) α β x
          ((chartModelBasis E) a)) i := rfl

/-- **Entry form of the mutual-inverse Jacobian identity.** Summing the forward
Jacobian entries against the reverse Jacobian entries (evaluated at `T_{αβ} y`)
yields the Kronecker delta. This is the index-level statement of
`chartTransitionAt_comp_chartTransitionAt`, in the form directly consumed by the
inverse-Gram pullback. -/
theorem chartTransitionJacEntry_mul_sum [I.Boundaryless]
    (α β : M) {y : E} (hy : y ∈ chartTransitionSource (I := I) α β)
    (c i : Fin (Module.finrank ℝ E)) :
    ∑ a : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) α β y a i *
        chartTransitionJacEntry (I := I) β α
          (chartTransitionMap (I := I) α β y) c a =
      (if c = i then (1 : ℝ) else 0) := by
  classical
  -- Apply the CLM identity to the basis vector `e_i` and read off the `c`-th coord.
  have hcomp := chartTransitionAt_comp_chartTransitionAt (I := I) α β hy
  -- LHS: the `c`-th coordinate of `J_{βα}(Ty)(J_{αβ}(y)(e_i))`.
  have happly :
      (chartTransitionAt (I := I) β α (chartTransitionMap (I := I) α β y))
          (chartTransitionAt (I := I) α β y ((chartModelBasis E) i)) =
        (chartModelBasis E) i := by
    have := congrArg (fun L : E →L[ℝ] E => L ((chartModelBasis E) i)) hcomp
    simpa using this
  -- Expand `J_{αβ}(y)(e_i)` in the model basis.
  have hexpand :
      chartTransitionAt (I := I) α β y ((chartModelBasis E) i) =
        ∑ a : Fin (Module.finrank ℝ E),
          chartTransitionJacEntry (I := I) α β y a i • (chartModelBasis E) a := by
    conv_lhs => rw [← (chartModelBasis E).sum_repr
      (chartTransitionAt (I := I) α β y ((chartModelBasis E) i))]
    rfl
  -- Apply `J_{βα}(Ty)` to the expansion and read coordinates.
  rw [hexpand, map_sum] at happly
  -- Take the `c`-th coordinate of both sides of `happly`.
  have hcoord : (chartModelBasis E).repr
      (∑ a, chartTransitionAt (I := I) β α (chartTransitionMap (I := I) α β y)
          (chartTransitionJacEntry (I := I) α β y a i • (chartModelBasis E) a)) c =
      (chartModelBasis E).repr ((chartModelBasis E) i) c :=
    congrArg (fun w => (chartModelBasis E).repr w c) happly
  -- LHS coordinate sum equals the target sum.
  have hlhs :
      (chartModelBasis E).repr
        (∑ a, chartTransitionAt (I := I) β α (chartTransitionMap (I := I) α β y)
            (chartTransitionJacEntry (I := I) α β y a i • (chartModelBasis E) a)) c =
      ∑ a, chartTransitionJacEntry (I := I) α β y a i *
        chartTransitionJacEntry (I := I) β α
          (chartTransitionMap (I := I) α β y) c a := by
    rw [map_sum]
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [map_smul, map_smul]
    simp only [Finsupp.smul_apply, smul_eq_mul, chartTransitionJacEntry_def]
  rw [hlhs] at hcoord
  -- RHS coordinate: `repr (e_i) c = δ_{c i}`.
  rw [hcoord]
  have hrepr : (chartModelBasis E).repr ((chartModelBasis E) i) c =
      (if c = i then (1 : ℝ) else 0) := by
    rw [(chartModelBasis E).repr_self i, Finsupp.single_apply]
    by_cases h : c = i
    · subst h; simp
    · rw [if_neg (fun hh : i = c => h hh.symm), if_neg h]
  exact hrepr

/-- **Entry form of the mutual-inverse Jacobian identity, other order.** Summing
the forward Jacobian entries (at `y`) against the reverse Jacobian entries (at
`T_{αβ} y`), contracting on the inner index, yields the Kronecker delta. This is
the index-level statement of `chartTransitionAt_comp_chartTransitionAt'`. -/
theorem chartTransitionJacEntry_mul_sum' [I.Boundaryless]
    (α β : M) {y : E} (hy : y ∈ chartTransitionSource (I := I) α β)
    (b i : Fin (Module.finrank ℝ E)) :
    ∑ m : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) α β y b m *
        chartTransitionJacEntry (I := I) β α
          (chartTransitionMap (I := I) α β y) m i =
      (if b = i then (1 : ℝ) else 0) := by
  classical
  have hcomp := chartTransitionAt_comp_chartTransitionAt' (I := I) α β hy
  -- Apply to `e_i`, read the `b`-th coordinate.
  have happly :
      (chartTransitionAt (I := I) α β y)
          (chartTransitionAt (I := I) β α (chartTransitionMap (I := I) α β y)
            ((chartModelBasis E) i)) =
        (chartModelBasis E) i := by
    have := congrArg (fun L : E →L[ℝ] E => L ((chartModelBasis E) i)) hcomp
    simpa using this
  have hexpand :
      chartTransitionAt (I := I) β α (chartTransitionMap (I := I) α β y)
          ((chartModelBasis E) i) =
        ∑ m : Fin (Module.finrank ℝ E),
          chartTransitionJacEntry (I := I) β α
            (chartTransitionMap (I := I) α β y) m i • (chartModelBasis E) m := by
    conv_lhs => rw [← (chartModelBasis E).sum_repr
      (chartTransitionAt (I := I) β α (chartTransitionMap (I := I) α β y)
        ((chartModelBasis E) i))]
    rfl
  rw [hexpand, map_sum] at happly
  have hcoord : (chartModelBasis E).repr
      (∑ m, chartTransitionAt (I := I) α β y
          (chartTransitionJacEntry (I := I) β α
            (chartTransitionMap (I := I) α β y) m i • (chartModelBasis E) m)) b =
      (chartModelBasis E).repr ((chartModelBasis E) i) b :=
    congrArg (fun w => (chartModelBasis E).repr w b) happly
  have hlhs :
      (chartModelBasis E).repr
        (∑ m, chartTransitionAt (I := I) α β y
            (chartTransitionJacEntry (I := I) β α
              (chartTransitionMap (I := I) α β y) m i • (chartModelBasis E) m)) b =
      ∑ m, chartTransitionJacEntry (I := I) α β y b m *
        chartTransitionJacEntry (I := I) β α
          (chartTransitionMap (I := I) α β y) m i := by
    rw [map_sum, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl ?_
    intro m _
    rw [map_smul, map_smul]
    simp only [Finsupp.smul_apply, smul_eq_mul, chartTransitionJacEntry_def]
    ring
  rw [hlhs] at hcoord
  rw [hcoord]
  rw [(chartModelBasis E).repr_self i, Finsupp.single_apply]
  by_cases h : b = i
  · subst h; simp
  · rw [if_neg (fun hh : i = b => h hh.symm), if_neg h]

omit [IsManifold I ∞ M] in
private lemma fderivWithin_range_I_eq_fderiv' [I.Boundaryless]
    (f : E → E) (y : E) :
    fderivWithin ℝ f (Set.range I) y = fderiv ℝ f y := by
  have h : (Set.range I : Set E) = Set.univ :=
    ModelWithCorners.Boundaryless.range_eq_univ (I := I)
  rw [h, fderivWithin_univ]

/-- Bridge: on the chart overlap, the manifold-level Jacobian `tangentCoordChange`
agrees with the chart-level Jacobian `chartTransitionAt` (in the boundaryless
setting, where `fderivWithin (range I) = fderiv`). -/
private lemma tangentCoordChange_eq_chartTransitionAt' [I.Boundaryless]
    (α β : M) (p : M) :
    tangentCoordChange I α β p =
      chartTransitionAt (I := I) α β (extChartAt I α p) := by
  rw [tangentCoordChange_def]
  rw [chartTransitionAt_def]
  rw [chartTransitionMap_def]
  exact fderivWithin_range_I_eq_fderiv' (I := I)
    (extChartAt I β ∘ (extChartAt I α).symm) (extChartAt I α p)

/-! ## Gram-matrix pullback under chart transition (standard direction)

The transformation law for the `(0,2)`-covariant metric tensor under chart
change, expressing the chart-α Gram matrix at `x` via the chart-β Gram matrix
at `T x`:
`G_α(x)_{ij} = ∑ a b, J^a_i J^b_j G_β(T x)_{ab}`,
with `J^a_i = chartTransitionJacEntry α β x a i`. -/

private theorem chartGramOnE_eq_sum_chartTransition' [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α β : M) (x : E)
    (hx : x ∈ (extChartAt I α) ''
              ((chartAt H α).source ∩ (chartAt H β).source))
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramOnE (I := I) g α i j x =
      ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) α β x a i *
        chartTransitionJacEntry (I := I) α β x b j *
        chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β x) := by
  classical
  obtain ⟨p, ⟨hp_α_src, hp_β_src⟩, hp_eq⟩ := hx
  have hp_ext_α : p ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]; exact hp_α_src
  have hp_ext_β : p ∈ (extChartAt I β).source := by
    rw [extChartAt_source (I := I)]; exact hp_β_src
  have hx_eq : extChartAt I α p = x := hp_eq
  have hp_symm : (extChartAt I α).symm x = p := by
    rw [← hx_eq, (extChartAt I α).left_inv hp_ext_α]
  have h_tβ : chartTransitionMap (I := I) α β x = extChartAt I β p := by
    change extChartAt I β ((extChartAt I α).symm x) = extChartAt I β p
    rw [hp_symm]
  have hp_triv_α : p ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    change p ∈ (chartAt H α).source; exact hp_α_src
  have hp_triv_β : p ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
    change p ∈ (chartAt H β).source; exact hp_β_src
  have h_lhs :
      chartGramOnE (I := I) g α i j x =
        chartGramMatrix g α p i j := by
    change chartGramMatrix g α ((extChartAt I α).symm x) i j =
        chartGramMatrix g α p i j
    rw [hp_symm]
  have h_rhs_inner : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g β a b
        (chartTransitionMap (I := I) α β x) =
      chartGramMatrix g β p a b := by
    intro a b
    change chartGramMatrix g β
        ((extChartAt I β).symm (chartTransitionMap (I := I) α β x)) a b =
      chartGramMatrix g β p a b
    rw [h_tβ, (extChartAt I β).left_inv hp_ext_β]
  rw [h_lhs]
  rw [chartGramMatrix_pullback_eq_sum (I := I) g β α
        hp_triv_β hp_triv_α i j]
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [h_rhs_inner k l]
  congr 1
  congr 1
  · rw [transitionMatrix_apply]
    rw [tangentCoordChange_eq_chartTransitionAt' (I := I) α β p]
    simp only [chartTransitionJacEntry_def, hx_eq]
  · rw [transitionMatrix_apply]
    rw [tangentCoordChange_eq_chartTransitionAt' (I := I) α β p]
    simp only [chartTransitionJacEntry_def, hx_eq]

/-! ## Inverse Gram-matrix pullback under chart transition

The contravariant transformation law for the inverse metric. Writing
`K^i_a := chartTransitionJacEntry β α (T x) i a` for the reverse (inverse)
chart-transition Jacobian evaluated at `T x = chartTransitionMap α β x`, the
inverse Gram matrix at the chart-α picture decomposes as
`G_α⁻¹(x)^{ij} = ∑ a b, K^i_a K^j_b G_β⁻¹(T x)^{ab}`.

The proof verifies the right-inverse relation `G_α · H = 1` for the candidate
matrix `H` and concludes by uniqueness of the matrix inverse, using the Gram
pullback (`chartGramOnE_eq_sum_chartTransition`) and the mutual-inverse Jacobian
identity (`chartTransitionJacEntry_mul_sum`). -/

/-- The candidate inverse-Gram pullback matrix at a chart-α point `x`, built
from the reverse Jacobian entries and the chart-β inverse Gram matrix at `T x`. -/
private def invGramPullbackCandidate [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α β : M) (p : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j =>
    ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      chartTransitionJacEntry (I := I) β α
        (chartTransitionMap (I := I) α β (extChartAt I α p)) i a *
      chartTransitionJacEntry (I := I) β α
        (chartTransitionMap (I := I) α β (extChartAt I α p)) j b *
      chartInvGramMatrix (I := I) g β p a b

/-- Right-inverse relation: the chart-α Gram matrix times the candidate equals
the identity matrix, at a point `p` in both chart sources. -/
private theorem chartGramMatrix_mul_invGramPullbackCandidate [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α β : M) {p : M}
    (hp_α : p ∈ (chartAt H α).source) (hp_β : p ∈ (chartAt H β).source) :
    chartGramMatrix (I := I) g α p *
        invGramPullbackCandidate (I := I) g α β p = 1 := by
  classical
  set x := extChartAt I α p with hx_def
  set Tx := chartTransitionMap (I := I) α β x with hTx_def
  have hp_triv_β : p ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
    change p ∈ (chartAt H β).source; exact hp_β
  -- Abbreviations.
  set J : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun a i => chartTransitionJacEntry (I := I) α β x a i with hJ_def
  set K : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i a => chartTransitionJacEntry (I := I) β α Tx i a with hK_def
  set Gβinv : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun a b => chartInvGramMatrix (I := I) g β p a b with hGβinv_def
  -- Membership of x in the image of the overlap.
  have hx_mem : x ∈ (extChartAt I α) ''
      ((chartAt H α).source ∩ (chartAt H β).source) := by
    refine ⟨p, ⟨hp_α, hp_β⟩, rfl⟩
  -- The Gram pullback in matrix form: `Gα_{k m} = ∑ a b, J_{a k} J_{b m} Gβ_{a b}`.
  have hGram : ∀ k m : Fin (Module.finrank ℝ E),
      chartGramMatrix (I := I) g α p k m =
        ∑ a, ∑ b, J a k * J b m *
          chartGramMatrix (I := I) g β p a b := by
    intro k m
    have h := chartGramOnE_eq_sum_chartTransition' (I := I) g α β x hx_mem k m
    -- (extChartAt I α).symm x = p
    have hp_ext_α : p ∈ (extChartAt I α).source := by
      rw [extChartAt_source (I := I)]; exact hp_α
    have hsymm : (extChartAt I α).symm x = p := by
      rw [hx_def, (extChartAt I α).left_inv hp_ext_α]
    have hp_ext_β : p ∈ (extChartAt I β).source := by
      rw [extChartAt_source (I := I)]; exact hp_β
    have hTx_eq : Tx = extChartAt I β p := by
      rw [hTx_def, hx_def]
      change extChartAt I β ((extChartAt I α).symm (extChartAt I α p)) = _
      rw [(extChartAt I α).left_inv hp_ext_α]
    -- LHS: chartGramOnE α k m x = chartGramMatrix α p k m.
    have hLHS : chartGramOnE (I := I) g α k m x = chartGramMatrix (I := I) g α p k m := by
      rw [chartGramOnE_def (I := I) g α k m x, hsymm]
    rw [hLHS] at h
    rw [h]
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    -- chartGramOnE β a b Tx = chartGramMatrix β p a b
    have hGβ : chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β x) =
        chartGramMatrix (I := I) g β p a b := by
      rw [chartGramOnE_def (I := I) g β a b (chartTransitionMap (I := I) α β x),
        ← hTx_def, hTx_eq, (extChartAt I β).left_inv hp_ext_β]
    rw [hGβ]
  -- The mutual-inverse Jacobian identity at `x` (note `Tx = chartTransitionMap α β x`).
  have hx_src : x ∈ chartTransitionSource (I := I) α β :=
    extChartAt_mem_chartTransitionSource (I := I) α β hp_α hp_β
  have hMut : ∀ c i : Fin (Module.finrank ℝ E),
      ∑ a, J a i * K c a = (if c = i then (1 : ℝ) else 0) := by
    intro c i
    have h := chartTransitionJacEntry_mul_sum (I := I) α β hx_src c i
    rw [← hTx_def] at h
    exact h
  -- Gβ⁻¹ is a right inverse of Gβ: `∑ b, Gβ_{a b} Gβ⁻¹_{b d} = δ_{a d}`.
  have hGβinvR : ∀ a d : Fin (Module.finrank ℝ E),
      ∑ b, chartGramMatrix (I := I) g β p a b * Gβinv b d =
        (if a = d then (1 : ℝ) else 0) := by
    intro a d
    have hmul := chartGramMatrix_mul_chartInvGramMatrix (I := I) g β hp_triv_β
    have := congrFun (congrFun hmul a) d
    rw [Matrix.mul_apply] at this
    rw [hGβinv_def]
    rw [show (∑ b, chartGramMatrix (I := I) g β p a b *
        chartInvGramMatrix (I := I) g β p b d) =
        (1 : Matrix _ _ ℝ) a d from this]
    rw [Matrix.one_apply]
  -- The transposed mutual identity: `∑ m, J_{b m} K_{m i} = δ_{b i}`.
  have hMut' : ∀ b i : Fin (Module.finrank ℝ E),
      ∑ m, J b m * K m i = (if b = i then (1 : ℝ) else 0) := by
    intro b i
    have h := chartTransitionJacEntry_mul_sum' (I := I) α β hx_src b i
    rw [← hTx_def] at h
    exact h
  -- Now verify the product entry by entry.
  ext k l
  rw [Matrix.mul_apply, Matrix.one_apply]
  -- LHS = ∑ m, Gα_{k m} * H_{m l}.
  -- Expand H_{m l} = ∑ i j, K_{m i} K_{l j} Gβ⁻¹_{i j}.
  have hH : ∀ m : Fin (Module.finrank ℝ E),
      invGramPullbackCandidate (I := I) g α β p m l =
        ∑ i, ∑ j, K m i * K l j * Gβinv i j := by
    intro m
    rfl
  -- Master nested-sum abbreviation `Φ a b i j m`.
  set Φ : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
    fun a b i j m =>
      (J a k * chartGramMatrix (I := I) g β p a b) * (K l j * Gβinv i j) *
        (J b m * K m i) with hΦ_def
  -- Expand Gα_{k m} via hGram, then distribute everything into the 5-fold sum of `Φ`.
  calc ∑ m, chartGramMatrix (I := I) g α p k m *
          invGramPullbackCandidate (I := I) g α β p m l
      = ∑ m, (∑ a, ∑ b, J a k * J b m *
            chartGramMatrix (I := I) g β p a b) *
          (∑ i, ∑ j, K m i * K l j * Gβinv i j) := by
        refine Finset.sum_congr rfl ?_
        intro m _
        rw [hGram k m, hH m]
    -- Distribute into the canonical 5-fold sum of `Φ`.
    _ = ∑ m, ∑ a, ∑ b, ∑ i, ∑ j, Φ a b i j m := by
        refine Finset.sum_congr rfl ?_
        intro m _
        -- (∑ a, F a) * (∑ i, G i) = ∑ a, ∑ i, F a * G i, then distribute inner sums.
        rw [Fintype.sum_mul_sum]
        -- ∑ a, ∑ i, (∑ b, J a k * J b m * Gβ_{ab}) * (∑ j, K m i * K l j * Gβinv_{ij})
        -- We need: ∑ a, ∑ b, ∑ i, ∑ j, Φ.  Reorder (a, i, b, j) → (a, b, i, j).
        rw [Finset.sum_congr rfl (fun a _ =>
          Finset.sum_congr rfl (fun i _ => by
            rw [Finset.sum_mul_sum]))]
        -- Now: ∑ a, ∑ i, ∑ b, ∑ j, (J a k * J b m * Gβ_{ab}) * (K m i * K l j * Gβinv_{ij}).
        -- Swap the `i` and `b` sums to reach ∑ a, ∑ b, ∑ i, ∑ j.
        refine Finset.sum_congr rfl ?_; intro a _
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_; intro b _
        refine Finset.sum_congr rfl ?_; intro i _
        refine Finset.sum_congr rfl ?_; intro j _
        rw [hΦ_def]; ring
    -- Move the `m`-sum innermost (commute past a, b, i, j).
    _ = ∑ a, ∑ b, ∑ i, ∑ j, ∑ m, Φ a b i j m := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_; intro a _
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_; intro b _
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_; intro i _
        rw [Finset.sum_comm]
    -- Collapse the `m`-sum: `∑ m, Φ a b i j m = (coef) * (if b = i then 1 else 0)`.
    _ = ∑ a, ∑ b, ∑ i, ∑ j,
          (J a k * chartGramMatrix (I := I) g β p a b) * (K l j * Gβinv i j) *
            (if b = i then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl ?_; intro a _
        refine Finset.sum_congr rfl ?_; intro b _
        refine Finset.sum_congr rfl ?_; intro i _
        refine Finset.sum_congr rfl ?_; intro j _
        rw [hΦ_def, ← Finset.mul_sum, hMut' b i]
    -- Collapse `i = b` (swap `i,j` sums first, then collapse the `i`-sum).
    _ = ∑ a, ∑ b, ∑ j,
          (J a k * chartGramMatrix (I := I) g β p a b) * (K l j * Gβinv b j) := by
        refine Finset.sum_congr rfl ?_; intro a _
        refine Finset.sum_congr rfl ?_; intro b _
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_; intro j _
        -- Reshape each `i`-term into `if b = i then (…) else 0`, then `sum_ite_eq`.
        rw [show (∑ i, (J a k * chartGramMatrix (I := I) g β p a b) *
                (K l j * Gβinv i j) * (if b = i then (1 : ℝ) else 0)) =
              ∑ i, (if b = i then
                (J a k * chartGramMatrix (I := I) g β p a b) * (K l j * Gβinv i j)
                else 0) from by
          refine Finset.sum_congr rfl ?_; intro i _
          by_cases h : b = i
          · rw [if_pos h, if_pos h, mul_one]
          · rw [if_neg h, if_neg h, mul_zero]]
        rw [Finset.sum_ite_eq Finset.univ b
          (fun i => (J a k * chartGramMatrix (I := I) g β p a b) * (K l j * Gβinv i j))]
        rw [if_pos (Finset.mem_univ b)]
    -- Collapse `j = a` via `∑ b, Gβ_{a b} Gβinv_{b j} = δ_{a j}` (note Gβinv b j).
    _ = ∑ a, J a k * K l a := by
        refine Finset.sum_congr rfl ?_; intro a _
        -- Current LHS: ∑ b, ∑ j, (J a k * Gβ_{a b}) * (K l j * Gβinv b j).
        -- Swap the `b` and `j` sums so the `b`-sum is innermost.
        rw [Finset.sum_comm]
        -- Now: ∑ j, ∑ b, (J a k * Gβ_{a b}) * (K l j * Gβinv b j).
        have hstep : ∀ j : Fin (Module.finrank ℝ E),
            (∑ b, (J a k * chartGramMatrix (I := I) g β p a b) * (K l j * Gβinv b j)) =
              (if a = j then J a k * K l j else 0) := by
          intro j
          have : (∑ b, (J a k * chartGramMatrix (I := I) g β p a b) *
                (K l j * Gβinv b j)) =
              J a k * K l j *
                (∑ b, chartGramMatrix (I := I) g β p a b * Gβinv b j) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_; intro b _
            ring
          rw [this, hGβinvR a j]
          by_cases h : a = j
          · rw [if_pos h, if_pos h, mul_one]
          · rw [if_neg h, if_neg h, mul_zero]
        rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hstep j)]
        -- ∑ j, (if a = j then J a k * K l j else 0) = J a k * K l a.
        rw [Finset.sum_ite_eq Finset.univ a (fun j => J a k * K l j)]
        rw [if_pos (Finset.mem_univ a)]
    _ = (if k = l then (1 : ℝ) else 0) := by
        rw [hMut l k]
        by_cases h : k = l
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (fun hh : l = k => h hh.symm)]

/-- **Inverse Gram-matrix pullback under chart transition.** The contravariant
transformation law for the inverse metric: at a manifold point `p` lying in both
chart sources, the chart-α inverse Gram matrix entry decomposes against the
chart-β inverse Gram matrix at `T x` via the reverse chart-transition Jacobian:
`G_α⁻¹(p)^{ij} = ∑ a b, K^i_a K^j_b G_β⁻¹(p)^{ab}`, where
`K^i_a = chartTransitionJacEntry β α (T x) i a` and `x = extChartAt I α p`. -/
theorem chartInvGramMatrix_eq_sum_chartTransition [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α β : M) {p : M}
    (hp_α : p ∈ (chartAt H α).source) (hp_β : p ∈ (chartAt H β).source)
    (i j : Fin (Module.finrank ℝ E)) :
    chartInvGramMatrix (I := I) g α p i j =
      ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) β α
          (chartTransitionMap (I := I) α β (extChartAt I α p)) i a *
        chartTransitionJacEntry (I := I) β α
          (chartTransitionMap (I := I) α β (extChartAt I α p)) j b *
        chartInvGramMatrix (I := I) g β p a b := by
  -- `chartInvGramMatrix α p = (chartGramMatrix α p)⁻¹`, and the candidate is a
  -- right inverse, so equals the inverse by uniqueness.
  have hright := chartGramMatrix_mul_invGramPullbackCandidate (I := I) g α β hp_α hp_β
  have hinv : chartInvGramMatrix (I := I) g α p =
      invGramPullbackCandidate (I := I) g α β p := by
    unfold chartInvGramMatrix
    exact Matrix.inv_eq_right_inv hright
  have hentry := congrFun (congrFun hinv i) j
  rw [hentry]
  rfl

/-! ## Differentiated Gram pullback and the chart-Christoffel transformation law

We now differentiate the covariant Gram-pullback identity
`G_α(y)_{ij} = ∑ a b, J^a_i(y) J^b_j(y) G_β(T y)_{ab}` (where
`J^a_i(y) = chartTransitionJacEntry α β y a i` is the chart-transition Jacobian
and `T = chartTransitionMap α β`), valid on the open overlap source, to obtain
the transformation law for the chart-Christoffel contraction. The second
derivative of `T` (the failure of the Jacobian to be constant) is precisely the
inhomogeneous term in the Christoffel transformation law. -/

/-- Every point of the open chart-transition source `chartTransitionSource α β`
lies in the chart-α image of the chart overlap. This lets us apply the Gram
pullback at every point of a neighbourhood, not just a single overlap image. -/
lemma mem_overlap_image_of_mem_chartTransitionSource
    (α β : M) {y : E} (hy : y ∈ chartTransitionSource (I := I) α β) :
    y ∈ (extChartAt I α) ''
      ((chartAt H α).source ∩ (chartAt H β).source) := by
  obtain ⟨hy_tgt, hy_pre⟩ := hy
  have hy_pre' : (extChartAt I α).symm y ∈ (extChartAt I β).source := hy_pre
  set p := (extChartAt I α).symm y with hp_def
  have hp_α_ext : p ∈ (extChartAt I α).source := (extChartAt I α).map_target hy_tgt
  have hp_β_ext : p ∈ (extChartAt I β).source := hy_pre'
  have hp_α : p ∈ (chartAt H α).source := by
    rw [← extChartAt_source (I := I)]; exact hp_α_ext
  have hp_β : p ∈ (chartAt H β).source := by
    rw [← extChartAt_source (I := I)]; exact hp_β_ext
  refine ⟨p, ⟨hp_α, hp_β⟩, ?_⟩
  rw [hp_def]
  exact (extChartAt I α).right_inv hy_tgt

/-- The covariant Gram pullback holds at every point `y` of the open
chart-transition source `chartTransitionSource α β`. This is the
neighbourhood-wide version of `chartGramOnE_eq_sum_chartTransition'`. -/
lemma chartGramOnE_eq_sum_chartTransition_on_source [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α β : M) {y : E}
    (hy : y ∈ chartTransitionSource (I := I) α β)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramOnE (I := I) g α i j y =
      ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) α β y a i *
        chartTransitionJacEntry (I := I) α β y b j *
        chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β y) :=
  chartGramOnE_eq_sum_chartTransition' (I := I) g α β y
    (mem_overlap_image_of_mem_chartTransitionSource (I := I) α β hy) i j

/-- The chart-transition Jacobian entry `y ↦ chartTransitionJacEntry α β y a i`
is `ContDiffOn ℝ ∞` on the open chart-transition source. It is the composition
of the smooth CLM-valued map `chartTransitionAt α β` with the (continuous,
linear, hence smooth) evaluation-and-coordinate functional
`L ↦ (chartModelBasis E).repr (L (e_a)) i`. -/
lemma chartTransitionJacEntry_contDiffOn [I.Boundaryless]
    (α β : M) (a i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y => chartTransitionJacEntry (I := I) α β y a i)
      (chartTransitionSource (I := I) α β) := by
  -- The coordinate functional `E →L[ℝ] ℝ` (continuous since `E` is finite-dim).
  -- Note: `chartTransitionJacEntry α β y a i = repr (chartTransitionAt α β y (e_i)) a`,
  -- so the row index is `a` and the evaluated basis vector is `e_i`.
  set coordCLM : E →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((chartModelBasis E).coord a) with hcoordCLM
  -- The coordinate-evaluation functional `(E →L[ℝ] E) →L[ℝ] ℝ`.
  set evalCoord : (E →L[ℝ] E) →L[ℝ] ℝ :=
    coordCLM.comp
      (ContinuousLinearMap.apply ℝ E ((chartModelBasis E) i)) with hevalCoord
  have hfun : (fun y => chartTransitionJacEntry (I := I) α β y a i) =
      evalCoord ∘ (fun y => (chartTransitionAt (I := I) α β y : E →L[ℝ] E)) := by
    funext y
    rw [chartTransitionJacEntry_def, hevalCoord, hcoordCLM]
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
  rw [hfun]
  exact evalCoord.contDiff.comp_contDiffOn (chartTransitionAt_smooth (I := I) α β)

/-- The chart-transition Jacobian entry is `DifferentiableAt` at any point of
the open chart-transition source. -/
lemma chartTransitionJacEntry_differentiableAt [I.Boundaryless]
    (α β : M) (a i : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ chartTransitionSource (I := I) α β) :
    DifferentiableAt ℝ
      (fun z => chartTransitionJacEntry (I := I) α β z a i) y := by
  have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
    chartTransitionSource_isOpen (I := I) α β
  have hcd : ContDiffOn ℝ ∞
      (fun z => chartTransitionJacEntry (I := I) α β z a i)
      (chartTransitionSource (I := I) α β) :=
    chartTransitionJacEntry_contDiffOn (I := I) α β a i
  exact (hcd.contDiffAt (h_open.mem_nhds hy)).differentiableAt (by simp)

/-- The image `chartTransitionMap α β y` of a chart-transition-source point lies
in the interior of `(extChartAt I β).target` (which, being open in the
boundaryless setting, equals its own interior). -/
lemma chartTransitionMap_mem_interior_target [I.Boundaryless]
    (α β : M) {y : E} (hy : y ∈ chartTransitionSource (I := I) α β) :
    chartTransitionMap (I := I) α β y ∈ interior (extChartAt I β).target := by
  have hTy : chartTransitionMap (I := I) α β y ∈ chartTransitionSource (I := I) β α :=
    chartTransitionMap_mapsTo_source (I := I) α β hy
  -- The first component of membership in `chartTransitionSource β α` is
  -- membership in `(extChartAt I β).target`.
  have hTy_tgt : chartTransitionMap (I := I) α β y ∈ (extChartAt I β).target :=
    hTy.1
  rw [(isOpen_extChartAt_target (I := I) β).interior_eq]
  exact hTy_tgt

/-- **Chain rule for the Gram pullback.** The chart-coordinate partial derivative
`∂_k` of the composite `y ↦ G_β(a b)(T y)` (where `T = chartTransitionMap α β`)
at a chart-transition-source point `y` distributes over the chart-transition
Jacobian:
`∂_k (G_β(a b) ∘ T)(y) = ∑ c, J^c_k(y) · (∂_c G_β(a b))(T y)`. -/
lemma partialDeriv_chartGramOnE_comp_chartTransitionMap [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α β : M)
    (a b k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ chartTransitionSource (I := I) α β) :
    partialDeriv (E := E) k
        (fun z => chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β z)) y =
      ∑ c : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) α β y c k *
          partialDeriv (E := E) c (chartGramOnE (I := I) g β a b)
            (chartTransitionMap (I := I) α β y) := by
  classical
  set T := chartTransitionMap (I := I) α β with hT_def
  set Ty := T y with hTy_def
  -- `G_β(a b)` is differentiable at `Ty` (interior of target_β).
  have hTy_int : Ty ∈ interior (extChartAt I β).target := by
    rw [hTy_def, hT_def]
    exact chartTransitionMap_mem_interior_target (I := I) α β hy
  have hGβ_diff : DifferentiableAt ℝ (chartGramOnE (I := I) g β a b) Ty := by
    have hcd : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g β a b)
        (extChartAt I β).target := chartGramOnE_contDiffOn (I := I) g β a b
    have hcd_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g β a b)
        (interior (extChartAt I β).target) := hcd.mono interior_subset
    exact (hcd_int.contDiffAt
      (isOpen_interior.mem_nhds hTy_int)).differentiableAt (by simp)
  -- `T` is differentiable at `y`.
  have hT_diff : DifferentiableAt ℝ T y := by
    rw [hT_def]; exact chartTransitionMap_differentiableAt (I := I) α β hy
  -- Chain rule for the composite.
  unfold partialDeriv
  have hcomp_eq :
      (fun z => chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β z)) =
        (chartGramOnE (I := I) g β a b) ∘ T := by
    funext z; rw [hT_def]; rfl
  rw [hcomp_eq]
  rw [fderiv_comp y hGβ_diff hT_diff]
  rw [ContinuousLinearMap.comp_apply]
  -- `fderiv T y (e_k) = chartTransitionAt α β y (e_k) = ∑ c, J^c_k • e_c`.
  have hTk : fderiv ℝ T y ((chartModelBasis E) k) =
      ∑ c : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) α β y c k • (chartModelBasis E) c := by
    have hexp : chartTransitionAt (I := I) α β y ((chartModelBasis E) k) =
        ∑ c : Fin (Module.finrank ℝ E),
          chartTransitionJacEntry (I := I) α β y c k • (chartModelBasis E) c := by
      conv_lhs => rw [← (chartModelBasis E).sum_repr
        (chartTransitionAt (I := I) α β y ((chartModelBasis E) k))]
      rfl
    rw [chartTransitionAt_def] at hexp
    rw [hT_def]
    exact hexp
  rw [hTk]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro c _
  rw [map_smul]
  rw [smul_eq_mul]

omit [IsManifold I ∞ M] in
/-- Leibniz rule for `partialDeriv` of a product of two differentiable functions. -/
lemma partialDeriv_mul (k : Fin (Module.finrank ℝ E)) (u v : E → ℝ) {y : E}
    (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) :
    partialDeriv (E := E) k (fun z => u z * v z) y =
      partialDeriv (E := E) k u y * v y + u y * partialDeriv (E := E) k v y := by
  unfold partialDeriv
  have hmul : fderiv ℝ (fun z => u z * v z) y =
      u y • fderiv ℝ v y + v y • fderiv ℝ u y := fderiv_mul hu hv
  rw [hmul]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul]
  ring

/-- Each summand of the Gram pullback, `y ↦ J^a_i(y) · J^b_j(y) · G_β(a b)(T y)`,
is a triple product of functions differentiable on the chart-transition source.
This packages the Leibniz expansion of its `∂_k`. -/
lemma partialDeriv_chartTransition_pullback_summand [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α β : M)
    (a b i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ chartTransitionSource (I := I) α β) :
    partialDeriv (E := E) k
        (fun z => chartTransitionJacEntry (I := I) α β z a i *
          chartTransitionJacEntry (I := I) α β z b j *
          chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β z)) y =
      (partialDeriv (E := E) k
          (fun z => chartTransitionJacEntry (I := I) α β z a i) y) *
        chartTransitionJacEntry (I := I) α β y b j *
        chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β y) +
      chartTransitionJacEntry (I := I) α β y a i *
        (partialDeriv (E := E) k
          (fun z => chartTransitionJacEntry (I := I) α β z b j) y) *
        chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β y) +
      chartTransitionJacEntry (I := I) α β y a i *
        chartTransitionJacEntry (I := I) α β y b j *
        (partialDeriv (E := E) k
          (fun z => chartGramOnE (I := I) g β a b
            (chartTransitionMap (I := I) α β z)) y) := by
  classical
  -- Differentiability of the three factors at `y`.
  have hJa : DifferentiableAt ℝ
      (fun z => chartTransitionJacEntry (I := I) α β z a i) y :=
    chartTransitionJacEntry_differentiableAt (I := I) α β a i hy
  have hJb : DifferentiableAt ℝ
      (fun z => chartTransitionJacEntry (I := I) α β z b j) y :=
    chartTransitionJacEntry_differentiableAt (I := I) α β b j hy
  have hG : DifferentiableAt ℝ
      (fun z => chartGramOnE (I := I) g β a b
        (chartTransitionMap (I := I) α β z)) y := by
    set T := chartTransitionMap (I := I) α β with hT_def
    have hTy_int : T y ∈ interior (extChartAt I β).target := by
      rw [hT_def]; exact chartTransitionMap_mem_interior_target (I := I) α β hy
    have hGβ_diff : DifferentiableAt ℝ (chartGramOnE (I := I) g β a b) (T y) := by
      have hcd : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g β a b)
          (extChartAt I β).target := chartGramOnE_contDiffOn (I := I) g β a b
      have hcd_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g β a b)
          (interior (extChartAt I β).target) := hcd.mono interior_subset
      exact (hcd_int.contDiffAt
        (isOpen_interior.mem_nhds hTy_int)).differentiableAt (by simp)
    have hT_diff : DifferentiableAt ℝ T y := by
      rw [hT_def]; exact chartTransitionMap_differentiableAt (I := I) α β hy
    exact hGβ_diff.comp y hT_diff
  -- Apply the two-factor Leibniz rule twice. First split `(Ja * Jb) * G`.
  have hJab : DifferentiableAt ℝ
      (fun z => chartTransitionJacEntry (I := I) α β z a i *
        chartTransitionJacEntry (I := I) α β z b j) y := hJa.mul hJb
  rw [partialDeriv_mul k _ _ hJab hG]
  rw [partialDeriv_mul k _ _ hJa hJb]
  ring

omit [IsManifold I ∞ M] in
/-- `partialDeriv` commutes with a finite sum of differentiable functions. -/
lemma partialDeriv_finset_sum {ι : Type*} (s : Finset ι)
    (k : Fin (Module.finrank ℝ E)) (f : ι → E → ℝ) {y : E}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) y) :
    partialDeriv (E := E) k (fun z => ∑ i ∈ s, f i z) y =
      ∑ i ∈ s, partialDeriv (E := E) k (f i) y := by
  unfold partialDeriv
  rw [fderiv_fun_sum hf]
  rw [ContinuousLinearMap.sum_apply]

omit [IsManifold I ∞ M] in
/-- `partialDeriv` of a double finite sum of differentiable functions. -/
lemma partialDeriv_double_finset_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (k : Fin (Module.finrank ℝ E)) (f : ι → κ → E → ℝ) {y : E}
    (hf : ∀ a ∈ s, ∀ b ∈ t, DifferentiableAt ℝ (f a b) y) :
    partialDeriv (E := E) k (fun z => ∑ a ∈ s, ∑ b ∈ t, f a b z) y =
      ∑ a ∈ s, ∑ b ∈ t, partialDeriv (E := E) k (f a b) y := by
  rw [partialDeriv_finset_sum s k (fun a z => ∑ b ∈ t, f a b z)
    (fun a ha => DifferentiableAt.fun_sum (fun b hb => hf a ha b hb))]
  refine Finset.sum_congr rfl ?_
  intro a ha
  exact partialDeriv_finset_sum t k (fun b z => f a b z) (fun b hb => hf a ha b hb)

/-- **Differentiated Gram pullback.** Differentiating the covariant Gram-pullback
identity at a chart-transition-source point `y`, the chart-coordinate partial
derivative `∂_k G_α(y)_{ij}` expands as the sum of three groups of terms: the
two Jacobian-derivative ("second derivative of `T`") terms, and the
chart-rule term that pulls `∂_c G_β(T y)_{ab}` through the Jacobian. -/
theorem partialDeriv_chartGramOnE_eq_sum_chartTransition [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α β : M)
    (i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ chartTransitionSource (I := I) α β) :
    partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y =
      ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        ((partialDeriv (E := E) k
            (fun z => chartTransitionJacEntry (I := I) α β z a i) y) *
          chartTransitionJacEntry (I := I) α β y b j *
          chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β y) +
        chartTransitionJacEntry (I := I) α β y a i *
          (partialDeriv (E := E) k
            (fun z => chartTransitionJacEntry (I := I) α β z b j) y) *
          chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β y) +
        chartTransitionJacEntry (I := I) α β y a i *
          chartTransitionJacEntry (I := I) α β y b j *
          (∑ c : Fin (Module.finrank ℝ E),
            chartTransitionJacEntry (I := I) α β y c k *
              partialDeriv (E := E) c (chartGramOnE (I := I) g β a b)
                (chartTransitionMap (I := I) α β y))) := by
  classical
  have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
    chartTransitionSource_isOpen (I := I) α β
  have h_nhds : chartTransitionSource (I := I) α β ∈ nhds y := h_open.mem_nhds hy
  -- Step 1: the pullback identity holds on a neighbourhood of `y`.
  have h_eventually :
      chartGramOnE (I := I) g α i j =ᶠ[nhds y]
        (fun z => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartTransitionJacEntry (I := I) α β z a i *
            chartTransitionJacEntry (I := I) α β z b j *
            chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β z)) := by
    filter_upwards [h_nhds] with z hz
    exact chartGramOnE_eq_sum_chartTransition_on_source (I := I) g α β hz i j
  -- Step 2: equal `partialDeriv` because they agree on a neighbourhood.
  have h_pd_eq : partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y =
      partialDeriv (E := E) k
        (fun z => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartTransitionJacEntry (I := I) α β z a i *
            chartTransitionJacEntry (I := I) α β z b j *
            chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β z)) y := by
    unfold partialDeriv
    rw [h_eventually.fderiv_eq]
  rw [h_pd_eq]
  -- Step 3: distribute `∂_k` over the double sum.
  have hdiff : ∀ a ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
      ∀ b ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
      DifferentiableAt ℝ
        (fun z => chartTransitionJacEntry (I := I) α β z a i *
          chartTransitionJacEntry (I := I) α β z b j *
          chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β z)) y := by
    intro a _ b _
    have hJa : DifferentiableAt ℝ
        (fun z => chartTransitionJacEntry (I := I) α β z a i) y :=
      chartTransitionJacEntry_differentiableAt (I := I) α β a i hy
    have hJb : DifferentiableAt ℝ
        (fun z => chartTransitionJacEntry (I := I) α β z b j) y :=
      chartTransitionJacEntry_differentiableAt (I := I) α β b j hy
    have hG : DifferentiableAt ℝ
        (fun z => chartGramOnE (I := I) g β a b
          (chartTransitionMap (I := I) α β z)) y := by
      set T := chartTransitionMap (I := I) α β with hT_def
      have hTy_int : T y ∈ interior (extChartAt I β).target := by
        rw [hT_def]; exact chartTransitionMap_mem_interior_target (I := I) α β hy
      have hGβ_diff : DifferentiableAt ℝ (chartGramOnE (I := I) g β a b) (T y) := by
        have hcd : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g β a b)
            (extChartAt I β).target := chartGramOnE_contDiffOn (I := I) g β a b
        have hcd_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g β a b)
            (interior (extChartAt I β).target) := hcd.mono interior_subset
        exact (hcd_int.contDiffAt
          (isOpen_interior.mem_nhds hTy_int)).differentiableAt (by simp)
      have hT_diff : DifferentiableAt ℝ T y := by
        rw [hT_def]; exact chartTransitionMap_differentiableAt (I := I) α β hy
      exact hGβ_diff.comp y hT_diff
    exact (hJa.mul hJb).mul hG
  rw [partialDeriv_double_finset_sum Finset.univ Finset.univ k
    (fun a b z => chartTransitionJacEntry (I := I) α β z a i *
      chartTransitionJacEntry (I := I) α β z b j *
      chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β z)) hdiff]
  -- Step 4: expand each summand via the Leibniz lemma + chain rule.
  refine Finset.sum_congr rfl ?_
  intro a _
  refine Finset.sum_congr rfl ?_
  intro b _
  rw [partialDeriv_chartTransition_pullback_summand (I := I) g α β a b i j k hy]
  rw [partialDeriv_chartGramOnE_comp_chartTransitionMap (I := I) g α β a b k hy]

/-! ## The chart-Christoffel transformation law under chart transition

We assemble the transformation law for the chart-Christoffel contraction under
the chart-transition map `T = chartTransitionMap α β`. Writing `Tv` for the
Jacobian pushforward `chartTransitionAt α β x v` of a vector `v` (chart-α
picture) into the chart-β picture, the law is
`chartChristoffelContraction g α v w x =
   chartTransitionAt β α (T x) (chartChristoffelContraction g β (Tv) (Tw) (T x))
     + D²T(v, w)`,
where the inhomogeneous "`D²T`" term is the second-derivative correction
`∑ c k, K^k_c · (∑_{ij} (∂_i J^c_j x) v^i w^j) • e_k`, with `K = `reverse
Jacobian at `T x` and `J = `forward Jacobian at `x`. -/

/-- The chart-β coordinate `a` of the Jacobian pushforward
`chartTransitionAt α β x v` is the contraction of the forward Jacobian entries
against the chart-α coordinates of `v`:
`(chartTransitionAt α β x v)^a = ∑ i, J^a_i(x) · v^i`. -/
lemma chartCoord_chartTransitionAt (α β : M) (x : E) (v : E)
    (a : Fin (Module.finrank ℝ E)) :
    chartCoord (E := E) a (chartTransitionAt (I := I) α β x v) =
      ∑ i : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) α β x a i * chartCoord (E := E) i v := by
  classical
  -- Expand `v` in the model basis, apply the (linear) CLM, read coordinate `a`.
  unfold chartCoord chartTransitionJacEntry
  have hexp : chartTransitionAt (I := I) α β x v =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr v i •
          chartTransitionAt (I := I) α β x ((chartModelBasis E) i) := by
    conv_lhs => rw [← (chartModelBasis E).sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [map_smul]
  rw [hexp, map_sum]
  rw [Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  ring

/-- The forward Jacobian at `x = extChartAt I α p` contracted on its lower index
against the reverse Jacobian at `T x` collapses to a Kronecker delta:
`∑ l, J^a_l(x) · K^l_d(T x) = δ_{a d}`, where `J = `forward Jacobian at `x`,
`K = `reverse Jacobian at `T x`. This is `chartTransitionJacEntry_mul_sum'`
packaged with the source-membership discharged from chart-source membership of
`p`. -/
lemma chartTransitionJacEntry_forward_reverse_collapse [I.Boundaryless]
    (α β : M) {p : M}
    (hp_α : p ∈ (chartAt H α).source) (hp_β : p ∈ (chartAt H β).source)
    (a d : Fin (Module.finrank ℝ E)) :
    ∑ l : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) α β (extChartAt I α p) a l *
        chartTransitionJacEntry (I := I) β α
          (chartTransitionMap (I := I) α β (extChartAt I α p)) l d =
      (if a = d then (1 : ℝ) else 0) := by
  have hx_src : extChartAt I α p ∈ chartTransitionSource (I := I) α β :=
    extChartAt_mem_chartTransitionSource (I := I) α β hp_α hp_β
  exact chartTransitionJacEntry_mul_sum' (I := I) α β hx_src a d

/-- The reverse Jacobian at `T x` contracted on its upper index against the
forward Jacobian at `x` collapses to a Kronecker delta:
`∑ a, J^a_i(x) · K^c_a(T x) = δ_{c i}`. This is `chartTransitionJacEntry_mul_sum`
packaged with the source-membership discharged from chart-source membership of
`p`. -/
lemma chartTransitionJacEntry_reverse_forward_collapse [I.Boundaryless]
    (α β : M) {p : M}
    (hp_α : p ∈ (chartAt H α).source) (hp_β : p ∈ (chartAt H β).source)
    (c i : Fin (Module.finrank ℝ E)) :
    ∑ a : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) α β (extChartAt I α p) a i *
        chartTransitionJacEntry (I := I) β α
          (chartTransitionMap (I := I) α β (extChartAt I α p)) c a =
      (if c = i then (1 : ℝ) else 0) := by
  have hx_src : extChartAt I α p ∈ chartTransitionSource (I := I) α β :=
    extChartAt_mem_chartTransitionSource (I := I) α β hp_α hp_β
  exact chartTransitionJacEntry_mul_sum (I := I) α β hx_src c i

/-- The second-derivative ("`D²T`") inhomogeneous correction in the
chart-Christoffel transformation law, as an `E`-valued bilinear contraction.
With `K = `reverse Jacobian at `T x`, `J = `forward Jacobian at `x`, and
`∂_i J^c_j(x)` the chart-coordinate partial derivative of the forward Jacobian
entry, it is
`∑ k c, K^k_c(T x) · (∑_{ij} (∂_i J^c_j x) v^i w^j) • e_k`. -/
def chartTransitionSecondDerivCorrection (α β : M) (v w : E) (x : E) : E :=
  ∑ k : Fin (Module.finrank ℝ E),
    (∑ c : Fin (Module.finrank ℝ E),
      chartTransitionJacEntry (I := I) β α (chartTransitionMap (I := I) α β x) k c *
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i
            (fun z => chartTransitionJacEntry (I := I) α β z c j) x *
            chartCoord (E := E) i v * chartCoord (E := E) j w)) •
      chartModelBasis E k

@[simp] lemma chartTransitionSecondDerivCorrection_def
    (α β : M) (v w : E) (x : E) :
    chartTransitionSecondDerivCorrection (I := I) α β v w x =
      ∑ k : Fin (Module.finrank ℝ E),
        (∑ c : Fin (Module.finrank ℝ E),
          chartTransitionJacEntry (I := I) β α
            (chartTransitionMap (I := I) α β x) k c *
            (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) i
                (fun z => chartTransitionJacEntry (I := I) α β z c j) x *
                chartCoord (E := E) i v * chartCoord (E := E) j w)) •
          chartModelBasis E k := rfl

/-- **Schwarz symmetry of the chart-transition Jacobian entry.** The mixed
second derivative of the chart-transition map is symmetric: differentiating the
forward Jacobian entry `z ↦ J^a_l(z)` in direction `i` equals differentiating
`z ↦ J^a_i(z)` in direction `l`, at any point of the open source. -/
lemma partialDeriv_chartTransitionJacEntry_swap [I.Boundaryless]
    (α β : M) (a i l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ chartTransitionSource (I := I) α β) :
    partialDeriv (E := E) i
        (fun z => chartTransitionJacEntry (I := I) α β z a l) y =
      partialDeriv (E := E) l
        (fun z => chartTransitionJacEntry (I := I) α β z a i) y := by
  classical
  set T := chartTransitionMap (I := I) α β with hT_def
  -- The coordinate functional `coord a : E →L[ℝ] ℝ` (continuous, finite dim).
  set coordCLM : E →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((chartModelBasis E).coord a) with hcoordCLM
  -- Schwarz at `y`: `T` is `ContDiffAt ∞`.
  have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
    chartTransitionSource_isOpen (I := I) α β
  have hcontDiffAt : ContDiffAt ℝ ∞ T y := by
    rw [hT_def]; exact chartTransitionMap_contDiffAt (I := I) α β hy
  have hsymm : IsSymmSndFDerivAt ℝ T y := by
    refine ContDiffAt.isSymmSndFDerivAt hcontDiffAt ?_
    rw [minSmoothness_of_isRCLikeNormedField]
    decide
  -- `fderiv T` is differentiable at `y` (smooth on the open source).
  have hsmooth_on : ContDiffOn ℝ ∞ T (chartTransitionSource (I := I) α β) := by
    rw [hT_def]; exact chartTransitionMap_contDiffOn (I := I) α β
  have hT_diff : DifferentiableAt ℝ (fderiv ℝ T) y := by
    have hfderiv_smooth : ContDiffOn ℝ ∞ (fderiv ℝ T)
        (chartTransitionSource (I := I) α β) :=
      hsmooth_on.fderiv_of_isOpen h_open (by rw [ENat.coe_top_add_one])
    exact (hfderiv_smooth.contDiffAt (h_open.mem_nhds hy)).differentiableAt (by simp)
  -- The Jacobian entry as a composite `coord a ∘ apply e_l ∘ fderiv T`.
  have hkey : ∀ p q : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) p
          (fun z => chartTransitionJacEntry (I := I) α β z a q) y =
        coordCLM ((fderiv ℝ (fderiv ℝ T) y ((chartModelBasis E) p))
          ((chartModelBasis E) q)) := by
    intro p q
    unfold partialDeriv
    -- `J^a_q (z) = coordCLM (fderiv T z (e_q))`.
    set L : (E →L[ℝ] E) →L[ℝ] ℝ :=
      coordCLM.comp (ContinuousLinearMap.apply ℝ E ((chartModelBasis E) q)) with hL
    have hcomp_eq : (fun z : E =>
          chartTransitionJacEntry (I := I) α β z a q) = L ∘ (fderiv ℝ T) := by
      funext z
      rw [chartTransitionJacEntry_def, hL, hcoordCLM]
      simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.apply_apply, LinearMap.coe_toContinuousLinearMap',
        Module.Basis.coord_apply, chartTransitionAt_def, hT_def]
    rw [hcomp_eq, fderiv_comp y L.differentiableAt hT_diff]
    rw [ContinuousLinearMap.comp_apply, L.fderiv]
    rw [hL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  rw [hkey i l, hkey l i]
  -- Schwarz: `D²T(e_i)(e_l) = D²T(e_l)(e_i)`.
  rw [hsymm ((chartModelBasis E) i) ((chartModelBasis E) l)]

/-! ## The chart-Christoffel transformation law (symbol level)

We assemble the classical transformation law for the chart-coordinate
Christoffel symbol under the chart-transition map. Fix a manifold point `p`
lying in both chart sources, write `x := extChartAt I α p` and
`T x := chartTransitionMap α β x`, and abbreviate

* `J^a_i := chartTransitionJacEntry α β x a i` (forward Jacobian at `x`),
* `K^k_c := chartTransitionJacEntry β α (T x) k c` (reverse Jacobian at `T x`),
* `Γ̄^c_{ab} := chartChristoffel g β a b c (T x)` (chart-β Christoffel at `T x`),
* `∂_i J^c_j := partialDeriv i (fun z => chartTransitionJacEntry α β z c j) x`.

The transformation law reads
`Γ_α^k_{ij}(x) = ∑_c K^k_c · (∑_{ab} Γ̄^c_{ab} · J^a_i · J^b_j) + ∑_c K^k_c · ∂_i J^c_j`,
the second (inhomogeneous) group being the failure of the Jacobian to be
constant. -/

/-- The chart-β inverse picture of the transition image returns the base
point: `(extChartAt I β).symm (T x) = p` whenever `x = extChartAt I α p` and
`p` lies in both chart sources. -/
lemma chartTransitionMap_extChartAt_symm
    (α β : M) {p : M}
    (hp_α : p ∈ (chartAt H α).source) (hp_β : p ∈ (chartAt H β).source) :
    (extChartAt I β).symm
        (chartTransitionMap (I := I) α β (extChartAt I α p)) = p := by
  rw [chartTransitionMap_apply_extChartAt (I := I) α β hp_α]
  have hp_β_src : p ∈ (extChartAt I β).source := by
    rw [extChartAt_source (I := I)]; exact hp_β
  exact (extChartAt I β).left_inv hp_β_src

/-- Diagonal contraction of the chart-β inverse Gram at `p` against the chart-β
Gram pulled to the transition image `T x`: `∑_d Ḡ⁻¹(p)^{cd} Ḡ_{db}(T x) = δ_{cb}`,
where `x = extChartAt I α p`, `T x = chartTransitionMap α β x`, and we use
`(extChartAt I β).symm (T x) = p`. -/
lemma chartInvGramBeta_mul_chartGramOnE_diag
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α β : M) {p : M}
    (hp_α : p ∈ (chartAt H α).source) (hp_β : p ∈ (chartAt H β).source)
    (c b : Fin (Module.finrank ℝ E)) :
    ∑ d : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g β p c d *
        chartGramOnE (I := I) g β d b
          (chartTransitionMap (I := I) α β (extChartAt I α p)) =
      (if c = b then (1 : ℝ) else 0) := by
  classical
  have hp_triv_β : p ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
    change p ∈ (chartAt H β).source; exact hp_β
  have hsymm : (extChartAt I β).symm
      (chartTransitionMap (I := I) α β (extChartAt I α p)) = p :=
    chartTransitionMap_extChartAt_symm (I := I) α β hp_α hp_β
  have hG : ∀ d : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g β d b
          (chartTransitionMap (I := I) α β (extChartAt I α p)) =
        chartGramMatrix (I := I) g β p d b := by
    intro d
    rw [chartGramOnE_def, hsymm]
  rw [Finset.sum_congr rfl (fun d (_ : d ∈ Finset.univ) =>
    congrArg (fun t => chartInvGramMatrix (I := I) g β p c d * t) (hG d))]
  have hmul := chartInvGramMatrix_mul_chartGramMatrix (I := I) g β hp_triv_β
  have := congrFun (congrFun hmul c) b
  rw [Matrix.mul_apply] at this
  rw [this, Matrix.one_apply]

/-- **The raw collapse identity.** Contracting the chart-α symmetrised metric
derivative bundle `S(i,j,l) := ∂_i G_α(l,j) + ∂_j G_α(l,i) - ∂_l G_α(i,j)` against
the reverse Jacobian `K^l_d` reproduces the chart-β symmetrised bundle
`S̄(a,b,d) := ∂_a Ḡ(d,b) + ∂_b Ḡ(d,a) - ∂_d Ḡ(a,b)` evaluated at `T x` and
contracted with the forward Jacobian, plus twice the chart-β Gram against the
second derivative of the Jacobian:
`∑_l K^l_d S(i,j,l) = ∑_{ab} S̄(a,b,d)(T x) J^a_i J^b_j + 2 ∑_b Ḡ_{db}(T x) ∂_i J^b_j`. -/
lemma chartTransition_raw_collapse [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α β : M) {p : M}
    (hp_α : p ∈ (chartAt H α).source) (hp_β : p ∈ (chartAt H β).source)
    (i j d : Fin (Module.finrank ℝ E)) :
    ∑ l : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) β α
            (chartTransitionMap (I := I) α β (extChartAt I α p)) l d *
          (partialDeriv (E := E) i
              (chartGramOnE (I := I) g α l j) (extChartAt I α p) +
            partialDeriv (E := E) j
              (chartGramOnE (I := I) g α l i) (extChartAt I α p) -
            partialDeriv (E := E) l
              (chartGramOnE (I := I) g α i j) (extChartAt I α p)) =
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) a
              (chartGramOnE (I := I) g β d b)
              (chartTransitionMap (I := I) α β (extChartAt I α p)) +
            partialDeriv (E := E) b
              (chartGramOnE (I := I) g β d a)
              (chartTransitionMap (I := I) α β (extChartAt I α p)) -
            partialDeriv (E := E) d
              (chartGramOnE (I := I) g β a b)
              (chartTransitionMap (I := I) α β (extChartAt I α p))) *
            chartTransitionJacEntry (I := I) α β (extChartAt I α p) a i *
            chartTransitionJacEntry (I := I) α β (extChartAt I α p) b j) +
      2 * ∑ b : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g β d b
            (chartTransitionMap (I := I) α β (extChartAt I α p)) *
            partialDeriv (E := E) i
              (fun z => chartTransitionJacEntry (I := I) α β z b j)
              (extChartAt I α p) := by
  classical
  set x := extChartAt I α p with hx_def
  set Tx := chartTransitionMap (I := I) α β x with hTx_def
  have hx_src : x ∈ chartTransitionSource (I := I) α β :=
    extChartAt_mem_chartTransitionSource (I := I) α β hp_α hp_β
  -- Abbreviations.
  set J : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun a r => chartTransitionJacEntry (I := I) α β x a r with hJ
  set K : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun l c => chartTransitionJacEntry (I := I) β α Tx l c with hK
  set dJ : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
    fun t a r => partialDeriv (E := E) t
      (fun z => chartTransitionJacEntry (I := I) α β z a r) x with hdJ
  set Gb : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun a b => chartGramOnE (I := I) g β a b Tx with hGb
  set dGb : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
    fun t a b => partialDeriv (E := E) t (chartGramOnE (I := I) g β a b) Tx with hdGb
  -- Forward/reverse collapse: `∑_l J^a_l K^l_d = δ_{a d}`.
  have hFR : ∀ a d : Fin (Module.finrank ℝ E),
      ∑ l, J a l * K l d = (if a = d then (1 : ℝ) else 0) := by
    intro a d
    have h := chartTransitionJacEntry_forward_reverse_collapse (I := I) α β hp_α hp_β a d
    simpa [hJ, hK, hx_def, hTx_def] using h
  -- Symmetry of Gb.
  have hGbsymm : ∀ a b : Fin (Module.finrank ℝ E), Gb a b = Gb b a := by
    intro a b; rw [hGb]; exact chartGramOnE_symm (I := I) g β a b Tx
  -- Schwarz: `dJ t a r = dJ r a t`.
  have hSchwarz : ∀ t a r : Fin (Module.finrank ℝ E), dJ t a r = dJ r a t := by
    intro t a r
    rw [hdJ]
    exact partialDeriv_chartTransitionJacEntry_swap (I := I) α β a t r hx_src
  -- Differentiated Gram, abbreviated form: for diff index `t` and gram indices `r s`,
  -- `∂_t G_α(r,s)(x) = ∑_a ∑_b [ dJ t a r · J b s · Gb a b + J a r · dJ t b s · Gb a b
  --                              + J a r · J b s · (∑_c J c t · dGb c a b) ]`.
  have hDG : ∀ t r s : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) t (chartGramOnE (I := I) g α r s) x =
        ∑ a, ∑ b, (dJ t a r * J b s * Gb a b
          + J a r * dJ t b s * Gb a b
          + J a r * J b s * (∑ c, J c t * dGb c a b)) := by
    intro t r s
    have h := partialDeriv_chartGramOnE_eq_sum_chartTransition (I := I) g α β r s t hx_src
    rw [h]
  -- Collapse helper: `∑_l ∑_a ∑_b (K l d * J a l) * W a b = ∑_b W d b`.
  have hCol : ∀ (W : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ),
      ∑ l, ∑ a, ∑ b, (K l d * J a l) * W a b = ∑ b, W d b := by
    intro W
    -- Reorder to `∑ a, ∑ b, ∑ l`.
    have hreorder :
        (∑ l, ∑ a, ∑ b, (K l d * J a l) * W a b) =
          ∑ a, ∑ b, ∑ l, (K l d * J a l) * W a b := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro a _
      rw [Finset.sum_comm]
    rw [hreorder]
    -- Collapse the `l`-sum to `δ_{a d} * W a b`.
    have hinner : ∀ a b : Fin (Module.finrank ℝ E),
        (∑ l, (K l d * J a l) * W a b) =
          (if a = d then (1 : ℝ) else 0) * W a b := by
      intro a b
      rw [← Finset.sum_mul]
      congr 1
      rw [← hFR a d]
      refine Finset.sum_congr rfl ?_; intro l _
      ring
    rw [Finset.sum_congr rfl (fun a _ =>
      Finset.sum_congr rfl (fun b _ => hinner a b))]
    -- ∑ a, ∑ b, (if a=d then 1 else 0) * W a b = ∑ b, W d b.
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_; intro b _
    rw [Finset.sum_eq_single d]
    · rw [if_pos rfl, one_mul]
    · intro a _ ha; rw [if_neg ha, zero_mul]
    · intro hd; exact absurd (Finset.mem_univ d) hd
  -- Group-A coefficient (no collapse): `Acoef t a := ∑_l K l d * dJ t a l`.
  set Acoef : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun t a => ∑ l, K l d * dJ t a l with hAcoef
  -- The three group-A aggregates.
  set A1 : ℝ := ∑ a, ∑ b, Acoef i a * J b j * Gb a b with hA1
  set A2 : ℝ := ∑ a, ∑ b, Acoef j a * J b i * Gb a b with hA2
  -- The surviving second-derivative term.
  set BB : ℝ := ∑ b, Gb d b * dJ i b j with hBB
  -- The three chain-rule aggregates.
  set C1 : ℝ := ∑ a, ∑ b, J a i * J b j * dGb a d b with hC1
  set C2 : ℝ := ∑ a, ∑ b, J a i * J b j * dGb b d a with hC2
  set C3 : ℝ := ∑ a, ∑ b, J a i * J b j * dGb d a b with hC3
  -- Term 1: `∑_l K l d · ∂_i G_α(l,j)(x) = A1 + BB + C1`.
  have hTerm1 :
      (∑ l, K l d * partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x) =
        A1 + BB + C1 := by
    have hstep : ∀ l, K l d * partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x =
        (∑ a, ∑ b, K l d * (dJ i a l * J b j * Gb a b))
          + (∑ a, ∑ b, (K l d * J a l) * (dJ i b j * Gb a b))
          + (∑ a, ∑ b, (K l d * J a l) * (J b j * (∑ c, J c i * dGb c a b))) := by
      intro l
      rw [hDG i l j, Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_; intro a _
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_; intro b _
      ring
    rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hstep l)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    refine congr_arg₂ (· + ·) (congr_arg₂ (· + ·) ?_ ?_) ?_
    · -- Group A1: ∑_l ∑_a ∑_b K l d (dJ i a l · J b j · Gb a b) = A1.
      rw [hA1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro a _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro b _
      rw [hAcoef]
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_; intro l _
      ring
    · -- Group B → BB via hCol with W a b := dJ i b j · Gb a b.
      rw [hBB]
      have := hCol (fun a b => dJ i b j * Gb a b)
      rw [this]
      refine Finset.sum_congr rfl ?_; intro b _
      ring
    · -- Group C → C1 via hCol with W a b := J b j · (∑ c J c i dGb c a b).
      rw [hC1]
      have := hCol (fun a b => J b j * (∑ c, J c i * dGb c a b))
      rw [this]
      -- ∑ b, J b j · (∑ c, J c i dGb c d b) = ∑ a ∑ b, J a i J b j dGb a d b.
      rw [show (∑ b, J b j * (∑ c, J c i * dGb c d b)) =
            ∑ b, ∑ c, J c i * J b j * dGb c d b from by
        refine Finset.sum_congr rfl ?_; intro b _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_; intro c _
        ring]
      rw [Finset.sum_comm]
  -- Term 2: `∑_l K l d · ∂_j G_α(l,i)(x) = A2 + BB + C2`.
  have hTerm2 :
      (∑ l, K l d * partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x) =
        A2 + BB + C2 := by
    have hstep : ∀ l, K l d * partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x =
        (∑ a, ∑ b, K l d * (dJ j a l * J b i * Gb a b))
          + (∑ a, ∑ b, (K l d * J a l) * (dJ j b i * Gb a b))
          + (∑ a, ∑ b, (K l d * J a l) * (J b i * (∑ c, J c j * dGb c a b))) := by
      intro l
      rw [hDG j l i, Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_; intro a _
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_; intro b _
      ring
    rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hstep l)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    refine congr_arg₂ (· + ·) (congr_arg₂ (· + ·) ?_ ?_) ?_
    · -- Group A2.
      rw [hA2]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro a _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro b _
      rw [hAcoef]
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_; intro l _
      ring
    · -- Group B → BB (using Schwarz: dJ j b i = dJ i b j).
      rw [hBB]
      have := hCol (fun a b => dJ j b i * Gb a b)
      rw [this]
      refine Finset.sum_congr rfl ?_; intro b _
      rw [hSchwarz j b i]
      ring
    · -- Group C → C2.
      rw [hC2]
      have := hCol (fun a b => J b i * (∑ c, J c j * dGb c a b))
      rw [this]
      -- ∑ b, J b i · (∑ c, J c j dGb c d b) = ∑ a ∑ b, J a i J b j dGb b d a.
      -- ∑ b, J b i · (∑ c, J c j dGb c d b): rename (b,c)→(a,b) to match C2.
      refine Finset.sum_congr rfl ?_; intro a _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_; intro b _
      ring
  -- Term 3: `∑_l K l d · ∂_l G_α(i,j)(x) = A1 + A2 + C3`.
  have hTerm3 :
      (∑ l, K l d * partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x) =
        A1 + A2 + C3 := by
    have hstep : ∀ l, K l d * partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x =
        (∑ a, ∑ b, K l d * (dJ l a i * J b j * Gb a b))
          + (∑ a, ∑ b, K l d * (J a i * dJ l b j * Gb a b))
          + (∑ a, ∑ b, J a i * J b j * (∑ c, (K l d * J c l) * dGb c a b)) := by
      intro l
      rw [hDG l i j, Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_; intro a _
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_; intro b _
      rw [show J a i * J b j * (∑ c, (K l d * J c l) * dGb c a b) =
            K l d * (J a i * J b j * (∑ c, J c l * dGb c a b)) from by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_; intro c _
        ring]
      ring
    rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hstep l)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    refine congr_arg₂ (· + ·) (congr_arg₂ (· + ·) ?_ ?_) ?_
    · -- Group A3 = A1 (Schwarz: dJ l a i = dJ i a l).
      rw [hA1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro a _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro b _
      rw [hAcoef]
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_; intro l _
      rw [hSchwarz l a i]
      ring
    · -- Group B3 = A2 (Schwarz: dJ l b j = dJ j b l, then a↔b, Gb symm).
      rw [hA2]
      -- Convert LHS to `∑ a ∑ b (∑ l K l d dJ j b l) J a i Gb a b`.
      rw [show (∑ l, ∑ a, ∑ b, K l d * (J a i * dJ l b j * Gb a b)) =
            ∑ a, ∑ b, (∑ l, K l d * dJ j b l) * J a i * Gb a b from by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_; intro a _
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_; intro b _
        simp only [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_; intro l _
        rw [hSchwarz l b j]; ring]
      -- Swap (a,b), Gb symm; A2 = ∑ a ∑ b Acoef j a · J b i · Gb a b.
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro a _
      refine Finset.sum_congr rfl ?_; intro b _
      rw [hAcoef, hGbsymm b a]
    · -- Group C3 = C3 (collapse `∑_c (∑_l K l d J c l) dGb c a b = ∑_c δ_{cd} ... = dGb d a b`).
      rw [hC3]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro a _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro b _
      -- ∑ l, J a i J b j (∑ c (K l d J c l) dGb c a b) = J a i J b j dGb d a b.
      rw [show (∑ l, J a i * J b j * (∑ c, (K l d * J c l) * dGb c a b)) =
            J a i * J b j * (∑ c, (∑ l, K l d * J c l) * dGb c a b) from by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_; intro c _
        rw [Finset.sum_mul]]
      congr 1
      rw [Finset.sum_eq_single d]
      · rw [show (∑ l, K l d * J d l) = (if d = d then (1 : ℝ) else 0) from by
          rw [← hFR d d]; refine Finset.sum_congr rfl ?_; intro l _; ring]
        rw [if_pos rfl, one_mul]
      · intro c _ hc
        rw [show (∑ l, K l d * J c l) = (if c = d then (1 : ℝ) else 0) from by
          rw [← hFR c d]; refine Finset.sum_congr rfl ?_; intro l _; ring]
        rw [if_neg hc, zero_mul]
      · intro hd; exact absurd (Finset.mem_univ d) hd
  -- Combine: `Σ(d) = Term1 + Term2 - Term3 = 2·BB + (C1 + C2 - C3)`.
  have hSigma :
      (∑ l, K l d *
          (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x +
            partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x -
            partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x)) =
        2 * BB + (C1 + C2 - C3) := by
    rw [show (∑ l, K l d *
          (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x +
            partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x -
            partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x)) =
        (∑ l, K l d * partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x)
          + (∑ l, K l d * partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x)
          - (∑ l, K l d * partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x) from by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_; intro l _; ring]
    rw [hTerm1, hTerm2, hTerm3]
    ring
  -- Conclude: rewrite the goal's LHS via hSigma, RHS via the S̄ split.
  rw [show (∑ l, chartTransitionJacEntry (I := I) β α Tx l d *
        (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x +
          partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x -
          partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x)) =
      (∑ l, K l d *
        (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x +
          partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x -
          partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x)) from rfl]
  rw [hSigma]
  -- RHS of the goal: `(∑ a ∑ b S̄(a,b,d) J^a_i J^b_j) + 2 ∑ b Gb_{db} ∂_i J^b_j`.
  -- `S̄(a,b,d) = dGb a d b + dGb b d a - dGb d a b`, and `2·BB` matches the last group.
  have hRHS_S :
      (∑ a, ∑ b, (dGb a d b + dGb b d a - dGb d a b) * J a i * J b j) =
        C1 + C2 - C3 := by
    rw [hC1, hC2, hC3]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_; intro a _
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_; intro b _
    ring
  rw [show (∑ a, ∑ b,
        (partialDeriv (E := E) a (chartGramOnE (I := I) g β d b) Tx +
          partialDeriv (E := E) b (chartGramOnE (I := I) g β d a) Tx -
          partialDeriv (E := E) d (chartGramOnE (I := I) g β a b) Tx) *
          chartTransitionJacEntry (I := I) α β x a i *
          chartTransitionJacEntry (I := I) α β x b j) =
      (∑ a, ∑ b, (dGb a d b + dGb b d a - dGb d a b) * J a i * J b j) from rfl]
  rw [hRHS_S]
  rw [show (2 * ∑ b, chartGramOnE (I := I) g β d b Tx *
        partialDeriv (E := E) i
          (fun z => chartTransitionJacEntry (I := I) α β z b j) x) =
      2 * BB from rfl]
  ring

/-- **Chart-Christoffel transformation law (symbol level).** At `x = extChartAt I α p`
with `p` in both chart sources, the chart-α Christoffel symbol decomposes into the
covariant pullback of the chart-β Christoffel symbol at `T x` plus the
second-derivative inhomogeneous correction:
`Γ_α^k_{ij}(x) = ∑_c K^k_c (∑_{ab} Γ̄^c_{ab}(T x) J^a_i J^b_j) + ∑_c K^k_c (∂_i J^c_j)`. -/
theorem chartChristoffel_transform [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α β : M) {p : M}
    (hp_α : p ∈ (chartAt H α).source) (hp_β : p ∈ (chartAt H β).source)
    (i j k : Fin (Module.finrank ℝ E)) :
    chartChristoffel (I := I) g α i j k (extChartAt I α p) =
      (∑ c : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) β α
            (chartTransitionMap (I := I) α β (extChartAt I α p)) k c *
          (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g β a b c
                (chartTransitionMap (I := I) α β (extChartAt I α p)) *
              chartTransitionJacEntry (I := I) α β (extChartAt I α p) a i *
              chartTransitionJacEntry (I := I) α β (extChartAt I α p) b j)) +
      (∑ c : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) β α
            (chartTransitionMap (I := I) α β (extChartAt I α p)) k c *
          partialDeriv (E := E) i
            (fun z => chartTransitionJacEntry (I := I) α β z c j)
            (extChartAt I α p)) := by
  classical
  set x := extChartAt I α p with hx_def
  set Tx := chartTransitionMap (I := I) α β x with hTx_def
  have hsymm_α : (extChartAt I α).symm x = p := by
    rw [hx_def]
    have hp_ext_α : p ∈ (extChartAt I α).source := by
      rw [extChartAt_source (I := I)]; exact hp_α
    exact (extChartAt I α).left_inv hp_ext_α
  have hsymm_β : (extChartAt I β).symm Tx = p := by
    rw [hTx_def, hx_def]
    exact chartTransitionMap_extChartAt_symm (I := I) α β hp_α hp_β
  -- Abbreviations matching the raw-collapse lemma.
  set K : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun l c => chartTransitionJacEntry (I := I) β α Tx l c with hK
  set J : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun a r => chartTransitionJacEntry (I := I) α β x a r with hJ
  set Gbinv : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun c d => chartInvGramMatrix (I := I) g β p c d with hGbinv
  set Gb : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun a b => chartGramOnE (I := I) g β a b Tx with hGb
  set S : Fin (Module.finrank ℝ E) → ℝ :=
    fun l => partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x +
      partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x -
      partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x with hS
  set Sbar : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
    fun a b d => partialDeriv (E := E) a (chartGramOnE (I := I) g β d b) Tx +
      partialDeriv (E := E) b (chartGramOnE (I := I) g β d a) Tx -
      partialDeriv (E := E) d (chartGramOnE (I := I) g β a b) Tx with hSbar
  set dJ : Fin (Module.finrank ℝ E) → ℝ :=
    fun c => partialDeriv (E := E) i
      (fun z => chartTransitionJacEntry (I := I) α β z c j) x with hdJ
  -- Chart-β Christoffel at `Tx`: `Γ̄^c_{ab} = (1/2) ∑_d Gbinv c d · Sbar a b d`.
  have hGammaBar : ∀ a b c : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g β a b c Tx =
        (1 / 2 : ℝ) * ∑ d, Gbinv c d * Sbar a b d := by
    intro a b c
    rw [chartChristoffel_def, hsymm_β]
  -- The diagonal contraction `∑_d Gbinv c d · Gb d b = δ_{c b}`.
  have hDiag : ∀ c b : Fin (Module.finrank ℝ E),
      ∑ d, Gbinv c d * Gb d b = (if c = b then (1 : ℝ) else 0) := by
    intro c b
    have h := chartInvGramBeta_mul_chartGramOnE_diag (I := I) g α β hp_α hp_β c b
    simpa [hGbinv, hGb, hx_def, hTx_def] using h
  -- The raw collapse, abbreviated.
  have hRaw : ∀ d : Fin (Module.finrank ℝ E),
      ∑ l, K l d * S l =
        (∑ a, ∑ b, Sbar a b d * J a i * J b j)
          + 2 * ∑ b, Gb d b *
              partialDeriv (E := E) i
                (fun z => chartTransitionJacEntry (I := I) α β z b j) x := by
    intro d
    have h := chartTransition_raw_collapse (I := I) g α β hp_α hp_β i j d
    rw [hK, hS]
    rw [show (∑ l, chartTransitionJacEntry (I := I) β α Tx l d *
        (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x +
          partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x -
          partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x)) =
        ∑ l, chartTransitionJacEntry (I := I) β α
            (chartTransitionMap (I := I) α β (extChartAt I α p)) l d *
          (partialDeriv (E := E) i
              (chartGramOnE (I := I) g α l j) (extChartAt I α p) +
            partialDeriv (E := E) j
              (chartGramOnE (I := I) g α l i) (extChartAt I α p) -
            partialDeriv (E := E) l
              (chartGramOnE (I := I) g α i j) (extChartAt I α p)) from rfl]
    rw [h, hSbar, hGb]
  -- Master per-`c` identity.
  have hMaster : ∀ c : Fin (Module.finrank ℝ E),
      (1 / 2 : ℝ) * ∑ d, Gbinv c d * (∑ l, K l d * S l) =
        (∑ a, ∑ b, chartChristoffel (I := I) g β a b c Tx * J a i * J b j)
          + dJ c := by
    intro c
    rw [Finset.sum_congr rfl (fun d (_ : d ∈ Finset.univ) =>
      congrArg (fun t => Gbinv c d * t) (hRaw d))]
    rw [show (∑ d, Gbinv c d * ((∑ a, ∑ b, Sbar a b d * J a i * J b j)
          + 2 * ∑ b, Gb d b *
              partialDeriv (E := E) i
                (fun z => chartTransitionJacEntry (I := I) α β z b j) x)) =
        (∑ d, Gbinv c d * (∑ a, ∑ b, Sbar a b d * J a i * J b j))
          + (∑ d, Gbinv c d * (2 * ∑ b, Gb d b *
              partialDeriv (E := E) i
                (fun z => chartTransitionJacEntry (I := I) α β z b j) x)) from by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_; intro d _; ring]
    rw [mul_add]
    congr 1
    · -- Both sides equal `∑ a ∑ b ∑ d (1/2) Gbinv c d Sbar a b d J a i J b j`.
      have hLHS : (1 / 2 : ℝ) * ∑ d, Gbinv c d * (∑ a, ∑ b, Sbar a b d * J a i * J b j) =
          ∑ d, ∑ a, ∑ b, (1 / 2 : ℝ) * (Gbinv c d * Sbar a b d * J a i * J b j) := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_; intro d _
        refine Finset.sum_congr rfl ?_; intro a _
        refine Finset.sum_congr rfl ?_; intro b _
        ring
      have hRHS : (∑ a, ∑ b, chartChristoffel (I := I) g β a b c Tx * J a i * J b j) =
          ∑ a, ∑ b, ∑ d, (1 / 2 : ℝ) * (Gbinv c d * Sbar a b d * J a i * J b j) := by
        refine Finset.sum_congr rfl ?_; intro a _
        refine Finset.sum_congr rfl ?_; intro b _
        rw [hGammaBar a b c]
        simp only [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_; intro d _
        ring
      rw [hLHS, hRHS]
      -- Reorder `∑ d ∑ a ∑ b` to `∑ a ∑ b ∑ d`.
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro a _
      rw [Finset.sum_comm]
    · rw [hdJ]
      rw [show (∑ d, Gbinv c d * (2 * ∑ b, Gb d b *
            partialDeriv (E := E) i
              (fun z => chartTransitionJacEntry (I := I) α β z b j) x)) =
          2 * ∑ b, (∑ d, Gbinv c d * Gb d b) *
            partialDeriv (E := E) i
              (fun z => chartTransitionJacEntry (I := I) α β z b j) x from by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_; intro b _
        refine Finset.sum_congr rfl ?_; intro d _
        ring]
      rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) =>
        show (∑ d, Gbinv c d * Gb d b) * partialDeriv (E := E) i
            (fun z => chartTransitionJacEntry (I := I) α β z b j) x =
          (if c = b then partialDeriv (E := E) i
            (fun z => chartTransitionJacEntry (I := I) α β z b j) x else 0) from by
          rw [hDiag c b]
          by_cases h : c = b
          · rw [if_pos h, if_pos h, one_mul]
          · rw [if_neg h, if_neg h, zero_mul])]
      rw [Finset.sum_ite_eq Finset.univ c
        (fun b => partialDeriv (E := E) i
          (fun z => chartTransitionJacEntry (I := I) α β z b j) x)]
      rw [if_pos (Finset.mem_univ c)]
      ring
  -- Assemble.
  rw [chartChristoffel_def, hsymm_α]
  rw [show ((1 / 2 : ℝ) * ∑ l, chartInvGramMatrix (I := I) g α p k l *
        (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x +
          partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x -
          partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x)) =
      ∑ c, K k c * ((1 / 2 : ℝ) * ∑ d, Gbinv c d * (∑ l, K l d * S l)) from by
    rw [Finset.mul_sum]
    have hExpand : ∀ l, (1 / 2 : ℝ) * (chartInvGramMatrix (I := I) g α p k l * S l) =
        ∑ c, ∑ d, (1 / 2 : ℝ) * (K k c * (K l d * Gbinv c d)) * S l := by
      intro l
      rw [chartInvGramMatrix_eq_sum_chartTransition (I := I) g α β hp_α hp_β k l]
      rw [← hx_def, ← hTx_def]
      simp only [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_; intro c _
      refine Finset.sum_congr rfl ?_; intro d _
      rw [hK, hGbinv]
      ring
    rw [show (∑ l, (1 / 2 : ℝ) * (chartInvGramMatrix (I := I) g α p k l *
            (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x +
              partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x -
              partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x))) =
          ∑ l, ∑ c, ∑ d, (1 / 2 : ℝ) * (K k c * (K l d * Gbinv c d)) * S l from by
      refine Finset.sum_congr rfl ?_; intro l _
      rw [show chartInvGramMatrix (I := I) g α p k l *
            (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x +
              partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x -
              partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x) =
          chartInvGramMatrix (I := I) g α p k l * S l from rfl]
      rw [hExpand l]]
    -- LHS now `∑ l ∑ c ∑ d (...)`; RHS `∑ c, K k c ((1/2) ∑ d Gbinv c d (∑ l K l d S l))`.
    rw [show (∑ c, K k c * ((1 / 2 : ℝ) * ∑ d, Gbinv c d * (∑ l, K l d * S l))) =
          ∑ c, ∑ d, ∑ l, (1 / 2 : ℝ) * (K k c * (K l d * Gbinv c d)) * S l from by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_; intro c _
      refine Finset.sum_congr rfl ?_; intro d _
      refine Finset.sum_congr rfl ?_; intro l _
      ring]
    -- Reorder LHS `∑ l ∑ c ∑ d` to `∑ c ∑ d ∑ l`.
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_; intro c _
    rw [Finset.sum_comm]]
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) =>
    congrArg (fun t => K k c * t) (hMaster c))]
  rw [show (∑ c, K k c *
        ((∑ a, ∑ b, chartChristoffel (I := I) g β a b c Tx * J a i * J b j) + dJ c)) =
      (∑ c, K k c * (∑ a, ∑ b, chartChristoffel (I := I) g β a b c Tx * J a i * J b j))
        + (∑ c, K k c * dJ c) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_; intro c _; ring]

/-! ## The chart-Christoffel transformation law (bilinear-contraction level) -/

/-- The `l`-th chart-coordinate of the Christoffel contraction:
`chartCoord l (Γ_α(v, w)(y)) = ∑_{i,j} Γ^l_{ij}(y) · vⁱ · wʲ`. This is the
coordinate read-out of `chartChristoffelContraction`, reproved locally so the
contraction-level transformation law can be assembled in this file. -/
lemma chartCoord_chartChristoffelContraction
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α : M) (v w y : E)
    (l : Fin (Module.finrank ℝ E)) :
    chartCoord (E := E) l
        (chartChristoffelContraction (I := I) g α v w y) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j l y *
          chartCoord (E := E) i v * chartCoord (E := E) j w := by
  classical
  rw [chartChristoffelContraction_def, chartCoord, map_sum, Finsupp.finset_sum_apply]
  have hbasis : ∀ k : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr ((chartModelBasis E) k) l = if k = l then 1 else 0 :=
    fun k => (chartModelBasis E).repr_self_apply k l
  calc
    ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
          ((∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
            chartCoord (E := E) i v * chartCoord (E := E) j w) •
            chartModelBasis E k)) l
      = ∑ k : Fin (Module.finrank ℝ E),
          (∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
            chartCoord (E := E) i v * chartCoord (E := E) j w) *
            ((chartModelBasis E).repr (chartModelBasis E k) l) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    _ = ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j l y *
            chartCoord (E := E) i v * chartCoord (E := E) j w := by
        rw [Finset.sum_eq_single l]
        · rw [hbasis l]; simp
        · intro k _ hkl; rw [hbasis k, if_neg hkl]; ring
        · intro hl; exact absurd (Finset.mem_univ l) hl

/-- Reorder a five-fold finite sum, moving the fourth and fifth summation indices
to the front. -/
private lemma sum5_reorder {n : ℕ}
    (F : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ c, ∑ a, ∑ b, ∑ i, ∑ j, F c a b i j) =
      ∑ i, ∑ j, ∑ c, ∑ a, ∑ b, F c a b i j := by
  classical
  have hi : (∑ c, ∑ a, ∑ b, ∑ i, ∑ j, F c a b i j)
      = ∑ i, ∑ c, ∑ a, ∑ b, ∑ j, F c a b i j := by
    have s1 : (∑ c, ∑ a, ∑ b, ∑ i, ∑ j, F c a b i j)
        = ∑ c, ∑ a, ∑ i, ∑ b, ∑ j, F c a b i j := by
      refine Finset.sum_congr rfl (fun c _ => ?_)
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_comm]
    have s2 : (∑ c, ∑ a, ∑ i, ∑ b, ∑ j, F c a b i j)
        = ∑ c, ∑ i, ∑ a, ∑ b, ∑ j, F c a b i j := by
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Finset.sum_comm]
    have s3 : (∑ c, ∑ i, ∑ a, ∑ b, ∑ j, F c a b i j)
        = ∑ i, ∑ c, ∑ a, ∑ b, ∑ j, F c a b i j := by
      rw [Finset.sum_comm]
    rw [s1, s2, s3]
  rw [hi]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have t1 : (∑ c, ∑ a, ∑ b, ∑ j, F c a b i j)
      = ∑ c, ∑ a, ∑ j, ∑ b, F c a b i j := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
  have t2 : (∑ c, ∑ a, ∑ j, ∑ b, F c a b i j)
      = ∑ c, ∑ j, ∑ a, ∑ b, F c a b i j := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_comm]
  have t3 : (∑ c, ∑ j, ∑ a, ∑ b, F c a b i j)
      = ∑ j, ∑ c, ∑ a, ∑ b, F c a b i j := by
    rw [Finset.sum_comm]
  rw [t1, t2, t3]

/-- Reorder a three-fold finite sum, moving the second and third indices to the
front. -/
private lemma sum3_reorder {n : ℕ} (F : Fin n → Fin n → Fin n → ℝ) :
    (∑ c, ∑ i, ∑ j, F c i j) = ∑ i, ∑ j, ∑ c, F c i j := by
  classical
  have hi : (∑ c, ∑ i, ∑ j, F c i j) = ∑ i, ∑ c, ∑ j, F c i j := by
    rw [Finset.sum_comm]
  rw [hi]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]

/-- Reorganization helper: a `∑ c`-weighted bilinear contraction of the velocity
coordinates can be moved outside the velocity sums. Both sides equal the
fully-expanded five-fold sum `∑ i ∑ j ∑ c K^l_c (∑ab Γ̄ J^a_i J^b_j) v^i w^j`. -/
private lemma chartTransitionContractionReorderMain
    {n : ℕ} (K : Fin n → ℝ) (Γ : Fin n → Fin n → Fin n → ℝ)
    (J : Fin n → Fin n → ℝ) (vi wj : Fin n → ℝ) :
    (∑ c, K c *
        (∑ a, ∑ b, Γ a b c *
          (∑ i, J a i * vi i) * (∑ j, J b j * wj j))) =
      ∑ i, ∑ j, (∑ c, K c *
        (∑ a, ∑ b, Γ a b c * J a i * J b j)) * vi i * wj j := by
  classical
  -- Canonical fully-expanded five-fold sum.
  have hLHS : (∑ c, K c *
        (∑ a, ∑ b, Γ a b c *
          (∑ i, J a i * vi i) * (∑ j, J b j * wj j))) =
      ∑ c, ∑ a, ∑ b, ∑ i, ∑ j,
        K c * (Γ a b c * (J a i * vi i) * (J b j * wj j)) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [mul_assoc (Γ a b c), Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hRHS : (∑ i, ∑ j, (∑ c, K c *
        (∑ a, ∑ b, Γ a b c * J a i * J b j)) * vi i * wj j) =
      ∑ i, ∑ j, ∑ c, ∑ a, ∑ b,
        K c * (Γ a b c * (J a i * vi i) * (J b j * wj j)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hLHS, hRHS]
  -- Reorder `∑ c ∑ a ∑ b ∑ i ∑ j` into `∑ i ∑ j ∑ c ∑ a ∑ b`.
  exact sum5_reorder
    (fun c a b i j => K c * (Γ a b c * (J a i * vi i) * (J b j * wj j)))

/-- Reorganization helper for the inhomogeneous correction term: a `∑ c`-weighted
bilinear contraction of the second-derivative bundle moves outside the velocity
sums, both sides equalling `∑ i ∑ j (∑ c K^l_c ∂_i J^c_j) v^i w^j`. -/
private lemma chartTransitionContractionReorderCorr
    {n : ℕ} (K : Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (vi wj : Fin n → ℝ) :
    (∑ c, K c *
        (∑ i, ∑ j, D c i j * vi i * wj j)) =
      ∑ i, ∑ j, (∑ c, K c * D c i j) * vi i * wj j := by
  classical
  have hLHS : (∑ c, K c *
        (∑ i, ∑ j, D c i j * vi i * wj j)) =
      ∑ c, ∑ i, ∑ j, K c * (D c i j * vi i * wj j) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  have hRHS : (∑ i, ∑ j, (∑ c, K c * D c i j) * vi i * wj j) =
      ∑ i, ∑ j, ∑ c, K c * (D c i j * vi i * wj j) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring
  rw [hLHS, hRHS]
  -- Reorder `∑ c ∑ i ∑ j` into `∑ i ∑ j ∑ c`.
  exact sum3_reorder (fun c i j => K c * (D c i j * vi i * wj j))

/-- **The chart-Christoffel transformation law, bilinear-contraction form.**
Fix a manifold point `p` lying in both chart sources, write `x := extChartAt I α p`
and `T x := chartTransitionMap α β x`, and let `v w : E` be velocity vectors in
the chart-α picture. The chart-α Christoffel contraction at `x` equals the
chart-β contraction at `T x` evaluated on the Jacobian-pushforwards
`chartTransitionAt α β x v`, `chartTransitionAt α β x w`, then pulled back through
the reverse Jacobian `chartTransitionAt β α (T x)`, plus the inhomogeneous
second-derivative correction `chartTransitionSecondDerivCorrection`:
`Γ_α(v, w)(x) =
   (chartTransitionAt β α (T x)) (Γ_β(J v, J w)(T x))
     + D²T(v, w)(x)`.
This is `chartChristoffel_transform` contracted against the velocity vectors. -/
theorem chartChristoffelContraction_transform [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α β : M) {p : M}
    (hp_α : p ∈ (chartAt H α).source) (hp_β : p ∈ (chartAt H β).source)
    (v w : E) :
    chartChristoffelContraction (I := I) g α v w (extChartAt I α p) =
      chartTransitionAt (I := I) β α
          (chartTransitionMap (I := I) α β (extChartAt I α p))
          (chartChristoffelContraction (I := I) g β
            (chartTransitionAt (I := I) α β (extChartAt I α p) v)
            (chartTransitionAt (I := I) α β (extChartAt I α p) w)
            (chartTransitionMap (I := I) α β (extChartAt I α p)))
        + chartTransitionSecondDerivCorrection (I := I) α β v w
            (extChartAt I α p) := by
  classical
  set x := extChartAt I α p with hx_def
  set Tx := chartTransitionMap (I := I) α β x with hTx_def
  set Jv := chartTransitionAt (I := I) α β x v with hJv
  set Jw := chartTransitionAt (I := I) α β x w with hJw
  -- Reduce to a coordinate-by-coordinate identity in the model basis.
  refine (chartModelBasis E).ext_elem (fun l => ?_)
  -- `chartCoord l (·) = (chartModelBasis E).repr (·) l`, by definition.
  change chartCoord (E := E) l
      (chartChristoffelContraction (I := I) g α v w x) =
    chartCoord (E := E) l
      (chartTransitionAt (I := I) β α Tx
          (chartChristoffelContraction (I := I) g β Jv Jw Tx)
        + chartTransitionSecondDerivCorrection (I := I) α β v w x)
  -- Left side coordinate.
  rw [chartCoord_chartChristoffelContraction (I := I) g α v w x l]
  -- Right side coordinate: additivity of `chartCoord`.
  have hcoord_add : ∀ a b : E,
      chartCoord (E := E) l (a + b) =
        chartCoord (E := E) l a + chartCoord (E := E) l b := by
    intro a b; simp [chartCoord, map_add]
  rw [hcoord_add]
  -- Coordinate of the pullback term: apply `chartCoord_chartTransitionAt`.
  rw [chartCoord_chartTransitionAt (I := I) β α Tx
    (chartChristoffelContraction (I := I) g β Jv Jw Tx) l]
  -- Coordinate of the second-derivative correction.
  have hcorr : chartCoord (E := E) l
      (chartTransitionSecondDerivCorrection (I := I) α β v w x) =
      ∑ c : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) β α Tx l c *
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) i
              (fun z => chartTransitionJacEntry (I := I) α β z c j) x *
              chartCoord (E := E) i v * chartCoord (E := E) j w) := by
    rw [chartTransitionSecondDerivCorrection_def, chartCoord, map_sum,
      Finsupp.finset_sum_apply]
    rw [← hTx_def]
    -- `repr (coeff_k • e_k) l = coeff_k · δ_{kl}`; the surviving term is `k = l`.
    rw [Finset.sum_eq_single_of_mem l (Finset.mem_univ l)]
    · rw [map_smul, Finsupp.smul_apply, smul_eq_mul,
        (chartModelBasis E).repr_self_apply l l, if_pos rfl, mul_one]
    · intro k _ hkl
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul,
        (chartModelBasis E).repr_self_apply k l, if_neg hkl, mul_zero]
  rw [hcorr]
  -- Coordinate of the inner chart-β contraction, expanding the Jacobian pushes.
  have hinner : ∀ c : Fin (Module.finrank ℝ E),
      chartCoord (E := E) c
          (chartChristoffelContraction (I := I) g β Jv Jw Tx) =
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g β a b c Tx *
            (∑ i, chartTransitionJacEntry (I := I) α β x a i *
              chartCoord (E := E) i v) *
            (∑ j, chartTransitionJacEntry (I := I) α β x b j *
              chartCoord (E := E) j w) := by
    intro c
    rw [chartCoord_chartChristoffelContraction (I := I) g β Jv Jw Tx c]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hJv, hJw,
      chartCoord_chartTransitionAt (I := I) α β x v a,
      chartCoord_chartTransitionAt (I := I) α β x w b]
  -- Rewrite the pullback coordinate with `hinner`.
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) =>
    congrArg (fun t => chartTransitionJacEntry (I := I) β α Tx l c * t)
      (hinner c))]
  -- Now both sides are `∑ i ∑ j Γ_α^{ijl}(x) v^i w^j` after substituting the
  -- symbol-level transformation law for each `(i, j)`.
  have htrans : ∀ i j : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g α i j l x =
        (∑ c, chartTransitionJacEntry (I := I) β α Tx l c *
          (∑ a, ∑ b, chartChristoffel (I := I) g β a b c Tx *
            chartTransitionJacEntry (I := I) α β x a i *
            chartTransitionJacEntry (I := I) α β x b j)) +
        (∑ c, chartTransitionJacEntry (I := I) β α Tx l c *
          partialDeriv (E := E) i
            (fun z => chartTransitionJacEntry (I := I) α β z c j) x) := by
    intro i j
    rw [hx_def, hTx_def]
    exact chartChristoffel_transform (I := I) g α β hp_α hp_β i j l
  -- LHS = ∑_i ∑_j (htrans i j) · v^i · w^j; split the two groups.
  calc
    (∑ i, ∑ j, chartChristoffel (I := I) g α i j l x *
        chartCoord (E := E) i v * chartCoord (E := E) j w)
      = ∑ i, ∑ j,
          (((∑ c, chartTransitionJacEntry (I := I) β α Tx l c *
            (∑ a, ∑ b, chartChristoffel (I := I) g β a b c Tx *
              chartTransitionJacEntry (I := I) α β x a i *
              chartTransitionJacEntry (I := I) α β x b j)) +
          (∑ c, chartTransitionJacEntry (I := I) β α Tx l c *
            partialDeriv (E := E) i
              (fun z => chartTransitionJacEntry (I := I) α β z c j) x))
            * chartCoord (E := E) i v * chartCoord (E := E) j w) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [htrans i j]
    _ = (∑ c, chartTransitionJacEntry (I := I) β α Tx l c *
            (∑ a, ∑ b, chartChristoffel (I := I) g β a b c Tx *
              (∑ i, chartTransitionJacEntry (I := I) α β x a i *
                chartCoord (E := E) i v) *
              (∑ j, chartTransitionJacEntry (I := I) α β x b j *
                chartCoord (E := E) j w)))
        + (∑ c, chartTransitionJacEntry (I := I) β α Tx l c *
            (∑ i, ∑ j,
              partialDeriv (E := E) i
                (fun z => chartTransitionJacEntry (I := I) α β z c j) x *
                chartCoord (E := E) i v * chartCoord (E := E) j w)) := by
        -- Reorganize each group into `∑ i ∑ j (...) v w` via the reorder helpers.
        rw [chartTransitionContractionReorderMain
              (fun c => chartTransitionJacEntry (I := I) β α Tx l c)
              (fun a b c => chartChristoffel (I := I) g β a b c Tx)
              (fun a i => chartTransitionJacEntry (I := I) α β x a i)
              (fun i => chartCoord (E := E) i v)
              (fun j => chartCoord (E := E) j w)]
        rw [chartTransitionContractionReorderCorr
              (fun c => chartTransitionJacEntry (I := I) β α Tx l c)
              (fun c i j => partialDeriv (E := E) i
                (fun z => chartTransitionJacEntry (I := I) α β z c j) x)
              (fun i => chartCoord (E := E) i v)
              (fun j => chartCoord (E := E) j w)]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring

/-! ## Moving-foot derivative of the chart-transition Jacobian

The lemmas `partialDeriv_chartTransitionJacEntry_swap` and friends differentiate
the chart-transition Jacobian in its *spatial* `E`-variable. The lemmas below
differentiate it along a smooth curve `cE : ℝ → E` in that variable — the precise
form a fixed-chart commutation argument needs, where the moving foot enters as
the image curve of the foot in the fixed chart `α` and the curve velocity `cE'`
plays the role of the foot velocity. -/

/-- Expansion of the Fréchet derivative of the Jacobian entry along a vector in
the model basis: `fderiv ℝ (J^a_i) y v = ∑_k vᵏ · ∂_k J^a_i(y)`. -/
lemma fderiv_chartTransitionJacEntry_eq_sum_partialDeriv
    (α β : M) (a i : Fin (Module.finrank ℝ E)) (y v : E) :
    fderiv ℝ (fun z => chartTransitionJacEntry (I := I) α β z a i) y v =
      ∑ k : Fin (Module.finrank ℝ E),
        chartCoord (E := E) k v *
          partialDeriv (E := E) k
            (fun z => chartTransitionJacEntry (I := I) α β z a i) y := by
  classical
  have hv : v = ∑ k : Fin (Module.finrank ℝ E),
      chartCoord (E := E) k v • (chartModelBasis E) k := by
    conv_lhs => rw [← (chartModelBasis E).sum_repr v]
    rfl
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, smul_eq_mul]
  rfl

/-- **Moving-foot chain rule for the chart-transition Jacobian entry.** For a
smooth curve `cE : ℝ → E` differentiable at `t` with `cE t` in the open
chart-transition source, the composite `s ↦ J^a_i(cE s)` has derivative
`∑_k (cE' t)ᵏ · ∂_k J^a_i(cE t)`, where `cE' t` is the curve velocity (the
foot velocity in the fixed chart at `α`) and `∂_k J^a_i` is the spatial
transition derivative. -/
theorem chartTransitionJacEntry_comp_hasDerivAt [I.Boundaryless]
    (α β : M) (a i : Fin (Module.finrank ℝ E))
    {cE : ℝ → E} {cE' : ℝ → E} {t : ℝ}
    (hc : HasDerivAt cE (cE' t) t)
    (hmem : cE t ∈ chartTransitionSource (I := I) α β) :
    HasDerivAt (fun s => chartTransitionJacEntry (I := I) α β (cE s) a i)
      (∑ k : Fin (Module.finrank ℝ E),
        chartCoord (E := E) k (cE' t) *
          partialDeriv (E := E) k
            (fun z => chartTransitionJacEntry (I := I) α β z a i) (cE t)) t := by
  classical
  have hdiff : DifferentiableAt ℝ
      (fun z => chartTransitionJacEntry (I := I) α β z a i) (cE t) :=
    chartTransitionJacEntry_differentiableAt (I := I) α β a i hmem
  have hchain : HasDerivAt
      (fun s => chartTransitionJacEntry (I := I) α β (cE s) a i)
      (fderiv ℝ (fun z => chartTransitionJacEntry (I := I) α β z a i) (cE t)
        (cE' t)) t :=
    hdiff.hasFDerivAt.comp_hasDerivAt t hc
  rw [fderiv_chartTransitionJacEntry_eq_sum_partialDeriv (I := I) α β a i] at hchain
  exact hchain

/-- **Moving-foot chain rule for the chart-transition pushforward, coordinatewise.**
For a fixed model vector `v : E` and a smooth curve `cE : ℝ → E` differentiable
at `t` with `cE t` in the chart-transition source, each chart-`β` coordinate `a`
of the foot-dependent pushforward `s ↦ chartTransitionAt α β (cE s) v` has
derivative `∑_i (∑_k (cE' t)ᵏ · ∂_k J^a_i(cE t)) · vⁱ`. The foot motion `cE'`
enters only through the spatial transition derivative `∂_k J^a_i`. -/
theorem chartCoord_chartTransitionAt_comp_hasDerivAt [I.Boundaryless]
    (α β : M) (a : Fin (Module.finrank ℝ E)) (v : E)
    {cE : ℝ → E} {cE' : ℝ → E} {t : ℝ}
    (hc : HasDerivAt cE (cE' t) t)
    (hmem : cE t ∈ chartTransitionSource (I := I) α β) :
    HasDerivAt
      (fun s => chartCoord (E := E) a (chartTransitionAt (I := I) α β (cE s) v))
      (∑ i : Fin (Module.finrank ℝ E),
        (∑ k : Fin (Module.finrank ℝ E),
          chartCoord (E := E) k (cE' t) *
            partialDeriv (E := E) k
              (fun z => chartTransitionJacEntry (I := I) α β z a i) (cE t)) *
          chartCoord (E := E) i v) t := by
  classical
  have hfun : (fun s => chartCoord (E := E) a
        (chartTransitionAt (I := I) α β (cE s) v)) =
      (fun s => ∑ i : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) α β (cE s) a i *
          chartCoord (E := E) i v) := by
    funext s
    rw [chartCoord_chartTransitionAt (I := I) α β (cE s) v a]
  rw [hfun]
  refine HasDerivAt.fun_sum (fun i _ => ?_)
  have hJ : HasDerivAt (fun s => chartTransitionJacEntry (I := I) α β (cE s) a i)
      (∑ k : Fin (Module.finrank ℝ E),
        chartCoord (E := E) k (cE' t) *
          partialDeriv (E := E) k
            (fun z => chartTransitionJacEntry (I := I) α β z a i) (cE t)) t :=
    chartTransitionJacEntry_comp_hasDerivAt (I := I) α β a i hc hmem
  simpa using hJ.mul_const (chartCoord (E := E) i v)

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

