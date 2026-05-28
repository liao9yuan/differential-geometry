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

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry
