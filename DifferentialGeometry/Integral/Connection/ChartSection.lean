import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import DifferentialGeometry.Integral.Measure.ChartDensity

/-!
# Chart-trivialised representation of a tangent-bundle section

Bridge between manifold-level differentiation of a tangent-bundle section and
Fréchet-level differentiation of its chart-trivialised `E`-valued representation.

Given a section `σ : Π x : M, TangentSpace I x` of the tangent bundle and a
basepoint `α : M` (with associated chart `(extChartAt I α)` and tangent-bundle
trivialization `triv := trivializationAt E (TangentSpace I) α`), define the
*chart-trivialised representation* of `σ` at `α` as the `E`-valued map on `M`
$$
  \sigma^E_\alpha : M \to E,
  \quad \sigma^E_\alpha(x) = \mathrm{triv}.\mathrm{continuousLinearMapAt}\,\mathbb{R}\,x\,(\sigma\,x).
$$
On the base set this equals the second component of the trivialization applied
to the total-space point `⟨x, σ x⟩`; off the base set, the Mathlib
`continuousLinearMapAt` is the zero map and the representation takes the junk
value `0`.

The file proves three groups of results:

* **(A)** Section MDifferentiability ↔ chart-pulled-back differentiability.
* **(B)** Manifold derivative of the section identifies, via the canonical defeq
  `TangentSpace 𝓘(ℝ, E) y = E`, with the Fréchet derivative of the
  chart-pulled-back representation, evaluated at the trivialization-image of
  the tangent vector. [Formulation `(B′′)` in the file's design — bypasses the
  total-space tangent altogether.]
* **(C)** Smoothness preservation: a `C^k` section gives a `C^k` chart-pulled-
  back `E → E` map.

Together with the Mathlib trivialization linear-action helpers
(`continuousLinearMapAt`, `symmL` and their composition identities), this
provides the foundational toolkit for chart-local covariant-derivative
constructions on the tangent bundle.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

/-! ## The chart-trivialised representation -/

/-- The chart-trivialised `E`-valued representation of a tangent-bundle section, taken
through the canonical trivialization at the base point `α`.

On the base set `(trivializationAt E (TangentSpace I) α).baseSet`, this equals
the second component of `(trivializationAt E (TangentSpace I) α) ⟨x, σ x⟩`; off
the base set, `continuousLinearMapAt` is the zero map, so the representation is
`0`. -/
def chartE_section_repr (α : M) (σ : Π x : M, TangentSpace I x) (x : M) : E :=
  (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x (σ x)

/-- Variant unfolding: the chart-trivialised representation as a function on `M`. -/
lemma chartE_section_repr_def (α : M) (σ : Π x : M, TangentSpace I x) :
    chartE_section_repr (I := I) α σ =
      fun x : M =>
        (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x (σ x) :=
  rfl

/-- Pointwise evaluation: alias making the definitional equality available. -/
lemma chartE_section_repr_apply
    (α : M) (σ : Π x : M, TangentSpace I x) (x : M) :
    chartE_section_repr (I := I) α σ x =
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x (σ x) := rfl

/-- On the base set of the canonical trivialization at `α`, the chart-trivialised
representation equals the trivialization-second-component of the section's total-space
point. -/
lemma chartE_section_repr_eq_trivialization_snd
    (α : M) (σ : Π x : M, TangentSpace I x) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartE_section_repr (I := I) α σ x =
      (trivializationAt E (TangentSpace I) α ⟨x, σ x⟩).2 := by
  classical
  -- `triv.continuousLinearMapAt ℝ x v = (triv ⟨x, v⟩).2` for `x ∈ baseSet`.
  -- Use `apply_eq_prod_continuousLinearEquivAt` which gives `e ⟨b, z⟩ = (b, e.continuousLinearEquivAt R b hb z)`,
  -- and `coe_continuousLinearEquivAt_eq` which identifies the equiv with the CLM.
  unfold chartE_section_repr
  set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α
  rw [T.apply_eq_prod_continuousLinearEquivAt ℝ x hx (σ x)]
  -- Now goal: `T.continuousLinearMapAt ℝ x (σ x) = (x, T.continuousLinearEquivAt ℝ x hx (σ x)).2`
  -- The `.2` unfolds via `coe_continuousLinearEquivAt_eq`.
  rw [show (x, (T.continuousLinearEquivAt ℝ x hx) (σ x)).2 =
        T.continuousLinearEquivAt ℝ x hx (σ x) from rfl]
  rw [show (T.continuousLinearEquivAt ℝ x hx (σ x) : E) =
          T.continuousLinearMapAt ℝ x (σ x) from
        congrFun (T.coe_continuousLinearEquivAt_eq (R := ℝ) hx) (σ x)]

/-! ## (A) Section MDifferentiability ↔ chart-image MDifferentiability

The first half of the bridge: at a point `x` in the trivialization base set, a
section is MDifferentiable as a map `M → TotalSpace E (TangentSpace I)` iff its
chart-trivialised `E`-valued representation is MDifferentiable as a map
`M → E`. This relies directly on the Mathlib characterization
`mdifferentiableAt_section_iff`. -/

variable (I) in
/-- **Section MDifferentiability bridge (within-at form).** A section `σ` of the
tangent bundle is `MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E))` at a point of the
base set iff its chart-trivialised representation is
`MDifferentiableWithinAt I 𝓘(ℝ, E)` there. -/
theorem mdifferentiableWithinAt_section_iff_chartE
    (α : M) (σ : Π x : M, TangentSpace I x) {u : Set M} {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    MDiffAt[u] (T% σ) x ↔ MDiffAt[u] (chartE_section_repr (I := I) α σ) x := by
  classical
  have hiff :=
    Bundle.Trivialization.mdifferentiableWithinAt_section_iff (𝕜 := ℝ) I (u := u)
      (e := trivializationAt E (TangentSpace I) α) σ hx
  refine hiff.trans ?_
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine h.congr_of_eventuallyEq (f₁ := chartE_section_repr (I := I) α σ) ?_ ?_
    · filter_upwards
        [mem_nhdsWithin_of_mem_nhds
          ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx)] with y hy
      exact chartE_section_repr_eq_trivialization_snd (I := I) α σ hy
    · exact chartE_section_repr_eq_trivialization_snd (I := I) α σ hx
  · refine h.congr_of_eventuallyEq
        (f₁ := fun y => (trivializationAt E (TangentSpace I) α ⟨y, σ y⟩).2) ?_ ?_
    · filter_upwards
        [mem_nhdsWithin_of_mem_nhds
          ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx)] with y hy
      exact (chartE_section_repr_eq_trivialization_snd (I := I) α σ hy).symm
    · exact (chartE_section_repr_eq_trivialization_snd (I := I) α σ hx).symm

variable (I) in
/-- **Section MDifferentiability bridge (at-form).** A section `σ` of the tangent
bundle is `MDifferentiableAt I (I.prod 𝓘(ℝ, E))` at a point of the base set iff
its chart-trivialised representation is `MDifferentiableAt I 𝓘(ℝ, E)` there. -/
theorem mdifferentiableAt_section_iff_chartE
    (α : M) (σ : Π x : M, TangentSpace I x) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    MDiffAt (T% σ) x ↔ MDiffAt (chartE_section_repr (I := I) α σ) x := by
  classical
  rw [← mdifferentiableWithinAt_univ, ← mdifferentiableWithinAt_univ]
  exact mdifferentiableWithinAt_section_iff_chartE I α σ hx

/-! ### Bridging the `E → E` chart-pulled-back map

The chart-trivialised representation `σ^E_α : M → E` can be further pulled back
through `(extChartAt I α).symm` to a function `E → E`, defined on the chart
target. The MDifferentiability statement then translates to ordinary Fréchet
`DifferentiableAt`, since both source and target are vector spaces.

We expose two flavours:

* `mdifferentiableAt_iff_pullback_of_mem_source` — the
  `MDifferentiableAt I 𝓘(ℝ, E)` of a function `M → E` is equivalent to the
  `MDifferentiableWithinAt` of its chart-pull-back, on the appropriate
  range subset of `E`.
* `mdifferentiableAt_section_iff_chartE_fderiv` — at an interior point of the
  chart target, the section's MDifferentiability collapses fully to ordinary
  Fréchet `DifferentiableAt` of the chart-pulled-back `E → E` map. -/

/-- An `E`-valued function on `M` is `MDifferentiableAt I 𝓘(ℝ, E)` at a point in
the chart source iff its pull-back through `(extChartAt I α).symm` is
`MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E)` over `range I` at the corresponding
chart point. This is a direct application of `mdifferentiableAt_iff_source_of_mem_source`
specialised to a vector-space target. -/
private lemma mdifferentiableAt_iff_pullback_of_mem_source
    (α : M) (f : M → E) {x : M} (hx : x ∈ (chartAt H α).source) :
    MDiffAt f x ↔
      MDiffAt[range I] (f ∘ (extChartAt I α).symm) (extChartAt I α x) :=
  mdifferentiableAt_iff_source_of_mem_source (x := α) (x' := x) hx

/-- For an interior point of the chart target, `MDifferentiableWithinAt 𝓘(ℝ,E) 𝓘(ℝ,E)`
over `range I` of an `E → E` map collapses to ordinary `DifferentiableAt`. -/
private lemma mdifferentiableWithinAt_range_iff_differentiableAt_of_interior
    {α : M} {f : E → E} {y : E}
    (hy_int : y ∈ interior ((extChartAt I α).target : Set E)) :
    MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E) f (range I) y ↔ DifferentiableAt ℝ f y := by
  classical
  -- `interior target ⊆ target ⊆ range I`, so on the interior, `range I ∈ 𝓝 y`.
  have htgt : (extChartAt I α).target ⊆ range I := extChartAt_target_subset_range α
  have hint_open : IsOpen (interior ((extChartAt I α).target : Set E)) := isOpen_interior
  have hrange_nhds : range I ∈ 𝓝 y :=
    Filter.mem_of_superset (hint_open.mem_nhds hy_int)
      (interior_subset.trans htgt)
  rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
  exact ⟨fun h => h.differentiableAt hrange_nhds, fun h => h.differentiableWithinAt⟩

variable (I) in
/-- **Section ↔ chart-pulled-back differentiability (at-form).** For a point `x`
in the intersection of the chart source and the trivialization base set, with
`extChartAt I α x` in the interior of the chart target, the section `σ` is
`MDifferentiableAt I (I.prod 𝓘(ℝ, E))` at `x` iff the chart-pulled-back
`E → E` map `chartE_section_repr α σ ∘ (extChartAt I α).symm` is
`DifferentiableAt ℝ` at `extChartAt I α x`. -/
theorem mdifferentiableAt_section_iff_chartE_fderiv
    (α : M) (σ : Π x : M, TangentSpace I x) {x : M}
    (hx_src : x ∈ (chartAt H α).source)
    (hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hx_int : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E)) :
    MDiffAt (T% σ) x ↔
      DifferentiableAt ℝ
        (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
        (extChartAt I α x) := by
  classical
  rw [mdifferentiableAt_section_iff_chartE I α σ hx_base]
  rw [mdifferentiableAt_iff_pullback_of_mem_source α
      (chartE_section_repr (I := I) α σ) hx_src]
  exact mdifferentiableWithinAt_range_iff_differentiableAt_of_interior (α := α) hx_int

/-! ## (A′) Section ContMDiff ↔ chart-image ContMDiff -/

variable (I) in
/-- **Section ContMDiff bridge (within-at form).** A section `σ` of the tangent
bundle is `ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) k` at a point `x` of the
trivialization base set iff its chart-trivialised representation is
`ContMDiffWithinAt I 𝓘(ℝ, E) k` there. The smoothness order `k : ℕ∞` is
restricted so that the auto-instance `ContMDiffVectorBundle k` from
`[ContMDiffVectorBundle ∞]` fires. -/
theorem contMDiffWithinAt_section_iff_chartE
    {k : ℕ∞} (α : M) (σ : Π x : M, TangentSpace I x) {u : Set M} {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) k (T% σ) u x ↔
      ContMDiffWithinAt I 𝓘(ℝ, E) k (chartE_section_repr (I := I) α σ) u x := by
  classical
  -- The Mathlib `_iff` form for an arbitrary trivialization needs
  -- `ContMDiffVectorBundle 1`, which is auto-instated from `ContMDiffVectorBundle ∞`.
  have hiff :=
    Bundle.Trivialization.contMDiffWithinAt_section (𝕜 := ℝ) (IB := I)
      (n := (k : WithTop ℕ∞)) (s := σ) (a := u)
      (e := trivializationAt E (TangentSpace I) α) hx
  refine hiff.trans ?_
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine h.congr_of_eventuallyEq (f₁ := chartE_section_repr (I := I) α σ) ?_ ?_
    · filter_upwards
        [mem_nhdsWithin_of_mem_nhds
          ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx)] with y hy
      exact (chartE_section_repr_eq_trivialization_snd (I := I) α σ hy)
    · exact chartE_section_repr_eq_trivialization_snd (I := I) α σ hx
  · refine h.congr_of_eventuallyEq
        (f₁ := fun y => (trivializationAt E (TangentSpace I) α ⟨y, σ y⟩).2) ?_ ?_
    · filter_upwards
        [mem_nhdsWithin_of_mem_nhds
          ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx)] with y hy
      exact (chartE_section_repr_eq_trivialization_snd (I := I) α σ hy).symm
    · exact (chartE_section_repr_eq_trivialization_snd (I := I) α σ hx).symm

variable (I) in
/-- **Section ContMDiff bridge (at-form).** A section `σ` of the tangent bundle
is `ContMDiffAt I (I.prod 𝓘(ℝ, E)) k` at a point of the base set iff its
chart-trivialised representation is `ContMDiffAt I 𝓘(ℝ, E) k` there. -/
theorem contMDiffAt_section_iff_chartE
    {k : ℕ∞} (α : M) (σ : Π x : M, TangentSpace I x) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) k (T% σ) x ↔
      ContMDiffAt I 𝓘(ℝ, E) k (chartE_section_repr (I := I) α σ) x := by
  classical
  rw [← contMDiffWithinAt_univ, ← contMDiffWithinAt_univ]
  exact contMDiffWithinAt_section_iff_chartE I α σ hx

/-! ## (B′′) Manifold derivative of the section in chart coordinates

The Mathlib defeq `TangentSpace 𝓘(ℝ, E) y = E` permits us to view the
`mfderiv` of an `E`-valued function on `M` as a CLM `T_xM →L[ℝ] E`. For our
chart-trivialised representation, this identifies, via the chain rule for
`mfderiv` of a composition with `extChartAt`, with the Fréchet `fderiv` of the
chart-pulled-back `E → E` map composed with the chart differential.

The key observation: for the canonical tangent-bundle trivialization at `α`,
the trivialization's `continuousLinearMapAt ℝ x` *equals* the manifold
derivative of `extChartAt I α` at `x` (Mathlib's
`TangentBundle.continuousLinearMapAt_trivializationAt`). So the
chart-differential image of a tangent vector `v` is just
`triv.continuousLinearMapAt ℝ x v` — exactly what we want for the downstream
chart-local Levi-Civita construction. -/

variable (I) in
/-- **Manifold derivative of the chart-trivialised representation.** At a point
`x` in the chart source whose chart image lies in the interior of the chart
target, the manifold derivative of `σ^E_α : M → E` at `x` applied to a tangent
vector `v` equals the Fréchet derivative of the chart-pulled-back `E → E` map
at `extChartAt I α x` applied to the trivialization-image
`triv.continuousLinearMapAt ℝ x v`.

This is the chart-local form of the section-side of the Levi-Civita identity,
expressing the directional derivative of `σ^E_α` along `v` purely in terms of
the Fréchet derivative on `E`. -/
theorem mfderiv_section_eq_chartE_fderiv
    (α : M) (σ : Π x : M, TangentSpace I x) {x : M}
    (hx_src : x ∈ (chartAt H α).source)
    (hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hx_int : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E))
    (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ, E) (chartE_section_repr (I := I) α σ) x) v =
      fderiv ℝ (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
        (extChartAt I α x)
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x v) := by
  classical
  set fE := chartE_section_repr (I := I) α σ
  set φ := extChartAt I α
  set y₀ : E := φ x
  set gE : E → E := fE ∘ φ.symm
  -- Step 1: `fE = gE ∘ φ` on the chart source, which is in `𝓝 x`.
  have hfE_eqOn : ∀ y, y ∈ φ.source → fE y = gE (φ y) := by
    intro y hy
    change fE y = fE (φ.symm (φ y))
    have : φ.symm (φ y) = y := φ.left_inv hy
    rw [this]
  have hsrc_extChart : x ∈ φ.source := by
    rw [extChartAt_source]; exact hx_src
  have hsrc_nhds : φ.source ∈ 𝓝 x := extChartAt_source_mem_nhds' (I := I) hsrc_extChart
  have hev : fE =ᶠ[𝓝 x] gE ∘ φ := by
    filter_upwards [hsrc_nhds] with y hy
    exact hfE_eqOn y hy
  have hmfderiv_eq :
      mfderiv I 𝓘(ℝ, E) fE x = mfderiv I 𝓘(ℝ, E) (gE ∘ φ) x :=
    Filter.EventuallyEq.mfderiv_eq hev
  -- Step 2: chart smoothness, section differentiability give chain rule applicability.
  have hφ_mdiff : MDiffAt φ x := mdifferentiableAt_extChartAt (I := I) (x := α) hx_src
  have hgE_diff : DifferentiableAt ℝ gE y₀ :=
    (mdifferentiableAt_section_iff_chartE_fderiv (I := I) α σ hx_src hx_base hx_int).mp hσ
  have hgE_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) gE y₀ :=
    hgE_diff.mdifferentiableAt
  have hchain :
      mfderiv I 𝓘(ℝ, E) (gE ∘ φ) x =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) gE (φ x)).comp (mfderiv I 𝓘(ℝ, E) φ x) :=
    mfderiv_comp x hgE_mdiff hφ_mdiff
  -- `mfderiv` for a vector-space-target map equals `fderiv`.
  have hmf_to_fderiv :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) gE (φ x) = fderiv ℝ gE (φ x) :=
    mfderiv_eq_fderiv (𝕜 := ℝ) (E := E) (E' := E) (f := gE) (x := φ x)
  -- For the canonical tangent-bundle trivialization at `α`,
  -- `triv.continuousLinearMapAt ℝ x = mfderiv (extChartAt I α) x`.
  have htriv_eq :
      mfderiv I 𝓘(ℝ, E) (extChartAt I α) x =
        (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x :=
    (TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
      (x₀ := α) (x := x) hx_src).symm
  -- Now combine: rewrite the LHS via `hmfderiv_eq`, `hchain`, `hmf_to_fderiv`.
  rw [hmfderiv_eq, hchain, hmf_to_fderiv]
  -- Goal: `((fderiv ℝ gE (φ x)).comp (mfderiv I 𝓘(ℝ,E) φ x)) v = fderiv ℝ gE y₀ (triv v)`.
  -- Reduce `comp` and replace `mfderiv φ x v` with `triv.continuousLinearMapAt ℝ x v`
  -- using `htriv_eq` (recall `φ := extChartAt I α`, `y₀ := φ x`, definitionally).
  change (fderiv ℝ gE (φ x))
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I α) x) v) =
      fderiv ℝ gE y₀
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x v)
  rw [htriv_eq]
  rfl

/-! ## (C) Smoothness preservation -/

variable (I) in
/-- **ContMDiff section ⟹ ContDiffOn chart pull-back.** A globally `C^k` section
gives a `C^k` chart-pulled-back `E → E` map on the chart-image of the
trivialization base set intersected with the chart source. -/
theorem contDiffOn_chartE_pullback_of_contMDiff_section
    {k : ℕ∞} (α : M) (σ : Π x : M, TangentSpace I x)
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) k (T% σ)) :
    ContDiffOn ℝ k
      (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
      ((extChartAt I α) ''
        ((chartAt H α).source ∩ (trivializationAt E (TangentSpace I) α).baseSet) ∩
        (extChartAt I α).target) := by
  classical
  intro y hy
  obtain ⟨⟨x, ⟨hx_src, hx_base⟩, hx_eq⟩, hy_target⟩ := hy
  subst hx_eq
  set fE := chartE_section_repr (I := I) α σ
  set φ := extChartAt I α
  -- `fE` is `ContMDiffAt I 𝓘(ℝ, E) k` at `x` via the section bridge.
  have hfE_at : ContMDiffAt I 𝓘(ℝ, E) k fE x :=
    (contMDiffAt_section_iff_chartE I α σ hx_base).mp (hσ x)
  -- `(extChartAt I α).symm` is `ContMDiffWithinAt 𝓘(ℝ,E) I k` at `φ x` over `φ.target`.
  have hxφ_src : x ∈ φ.source := by rw [extChartAt_source]; exact hx_src
  have hxφ_tgt : φ x ∈ φ.target := φ.map_source hxφ_src
  have hxφ_inv : φ.symm (φ x) = x := φ.left_inv hxφ_src
  have hsymm_at : ContMDiffWithinAt 𝓘(ℝ, E) I (k : WithTop ℕ∞) φ.symm φ.target (φ x) := by
    have hsymm_on_inf : ContMDiffOn 𝓘(ℝ, E) I (∞ : WithTop ℕ∞) φ.symm φ.target :=
      contMDiffOn_extChartAt_symm (I := I) (n := ∞) (x := α)
    have hsymm_on : ContMDiffOn 𝓘(ℝ, E) I (k : WithTop ℕ∞) φ.symm φ.target :=
      hsymm_on_inf.of_le (by exact_mod_cast le_top)
    exact hsymm_on (φ x) hxφ_tgt
  -- Composition: `fE ∘ φ.symm` is `ContMDiffWithinAt 𝓘(ℝ,E) 𝓘(ℝ,E) k` at `φ x` over `φ.target`.
  -- Use the chain rule: `ContMDiffAt.comp_contMDiffWithinAt` evaluates `g` at `f x`, here
  -- `f x = φ.symm (φ x) = x`, so we rewrite `hfE_at` to be at `φ.symm (φ x)`.
  have hcomp_at : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E) k (fE ∘ φ.symm) φ.target (φ x) := by
    have hfE_at' : ContMDiffAt I 𝓘(ℝ, E) k fE (φ.symm (φ x)) := by
      rw [hxφ_inv]; exact hfE_at
    exact hfE_at'.comp_contMDiffWithinAt (φ x) hsymm_at
  -- Translate to `ContDiffWithinAt` (vector-space target / source).
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hcomp_at
  refine hcomp_at.mono ?_
  exact inter_subset_right

/-! ## (D) Trivialization linear-action helpers

Mathlib already provides `(trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x`
as a CLM `TangentSpace I x →L[ℝ] E`, and `.symmL ℝ x` as a CLM `E →L[ℝ] TangentSpace I x`.
We expose convenient names for these and bundle the round-trip identities, so
the downstream Levi-Civita chart-local construction can use a small fixed
vocabulary. -/

variable (I) in
/-- The chart-trivialization CLM at `(α, x)`. -/
abbrev trivToE (α x : M) : TangentSpace I x →L[ℝ] E :=
  (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x

variable (I) in
/-- The inverse chart-trivialization CLM at `(α, x)`. -/
abbrev trivFromE (α x : M) : E →L[ℝ] TangentSpace I x :=
  (trivializationAt E (TangentSpace I) α).symmL ℝ x

variable (I) in
/-- Round-trip identity: `trivFromE ∘ trivToE = id` on the trivialization base set. -/
@[simp] lemma trivFromE_trivToE
    (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (v : TangentSpace I x) :
    trivFromE (I := I) α x (trivToE (I := I) α x v) = v :=
  (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hx v

variable (I) in
/-- Round-trip identity: `trivToE ∘ trivFromE = id` on the trivialization base set. -/
@[simp] lemma trivToE_trivFromE
    (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (w : E) :
    trivToE (I := I) α x (trivFromE (I := I) α x w) = w :=
  (trivializationAt E (TangentSpace I) α).continuousLinearMapAt_symmL (R := ℝ) hx w

/-- The chart-trivialised representation in terms of `trivToE`. -/
@[simp] lemma chartE_section_repr_eq_trivToE
    (α : M) (σ : Π x : M, TangentSpace I x) (x : M) :
    chartE_section_repr (I := I) α σ x = trivToE (I := I) α x (σ x) := rfl

/-- Additivity of `chartE_section_repr`: `(σ + τ)^E_α = σ^E_α + τ^E_α` pointwise. -/
lemma chartE_section_repr_add
    (α : M) (σ τ : Π x : M, TangentSpace I x) (x : M) :
    chartE_section_repr (I := I) α (σ + τ) x =
      chartE_section_repr (I := I) α σ x + chartE_section_repr (I := I) α τ x := by
  classical
  unfold chartE_section_repr
  rw [Pi.add_apply, map_add]

/-- Smul-compatibility of `chartE_section_repr`: `(c • σ)^E_α = c • σ^E_α`. -/
lemma chartE_section_repr_smul
    (α : M) (c : ℝ) (σ : Π x : M, TangentSpace I x) (x : M) :
    chartE_section_repr (I := I) α (c • σ) x = c • chartE_section_repr (I := I) α σ x := by
  classical
  unfold chartE_section_repr
  rw [Pi.smul_apply, map_smul]

/-- Pointwise smul by a scalar function `f : M → ℝ`: `chartE_section_repr` distributes. -/
lemma chartE_section_repr_smul_function
    (α : M) (f : M → ℝ) (σ : Π x : M, TangentSpace I x) (x : M) :
    chartE_section_repr (I := I) α (fun y => f y • σ y) x =
      f x • chartE_section_repr (I := I) α σ x := by
  classical
  unfold chartE_section_repr
  rw [map_smul]

/-- Zero section: `chartE_section_repr α 0 x = 0`. -/
lemma chartE_section_repr_zero (α : M) (x : M) :
    chartE_section_repr (I := I) α (fun _ => (0 : TangentSpace I _)) x = 0 := by
  classical
  unfold chartE_section_repr
  rw [map_zero]

/-! ## (E) Manifold derivative of a scalar function in chart coordinates

For a scalar function `f : M → ℝ`, the manifold derivative `mfderiv I 𝓘(ℝ) f x`
is identified, at an interior point of the chart target, with the Fréchet
derivative of the chart-pulled-back map `f ∘ (extChartAt I α).symm` precomposed
with the trivialization map `trivToE α x`. This is the scalar-function analogue
of `mfderiv_section_eq_chartE_fderiv`. -/

variable (I) in
/-- **Manifold derivative of a scalar function in chart coordinates.** At a
point `x` of the chart source whose chart image lies in the interior of the
chart target, the manifold derivative `mfderiv I 𝓘(ℝ) f x` applied to a tangent
vector `v` equals the Fréchet derivative of the chart pullback
`f ∘ (extChartAt I α).symm` at `extChartAt I α x` applied to the
trivialization-image `trivToE α x v`. -/
theorem mfderiv_scalar_eq_chart_fderiv
    (α : M) (f : M → ℝ) {x : M}
    (hx_src : x ∈ (chartAt H α).source)
    (hx_int : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E))
    (hf : MDiffAt f x)
    (v : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ) f x) v =
      fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α x)
        (trivToE (I := I) α x v) := by
  classical
  set φ := extChartAt I α
  set g : E → ℝ := f ∘ φ.symm
  -- Step 1: `f = g ∘ φ` on the chart source, which is in `𝓝 x`.
  have hf_eqOn : ∀ y, y ∈ φ.source → f y = g (φ y) := by
    intro y hy
    change f y = f (φ.symm (φ y))
    rw [φ.left_inv hy]
  have hsrc_extChart : x ∈ φ.source := by
    rw [extChartAt_source]; exact hx_src
  have hsrc_nhds : φ.source ∈ 𝓝 x := extChartAt_source_mem_nhds' (I := I) hsrc_extChart
  have hev : f =ᶠ[𝓝 x] g ∘ φ := by
    filter_upwards [hsrc_nhds] with y hy
    exact hf_eqOn y hy
  have hmfderiv_eq :
      mfderiv I 𝓘(ℝ) f x = mfderiv I 𝓘(ℝ) (g ∘ φ) x :=
    Filter.EventuallyEq.mfderiv_eq hev
  -- Step 2: chart smoothness, scalar function differentiability give chain rule applicability.
  have hφ_mdiff : MDiffAt φ x := mdifferentiableAt_extChartAt (I := I) (x := α) hx_src
  -- The pullback `g = f ∘ φ.symm` is `MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ)` at `φ x`,
  -- because `f` is `MDifferentiableAt I 𝓘(ℝ)` at `x = φ.symm (φ x)` and `φ.symm` is
  -- `MDifferentiableWithinAt 𝓘(ℝ,E) I (range I)` at `φ x` with `range I ∈ 𝓝 (φ x)`.
  -- Once we have `MDifferentiableAt`, vector-space target reduces to `DifferentiableAt`.
  have hxφ_tgt : φ x ∈ φ.target := φ.map_source hsrc_extChart
  have hxφ_inv : φ.symm (φ x) = x := φ.left_inv hsrc_extChart
  have hsymm_within :
      MDifferentiableWithinAt 𝓘(ℝ, E) I φ.symm (range I) (φ x) :=
    mdifferentiableWithinAt_extChartAt_symm (I := I) (x := α) hxφ_tgt
  have hrange_nhds : range I ∈ 𝓝 (φ x) := by
    have hint_open : IsOpen (interior ((extChartAt I α).target : Set E)) := isOpen_interior
    exact Filter.mem_of_superset
      (Filter.mem_of_superset (hint_open.mem_nhds hx_int) interior_subset)
      (extChartAt_target_subset_range α)
  have hg_within :
      MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ) g (range I) (φ x) :=
    MDifferentiableAt.comp_mdifferentiableWithinAt_of_eq
      (I' := I) (I'' := 𝓘(ℝ)) (g := f) (f := φ.symm)
      (s := range I) (x := φ x) (y := x)
      hf hsymm_within hxφ_inv
  have hg_at : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) g (φ x) :=
    hg_within.mdifferentiableAt hrange_nhds
  -- Chain rule for `mfderiv (g ∘ φ) x`.
  have hchain :
      mfderiv I 𝓘(ℝ) (g ∘ φ) x =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) g (φ x)).comp (mfderiv I 𝓘(ℝ, E) φ x) :=
    mfderiv_comp x hg_at hφ_mdiff
  -- For a vector-space-source/target map, `mfderiv` equals `fderiv`. We need the
  -- domain to be a vector space (E) and the codomain (ℝ).
  have hg_diff : DifferentiableAt ℝ g (φ x) :=
    hg_at.differentiableAt
  have hmf_to_fderiv :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ) g (φ x) = fderiv ℝ g (φ x) :=
    mfderiv_eq_fderiv (𝕜 := ℝ) (E := E) (E' := ℝ) (f := g) (x := φ x)
  -- For the canonical tangent-bundle trivialization at `α`,
  -- `triv.continuousLinearMapAt ℝ x = mfderiv (extChartAt I α) x`.
  have htriv_eq :
      mfderiv I 𝓘(ℝ, E) (extChartAt I α) x =
        (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x :=
    (TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
      (x₀ := α) (x := x) hx_src).symm
  rw [hmfderiv_eq, hchain, hmf_to_fderiv]
  -- Goal: `((fderiv ℝ g (φ x)).comp (mfderiv I 𝓘(ℝ,E) φ x)) v = fderiv ℝ g (φ x) (trivToE α x v)`.
  change (fderiv ℝ g (φ x))
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I α) x) v) =
      fderiv ℝ g (φ x)
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x v)
  rw [htriv_eq]
  rfl

end Connection
end Integral
end DifferentialGeometry
