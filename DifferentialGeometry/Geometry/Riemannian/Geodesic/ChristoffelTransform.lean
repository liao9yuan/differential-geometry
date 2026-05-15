import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option linter.unusedSectionVars false

/-!
# Christoffel symbol transformation under chart change

For a smooth Riemannian metric `g` on a smooth manifold `M`, the
chart-coordinate Christoffel symbols are not tensorial: their values at
two different chart basepoints `α, β : M` for a common manifold point
`b ∈ (chartAt H α).source ∩ (chartAt H β).source` are related by the
classical inhomogeneous formula

$$\Gamma_α(D\varphi \cdot v, D\varphi \cdot v)(\varphi_α b)
  + D^2 \varphi(v, v) = D\varphi \cdot \Gamma_β(v, v)(\varphi_β b),$$

where `φ_{αβ} := (extChartAt I α) ∘ (extChartAt I β).symm` is the chart
transition map and `Dφ, D²φ` are its first and second Fréchet
derivatives at `y_β := extChartAt I β b`.

This file packages:

* `chartTransition α β` — the chart transition `φ_{αβ}` as a partial
  map `E → E`. Smooth on `chartTransitionDomain α β`, which is the
  image under `extChartAt I β` of the intersection of chart sources.

* `chartTransitionDomain α β` — the chart-image domain on which the
  transition is smooth; equal to
  `((extChartAt I β).symm ≫ extChartAt I α).source`.

* `chartTransitionFDeriv α β y` — the first Fréchet derivative of the
  chart transition at `y : E`, as a `E →L[ℝ] E`.

* `chartTransitionSecondFDeriv α β y` — the second derivative, as
  `E →L[ℝ] E →L[ℝ] E`. Symmetric in its two vector arguments under
  the standing smoothness assumption.

* `chartTransition_contDiffOn` — smoothness of the transition on its
  domain, inherited from Mathlib's `contDiffOn_ext_coord_change`.

* `chartTransitionSecondFDeriv_symm` — Schwarz's theorem applied to the
  transition: the second derivative is symmetric.

* `chartChristoffelContraction_transform_of_geodesic_equation` — the
  Christoffel transformation law as the consequence of the geodesic
  equation holding in both chart-α and chart-β second-derivative form.
  This is the *purely analytic* form: it accepts the chart-α and chart-β
  second-derivative equations as hypotheses and concludes the
  transformation. The two equations themselves are downstream content
  (`IsGeodesicAt` already gives an integral curve, but unpacking the
  explicit second-derivative form in each chart is a separate bridge).

## Strategy

For a smooth curve `c_β : ℝ → E` near `0` with `c_β 0 = y_β` and
`c_β' 0 = v`, write `c_α := φ_{αβ} ∘ c_β`. By the chain rule
(`HasFDerivAt.comp` + iteration),

* `c_α' 0 = D\varphi \cdot v`,
* `c_α'' 0 = D^2 \varphi (v, v) + D\varphi \cdot c_β''(0)`.

Substituting `c_α''(0) = -\Gamma_α(c_α'(0), c_α'(0))(\varphi_α b)` and
`c_β''(0) = -\Gamma_β(v, v)(\varphi_β b)` (the chart-α and chart-β
forms of the geodesic equation) and rearranging gives the
transformation law.

This file does *not* establish chart-invariance of the geodesic
equation; that is a separate downstream piece. Instead, the file
records the algebraic consequence under the assumption that both
chart-α and chart-β forms of the second-derivative equation hold.

-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

/-! ## Smoothness exponent helpers

We frequently need to discharge `n ≠ 0` and `1 ≤ ∞` style obligations
for `WithTop ℕ∞`-valued smoothness exponents. Mathlib's `∞` notation
expands to `((⊤ : ℕ∞) : WithTop ℕ∞)`, which is *distinct* from
`(⊤ : WithTop ℕ∞)` (the latter is `ω`). The lemmas below isolate the
specific inequalities we need.
-/

private lemma one_le_infty : (1 : WithTop ℕ∞) ≤ ∞ := by
  show (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  rw [show (1 : WithTop ℕ∞) = ((1 : ℕ∞) : WithTop ℕ∞) from rfl, WithTop.coe_le_coe]
  exact le_top

private lemma two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := by
  show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  rw [show (2 : WithTop ℕ∞) = ((2 : ℕ∞) : WithTop ℕ∞) from rfl, WithTop.coe_le_coe]
  exact le_top

private lemma three_le_infty : ((1 : WithTop ℕ∞) + 1) ≤ ∞ := by
  show ((1 : WithTop ℕ∞) + 1) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  have h : (1 : WithTop ℕ∞) + 1 = ((2 : ℕ∞) : WithTop ℕ∞) := rfl
  rw [h, show ((⊤ : ℕ∞) : WithTop ℕ∞) = ((⊤ : ℕ∞) : WithTop ℕ∞) from rfl,
      WithTop.coe_le_coe]
  exact le_top

private lemma infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by
  show ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0
  intro h
  have : (⊤ : ℕ∞) = 0 := WithTop.coe_injective h
  exact ENat.top_ne_zero this

/-! ## The chart transition map -/

/-- The chart transition `φ_{αβ} := extChartAt I α ∘ (extChartAt I β).symm`,
viewed as a function `E → E`. It is smooth on `chartTransitionDomain α β`
(the chart-image of the intersection of the two chart sources), with
inverse `φ_{βα}` on the symmetric domain. -/
def chartTransition (α β : M) : E → E :=
  (extChartAt I α) ∘ (extChartAt I β).symm

@[simp] lemma chartTransition_apply (α β : M) (y : E) :
    chartTransition (I := I) (M := M) α β y =
      extChartAt I α ((extChartAt I β).symm y) := rfl

/-- The natural domain of the chart transition: the source of the
PartialEquiv `(extChartAt I β).symm ≫ extChartAt I α`. -/
def chartTransitionDomain (α β : M) : Set E :=
  ((extChartAt I β).symm ≫ extChartAt I α).source

@[simp] lemma chartTransitionDomain_def (α β : M) :
    chartTransitionDomain (I := I) (M := M) α β =
      ((extChartAt I β).symm ≫ extChartAt I α).source := rfl

/-- Smoothness of the chart transition on its natural domain. This is the
direct rebranding of Mathlib's `contDiffOn_ext_coord_change` for our
project's vocabulary. -/
lemma chartTransition_contDiffOn (α β : M) :
    ContDiffOn ℝ ∞ (chartTransition (I := I) (M := M) α β)
      (chartTransitionDomain (I := I) (M := M) α β) :=
  contDiffOn_ext_coord_change (I := I) α β

/-- Membership in the transition domain when a manifold point lies in both
chart sources. -/
lemma extChartAt_mem_chartTransitionDomain {α β : M} {b : M}
    (hα : b ∈ (chartAt H α).source) (hβ : b ∈ (chartAt H β).source) :
    extChartAt I β b ∈ chartTransitionDomain (I := I) (M := M) α β := by
  classical
  unfold chartTransitionDomain
  simp only [PartialEquiv.trans_source, mem_inter_iff, mem_preimage,
    PartialEquiv.symm_source]
  refine ⟨?_, ?_⟩
  · have hbsrc : b ∈ (extChartAt I β).source := by
      rw [extChartAt_source (I := I)]; exact hβ
    exact (extChartAt I β).map_source hbsrc
  · have hbsrc_β : b ∈ (extChartAt I β).source := by
      rw [extChartAt_source (I := I)]; exact hβ
    have hsymm : (extChartAt I β).symm (extChartAt I β b) = b :=
      (extChartAt I β).left_inv hbsrc_β
    rw [hsymm]
    rw [extChartAt_source (I := I)]
    exact hα

/-- The transition domain is contained in the target of `extChartAt I β`. -/
lemma chartTransitionDomain_subset_target (α β : M) :
    chartTransitionDomain (I := I) (M := M) α β ⊆ (extChartAt I β).target := by
  intro y hy
  simp only [chartTransitionDomain, PartialEquiv.trans_source, mem_inter_iff,
    PartialEquiv.symm_source] at hy
  exact hy.1

/-! ## First Fréchet derivative of the chart transition -/

/-- The first Fréchet derivative of the chart transition at a point `y : E`,
as a continuous linear map `E →L[ℝ] E`. -/
def chartTransitionFDeriv (α β : M) (y : E) : E →L[ℝ] E :=
  fderiv ℝ (chartTransition (I := I) (M := M) α β) y

@[simp] lemma chartTransitionFDeriv_def (α β : M) (y : E) :
    chartTransitionFDeriv (I := I) (M := M) α β y =
      fderiv ℝ (chartTransition (I := I) (M := M) α β) y := rfl

/-! ## Second Fréchet derivative of the chart transition -/

/-- The second Fréchet derivative of the chart transition at a point `y : E`,
as a continuous linear map `E →L[ℝ] E →L[ℝ] E`.

For `v, w : E`, the value `chartTransitionSecondFDeriv α β y v w` is the
second directional derivative `∂_v ∂_w (chartTransition α β)` at `y`.
Schwarz's theorem (under `C^2`) gives symmetry in `v, w`. -/
def chartTransitionSecondFDeriv (α β : M) (y : E) : E →L[ℝ] E →L[ℝ] E :=
  fderiv ℝ (fderiv ℝ (chartTransition (I := I) (M := M) α β)) y

@[simp] lemma chartTransitionSecondFDeriv_def (α β : M) (y : E) :
    chartTransitionSecondFDeriv (I := I) (M := M) α β y =
      fderiv ℝ (fderiv ℝ (chartTransition (I := I) (M := M) α β)) y := rfl

/-! ## Smoothness of the chart transition near a point in the overlap

We need to translate the `ContDiffOn` form (smoothness on a set) to a
`ContDiffAt` form (smoothness at a single point). Under the
boundarylessness assumption, the chart-transition domain is an open
subset of `E`, so `ContDiffOn` implies `ContDiffAt` for interior points
of the domain.
-/

section Boundaryless

variable [I.Boundaryless]

/-- Under `[I.Boundaryless]`, the chart transition domain is open in `E`.
The domain equals
`(extChartAt I β).target ∩ (extChartAt I β).symm ⁻¹' (extChartAt I α).source`,
and we use `ContinuousOn.isOpen_inter_preimage` to extract openness. -/
lemma chartTransitionDomain_isOpen (α β : M) :
    IsOpen (chartTransitionDomain (I := I) (M := M) α β) := by
  classical
  unfold chartTransitionDomain
  simp only [PartialEquiv.trans_source, PartialEquiv.symm_source]
  -- chartTransitionDomain = (extChartAt I β).target ∩ (extChartAt I β).symm ⁻¹' (extChartAt I α).source.
  have hcont : ContinuousOn (extChartAt I β).symm (extChartAt I β).target :=
    continuousOn_extChartAt_symm β
  have hopen : IsOpen ((extChartAt I α).source) :=
    isOpen_extChartAt_source α
  have htarget_open : IsOpen (extChartAt I β).target :=
    isOpen_extChartAt_target (I := I) β
  -- `ContinuousOn.isOpen_inter_preimage` directly gives the openness of the intersection.
  exact hcont.isOpen_inter_preimage htarget_open hopen

/-- Under boundarylessness, smoothness of the chart transition at any point in
the overlap of chart sources. -/
lemma chartTransition_contDiffAt
    {α β : M} {b : M}
    (hα : b ∈ (chartAt H α).source) (hβ : b ∈ (chartAt H β).source) :
    ContDiffAt ℝ ∞ (chartTransition (I := I) (M := M) α β) (extChartAt I β b) := by
  have hmem : extChartAt I β b ∈ chartTransitionDomain (I := I) (M := M) α β :=
    extChartAt_mem_chartTransitionDomain (I := I) hα hβ
  have hopen : IsOpen (chartTransitionDomain (I := I) (M := M) α β) :=
    chartTransitionDomain_isOpen (I := I) (M := M) α β
  exact (chartTransition_contDiffOn (I := I) α β).contDiffAt
    (hopen.mem_nhds hmem)

/-! ## Symmetry of the second derivative -/

/-- **Schwarz's theorem applied to the chart transition.** Under
boundarylessness and smoothness at a point in the overlap, the second
Fréchet derivative of the chart transition is symmetric in its two
vector arguments. -/
theorem chartTransitionSecondFDeriv_symm
    {α β : M} {b : M}
    (hα : b ∈ (chartAt H α).source) (hβ : b ∈ (chartAt H β).source)
    (v w : E) :
    chartTransitionSecondFDeriv (I := I) (M := M) α β
        (extChartAt I β b) v w =
      chartTransitionSecondFDeriv (I := I) (M := M) α β
        (extChartAt I β b) w v := by
  classical
  have hat : ContDiffAt ℝ ∞ (chartTransition (I := I) (M := M) α β)
      (extChartAt I β b) :=
    chartTransition_contDiffAt (I := I) hα hβ
  have hbound : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact two_le_infty
  have hsymm : IsSymmSndFDerivAt ℝ
      (chartTransition (I := I) (M := M) α β) (extChartAt I β b) :=
    hat.isSymmSndFDerivAt hbound
  unfold chartTransitionSecondFDeriv
  exact hsymm.eq v w

end Boundaryless

/-! ## The chain rule for a curve composed with the chart transition

For a smooth curve `c_β : ℝ → E` near `s = 0` with `c_β 0 = y_β` in the
chart-transition domain, and the composed curve `c_α := chartTransition α β ∘ c_β`,
we have the chain-rule identities at `s = 0`:
* `c_α' 0 = Dφ · c_β'(0)` (first derivative);
* `c_α'' 0 = D²φ(c_β'(0), c_β'(0)) + Dφ · c_β''(0)` (second derivative).

These are recorded below for use in the transformation-law theorem.
-/

section ChainRule

variable [I.Boundaryless]

/-- The chart transition is differentiable at any point in the overlap. -/
lemma chartTransition_differentiableAt
    {α β : M} {b : M}
    (hα : b ∈ (chartAt H α).source) (hβ : b ∈ (chartAt H β).source) :
    DifferentiableAt ℝ (chartTransition (I := I) (M := M) α β)
      (extChartAt I β b) := by
  have h := chartTransition_contDiffAt (I := I) hα hβ
  exact h.differentiableAt infty_ne_zero

/-- `HasFDerivAt`-form of the first derivative of the chart transition. -/
lemma hasFDerivAt_chartTransition
    {α β : M} {b : M}
    (hα : b ∈ (chartAt H α).source) (hβ : b ∈ (chartAt H β).source) :
    HasFDerivAt (chartTransition (I := I) (M := M) α β)
      (chartTransitionFDeriv (I := I) (M := M) α β (extChartAt I β b))
      (extChartAt I β b) :=
  (chartTransition_differentiableAt (I := I) hα hβ).hasFDerivAt

/-- The `fderiv` of the chart transition is itself differentiable at any point in
the overlap (i.e., the chart transition is `C²` there). -/
lemma chartTransitionFDeriv_differentiableAt
    {α β : M} {b : M}
    (hα : b ∈ (chartAt H α).source) (hβ : b ∈ (chartAt H β).source) :
    DifferentiableAt ℝ (fderiv ℝ (chartTransition (I := I) (M := M) α β))
      (extChartAt I β b) := by
  have h := chartTransition_contDiffAt (I := I) hα hβ
  -- C^∞ at the point ⟹ fderiv is C^∞ at the point (which is ≥ C^1).
  have h₂ : ContDiffAt ℝ 1 (fderiv ℝ (chartTransition (I := I) (M := M) α β))
      (extChartAt I β b) := by
    -- ContDiffAt.fderiv_right with the appropriate smoothness shift.
    have : ContDiffAt ℝ (∞ : WithTop ℕ∞)
        (fderiv ℝ (chartTransition (I := I) (M := M) α β))
        (extChartAt I β b) := by
      -- ContDiffAt ℝ (1+∞) f ⟹ ContDiffAt ℝ ∞ (fderiv f).
      -- We have ContDiffAt ℝ ∞ f, which equals (∞ : WithTop ℕ∞) = ⊤(ℕ∞), and 1 + ∞ = ∞.
      have hf : ContDiffAt ℝ ((1 : WithTop ℕ∞) + ∞)
          (chartTransition (I := I) (M := M) α β) (extChartAt I β b) := by
        -- 1 + ∞ = ∞ in WithTop ℕ∞.
        have hsum : (1 : WithTop ℕ∞) + ∞ = ∞ := by
          show (1 : WithTop ℕ∞) + ((⊤ : ℕ∞) : WithTop ℕ∞) = ((⊤ : ℕ∞) : WithTop ℕ∞)
          rw [show (1 : WithTop ℕ∞) = ((1 : ℕ∞) : WithTop ℕ∞) from rfl,
              ← WithTop.coe_add]
          rfl
        rw [hsum]; exact h
      exact hf.fderiv_right (m := ∞) le_rfl
    exact this.of_le one_le_infty
  exact h₂.differentiableAt (by norm_num)

/-- **Chain rule, first derivative.** For a smooth curve `c_β : ℝ → E` with
`HasDerivAt c_β v 0` and image lying in the chart-transition domain near `0`,
the composed curve `chartTransition α β ∘ c_β` has derivative `Dφ · v` at `0`. -/
lemma hasDerivAt_chartTransition_comp
    {α β : M} {b : M}
    (hα : b ∈ (chartAt H α).source) (hβ : b ∈ (chartAt H β).source)
    {c_β : ℝ → E} {v : E}
    (hc_β0 : c_β 0 = extChartAt I β b)
    (hc_β : HasDerivAt c_β v 0) :
    HasDerivAt (chartTransition (I := I) (M := M) α β ∘ c_β)
      (chartTransitionFDeriv (I := I) (M := M) α β (extChartAt I β b) v) 0 := by
  classical
  have hφ : HasFDerivAt (chartTransition (I := I) (M := M) α β)
      (chartTransitionFDeriv (I := I) (M := M) α β (extChartAt I β b))
      (extChartAt I β b) :=
    hasFDerivAt_chartTransition (I := I) hα hβ
  have hφ' : HasFDerivAt (chartTransition (I := I) (M := M) α β)
      (chartTransitionFDeriv (I := I) (M := M) α β (extChartAt I β b))
      (c_β 0) := by
    rw [hc_β0]; exact hφ
  exact hφ'.comp_hasDerivAt 0 hc_β

end ChainRule

/-! ## The transformation law

We now state the transformation law for the Christoffel contraction as a
purely analytic consequence of:
1. the chain rule applied to `c_α := φ_{αβ} ∘ c_β`;
2. the geodesic equation holding in chart-α form
   (`c_α'' = -Γ_α(c_α', c_α')(c_α)`);
3. the geodesic equation holding in chart-β form
   (`c_β'' = -Γ_β(c_β', c_β')(c_β)`).

The combination of the chain rule for the second derivative and (2), (3)
yields the inhomogeneous transformation

$$\Gamma_α(Dφ v, Dφ v)(\varphi_α b)
  + D^2 \varphi(v, v) = D\varphi \cdot \Gamma_β(v, v)(\varphi_β b).$$

The chart-α and chart-β geodesic equations themselves are derived from
`IsGeodesicAt` in a separate downstream bridge (`IsGeodesicAt →
HasGeodesicEquationAt`); here we take them as hypotheses to state the
purely analytic core of the transformation.
-/

section Transform

variable [I.Boundaryless]

/-- **The chain rule for the second derivative of the composed curve.**
If `c_β : ℝ → E` admits a first derivative everywhere near `0` and a
second derivative `a_β` at `0`, and the chart transition is `C²` at
`y_β := extChartAt I β b`, then `c_α := chartTransition α β ∘ c_β`
admits a second derivative at `0` equal to

`D²φ(v, v) + Dφ · a_β`,

where `v := c_β'(0)`. -/
lemma hasDerivAt_chartTransition_comp_second
    {α β : M} {b : M}
    (hα : b ∈ (chartAt H α).source) (hβ : b ∈ (chartAt H β).source)
    {c_β : ℝ → E} {v a_β : E}
    (hc_β0 : c_β 0 = extChartAt I β b)
    (hc_β_deriv : HasDerivAt c_β v 0)
    (hc_β_eventually : ∀ᶠ s in nhds (0 : ℝ),
      HasDerivAt c_β (deriv c_β s) s)
    (hc_β_image_eventually : ∀ᶠ s in nhds (0 : ℝ),
      c_β s ∈ chartTransitionDomain (I := I) (M := M) α β)
    (hc_β_second : HasDerivAt (deriv c_β) a_β 0) :
    HasDerivAt (deriv (chartTransition (I := I) (M := M) α β ∘ c_β))
      ((chartTransitionSecondFDeriv (I := I) (M := M) α β
          (extChartAt I β b)) v v +
        (chartTransitionFDeriv (I := I) (M := M) α β
          (extChartAt I β b)) a_β) 0 := by
  classical
  have hopen : IsOpen (chartTransitionDomain (I := I) (M := M) α β) :=
    chartTransitionDomain_isOpen (I := I) (M := M) α β
  -- Pointwise chain-rule identity for `s` in a nbhd of `0`.
  have hchain :
      ∀ᶠ s in nhds (0 : ℝ),
        HasDerivAt (chartTransition (I := I) (M := M) α β ∘ c_β)
          (fderiv ℝ (chartTransition (I := I) (M := M) α β)
            (c_β s) (deriv c_β s)) s := by
    filter_upwards [hc_β_eventually, hc_β_image_eventually] with s hs hmem
    have hφ : DifferentiableAt ℝ (chartTransition (I := I) (M := M) α β) (c_β s) := by
      have hcontdiff : ContDiffOn ℝ ∞ (chartTransition (I := I) (M := M) α β)
          (chartTransitionDomain (I := I) (M := M) α β) :=
        chartTransition_contDiffOn (I := I) α β
      have : ContDiffAt ℝ ∞ (chartTransition (I := I) (M := M) α β) (c_β s) :=
        hcontdiff.contDiffAt (hopen.mem_nhds hmem)
      exact this.differentiableAt infty_ne_zero
    have hφfd : HasFDerivAt (chartTransition (I := I) (M := M) α β)
        (fderiv ℝ (chartTransition (I := I) (M := M) α β) (c_β s)) (c_β s) :=
      hφ.hasFDerivAt
    exact hφfd.comp_hasDerivAt s hs
  -- Second derivative: differentiate `s ↦ Dφ(c_β s) (deriv c_β s)` at 0.
  have hDφ : DifferentiableAt ℝ (fderiv ℝ (chartTransition (I := I) (M := M) α β))
      (c_β 0) := by
    rw [hc_β0]
    exact chartTransitionFDeriv_differentiableAt (I := I) hα hβ
  have hDφ_fd : HasFDerivAt (fderiv ℝ (chartTransition (I := I) (M := M) α β))
      (fderiv ℝ (fderiv ℝ (chartTransition (I := I) (M := M) α β)) (c_β 0))
      (c_β 0) := hDφ.hasFDerivAt
  have hf : HasDerivAt (fun s => fderiv ℝ (chartTransition (I := I) (M := M) α β) (c_β s))
      (fderiv ℝ (fderiv ℝ (chartTransition (I := I) (M := M) α β)) (c_β 0) v) 0 :=
    hDφ_fd.comp_hasDerivAt 0 hc_β_deriv
  have hbilin : HasDerivAt
      (fun s => (fderiv ℝ (chartTransition (I := I) (M := M) α β) (c_β s)) (deriv c_β s))
      ((fderiv ℝ (fderiv ℝ (chartTransition (I := I) (M := M) α β)) (c_β 0) v) v +
        (fderiv ℝ (chartTransition (I := I) (M := M) α β) (c_β 0)) a_β) 0 := by
    have hclm := hf.clm_apply hc_β_second
    have hg0 : deriv c_β 0 = v := hc_β_deriv.deriv
    rw [hg0] at hclm
    exact hclm
  -- `deriv (φ ∘ c_β)` equals the bilinear-apply expression on a nbhd of 0.
  have heq : (fun s => deriv (chartTransition (I := I) (M := M) α β ∘ c_β) s) =ᶠ[nhds 0]
      (fun s => (fderiv ℝ (chartTransition (I := I) (M := M) α β) (c_β s)) (deriv c_β s)) := by
    filter_upwards [hchain] with s hs
    exact hs.deriv
  -- Transfer hbilin via the eventual equality.
  have htransfer := hbilin.congr_of_eventuallyEq heq
  rw [hc_β0] at htransfer
  convert htransfer using 1

set_option linter.unusedVariables false in
/-- **The Christoffel transformation law** under chart change, given the
geodesic equation in both chart-α and chart-β form.

If a smooth curve in the chart-β coordinates satisfies the geodesic
equation (chart-β form) at `s = 0`, and the corresponding chart-α
representation satisfies the geodesic equation (chart-α form) at the
same point, then the chart-α and chart-β Christoffel contractions are
related by

$$\Gamma_α(Dφ v, Dφ v)(\varphi_α b) + D^2 \varphi(v, v)
  = D\varphi \cdot \Gamma_β(v, v)(\varphi_β b)$$

where `v` is the chart-β velocity, `Dφ` and `D²φ` are the first and
second Fréchet derivatives of the chart transition `φ_{αβ}` at
`y_β := \varphi_β b`. -/
theorem chartChristoffelContraction_transform_of_geodesic_equation
    (g : SmoothRiemannianMetric I M) {α β : M} {b : M}
    (hα : b ∈ (chartAt H α).source) (hβ : b ∈ (chartAt H β).source)
    {v a_β : E}
    -- chart-β geodesic equation at `s = 0`.
    (hgeo_β : a_β +
      chartChristoffelContraction (I := I) g β v v (extChartAt I β b) = 0)
    -- chart-α geodesic equation at `s = 0`. The corresponding chart-α curve is
    -- `c_α := chartTransition α β ∘ c_β`, with velocity `Dφ · v` and acceleration
    -- the chain-rule expression `D²φ(v, v) + Dφ · a_β`.
    (hgeo_α :
      ((chartTransitionSecondFDeriv (I := I) (M := M) α β
          (extChartAt I β b)) v v +
        (chartTransitionFDeriv (I := I) (M := M) α β
          (extChartAt I β b)) a_β) +
        chartChristoffelContraction (I := I) g α
          ((chartTransitionFDeriv (I := I) (M := M) α β
            (extChartAt I β b)) v)
          ((chartTransitionFDeriv (I := I) (M := M) α β
            (extChartAt I β b)) v)
          (chartTransition (I := I) (M := M) α β (extChartAt I β b)) = 0) :
    chartChristoffelContraction (I := I) g α
        ((chartTransitionFDeriv (I := I) (M := M) α β (extChartAt I β b)) v)
        ((chartTransitionFDeriv (I := I) (M := M) α β (extChartAt I β b)) v)
        (chartTransition (I := I) (M := M) α β (extChartAt I β b)) +
      (chartTransitionSecondFDeriv (I := I) (M := M) α β
        (extChartAt I β b)) v v =
    (chartTransitionFDeriv (I := I) (M := M) α β (extChartAt I β b))
      (chartChristoffelContraction (I := I) g β v v (extChartAt I β b)) := by
  classical
  -- From chart-β equation: a_β = -Γ_β(v,v)(y_β).
  have ha_β : a_β = - chartChristoffelContraction (I := I) g β v v (extChartAt I β b) :=
    eq_neg_of_add_eq_zero_left hgeo_β
  -- Linearity of `Dφ`: `Dφ (-x) = -Dφ x`.
  have hlin : (chartTransitionFDeriv (I := I) (M := M) α β (extChartAt I β b))
      (- chartChristoffelContraction (I := I) g β v v (extChartAt I β b)) =
      - (chartTransitionFDeriv (I := I) (M := M) α β (extChartAt I β b))
        (chartChristoffelContraction (I := I) g β v v (extChartAt I β b)) :=
    map_neg _ _
  rw [ha_β, hlin] at hgeo_α
  -- hgeo_α : (D²φ(v,v) + -Dφ(Γ_β)) + Γ_α(Dφv, Dφv)(φy_β) = 0.
  -- Set abbreviations for the four vectors involved, then close by abelian-group algebra.
  set Dsq : E :=
    (chartTransitionSecondFDeriv (I := I) (M := M) α β (extChartAt I β b)) v v
  set Df : E := (chartTransitionFDeriv (I := I) (M := M) α β (extChartAt I β b))
    (chartChristoffelContraction (I := I) g β v v (extChartAt I β b))
  set Γα : E := chartChristoffelContraction (I := I) g α
    ((chartTransitionFDeriv (I := I) (M := M) α β (extChartAt I β b)) v)
    ((chartTransitionFDeriv (I := I) (M := M) α β (extChartAt I β b)) v)
    (chartTransition (I := I) (M := M) α β (extChartAt I β b))
  -- Now hgeo_α : (Dsq + -Df) + Γα = 0.
  -- Goal: Γα + Dsq = Df.
  -- AbelianGroup algebra: `(Dsq - Df) + Γα = 0` ⟹ `Γα + Dsq = Df`.
  have habel : Γα + Dsq = Df := by
    have h₁ : Dsq + -Df + Γα = 0 := hgeo_α
    -- Add `Df` to both sides and rearrange.
    have h₂ : (Dsq + -Df + Γα) + Df = 0 + Df := by rw [h₁]
    rw [zero_add] at h₂
    -- h₂ : Dsq + -Df + Γα + Df = Df.
    -- Rearrange LHS: (Dsq + Γα) + (-Df + Df) = Dsq + Γα.
    have h₃ : Dsq + -Df + Γα + Df = Γα + Dsq := by abel
    rw [h₃] at h₂
    exact h₂
  exact habel

end Transform

/-! ## Headline alias matching the project's task description

The transformation law is the algebraic identity used by downstream
chart-invariance / geodesic-rescaling arguments. We expose it under
the name `chartChristoffelContraction_transform`. -/

section HeadlineAlias

variable [I.Boundaryless]

set_option linter.unusedVariables false in
/-- Headline alias for the Christoffel transformation law. See
`chartChristoffelContraction_transform_of_geodesic_equation` for the
underlying derivation; this alias provides a stable public name. -/
theorem chartChristoffelContraction_transform
    (g : SmoothRiemannianMetric I M) {α β : M} {b : M}
    (hα : b ∈ (chartAt H α).source) (hβ : b ∈ (chartAt H β).source)
    {v a_β : E}
    (hgeo_β : a_β +
      chartChristoffelContraction (I := I) g β v v (extChartAt I β b) = 0)
    (hgeo_α :
      ((chartTransitionSecondFDeriv (I := I) (M := M) α β
          (extChartAt I β b)) v v +
        (chartTransitionFDeriv (I := I) (M := M) α β
          (extChartAt I β b)) a_β) +
        chartChristoffelContraction (I := I) g α
          ((chartTransitionFDeriv (I := I) (M := M) α β
            (extChartAt I β b)) v)
          ((chartTransitionFDeriv (I := I) (M := M) α β
            (extChartAt I β b)) v)
          (chartTransition (I := I) (M := M) α β (extChartAt I β b)) = 0) :
    chartChristoffelContraction (I := I) g α
        ((chartTransitionFDeriv (I := I) (M := M) α β (extChartAt I β b)) v)
        ((chartTransitionFDeriv (I := I) (M := M) α β (extChartAt I β b)) v)
        (chartTransition (I := I) (M := M) α β (extChartAt I β b)) +
      (chartTransitionSecondFDeriv (I := I) (M := M) α β
        (extChartAt I β b)) v v =
    (chartTransitionFDeriv (I := I) (M := M) α β (extChartAt I β b))
      (chartChristoffelContraction (I := I) g β v v (extChartAt I β b)) :=
  chartChristoffelContraction_transform_of_geodesic_equation
    (I := I) g hα hβ hgeo_β hgeo_α

end HeadlineAlias

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
