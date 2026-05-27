import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Local chart-coordinate continuity of `mfderiv` along a smooth curve

For a `C^∞` curve `γ : ℝ → M` into a smooth manifold modelled on
`(E, H, I)` and a chart basepoint `α : M`, the chart-`α`-coordinate of
the velocity vector,
$$
  t \;\longmapsto\; \bigl(\mathrm{d}\gamma_t(1)\bigr)_\alpha
   \;=\; \mathrm{d}(\mathrm{extChartAt}\,I\,\alpha)_{\gamma(t)}
        \bigl(\mathrm{mfderiv}\,\gamma\,t\,1\bigr)
   \;=\; \mathrm{fderiv}\,(\mathrm{extChartAt}\,I\,\alpha \circ \gamma)\,t\,1,
$$
is continuous on the open set
`U(α) := γ ⁻¹ ((chartAt H α).source)`.

This is the *chart-fixed* form of velocity-continuity. Together with the
chain-rule identity
`(trivializationAt α).continuousLinearMapAt ℝ (γ t) (mfderiv γ t 1)
 = fderiv (extChartAt I α ∘ γ) t 1`,
it is the analytic backbone for downstream integrability and
Lebesgue-number-style chart-patching arguments (e.g. in the
second-variation length-bound development).

## Main results

* `chartCoord_mfderiv_along_curve_eq_fderiv` —
  the chain-rule identity expressing the chart-`α`-coordinate of
  `mfderiv γ t 1` as a model-space `fderiv`.

* `continuousOn_chartCoord_mfderiv_along_curve` —
  continuity of the chart-`α`-coordinate of `mfderiv γ t 1`,
  on the open set `γ ⁻¹ ((chartAt H α).source)`. Stated equivalently
  as continuity of `t ↦ fderiv (extChartAt I α ∘ γ) t 1`.

* `chartCoord_mfderiv_along_curve_continuousOn` —
  the same continuity, packaged for a compact base set `s`. This is
  the chart-fixed counterpart of `mfderiv_along_curve_continuousOn_of_contMDiff`.

* `raw_mfderiv_eq_symmL_apply_fderiv` —
  the **raw-form rewrite identity**: for `γ t ∈ (chartAt H α).source`,
  `mfderiv γ t 1 = (trivializationAt α).symmL ℝ (γ t) (fderiv (extChartAt I α ∘ γ) t 1)`,
  obtained by applying the inverse trivialization at `γ t` to the
  chart-`α`-coordinate identity and using `Trivialization.symmL_continuousLinearMapAt`.
  This is the substantive bridge between the raw `mfderiv γ t 1 : E` (using the
  defeq `TangentSpace I (γ t) = E`) and the chart-pulled-back model-space
  `fderiv`.

The continuity of the *raw* `mfderiv γ t 1 : E` follows from the
rewrite identity above combined with the CLM-valued continuity of the family
`t ↦ (trivializationAt α).symmL ℝ (γ t)` on `γ ⁻¹ ((chartAt H α).source)`.
The latter is a vector-bundle infrastructure fact about the tangent bundle's
`symmL` family — it lives below this file (in the bundle / `tangentMap`
machinery) and is not duplicated here; downstream developments that need
it can route through the rewrite identity delivered above.
-/

noncomputable section

open Set Function Filter Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace MFDerivAlongCurve

/-! ### Chain-rule identity -/

/-- **Chart-`α`-coordinate of `mfderiv γ t 1` equals `fderiv (extChartAt I α ∘ γ) t 1`.**

For a `C^∞` curve `γ : ℝ → M` and a chart basepoint `α : M`, at any
`t : ℝ` with `γ t ∈ (chartAt H α).source`, the trivialization-`α`-coordinate
of the velocity vector,
  `(trivializationAt α).continuousLinearMapAt ℝ (γ t) (mfderiv γ t 1)`,
equals the ordinary `fderiv` of the chart-pulled-back curve,
  `fderiv (extChartAt I α ∘ γ) t 1`.

This is a direct consequence of the chain rule and the identification
`TangentBundle.continuousLinearMapAt_trivializationAt`. -/
theorem chartCoord_mfderiv_along_curve_eq_fderiv
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (α : M) {t : ℝ} (ht : γ t ∈ (chartAt H α).source) :
    ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ)) =
      (fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ) := by
  -- Rewrite the trivialization CLM as the mfderiv of `extChartAt`.
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (I := I)
        (x₀ := α) (x := γ t) ht]
  -- mdifferentiabilities.
  have hγ_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
    (hγ.contMDiffAt).mdifferentiableAt (by simp)
  have hφ_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) (γ t) :=
    mdifferentiableAt_extChartAt (I := I) (x := α) ht
  -- Chain rule on the composed manifold map.
  have hchain :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt I α) ∘ γ) t =
        (mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ t)).comp
          (mfderiv 𝓘(ℝ, ℝ) I γ t) :=
    mfderiv_comp t hφ_mdiff hγ_mdiff
  -- For maps between model spaces, `mfderiv = fderiv`.
  have hmf_eq_f :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt I α) ∘ γ) t =
        fderiv ℝ ((extChartAt I α) ∘ γ) t :=
    mfderiv_eq_fderiv (𝕜 := ℝ) (f := (extChartAt I α) ∘ γ) (x := t)
  -- Apply both sides to `(1 : ℝ)`.
  have hRHS :
      (fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ) =
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ t)).comp
            (mfderiv 𝓘(ℝ, ℝ) I γ t)) (1 : ℝ) := by
    rw [← hmf_eq_f, hchain]; rfl
  rw [hRHS]; rfl

/-! ### Continuity of the chart-`α`-pullback derivative -/

/-- The chart-`α`-pullback `t ↦ (fderiv ℝ (extChartAt I α ∘ γ) t : ℝ → E) 1`
is continuous on the open set `U := γ ⁻¹ ((chartAt H α).source)`. -/
theorem continuousOn_fderiv_extChartAt_comp_curve
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (α : M) :
    ContinuousOn
      (fun t : ℝ => (fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ → E) (1 : ℝ))
      (γ ⁻¹' (chartAt H α).source) := by
  classical
  set U : Set ℝ := γ ⁻¹' (chartAt H α).source with hU_def
  -- `U` is open in `ℝ`.
  have hU_open : IsOpen U := by
    have : IsOpen (chartAt H α).source := by
      rw [← extChartAt_source (I := I)]
      exact isOpen_extChartAt_source (I := I) α
    exact hγ.continuous.isOpen_preimage _ this
  -- The composition `extChartAt I α ∘ γ` is `C^∞` on `U` in the manifold sense.
  have h_comp_mdiff :
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ ((extChartAt I α) ∘ γ) U := by
    have hφ : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α)
        (chartAt H α).source :=
      contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
    have hγU : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ U := hγ.contMDiffOn
    have hmaps : MapsTo γ U (chartAt H α).source := fun _ ht => ht
    exact hφ.comp hγU hmaps
  -- Reduce to ordinary `ContDiffOn` between vector spaces.
  have h_comp_diff :
      ContDiffOn ℝ ∞ ((extChartAt I α) ∘ γ) U :=
    contMDiffOn_iff_contDiffOn.mp h_comp_mdiff
  -- `fderivWithin` of a `C^∞` function on an open set is continuous.
  have h1le : (1 : ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)
  have h_fdW :
      ContinuousOn (fderivWithin ℝ ((extChartAt I α) ∘ γ) U) U :=
    h_comp_diff.continuousOn_fderivWithin hU_open.uniqueDiffOn h1le
  -- On the open set `U`, `fderivWithin = fderiv`.
  have h_fderiv_cont :
      ContinuousOn (fun t : ℝ => fderiv ℝ ((extChartAt I α) ∘ γ) t) U := by
    refine h_fdW.congr ?_
    intro t ht
    exact (fderivWithin_of_isOpen hU_open ht).symm
  -- Apply at the canonical basis vector `1 : ℝ`.
  exact h_fderiv_cont.clm_apply continuousOn_const

/-! ### Headline (chart-`α`-coordinate form) -/

/-- **Continuity of the chart-`α`-coordinate of the velocity along a smooth curve.**

For a `C^∞` curve `γ : ℝ → M` and a chart basepoint `α : M`, the function
  `t ↦ (trivializationAt α).continuousLinearMapAt ℝ (γ t) (mfderiv γ t 1) : ℝ → E`
is continuous on the open set `γ ⁻¹ ((chartAt H α).source)`. -/
theorem continuousOn_chartCoord_mfderiv_along_curve
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (α : M) :
    ContinuousOn
      (fun t : ℝ =>
        (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
          ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ)) : E))
      (γ ⁻¹' (chartAt H α).source) := by
  -- Pointwise equality with the (continuous) chart-pulled-back derivative,
  -- on the open set where both make sense.
  refine ContinuousOn.congr
    (continuousOn_fderiv_extChartAt_comp_curve (I := I) (M := M) (γ := γ) hγ α) ?_
  intro t ht
  -- Apply the chain-rule identity.
  exact (chartCoord_mfderiv_along_curve_eq_fderiv (I := I) (M := M) (γ := γ) hγ
    α (t := t) ht)

/-! ### Compact-set packaging -/

/-- **Compact-domain version of the chart-`α`-coordinate continuity.**

For a `C^∞` curve `γ : ℝ → M`, a chart basepoint `α : M`, and a compact
subset `s ⊆ γ ⁻¹ ((chartAt H α).source)` contained in the chart-`α`
preimage, the chart-`α`-coordinate of `mfderiv γ t 1` is continuous on
`s`. -/
theorem chartCoord_mfderiv_along_curve_continuousOn
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (α : M)
    {s : Set ℝ} (_hs : IsCompact s)
    (hs_sub : s ⊆ γ ⁻¹' (chartAt H α).source) :
    ContinuousOn
      (fun t : ℝ =>
        (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
          ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ)) : E)) s := by
  exact (continuousOn_chartCoord_mfderiv_along_curve (I := I) (M := M)
    (γ := γ) hγ α).mono hs_sub

/-! ### Raw `E`-valued chart-form identity

For a `C^∞` curve `γ : ℝ → M` and a chart basepoint `α : M`, on the chart-pullback
preimage `U(α) := γ ⁻¹ ((chartAt H α).source)`, the raw `mfderiv γ t 1 : E`
(using the literal definitional identification `TangentSpace I (γ t) = E`)
factors through the `α`-trivialization's inverse-CLM and the chart-pulled-back
ordinary `fderiv`. This is the substantive **rewrite** identity for going
between the raw form and the chart-`α`-coordinate form. -/

/-- **Raw form equals `symmL` of chart-pulled-back `fderiv`.**

For `t : ℝ` with `γ t ∈ (chartAt H α).source`, the raw mfderiv-velocity along
the curve `γ` at `t`, evaluated at `1 : ℝ`, equals
  `(trivializationAt α).symmL ℝ (γ t) (fderiv (extChartAt I α ∘ γ) t 1)`.

This is the inverse-trivialization companion of `chartCoord_mfderiv_along_curve_eq_fderiv`,
obtained by applying `(trivializationAt α).symmL ℝ (γ t)` to both sides of the
chart-coordinate identity and using `Trivialization.symmL_continuousLinearMapAt`. -/
theorem raw_mfderiv_eq_symmL_apply_fderiv
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (α : M) {t : ℝ} (ht : γ t ∈ (chartAt H α).source) :
    ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ) : E) =
      ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t))
        ((fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ)) := by
  -- The trivialization `α`-coordinate form of the velocity.
  have hCC : ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
      ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ)) =
        (fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ) :=
    chartCoord_mfderiv_along_curve_eq_fderiv (I := I) (M := M) (γ := γ) hγ α ht
  -- Apply `symmL` to both sides and use the `symmL ∘ continuousLinearMapAt = id` identity
  -- on the chart base set.
  have hbaseSet : γ t ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact ht
  -- `symmL b (continuousLinearMapAt b y) = y` for `b ∈ baseSet` and `y : E b`.
  have hround :
      ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t))
          (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
            ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ))) =
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ)) :=
    (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
      (R := ℝ) hbaseSet _
  -- Combine.
  calc ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ) : E)
      = ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t))
          (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
            ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ))) := hround.symm
    _ = ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t))
          ((fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ)) := by rw [hCC]

/-! ### Bundled tangent map continuity along the curve

The tangent map of `γ`, evaluated at the input `⟨t, 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ`,
produces a continuous `TangentBundle I M`-valued function of `t`. This is the
substantive bundle-level continuity packaging the raw `mfderiv γ t 1 : E`
(via the defeq `TangentSpace I (γ t) = E`) and the base-point `γ t : M`
into a single continuous bundle-section-style map.

The continuity follows from Mathlib's `ContMDiff.continuous_tangentMap` applied
to the smooth curve `γ`, combined with the smoothness of the canonical input
`t ↦ ⟨t, 1⟩ : ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ` (the unit-vector lift).
-/

/-- **Tangent-bundle-valued unit-tangent map along a smooth curve is continuous.**

For a `C^∞` curve `γ : ℝ → M`, the function
  `t ↦ tangentMap 𝓘(ℝ, ℝ) I γ ⟨t, 1⟩ : ℝ → TangentBundle I M`
is continuous on `ℝ`. By definition of `tangentMap`, this equals
`t ↦ ⟨γ t, mfderiv 𝓘(ℝ, ℝ) I γ t 1⟩ : ℝ → TangentBundle I M`,
packaging the raw mfderiv-velocity together with its basepoint as a continuous
bundle-valued function.

This is the canonical *bundle-level* continuity statement underlying the raw
`E`-valued mfderiv-velocity continuity along the curve (via fibre extraction
through the local trivialisation at any chart basepoint). -/
theorem continuous_tangentMap_unitLift
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) :
    Continuous (fun t : ℝ =>
      tangentMap 𝓘(ℝ, ℝ) I γ (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
  -- `tangentMap γ` is continuous on `TangentBundle 𝓘(ℝ, ℝ) ℝ`.
  have h_tan_cont : Continuous (tangentMap 𝓘(ℝ, ℝ) I γ) :=
    hγ.continuous_tangentMap (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  -- The input `t ↦ ⟨t, 1⟩ : ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ` is continuous.
  -- Use `tangentBundleModelSpaceHomeomorph` to identify `TangentBundle 𝓘(ℝ, ℝ) ℝ ≃ₜ ℝ × ℝ`.
  have h_input_cont :
      Continuous (fun t : ℝ =>
        (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    have h_homeo :
        Continuous ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm :
          ModelProd ℝ ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ) :=
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous
    have h_pair : Continuous (fun t : ℝ => (t, (1 : ℝ))) :=
      continuous_id.prodMk continuous_const
    exact h_homeo.comp h_pair
  exact h_tan_cont.comp h_input_cont

/-! ### Hand-off note for the raw `E`-valued mfderiv continuity

The raw `E`-valued continuity of `t ↦ (mfderiv γ t 1 : E)` on the chart-pullback
preimage `γ ⁻¹ ((chartAt H α).source)` reduces, via the bundle-level continuity
above (`continuous_tangentMap_unitLift`), to a **fibre-extraction** problem from
`TangentBundle I M → E` on the chart-trivialisation source. Concretely, on
`π ⁻¹ ((chartAt H α).source) ⊆ TangentBundle I M`, the dependent-snd
`⟨b, v⟩ ↦ v : TangentSpace I b = E` equals
`(triv α).symmL ℝ b ∘ ((triv α)·)._snd`,
where the second factor is continuous (forward trivialisation is continuous on
its source) and the first factor is the **CLM-valued continuity of the inverse
trivialisation**:

  `b ↦ ((trivializationAt E (TangentSpace I) α).symmL ℝ b : E →L[ℝ] E)`
  is `ContinuousOn` on `(chartAt H α).source`.

This CLM-valued `symmL` continuity is the precise residual infrastructure piece.
By `TangentBundle.symmL_trivializationAt`, the family on the chart source
identifies with the manifold derivative
`mfderiv[range I] (extChartAt I α).symm (extChartAt I α b)`,
whose CLM-valued continuity in `b` requires either:

* the `Hom`-bundle smoothness pipeline applied to the `(extChartAt I α).symm`
  side and re-expressing via `contMDiffOn_coordChangeL` between two fixed
  trivialisations, picking up an auxiliary trivialisation on the inverse-chart
  image; or
* a direct `ContDiffOn 𝓘(ℝ, E) (fderivWithin ...)` continuity argument applied
  to the inverse extended chart, then transported through the manifold
  identifications.

The downstream consumer (the second-variation length bound) can extract the raw
`E`-valued continuity locally on each chart-pullback patch via this residual,
combined with `raw_mfderiv_eq_symmL_apply_fderiv` and the existing
`continuousOn_chartCoord_mfderiv_along_curve`. -/

/-! ### Lebesgue-number-style chart cover for a compact parameter set

For a `C^∞` curve `γ : ℝ → M` and a compact subset `s ⊆ ℝ`, the family of
open sets `{γ ⁻¹ ((chartAt H (γ t₀)).source) : t₀ ∈ s}` covers `s`, and
hence by compactness admits a finite subcover. This is the standard
chart-patching setup used in downstream length-bound and integrability
arguments. -/

/-- The open chart-pullback cover `{U(α) : α ∈ M}` covers `ℝ` (via `γ`)
in the following sense: every `t : ℝ` lies in `γ ⁻¹ ((chartAt H (γ t)).source)`. -/
theorem mem_chartPullback_self {γ : ℝ → M} (t : ℝ) :
    t ∈ γ ⁻¹' (chartAt H (γ t)).source := by
  -- `γ t ∈ (chartAt H (γ t)).source` by `mem_chart_source`.
  exact mem_chart_source H (γ t)

/-- For any subset `s ⊆ ℝ` and `C^∞` curve `γ : ℝ → M`, the family
`{γ ⁻¹ ((chartAt H (γ t₀)).source) : t₀ ∈ s}` covers `s`. (No
smoothness or compactness needed for the set-theoretic cover itself.) -/
theorem chartPullback_cover_compact
    {γ : ℝ → M} (_hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {s : Set ℝ} (_hs : IsCompact s) :
    s ⊆ ⋃ t₀ ∈ s, γ ⁻¹' (chartAt H (γ t₀)).source := by
  intro t ht
  refine mem_iUnion_of_mem t ?_
  refine mem_iUnion_of_mem ht ?_
  -- `γ t ∈ (chartAt H (γ t)).source` by `mem_chart_source`.
  exact mem_chart_source H (γ t)

/-- A compact set `s ⊆ ℝ` admits a finite chart-pullback subcover
adapted to a `C^∞` curve `γ : ℝ → M`: there is a finite subset
`T ⊆ s` such that `s ⊆ ⋃_{t₀ ∈ T} γ ⁻¹ ((chartAt H (γ t₀)).source)`.
This is the standard Heine–Borel reduction underlying chart-by-chart
continuity patching. -/
theorem exists_finite_chartPullback_subcover
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    {s : Set ℝ} (hs : IsCompact s) :
    ∃ T : Set ℝ, T ⊆ s ∧ Set.Finite T ∧
      s ⊆ ⋃ t₀ ∈ T, γ ⁻¹' (chartAt H (γ t₀)).source := by
  classical
  -- Each member of the cover is open.
  have hopen : ∀ t₀ : ℝ, t₀ ∈ s → IsOpen (γ ⁻¹' (chartAt H (γ t₀)).source) := by
    intro t₀ _
    have : IsOpen (chartAt H (γ t₀)).source := by
      rw [← extChartAt_source (I := I)]
      exact isOpen_extChartAt_source (I := I) (γ t₀)
    exact hγ.continuous.isOpen_preimage _ this
  -- Build the open cover.
  have hcover : s ⊆ ⋃ t₀ ∈ s, γ ⁻¹' (chartAt H (γ t₀)).source :=
    chartPullback_cover_compact (I := I) (M := M) (γ := γ) hγ hs
  -- Extract a finite subcover via compactness.
  exact hs.elim_finite_subcover_image hopen hcover

end MFDerivAlongCurve

end Riemannian
end Geometry
end DifferentialGeometry
