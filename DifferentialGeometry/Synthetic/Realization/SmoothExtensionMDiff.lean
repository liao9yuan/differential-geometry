import DifferentialGeometry.VectorBundle.Frame
import DifferentialGeometry.VectorBundle.Section
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# SmoothExtensionMDiff: 1-jet extension of an MDifferentiableAt tangent section

Phase B, Step A — 1-jet pathway.

## Summary

Given a raw tangent-section `σ : Π x : M, TangentSpace I x` whose total-space form
`fun y => ⟨y, σ y⟩` is `MDifferentiableAt I (I.prod 𝓘(ℝ, E))` at a single point `x₀`,
this file produces a globally smooth `ContMDiffSection` whose value and fiber-read
`mfderiv` at `x₀` match those of `σ`.

## Main declarations

* `smoothExtensionAt_MDiff` — globally smooth section matching `σ`'s 1-jet at `x₀`.
* `smoothExtensionAt_MDiff_value` — value at `x₀` equals `σ x₀`.
* `smoothExtensionAt_MDiff_fiberRead_mfderiv` — fiber-read `mfderiv` at `x₀`
  matches that of `σ`.

## Construction

We build a smooth section `σ'` with matching 1-jet via the following recipe:

1. Abbreviate `e := trivializationAt E (TangentSpace I) x₀`, `phi := extChartAt I x₀`.
2. Set `L₀ := mfderiv I 𝓘(ℝ, E) (fun y => (e ⟨y, σ y⟩).2) x₀` and
   `v₀ := (e ⟨x₀, σ x₀⟩).2 : E`.
3. Construct `hE : M → E`, a globally-defined function whose restriction to the
   chart source is smooth, with `hE x₀ = v₀` and `mfderiv hE x₀ = L₀` (the latter
   uses that `mfderiv (extChartAt I x₀) x₀ = e.continuousLinearMapAt ℝ x₀` via
   `TangentBundle.continuousLinearMapAt_trivializationAt`).
4. Multiply by a smooth bump function `χ` supported in the chart source and use
   `ContMDiffOn.smul_section_of_tsupport` to glue a global smooth section.

We package this as an existence theorem, then define the API via `Classical.choose`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff
open Bundle Filter ContinuousLinearMap

noncomputable section

namespace Realization

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### Existence lemma — the technical core -/

/-- Existence of a globally smooth tangent-section whose value and fiber-read
`mfderiv` at `x₀` both match those of a section `σ` that is `MDifferentiableAt`
at `x₀` (in total-space form). -/
theorem exists_smooth_section_matching_1jet
    (σ : Π x : M, TangentSpace I x) (x₀ : M)
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, σ y⟩ : TotalSpace E (TangentSpace I))) x₀) :
    ∃ (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      Y x₀ = σ x₀ ∧
      mfderiv I 𝓘(ℝ, E)
        (fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀
          ⟨y, (Y : Π x, TangentSpace I x) y⟩).2) x₀
      =
      mfderiv I 𝓘(ℝ, E)
        (fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, σ y⟩).2) x₀ := by
  -- Abbreviations
  set e : Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I : M → Type _) x₀ with he_def
  set phi : M → E := ⇑(extChartAt I x₀) with hphi_def
  set v₀ : E := (e ⟨x₀, σ x₀⟩).2 with hv₀_def
  set f : M → E := fun y => (e ⟨y, σ y⟩).2 with hf_def
  -- The fiber-read derivative of σ at x₀.
  have hf_mdiff : MDifferentiableAt I 𝓘(ℝ, E) f x₀ :=
    (mdifferentiableAt_section (IB := I) (F := E) σ (b₀ := x₀)).mp hσ
  set L₀ : TangentSpace I x₀ →L[ℝ] E := mfderiv I 𝓘(ℝ, E) f x₀ with hL₀_def
  -- x₀ is in baseSet and chart source.
  have hx₀_base : x₀ ∈ e.baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x₀
  have hx₀_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source _ _
  -- The fixed CLM T : E →L[ℝ] E := L₀ ∘L e.symmL ℝ x₀.
  set T : E →L[ℝ] E := L₀ ∘L (e.symmL ℝ x₀) with hT_def
  -- A smooth scalar function hE : M → E := T ∘ phi + (v₀ - T (phi x₀)).
  -- This is globally a well-defined function in E; it is smooth on chart source.
  let hE : M → E := fun y => T (phi y) + (v₀ - T (phi x₀))
  -- Raw section S y := e.symmL ℝ y (hE y), defined on all of M.
  let S : Π y : M, TangentSpace I y := fun y => e.symmL ℝ y (hE y)
  -- (A) hE is ContMDiffOn on chart source.
  have hE_smoothOn : ContMDiffOn I 𝓘(ℝ, E) ∞ hE (chartAt H x₀).source := by
    intro y hy
    have hphi_at : ContMDiffAt I 𝓘(ℝ, E) ∞ phi y :=
      (contMDiffOn_extChartAt (I := I) (x := x₀) (n := ∞)) y hy |>.contMDiffAt
        ((chartAt H x₀).open_source.mem_nhds hy)
    have hT_phi : ContMDiffAt I 𝓘(ℝ, E) ∞ (fun z => T (phi z)) y :=
      T.contMDiff.contMDiffAt.comp y hphi_at
    exact (hT_phi.add contMDiffAt_const).contMDiffWithinAt
  -- (B) Raw section `S` is smooth on chart source (as a total-space function).
  -- Strategy: use `contMDiffOn_section_iff` for the trivialization `e` on its baseSet
  -- (which equals chart source for the tangent bundle).
  have e_base_eq : e.baseSet = (chartAt H x₀).source := by
    simp [e, TangentBundle.trivializationAt_baseSet]
  have hS_smoothOn : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (⟨y, S y⟩ : TotalSpace E (TangentSpace I))) (chartAt H x₀).source := by
    rw [show (chartAt H x₀).source = e.baseSet from e_base_eq.symm,
        e.contMDiffOn_section_iff (IB := I) (n := ∞) e.open_baseSet (subset_refl _)]
    -- After the rewrite, goal is: ContMDiffOn I 𝓘(ℝ, E) ∞ (fun y => (e ⟨y, S y⟩).2) e.baseSet
    -- On e.baseSet, (e ⟨y, S y⟩).2 = e.continuousLinearMapAt ℝ y (S y)
    --                             = e.continuousLinearMapAt ℝ y (e.symmL ℝ y (hE y))
    --                             = hE y.
    apply ContMDiffOn.congr (hE_smoothOn.mono (e_base_eq ▸ subset_refl _))
    intro y hy
    -- hy : y ∈ e.baseSet
    have happly : (e ⟨y, S y⟩).2 = e.continuousLinearMapAt ℝ y (S y) := by
      rw [e.apply_eq_prod_continuousLinearEquivAt ℝ y hy,
          e.coe_continuousLinearEquivAt_eq (R := ℝ) hy]
    change (e ⟨y, S y⟩).2 = hE y
    rw [happly]
    change e.continuousLinearMapAt ℝ y (e.symmL ℝ y (hE y)) = hE y
    exact e.continuousLinearMapAt_symmL (R := ℝ) hy (hE y)
  -- (C) Smooth bump function at x₀ with tsupport ⊆ (chartAt H x₀).source.
  obtain ⟨χ, -, hχ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x₀).mem_iff.mp
      ((chartAt H x₀).open_source.mem_nhds hx₀_src)
  -- (D) Global smooth section σ' := χ • S.
  have hσ'_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (⟨y, (χ y : ℝ) • S y⟩ : TotalSpace E (TangentSpace I))) := by
    have h1 : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (χ : M → ℝ) (chartAt H x₀).source :=
      (χ.contMDiff.of_le (by exact_mod_cast le_top)).contMDiffOn
    exact h1.smul_section_of_tsupport (chartAt H x₀).open_source hχ hS_smoothOn
  refine ⟨⟨fun y => (χ y : ℝ) • S y, hσ'_smooth⟩, ?_, ?_⟩
  · -- Value at x₀ : σ' x₀ = χ x₀ • S x₀ = 1 • (e.symmL ℝ x₀ (hE x₀)) = σ x₀
    change (χ x₀ : ℝ) • S x₀ = σ x₀
    have hχ1 : (χ : M → ℝ) x₀ = 1 := χ.eq_one
    rw [hχ1, one_smul]
    -- S x₀ = e.symmL ℝ x₀ (hE x₀).
    -- hE x₀ = T (phi x₀) + (v₀ - T (phi x₀)) = v₀.
    -- So S x₀ = e.symmL ℝ x₀ v₀ = e.symmL ℝ x₀ (e.continuousLinearMapAt ℝ x₀ (σ x₀)) = σ x₀.
    change e.symmL ℝ x₀ (hE x₀) = σ x₀
    have hhEx₀ : hE x₀ = v₀ := by
      change T (phi x₀) + (v₀ - T (phi x₀)) = v₀
      abel
    rw [hhEx₀]
    -- v₀ = (e ⟨x₀, σ x₀⟩).2 = e.continuousLinearMapAt ℝ x₀ (σ x₀) since x₀ ∈ e.baseSet.
    have hv₀ : v₀ = e.continuousLinearMapAt ℝ x₀ (σ x₀) := by
      change (e ⟨x₀, σ x₀⟩).2 = e.continuousLinearMapAt ℝ x₀ (σ x₀)
      rw [e.apply_eq_prod_continuousLinearEquivAt ℝ x₀ hx₀_base,
          e.coe_continuousLinearEquivAt_eq (R := ℝ) hx₀_base]
    rw [hv₀]
    exact e.symmL_continuousLinearMapAt (R := ℝ) hx₀_base (σ x₀)
  · -- mfderiv match.
    -- On a neighborhood of x₀ (inside e.baseSet ∩ {χ = 1}), the fiber-read of σ' equals hE.
    -- Then mfderiv of σ'-fiber-read at x₀ = mfderiv hE at x₀ = L₀.
    set sigma' : Π y, TangentSpace I y := fun y => (χ y : ℝ) • S y with hsigma'_def
    change mfderiv I 𝓘(ℝ, E)
        (fun y => ((trivializationAt E (TangentSpace I : M → Type _) x₀)
          ⟨y, sigma' y⟩).2) x₀ = L₀
    -- The goal after `change` reads:
    --   mfderiv I 𝓘(ℝ, E) (fun y => (e ⟨y, sigma' y⟩).2) x₀ = mfderiv I 𝓘(ℝ, E) f x₀
    -- (since `f = fun y => (e ⟨y, σ y⟩).2` and `L₀ = mfderiv I _ f x₀`).
    -- Step 1: Produce eventual-equality `fun y => (e ⟨y, sigma' y⟩).2 =ᶠ[𝓝 x₀] hE`.
    have hee : (fun y => ((trivializationAt E (TangentSpace I : M → Type _) x₀)
        ⟨y, sigma' y⟩).2) =ᶠ[𝓝 x₀] hE := by
      filter_upwards [χ.eventuallyEq_one, e.open_baseSet.mem_nhds hx₀_base] with y hy hy_base
      -- (e ⟨y, sigma' y⟩).2 = e.continuousLinearMapAt ℝ y (sigma' y)
      have happly : (e ⟨y, sigma' y⟩).2 = e.continuousLinearMapAt ℝ y (sigma' y) := by
        rw [e.apply_eq_prod_continuousLinearEquivAt ℝ y hy_base,
            e.coe_continuousLinearEquivAt_eq (R := ℝ) hy_base]
      -- sigma' y = 1 • S y = S y = e.symmL ℝ y (hE y)
      have hsigma'_val : sigma' y = e.symmL ℝ y (hE y) := by
        change (χ y : ℝ) • S y = e.symmL ℝ y (hE y)
        rw [show (χ y : ℝ) = (1 : M → ℝ) y from hy]
        simp only [Pi.one_apply, one_smul]
        rfl
      change ((trivializationAt E (TangentSpace I : M → Type _) x₀) ⟨y, sigma' y⟩).2 = hE y
      rw [show (trivializationAt E (TangentSpace I : M → Type _) x₀) = e from rfl, happly,
          hsigma'_val]
      exact e.continuousLinearMapAt_symmL (R := ℝ) hy_base (hE y)
    -- Step 2: therefore mfderiv agrees.
    have h_mfderiv_eq : mfderiv I 𝓘(ℝ, E)
        (fun y => ((trivializationAt E (TangentSpace I : M → Type _) x₀) ⟨y, sigma' y⟩).2) x₀ =
        mfderiv I 𝓘(ℝ, E) hE x₀ :=
      Filter.EventuallyEq.mfderiv_eq hee
    -- Step 3: compute mfderiv hE x₀ = L₀.
    -- hE y = T (phi y) + const. So mfderiv hE x₀ = T ∘L mfderiv phi x₀.
    have hphi_mdiffAt : MDifferentiableAt I 𝓘(ℝ, E) phi x₀ :=
      mdifferentiableAt_extChartAt hx₀_src
    have hTphi_mdiffAt : MDifferentiableAt I 𝓘(ℝ, E) (fun z => T (phi z)) x₀ :=
      T.mdifferentiableAt.comp x₀ hphi_mdiffAt
    have hconst_mdiffAt : MDifferentiableAt I 𝓘(ℝ, E) (fun _ : M => v₀ - T (phi x₀)) x₀ :=
      mdifferentiableAt_const
    have hhE_mfderiv :
        mfderiv I 𝓘(ℝ, E) hE x₀ = T ∘L mfderiv I 𝓘(ℝ, E) phi x₀ := by
      -- mfderiv (f+g) = mfderiv f + mfderiv g; mfderiv const = 0; mfderiv (T∘phi) = T ∘ mfderiv phi.
      have hE_eq : hE = (fun z => T (phi z)) + (fun _ : M => v₀ - T (phi x₀)) := rfl
      rw [hE_eq, mfderiv_add hTphi_mdiffAt hconst_mdiffAt]
      have hTphi_mfderiv :
          mfderiv I 𝓘(ℝ, E) (fun z => T (phi z)) x₀ = T ∘L mfderiv I 𝓘(ℝ, E) phi x₀ := by
        rw [show (fun z => T (phi z)) = T ∘ phi from rfl,
            mfderiv_comp x₀ T.mdifferentiableAt hphi_mdiffAt, T.mfderiv_eq]
        rfl
      rw [hTphi_mfderiv]
      have hconst_mfderiv :
          mfderiv I 𝓘(ℝ, E) (fun _ : M => v₀ - T (phi x₀)) x₀ = 0 := mfderiv_const
      rw [hconst_mfderiv]
      exact add_zero _
    -- Step 4: T ∘L mfderiv phi x₀ = L₀ using
    --   mfderiv phi x₀ = e.continuousLinearMapAt ℝ x₀  (by continuousLinearMapAt_trivializationAt)
    --   and e.symmL ℝ x₀ ∘L e.continuousLinearMapAt ℝ x₀ = id  (by symmL_continuousLinearMapAt).
    have hphi_mfderiv :
        mfderiv I 𝓘(ℝ, E) phi x₀ = e.continuousLinearMapAt ℝ x₀ := by
      have := TangentBundle.continuousLinearMapAt_trivializationAt (I := I) (𝕜 := ℝ)
        (x₀ := x₀) (x := x₀) hx₀_src
      -- `this : e.continuousLinearMapAt ℝ x₀ = mfderiv (extChartAt I x₀) x₀`
      exact this.symm
    have hT_comp :
        T ∘L mfderiv I 𝓘(ℝ, E) phi x₀ = L₀ := by
      rw [hphi_mfderiv]
      -- T = L₀ ∘L e.symmL ℝ x₀
      -- (L₀ ∘L e.symmL ℝ x₀) ∘L e.continuousLinearMapAt ℝ x₀
      --   = L₀ ∘L (e.symmL ℝ x₀ ∘L e.continuousLinearMapAt ℝ x₀)
      --   = L₀ ∘L id = L₀
      change (L₀ ∘L e.symmL ℝ x₀) ∘L e.continuousLinearMapAt ℝ x₀ = L₀
      ext v
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
      exact congrArg L₀ (e.symmL_continuousLinearMapAt (R := ℝ) hx₀_base v)
    -- Combine.
    rw [h_mfderiv_eq, hhE_mfderiv, hT_comp]

/-! ### Primary definitions and properties -/

/-- Given `σ : Π x, TangentSpace I x` that is `MDifferentiableAt` at `x₀` (in
total-space form), produce a globally smooth `ContMDiffSection` whose value and
fiber-read `mfderiv` at `x₀` match `σ`'s. -/
noncomputable def smoothExtensionAt_MDiff
    (σ : Π x : M, TangentSpace I x) (x₀ : M)
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, σ y⟩ : TotalSpace E (TangentSpace I))) x₀) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  (exists_smooth_section_matching_1jet I M σ x₀ hσ).choose

/-- The extension has the same value as `σ` at `x₀`. -/
theorem smoothExtensionAt_MDiff_value
    (σ : Π x : M, TangentSpace I x) (x₀ : M)
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, σ y⟩ : TotalSpace E (TangentSpace I))) x₀) :
    (smoothExtensionAt_MDiff I M σ x₀ hσ) x₀ = σ x₀ :=
  (exists_smooth_section_matching_1jet I M σ x₀ hσ).choose_spec.1

/-- The fiber-read `mfderiv` of the extension at `x₀` matches that of `σ`. -/
theorem smoothExtensionAt_MDiff_fiberRead_mfderiv
    (σ : Π x : M, TangentSpace I x) (x₀ : M)
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, σ y⟩ : TotalSpace E (TangentSpace I))) x₀) :
    mfderiv I 𝓘(ℝ, E)
      (fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀
        ⟨y, (smoothExtensionAt_MDiff I M σ x₀ hσ) y⟩).2) x₀
    =
    mfderiv I 𝓘(ℝ, E)
      (fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀
        ⟨y, σ y⟩).2) x₀ :=
  (exists_smooth_section_matching_1jet I M σ x₀ hσ).choose_spec.2

end Realization

end
