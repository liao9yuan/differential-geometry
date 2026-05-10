import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.VectorField

/-!
# Partial derivative along the first factor of a product manifold

Auxiliary lemma for realized time-dependent calculus: the partial derivative in
the ℝ-factor of a jointly-`C^∞` real-valued function on `ℝ × M` is itself
jointly `C^∞`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

namespace RicciFlower

/-- The partial derivative along the first (real) factor of a jointly smooth
real-valued function on `ℝ × M` is itself jointly smooth. -/
theorem contMDiff_partial_deriv_fst
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (F : C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; ℝ⟯) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => deriv (fun t => F (t, p.2)) p.1) := by
  -- Rewrite `deriv` as `mfderiv ... 1`, so the result follows from the smoothness
  -- of `mfderiv` applied to a jointly smooth function.
  have hrw : (fun p : ℝ × M => deriv (fun t => F (t, p.2)) p.1) =
      fun p : ℝ × M => (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t => F (t, p.2)) p.1) (1 : ℝ) := by
    funext p
    rw [mfderiv_eq_fderiv]
    exact (fderiv_apply_one_eq_deriv (f := fun t => F (t, p.2)) (x := p.1)).symm
  rw [hrw]
  -- Reduce smoothness at `∞` to smoothness at every natural level.
  rw [contMDiff_infty]
  intro n p₀
  -- The composition `(q : (ℝ × M) × ℝ) ↦ F (q.2, q.1.2)` is jointly `C^∞`.
  have harg : ContMDiff ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : (ℝ × M) × ℝ => (q.2, q.1.2)) :=
    ContMDiff.prodMk contMDiff_snd contMDiff_fst.snd
  have hF : ContMDiff ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : (ℝ × M) × ℝ => F (q.2, q.1.2)) :=
    F.contMDiff.comp harg
  -- Apply `ContMDiffAt.mfderiv_apply` with `m = n`, `n' = n + 1` (inside `WithTop ℕ∞`).
  have h_apply :=
    ContMDiffAt.mfderiv_apply
      (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
      (f := fun (p : ℝ × M) (t : ℝ) => F (t, p.2))
      (g := fun p : ℝ × M => p.1)
      (g₁ := fun p : ℝ × M => p)
      (g₂ := fun _ : ℝ × M => (1 : ℝ))
      (x₀ := p₀)
      (m := (n : WithTop ℕ∞))
      ((hF.of_le (by exact_mod_cast le_top : ((n : WithTop ℕ∞) + 1) ≤ ∞)).contMDiffAt)
      contMDiffAt_fst
      contMDiffAt_id
      contMDiffAt_const
      le_rfl
  -- The source and target models are model spaces, so `inTangentCoordinates`
  -- collapses to the raw `mfderiv`.
  simpa [inTangentCoordinates_model_space] using h_apply

/-- Exterior derivative of a scalar multiple of a scalar function.

This is a small bridge for Ricci-flow component calculations, where
`partial_t g = -2 Ric` is differentiated once more in a frozen spatial
direction. -/
theorem extDerivFun_const_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (c : ℝ) {f : M -> ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    extDerivFun (I := I) (fun y : M => c * f y) x =
      c • extDerivFun (I := I) f x := by
  change extDerivFun (I := I) (c • f) x =
    c • extDerivFun (I := I) f x
  ext v
  have hmul := fromTangentSpace_mfderiv_smul_apply
    (I := I) (f := fun _ : M => c) (g := f)
    (by exact mdifferentiableAt_const (c := c)) hf v
  simpa [extDerivFun] using hmul

/-- Smoothness of the scalar exterior derivative applied to a smooth tangent field.

This packages the `ContMDiffAt.mfderiv_apply` theorem in the concrete form used
by tensor covariant-derivative smoothness proofs. -/
theorem extDerivFun_apply_contMDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (f : M -> ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M -> Type _)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun p : M => extDerivFun (I := I) f p (X p)) := by
  rw [contMDiff_infty]
  intro n x₀
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  let Xcoord : M -> E := fun p => e.continuousLinearMapAt ℝ p (X p)
  have hXcoord :
      ContMDiffAt I 𝓘(ℝ, E) (n : WithTop ℕ∞) Xcoord x₀ := by
    have hXTop :
        ContMDiffAt I 𝓘(ℝ, E) ∞
          (fun p : M => (e ⟨p, X p⟩).2) x₀ := by
      simpa [e] using
        (e.contMDiffAt_section_iff
          (s := fun p : M => X p)
          (x₀ := x₀)
          (by
            simp [e])).mp
          (X.contMDiff.contMDiffAt)
    refine (hXTop.of_le
      (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ ∞)).congr_of_eventuallyEq ?_
    · filter_upwards [e.open_baseSet.mem_nhds (by
        simp [e])] with p hp
      have hcoe : ⇑(e.linearMapAt ℝ p) = fun z => (e ⟨p, z⟩).2 :=
        e.coe_linearMapAt_of_mem (R := ℝ) hp
      simp [Xcoord, Bundle.Trivialization.continuousLinearMapAt_apply, hcoe]
  have hF :
      ContMDiffAt (I.prod I) 𝓘(ℝ, ℝ) ((n : WithTop ℕ∞) + 1)
        (fun q : M × M => f q.2) (x₀, x₀) := by
    exact (hf.contMDiffAt.comp (x₀, x₀) contMDiffAt_snd).of_le
      (by exact_mod_cast le_top : ((n : WithTop ℕ∞) + 1) ≤ ∞)
  have hApply :=
    ContMDiffAt.mfderiv_apply
      (I := I) (I' := 𝓘(ℝ, ℝ))
      (f := fun (_ : M) (p : M) => f p)
      (g := fun p : M => p)
      (g₁ := fun p : M => p)
      (g₂ := Xcoord)
      (x₀ := x₀)
      (m := (n : WithTop ℕ∞))
      hF contMDiffAt_id contMDiffAt_id hXcoord le_rfl
  refine hApply.congr_of_eventuallyEq ?_
  · filter_upwards [e.open_baseSet.mem_nhds (by
        simp [e])] with p hp
    have hp_src : p ∈ (chartAt H x₀).source := by
      simpa [e, TangentBundle.trivializationAt_baseSet] using hp
    have hf_src : f p ∈ (chartAt ℝ (f x₀)).source := by
      simp
    rw [inTangentCoordinates_eq (I := I) (I' := 𝓘(ℝ, ℝ))
      (f := fun p : M => p) (g := f)
      (ϕ := fun p : M => mfderiv I 𝓘(ℝ, ℝ) f p)
      hp_src hf_src]
    have htarget :
        (tangentBundleCore 𝓘(ℝ, ℝ) ℝ).coordChange
          (achart ℝ (f p)) (achart ℝ (f x₀)) (f p) = (1 : ℝ →L[ℝ] ℝ) := by
      simp
    have hsource :
        (tangentBundleCore I M).coordChange (achart H x₀) (achart H p) p =
          e.symmL ℝ p := by
      simpa [e] using
        (TangentBundle.symmL_trivializationAt_eq_core
          (𝕜 := ℝ) (I := I) (b₀ := x₀) (b := p) hp_src).symm
    have hcancel :
        e.symmL ℝ p (Xcoord p) = X p := by
      exact e.symmL_continuousLinearMapAt (R := ℝ) hp (X p)
    rw [htarget, hsource]
    change (mfderiv I 𝓘(ℝ, ℝ) f p) (X p) =
      (mfderiv I 𝓘(ℝ, ℝ) f p) (e.symmL ℝ p (Xcoord p))
    rw [hcancel]

/-- Pointwise version of `extDerivFun_apply_contMDiff`.

If a scalar function is smooth at `x₀` and `X` is a smooth tangent section,
then `p |-> extDerivFun f p (X p)` is smooth at `x₀`. -/
theorem extDerivFun_apply_contMDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {f : M -> ℝ} {x₀ : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x₀)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M -> Type _)) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun p : M => extDerivFun (I := I) f p (X p)) x₀ := by
  rw [contMDiffAt_infty]
  intro n
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  let Xcoord : M -> E := fun p => e.continuousLinearMapAt ℝ p (X p)
  have hXcoord :
      ContMDiffAt I 𝓘(ℝ, E) (n : WithTop ℕ∞) Xcoord x₀ := by
    have hXTop :
        ContMDiffAt I 𝓘(ℝ, E) ∞
          (fun p : M => (e ⟨p, X p⟩).2) x₀ := by
      simpa [e] using
        (e.contMDiffAt_section_iff
          (s := fun p : M => X p)
          (x₀ := x₀)
          (by
            simp [e])).mp
          (X.contMDiff.contMDiffAt)
    refine (hXTop.of_le
      (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ ∞)).congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds (by
        simp [e])] with p hp
    have hcoe : ⇑(e.linearMapAt ℝ p) = fun z => (e ⟨p, z⟩).2 :=
      e.coe_linearMapAt_of_mem (R := ℝ) hp
    simp [Xcoord, Bundle.Trivialization.continuousLinearMapAt_apply, hcoe]
  have hF :
      ContMDiffAt (I.prod I) 𝓘(ℝ, ℝ) ((n : WithTop ℕ∞) + 1)
        (fun q : M × M => f q.2) (x₀, x₀) := by
    exact (hf.comp (x₀, x₀) contMDiffAt_snd).of_le
      (by exact_mod_cast le_top : ((n : WithTop ℕ∞) + 1) ≤ ∞)
  have hApply :=
    ContMDiffAt.mfderiv_apply
      (I := I) (I' := 𝓘(ℝ, ℝ))
      (f := fun (_ : M) (p : M) => f p)
      (g := fun p : M => p)
      (g₁ := fun p : M => p)
      (g₂ := Xcoord)
      (x₀ := x₀)
      (m := (n : WithTop ℕ∞))
      hF contMDiffAt_id contMDiffAt_id hXcoord le_rfl
  refine hApply.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds (by
        simp [e])] with p hp
  have hp_src : p ∈ (chartAt H x₀).source := by
    simpa [e, TangentBundle.trivializationAt_baseSet] using hp
  have hf_src : f p ∈ (chartAt ℝ (f x₀)).source := by
    simp
  rw [inTangentCoordinates_eq (I := I) (I' := 𝓘(ℝ, ℝ))
    (f := fun p : M => p) (g := f)
    (ϕ := fun p : M => mfderiv I 𝓘(ℝ, ℝ) f p)
    hp_src hf_src]
  have htarget :
      (tangentBundleCore 𝓘(ℝ, ℝ) ℝ).coordChange
        (achart ℝ (f p)) (achart ℝ (f x₀)) (f p) = (1 : ℝ →L[ℝ] ℝ) := by
    simp
  have hsource :
      (tangentBundleCore I M).coordChange (achart H x₀) (achart H p) p =
        e.symmL ℝ p := by
    simpa [e] using
      (TangentBundle.symmL_trivializationAt_eq_core
        (𝕜 := ℝ) (I := I) (b₀ := x₀) (b := p) hp_src).symm
  have hcancel :
      e.symmL ℝ p (Xcoord p) = X p := by
    exact e.symmL_continuousLinearMapAt (R := ℝ) hp (X p)
  rw [htarget, hsource]
  change (mfderiv I 𝓘(ℝ, ℝ) f p) (X p) =
    (mfderiv I 𝓘(ℝ, ℝ) f p) (e.symmL ℝ p (Xcoord p))
  rw [hcancel]

section ModelMixed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem model_spatial_fderiv_eq
    (F : ℝ -> E -> ℝ)
    (hF : ContDiff ℝ 2 (fun p : ℝ × E => F p.1 p.2))
    (s : ℝ) (x V : E) :
    (fderiv ℝ (F s) x) V =
      (fderiv ℝ (fun p : ℝ × E => F p.1 p.2) (s, x)) (0, V) := by
  let G : ℝ × E -> ℝ := fun p => F p.1 p.2
  let L : E -> ℝ × E := fun y => (s, y)
  have hG : DifferentiableAt ℝ G (s, x) :=
    hF.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0) (s, x)
  have hL : DifferentiableAt ℝ L x := by
    fun_prop
  have hcomp := fderiv_comp (𝕜 := ℝ) (x := x) (f := L) (g := G) hG hL
  have hLderiv : (fderiv ℝ L x) V = (0, V) := by
    rw [DifferentiableAt.fderiv_prodMk]
    · simp
    · fun_prop
    · fun_prop
  change (fderiv ℝ (G ∘ L) x) V = (fderiv ℝ G (s, x)) (0, V)
  rw [hcomp]
  change (fderiv ℝ G (s, x)) ((fderiv ℝ L x) V) =
    (fderiv ℝ G (s, x)) (0, V)
  rw [hLderiv]

private theorem model_hasDerivAt_fixed_snd
    (A : ℝ × E -> ℝ) (t : ℝ) (x : E)
    (hA : DifferentiableAt ℝ A (t, x)) :
    HasDerivAt (fun s : ℝ => A (s, x))
      ((fderiv ℝ A (t, x)) (1, 0)) t := by
  let L : ℝ -> ℝ × E := fun s => (s, x)
  have hL : DifferentiableAt ℝ L t := by
    fun_prop
  have hcomp := (hA.hasFDerivAt.comp t hL.hasFDerivAt).hasDerivAt
  have hLderiv : deriv L t = (1, 0) := by
    rw [deriv]
    rw [DifferentiableAt.fderiv_prodMk]
    · simp
    · fun_prop
    · fun_prop
  simpa [hLderiv] using hcomp

/-- Model-space fixed-base mixed derivative.

This is the chart-level theorem behind
`∂t (d_x F_t(V)) = d_x(∂t F_t)(V)`.  The manifold version still needs the
coordinate transport from `extDerivFun` to chart derivatives, but the analytic
mixed-partial calculation itself is discharged here. -/
theorem fixedBaseFDerivTimeDerivativeAt_of_contDiff
    (F : ℝ -> E -> ℝ)
    (hF : ContDiff ℝ 2 (fun p : ℝ × E => F p.1 p.2))
    (t : ℝ) (x V : E) :
    HasDerivAt
      (fun s : ℝ => (fderiv ℝ (F s) x) V)
      ((fderiv ℝ
        (fun y : E =>
          (fderiv ℝ (fun p : ℝ × E => F p.1 p.2) (t, y)) (1, 0))
        x) V)
      t := by
  let G : ℝ × E -> ℝ := fun p => F p.1 p.2
  let A : ℝ × E -> ℝ := fun p => (fderiv ℝ G p) (0, V)
  let B : ℝ × E -> ℝ := fun p => (fderiv ℝ G p) (1, 0)
  have hAcont : ContDiff ℝ 1 A := by
    have hDA := hF.contDiff_fderiv_apply (m := (1 : WithTop ℕ∞)) (by norm_num)
    exact hDA.comp (contDiff_id.prodMk contDiff_const)
  have hA : DifferentiableAt ℝ A (t, x) :=
    (ContDiff.differentiable hAcont (by norm_num : (1 : WithTop ℕ∞) ≠ 0)) (t, x)
  have h0 := model_hasDerivAt_fixed_snd (E := E) A t x hA
  have hswap :
      (fderiv ℝ A (t, x)) (1, 0) =
        (fderiv ℝ (fun y : E => B (t, y)) x) V := by
    have hlie := VectorField.fderiv_apply_lieBracket
      (𝕜 := ℝ) (E := ℝ × E) (F := ℝ)
      (f := G)
      (V := fun _ : ℝ × E => (1, 0))
      (W := fun _ : ℝ × E => (0, V))
      (x := (t, x))
      hF.contDiffAt
      (by norm_num : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞))
      (by fun_prop)
      (by fun_prop)
    have hlie' :
        (fderiv ℝ A (t, x)) (1, 0) =
          (fderiv ℝ B (t, x)) (0, V) := by
      unfold A B
      simp [VectorField.lieBracket] at hlie
      linarith
    rw [hlie']
    symm
    have hBcont : ContDiff ℝ 1 B := by
      have hDB := hF.contDiff_fderiv_apply (m := (1 : WithTop ℕ∞)) (by norm_num)
      exact hDB.comp (contDiff_id.prodMk contDiff_const)
    have hBdiff : DifferentiableAt ℝ B (t, x) :=
      (ContDiff.differentiable hBcont (by norm_num : (1 : WithTop ℕ∞) ≠ 0)) (t, x)
    let L : E -> ℝ × E := fun y => (t, y)
    have hL : DifferentiableAt ℝ L x := by
      fun_prop
    have hcomp := fderiv_comp (𝕜 := ℝ) (x := x) (f := L) (g := B) hBdiff hL
    have hLderiv : (fderiv ℝ L x) V = (0, V) := by
      rw [DifferentiableAt.fderiv_prodMk]
      · simp
      · fun_prop
      · fun_prop
    change (fderiv ℝ (B ∘ L) x) V = (fderiv ℝ B (t, x)) (0, V)
    rw [hcomp]
    change (fderiv ℝ B (t, x)) ((fderiv ℝ L x) V) =
      (fderiv ℝ B (t, x)) (0, V)
    rw [hLderiv]
  refine (h0.congr_deriv hswap).congr_of_eventuallyEq ?_
  filter_upwards with s
  exact model_spatial_fderiv_eq (E := E) F hF s x V

theorem fixedBaseFDerivTimeDerivativeWithinAt_of_contDiff
    (F : ℝ -> E -> ℝ)
    (hF : ContDiff ℝ 2 (fun p : ℝ × E => F p.1 p.2))
    {timeSet : Set ℝ} {t : ℝ}
    (x V : E) :
    HasDerivWithinAt
      (fun s : ℝ => (fderiv ℝ (F s) x) V)
      ((fderiv ℝ
        (fun y : E =>
          (fderiv ℝ (fun p : ℝ × E => F p.1 p.2) (t, y)) (1, 0))
        x) V)
      timeSet
      t :=
  (fixedBaseFDerivTimeDerivativeAt_of_contDiff (E := E) F hF t x V).hasDerivWithinAt

end ModelMixed

/-- Fixed-base time derivative of a spatial exterior derivative.

This is the scalar mixed-partial frontier used by the Ricci-flow Christoffel
calculation.  It deliberately freezes the spatial base point and tangent vector:
the only varying parameter is the real time parameter.

The model-space analytic core is `fixedBaseFDerivTimeDerivativeAt_of_contDiff`.
To construct this predicate from manifold-level spacetime smoothness, the
remaining chart-local lemma should rewrite `extDerivFun` in a chart as the
model derivative and then apply that model-space theorem. -/
def FixedBaseExtDerivTimeDerivativeOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (timeSet : Set ℝ) (u : Set M)
    (F Ft : ℝ -> M -> ℝ) : Prop :=
  forall (t : ℝ) (x : M), x ∈ u ->
    forall V : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => extDerivFun (I := I) (F s) x V)
        (extDerivFun (I := I) (Ft t) x V)
        timeSet
        t

theorem fixedBaseExtDerivTimeDerivativeOn_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet : Set ℝ} {u : Set M}
    {F Ft : ℝ -> M -> ℝ}
    (h : FixedBaseExtDerivTimeDerivativeOn (I := I) timeSet u F Ft)
    {t : ℝ} {x : M} (hx : x ∈ u) (V : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : ℝ => extDerivFun (I := I) (F s) x V)
      (extDerivFun (I := I) (Ft t) x V)
      timeSet
      t :=
  h t x hx V

end RicciFlower
