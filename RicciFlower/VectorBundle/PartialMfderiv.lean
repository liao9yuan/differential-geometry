import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Analysis.Calculus.Deriv.Basic

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

/-- Fixed-base time derivative of a spatial exterior derivative.

This is the scalar mixed-partial frontier used by the Ricci-flow Christoffel
calculation.  It deliberately freezes the spatial base point and tangent vector:
the only varying parameter is the real time parameter.  A future coordinate
proof from joint `C^2` regularity should construct this predicate. -/
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
