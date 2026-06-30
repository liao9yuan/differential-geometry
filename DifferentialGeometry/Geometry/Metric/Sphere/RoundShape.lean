import DifferentialGeometry.Geometry.Metric.Sphere.RoundProjConnLC
import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# Shape operator and Gauss equation for the round sphere (Step C)

The outward unit normal of `S^n ⊂ E` at `x` is the position vector `↑x`.  Differentiating the
constraint `⟪dι Y, ↑·⟫ = 0` (tangent vectors are orthogonal to the normal) gives the shape-operator
identity `⟪D_v(dι Y), ↑x⟫ = −g(Y, v)`.  This is the analytic input to the Gauss equation that
computes the round sphere's sectional curvature.

## Main results

* `ambDeriv_inner_normal` — `⟪ambDeriv Y x v, ↑x⟫ = −roundInner x (Y x) v` (shape operator = identity).
* `ambDeriv_gauss` — the Gauss formula `D_v(dι Y) = dι(∇_v Y) − g(Y,v)·x`.
* `ambDeriv2` / `ambDeriv_bracket_symm` — the second ambient derivative and its bracket symmetry
  (ambient flatness), the keystone of the Gauss-equation computation.
* `inner_dIncl_metricCov` — the paired tangential reduction `⟪dι(∇_v S), dι W⟫ = ⟪D_v(dι S), dι W⟫`.
* `mdiffAt_inner_left` — differentiability of `p ↦ ⟪w, F p⟫`.
-/

noncomputable section

open Bundle Manifold Set Metric Module VectorField
open scoped Manifold Topology ContDiff RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

omit [FiniteDimensional ℝ E] in
/-- **Shape operator = identity.**  Differentiating the orthogonality `⟪dι Y, ↑·⟫ = 0`, the normal
component of the ambient derivative of a pushed section is `⟪ambDeriv Y x v, ↑x⟫ = −g(Y x, v)`. -/
theorem ambDeriv_inner_normal {Y : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x}
    {x : sphere (0 : E) 1}
    (hY : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (Y y))) x)
    (v : TangentSpace (𝓡 n) x) :
    ⟪ambDeriv (n := n) Y x v, (↑x : E)⟫ = - roundInner (n := n) x (Y x) v := by
  have hYd := dInclField_mdifferentiableAt (n := n) hY
  have hcoeC : ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞ ((↑) : sphere (0 : E) 1 → E) x :=
    contMDiff_coe_sphere.contMDiffAt
  have hcoe : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x :=
    hcoeC.mdifferentiableAt (by simp)
  -- The orthogonality constraint, identically zero on the sphere.
  have hf0 : (fun b => ⟪dInclField (n := n) Y b, (↑b : E)⟫) = fun _ => (0 : ℝ) := by
    funext b
    refine Submodule.inner_left_of_mem_orthogonal (Submodule.mem_span_singleton_self (↑b : E)) ?_
    rw [dInclField_apply, ← range_mfderiv_coe_sphere (n := n) b]
    exact ⟨Y b, rfl⟩
  -- Differentiate via the inner-product product rule; the constraint has zero derivative.
  have hmf := mfderiv_inner (n := n) hYd hcoe v
  have hf0' : mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
      (fun b => ⟪dInclField (n := n) Y b, (↑b : E)⟫) x v = 0 := by
    rw [hf0]; simp only [mfderiv_const]; rfl
  have hmf2 := hf0'.symm.trans hmf
  -- The normal-derivative term is the metric pairing.
  have hcoeval : mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x v = dIncl (n := n) x v := rfl
  have hroundeq : ⟪dInclField (n := n) Y x,
      mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x v⟫ = roundInner (n := n) x (Y x) v := by
    rw [hcoeval, dInclField_apply, roundInner_apply]
  rw [hroundeq] at hmf2
  exact eq_neg_of_add_eq_zero_left hmf2.symm

omit [FiniteDimensional ℝ E] in
/-- **Gauss formula for the round sphere.**  The ambient directional derivative of a pushed tangent
section splits into its tangential part (the projection connection `∇ = projConn`) and a normal part
governed by the metric: `D_v(dι Y) = dι(∇_v Y) − g(Y, v)·x`.  (Outward unit normal `ν = ↑x`.) -/
theorem ambDeriv_gauss {Y : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x}
    {x : sphere (0 : E) 1}
    (hY : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (Y y))) x)
    (v : TangentSpace (𝓡 n) x) :
    ambDeriv (n := n) Y x v
      = dIncl (n := n) x (projConn (n := n) Y x v) - roundInner (n := n) x (Y x) v • (↑x : E) := by
  have hnorm : ‖(↑x : E)‖ = 1 := norm_eq_of_mem_sphere x
  -- Singleton projection onto the normal line (unit `↑x`).
  have hsing : (ℝ ∙ (↑x : E)).starProjection (ambDeriv (n := n) Y x v)
      = ⟪(↑x : E), ambDeriv (n := n) Y x v⟫ • (↑x : E) := by
    rw [Submodule.starProjection_singleton, hnorm]; norm_num
  -- Tangential part = `w − ⟪x, w⟫ • x`.
  have hproj : dIncl (n := n) x (projConn (n := n) Y x v)
      = ambDeriv (n := n) Y x v - ⟪(↑x : E), ambDeriv (n := n) Y x v⟫ • (↑x : E) := by
    rw [dIncl_projConn, Submodule.coe_orthogonalProjection_apply]
    have hsplit := (ℝ ∙ (↑x : E)).starProjection_add_starProjection_orthogonal
      (ambDeriv (n := n) Y x v)
    rw [hsing] at hsplit
    exact eq_sub_of_add_eq (by rw [add_comm]; exact hsplit)
  -- Identify the normal coefficient via the shape-operator identity (C1).
  have hcomm : ⟪(↑x : E), ambDeriv (n := n) Y x v⟫ = - roundInner (n := n) x (Y x) v := by
    rw [real_inner_comm]; exact ambDeriv_inner_normal (n := n) hY v
  rw [hproj, hcomm]
  module

/-- The ambient second directional derivative `v ↦ D_v(D_W(dι Z))` as an `E`-valued CLM (codomain
ascribed to `E` to avoid the per-point `TangentSpace 𝓘(ℝ,E)` synonym, exactly as `ambDeriv` does). -/
noncomputable def ambDeriv2
    (Z W : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n), (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯)
    (x : sphere (0 : E) 1) : TangentSpace (𝓡 n) x →L[ℝ] E :=
  (mfderiv (𝓡 n) 𝓘(ℝ, E) (fun p => ambDeriv (n := n) (⇑Z) p (W p)) x :
    TangentSpace (𝓡 n) x →L[ℝ] E)

omit [FiniteDimensional ℝ E] in
@[simp] theorem ambDeriv2_apply
    (Z W : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n), (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯)
    (x : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) :
    ambDeriv2 (n := n) Z W x v
      = mfderiv (𝓡 n) 𝓘(ℝ, E) (fun p => ambDeriv (n := n) (⇑Z) p (W p)) x v := rfl

/-- **Ambient flatness / second-derivative bracket symmetry.**  For a smooth section `Z` and smooth
fields `X, Y` on the sphere, the iterated ambient derivative of `dι Z` is symmetric up to the bracket:
`D_X(D_Y(dι Z)) − D_Y(D_X(dι Z)) = D_{[X,Y]}(dι Z)`.  The two MDiffAt hypotheses are the smoothness of
the first covariant derivatives `D_Y(dι Z)`, `D_X(dι Z)` (supplied at the call site via
`cov_smooth_apply_contMDiffAt` + the Gauss formula).  Proved by the functional test against every
ambient `w`, applying `embedDeriv_mlieBracket` to the first-level field `embedDeriv Z (innerCoordFun w)`. -/
theorem ambDeriv_bracket_symm
    (Z X Y : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n), (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯)
    (x : sphere (0 : E) 1)
    (hDY : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E)
      (fun p => ambDeriv (n := n) (⇑Z) p (Y p)) x)
    (hDX : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E)
      (fun p => ambDeriv (n := n) (⇑Z) p (X p)) x) :
    ambDeriv2 (n := n) Z Y x (X x) - ambDeriv2 (n := n) Z X x (Y x)
      = ambDeriv (n := n) (⇑Z) x (mlieBracket (𝓡 n) (⇑X) (⇑Y) x) := by
  simp only [ambDeriv2_apply]
  refine ext_inner_left ℝ fun w => ?_
  -- `dι Z` is differentiable everywhere (smooth section).
  have hZdiff : ∀ p : sphere (0 : E) 1,
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (dInclField (n := n) (⇑Z)) p := fun p =>
    dInclField_mdifferentiableAt (n := n) (Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  -- Level-0 field `g w = embedDeriv Z (innerCoordFun w) = ⟪w, dι Z ·⟫`.
  set gw := embedDeriv (𝓡 n) (sphere (0 : E) 1) Z (innerCoordFun (E := E) (n := n) w) with hgwdef
  have hgw : (⇑gw : sphere (0 : E) 1 → ℝ) = fun p => ⟪w, dInclField (n := n) (⇑Z) p⟫ := by
    funext p
    change vectorFieldAction (𝓡 n) (sphere (0 : E) 1) Z (innerCoordFun w) p = _
    simp only [vectorFieldAction]
    rw [show extDerivFun (I := 𝓡 n) (innerCoordFun w) p (Z p)
          = mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (innerCoordFun (E := E) (n := n) w) p (Z p) from rfl,
      mfderiv_innerCoordFun, dInclField_apply]
  -- Level-1 field `embedDeriv W g w = ⟪w, D_W(dι Z) ·⟫`, for any smooth field `W`.
  have hWlevel : ∀ (W : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n),
        (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯),
      (⇑(embedDeriv (𝓡 n) (sphere (0 : E) 1) W gw) : sphere (0 : E) 1 → ℝ)
        = fun p => ⟪w, ambDeriv (n := n) (⇑Z) p (W p)⟫ := by
    intro W
    funext p
    change vectorFieldAction (𝓡 n) (sphere (0 : E) 1) W gw p = _
    simp only [vectorFieldAction]
    rw [show extDerivFun (I := 𝓡 n) gw p (W p)
          = mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (⇑gw) p (W p) from rfl,
      hgw, mfderiv_inner_left w (hZdiff p) (W p), ambDeriv_apply]
  -- Level-2: differentiate the level-1 field, using the supplied smoothness of `D_W(dι Z)`.
  have hsecond : ∀ (V W : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n),
        (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯),
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (fun p => ambDeriv (n := n) (⇑Z) p (W p)) x →
      (embedDeriv (𝓡 n) (sphere (0 : E) 1) V
          (embedDeriv (𝓡 n) (sphere (0 : E) 1) W gw) : sphere (0 : E) 1 → ℝ) x
        = ⟪w, mfderiv (𝓡 n) 𝓘(ℝ, E)
            (fun p => ambDeriv (n := n) (⇑Z) p (W p)) x (V x)⟫ := by
    intro V W hD
    change vectorFieldAction (𝓡 n) (sphere (0 : E) 1) V
      (embedDeriv (𝓡 n) (sphere (0 : E) 1) W gw) x = _
    simp only [vectorFieldAction]
    rw [show extDerivFun (I := 𝓡 n) (embedDeriv (𝓡 n) (sphere (0 : E) 1) W gw) x (V x)
          = mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
              (⇑(embedDeriv (𝓡 n) (sphere (0 : E) 1) W gw)) x (V x) from rfl,
      hWlevel W, mfderiv_inner_left w hD (V x)]
  -- The bracket identity at `x`.
  have hbr := embedDeriv_mlieBracket (I := 𝓡 n) (M := sphere (0 : E) 1) X Y gw
  have hbrx : (embedDeriv (𝓡 n) (sphere (0 : E) 1)
        (mlieBracketSection (𝓡 n) (sphere (0 : E) 1) X Y) gw : sphere (0 : E) 1 → ℝ) x
      = (embedDeriv (𝓡 n) (sphere (0 : E) 1) X
          (embedDeriv (𝓡 n) (sphere (0 : E) 1) Y gw) : sphere (0 : E) 1 → ℝ) x
        - (embedDeriv (𝓡 n) (sphere (0 : E) 1) Y
            (embedDeriv (𝓡 n) (sphere (0 : E) 1) X gw) : sphere (0 : E) 1 → ℝ) x := by
    have h := DFunLike.congr_fun hbr x
    simpa using h
  -- Bracket-section level: `embedDeriv [X,Y] g w x = ⟪w, D_{[X,Y]}(dι Z)⟫`.
  have hbrlevel : (embedDeriv (𝓡 n) (sphere (0 : E) 1)
        (mlieBracketSection (𝓡 n) (sphere (0 : E) 1) X Y) gw : sphere (0 : E) 1 → ℝ) x
      = ⟪w, ambDeriv (n := n) (⇑Z) x (mlieBracket (𝓡 n) (⇑X) (⇑Y) x)⟫ := by
    rw [hWlevel (mlieBracketSection (𝓡 n) (sphere (0 : E) 1) X Y)]
    rfl
  rw [hbrlevel, hsecond X Y hDY, hsecond Y X hDX] at hbrx
  rw [inner_sub_right]
  exact hbrx.symm

/-- **Paired tangential reduction.**  The connection value `∇_v S = metricCov g S x v` paired against a
tangent vector equals the ambient derivative paired against it (the normal part of `D_v(dι S)` drops
out): `⟪dι(∇_v S), dι W⟫ = ⟪D_v(dι S), dι W⟫`.  The orthogonal projection is self-adjoint and fixes the
tangent vector `dι W`. -/
theorem inner_dIncl_metricCov
    {S : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x} {x : sphere (0 : E) 1}
    (hS : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (S y))) x)
    (v W : TangentSpace (𝓡 n) x) :
    ⟪dIncl (n := n) x (Integral.Connection.metricCov (roundMetric (E := E) (n := n)) S x v),
        dIncl (n := n) x W⟫
      = ⟪ambDeriv (n := n) S x v, dIncl (n := n) x W⟫ := by
  rw [← projConn_eq_metricCov hS v, dIncl_projConn, ← Submodule.starProjection_apply]
  have hmem : dIncl (n := n) x W ∈ (ℝ ∙ (↑x : E))ᗮ := by
    rw [← range_mfderiv_coe_sphere (n := n) x]; exact ⟨W, rfl⟩
  have h0 := Submodule.starProjection_inner_eq_zero (K := (ℝ ∙ (↑x : E))ᗮ)
    (ambDeriv (n := n) S x v) (dIncl (n := n) x W) hmem
  rw [inner_sub_left, sub_eq_zero] at h0
  exact h0.symm

omit [FiniteDimensional ℝ E] in
/-- Differentiability companion of `mfderiv_inner_left`: `p ↦ ⟪w, F p⟫` is differentiable.  Stated with
`F` generic so a concrete coercion is passed as an argument, avoiding the chart mis-inference that a
bare `MDifferentiableAt (fun p => ⟪w, ↑p⟫)` triggers. -/
theorem mdiffAt_inner_left (w : E) {F : sphere (0 : E) 1 → E} {x : sphere (0 : E) 1}
    (hF : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) F x) :
    MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun p => ⟪w, F p⟫) x := by
  haveI : InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E) (F x)) :=
    inferInstanceAs (InnerProductSpace ℝ E)
  exact ((innerSL ℝ w).hasFDerivAt.hasMFDerivAt.comp x hF.hasMFDerivAt).mdifferentiableAt

end Geometry
end DifferentialGeometry
