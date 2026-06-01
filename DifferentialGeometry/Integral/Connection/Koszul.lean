import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import DifferentialGeometry.Integral.Connection.MetricCompatible
import DifferentialGeometry.VectorBundle.Section

/-!
# The Koszul identity and uniqueness of the Levi-Civita connection

For any covariant derivative `cov` on the tangent bundle of a smooth Riemannian manifold
which is **torsion-free** and **metric-compatible** with respect to a smooth Riemannian
metric `g`, the value `cov Y x (X x)` (Mathlib convention: `cov σ x v ≅ ∇_v σ`) is
determined by the Koszul identity:
$$
2\,g_x(\nabla_X Y, Z)
  = X\bigl(g(Y, Z)\bigr)(x) + Y\bigl(g(X, Z)\bigr)(x) - Z\bigl(g(X, Y)\bigr)(x)
    + g_x([X, Y], Z) - g_x([X, Z], Y) - g_x([Y, Z], X).
$$
The right-hand side depends only on `g` and the sections `X, Y, Z`, so any two such
covariant derivatives must agree pointwise on differentiable inputs.

This file proves:

* `koszul_identity_on` — the displayed formula at a point `x ∈ s`, with `MDiffAt`
  hypotheses on the three tangent sections.
* `koszul_identity` — the global form, for a bundled torsion-free metric-compatible
  covariant derivative.
* `koszul_local_uniqueness` — two covariant-derivative-on-a-set families that are both
  torsion-free and metric-compatible on `s` agree pointwise on `s`, when applied to
  differentiable tangent sections.
* `koszul_levi_civita_unique_of_torsionFree_metricCompatible` — global pointwise uniqueness on differentiable inputs.

The non-degeneracy step uses `ContMDiffSection.exists_eq_at` to extend an arbitrary
tangent vector at a point to a smooth global tangent section, allowing the metric
pairing $\zeta \mapsto g_x(v, \zeta)$ to be evaluated on every fibre vector.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

/-! ## Auxiliary non-degeneracy lemma

If two tangent vectors at a point `x` pair identically with every tangent vector at `x`
under the metric `g`, then they are equal. This is a fibre-level consequence of
positive-definiteness. -/

/-- Non-degeneracy of `g.inner` at a single fibre: if `g_x(v, ζ) = g_x(w, ζ)` for every
tangent vector `ζ : TangentSpace I x`, then `v = w`. -/
lemma SmoothRiemannianMetric.eq_of_inner_eq
    (g : Measure.SmoothRiemannianMetric I M) {x : M} {v w : TangentSpace I x}
    (h : ∀ ζ : TangentSpace I x, g.inner x v ζ = g.inner x w ζ) : v = w := by
  -- It suffices to show `v - w = 0`. Pair `v - w` against itself.
  have hpair : ∀ ζ : TangentSpace I x, g.inner x (v - w) ζ = 0 := by
    intro ζ
    have hsub : g.inner x (v - w) ζ = g.inner x v ζ - g.inner x w ζ := by
      simp [map_sub, ContinuousLinearMap.sub_apply]
    rw [hsub, h ζ, sub_self]
  -- Apply at `ζ = v - w` and use positivity.
  have hself : g.inner x (v - w) (v - w) = 0 := hpair (v - w)
  by_contra hne
  have hne' : v - w ≠ 0 := sub_ne_zero.mpr hne
  exact (lt_irrefl (0 : ℝ)) (hself ▸ g.pos x _ hne')

/-! ## The Koszul identity -/

variable
  {cov : (Π x : M, TangentSpace I x) →
    (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)}
  {g : Measure.SmoothRiemannianMetric I M}

/-- The directional derivative of an `ℝ`-valued function `f : M → ℝ` at a point `x : M`
along a tangent vector `v : TangentSpace I x`, packaged as a plain real number.

This is a thin wrapper around `(mfderiv I 𝓘(ℝ) f x) v` whose codomain
`TangentSpace 𝓘(ℝ, ℝ) (f x)` is definitionally `ℝ` but is not transparently treated
as such by typeclass inference, which makes sums of such expressions awkward to
elaborate without an explicit cast. Bundling the cast into a helper avoids
repeating the ascription throughout the Koszul identity. -/
@[reducible] def directionalDeriv (f : M → ℝ) (x : M) (v : TangentSpace I x) : ℝ :=
  (mfderiv I 𝓘(ℝ) f x) v

@[simp] lemma directionalDeriv_eq (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    directionalDeriv (I := I) f x v = (mfderiv I 𝓘(ℝ) f x) v := rfl

/-- **Koszul identity** (on-set form). Given a covariant derivative `cov` on the
tangent bundle of a smooth Riemannian manifold which is metric-compatible (in the local
form on a set `s`) and whose torsion vanishes on `s` (expressed via the equation
`cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x` for differentiable `X, Y` at
points of `s`), the Koszul formula relates `g_x(cov Y x (X x), Z x)` to a sum of
directional derivatives of `g`-pairings plus inner products with Lie brackets.

Argument convention: Mathlib's `cov Y x v` corresponds to `(∇_v Y)(x)` on paper, so
`cov Y x (X x)` is `(∇_X Y)(x)`. -/
theorem koszul_identity_on
    {s : Set M}
    (hMC : IsMetricCompatibleOn cov g s)
    (hTF : ∀ ⦃X Y : Π x : M, TangentSpace I x⦄ ⦃x : M⦄,
      MDiffAt (T% X) x → MDiffAt (T% Y) x → x ∈ s →
      cov Y x (X x) - cov X x (Y x) = VectorField.mlieBracket I X Y x)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (hxs : x ∈ s) :
    2 * g.inner x (cov Y x (X x)) (Z x) =
      directionalDeriv (I := I) (fun b => g.inner b (Y b) (Z b)) x (X x)
      + directionalDeriv (I := I) (fun b => g.inner b (X b) (Z b)) x (Y x)
      - directionalDeriv (I := I) (fun b => g.inner b (X b) (Y b)) x (Z x)
      + g.inner x (VectorField.mlieBracket I X Y x) (Z x)
      - g.inner x (VectorField.mlieBracket I X Z x) (Y x)
      - g.inner x (VectorField.mlieBracket I Y Z x) (X x) := by
  -- Three applications of metric compatibility, evaluated at `X x`, `Y x`, `Z x`.
  have eq1 : directionalDeriv (I := I) (fun b => g.inner b (Y b) (Z b)) x (X x) =
      g.inner x (cov Y x (X x)) (Z x) + g.inner x (Y x) (cov Z x (X x)) :=
    hMC hY hZ hxs (X x)
  have eq2 : directionalDeriv (I := I) (fun b => g.inner b (X b) (Z b)) x (Y x) =
      g.inner x (cov X x (Y x)) (Z x) + g.inner x (X x) (cov Z x (Y x)) :=
    hMC hX hZ hxs (Y x)
  have eq3 : directionalDeriv (I := I) (fun b => g.inner b (X b) (Y b)) x (Z x) =
      g.inner x (cov X x (Z x)) (Y x) + g.inner x (X x) (cov Y x (Z x)) :=
    hMC hX hY hxs (Z x)
  -- Three applications of torsion-freeness.
  have tf_XY : cov Y x (X x) - cov X x (Y x) = VectorField.mlieBracket I X Y x :=
    hTF hX hY hxs
  have tf_XZ : cov Z x (X x) - cov X x (Z x) = VectorField.mlieBracket I X Z x :=
    hTF hX hZ hxs
  have tf_YZ : cov Z x (Y x) - cov Y x (Z x) = VectorField.mlieBracket I Y Z x :=
    hTF hY hZ hxs
  -- Symmetry of the inner product, applied where needed.
  have sym1 : g.inner x (Y x) (cov Z x (X x)) = g.inner x (cov Z x (X x)) (Y x) :=
    g.symm x _ _
  have sym2 : g.inner x (X x) (cov Z x (Y x)) = g.inner x (cov Z x (Y x)) (X x) :=
    g.symm x _ _
  have sym3 : g.inner x (X x) (cov Y x (Z x)) = g.inner x (cov Y x (Z x)) (X x) :=
    g.symm x _ _
  -- Linearity in the first argument of `g.inner x`.
  have lin_sub_1 : ∀ a b c : TangentSpace I x,
      g.inner x (a - b) c = g.inner x a c - g.inner x b c := by
    intro a b c
    simp [map_sub, ContinuousLinearMap.sub_apply]
  -- Inner product of a Lie bracket via the torsion-free identity.
  have step_XY :
      g.inner x (VectorField.mlieBracket I X Y x) (Z x)
        = g.inner x (cov Y x (X x)) (Z x) - g.inner x (cov X x (Y x)) (Z x) := by
    rw [← tf_XY, lin_sub_1]
  have step_XZ :
      g.inner x (VectorField.mlieBracket I X Z x) (Y x)
        = g.inner x (cov Z x (X x)) (Y x) - g.inner x (cov X x (Z x)) (Y x) := by
    rw [← tf_XZ, lin_sub_1]
  have step_YZ :
      g.inner x (VectorField.mlieBracket I Y Z x) (X x)
        = g.inner x (cov Z x (Y x)) (X x) - g.inner x (cov Y x (Z x)) (X x) := by
    rw [← tf_YZ, lin_sub_1]
  -- Rewrite eq1, eq2, eq3 using inner-product symmetry.
  rw [sym1] at eq1
  rw [sym2] at eq2
  rw [sym3] at eq3
  -- Plug everything in. The remaining identity is purely arithmetic.
  rw [eq1, eq2, eq3, step_XY, step_XZ, step_YZ]
  ring

/-- **Koszul identity** (global form). For a bundled torsion-free metric-compatible
covariant derivative, the Koszul formula holds at every point. -/
theorem koszul_identity
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (htor : cov.torsion = 0)
    (hMC : IsMetricCompatible cov g)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    2 * g.inner x (cov.toFun Y x (X x)) (Z x) =
      directionalDeriv (I := I) (fun b => g.inner b (Y b) (Z b)) x (X x)
      + directionalDeriv (I := I) (fun b => g.inner b (X b) (Z b)) x (Y x)
      - directionalDeriv (I := I) (fun b => g.inner b (X b) (Y b)) x (Z x)
      + g.inner x (VectorField.mlieBracket I X Y x) (Z x)
      - g.inner x (VectorField.mlieBracket I X Z x) (Y x)
      - g.inner x (VectorField.mlieBracket I Y Z x) (X x) := by
  -- Translate `cov.torsion = 0` into the pointwise torsion-free equation.
  have hTF : ∀ ⦃A B : Π y : M, TangentSpace I y⦄ ⦃y : M⦄,
      MDiffAt (T% A) y → MDiffAt (T% B) y → y ∈ (Set.univ : Set M) →
      cov.toFun B y (A y) - cov.toFun A y (B y) = VectorField.mlieBracket I A B y := by
    intro A B y hA hB _
    exact (CovariantDerivative.torsion_eq_zero_iff cov).mp htor hA hB
  -- Apply the on-set version with `s = univ`.
  exact koszul_identity_on (s := Set.univ) hMC hTF hX hY hZ trivial

/-! ## Local uniqueness via Koszul -/

/-- **Koszul local uniqueness.** Two covariant-derivative-on-a-set families on the
tangent bundle that are both torsion-free and metric-compatible on `s` agree on `s`
when applied to differentiable tangent sections. -/
theorem koszul_local_uniqueness
    {s : Set M}
    {cov₁ cov₂ : (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)}
    (hTF₁ : ∀ ⦃X Y : Π x : M, TangentSpace I x⦄ ⦃x : M⦄,
      MDiffAt (T% X) x → MDiffAt (T% Y) x → x ∈ s →
      cov₁ Y x (X x) - cov₁ X x (Y x) = VectorField.mlieBracket I X Y x)
    (hTF₂ : ∀ ⦃X Y : Π x : M, TangentSpace I x⦄ ⦃x : M⦄,
      MDiffAt (T% X) x → MDiffAt (T% Y) x → x ∈ s →
      cov₂ Y x (X x) - cov₂ X x (Y x) = VectorField.mlieBracket I X Y x)
    (hMC₁ : IsMetricCompatibleOn cov₁ g s)
    (hMC₂ : IsMetricCompatibleOn cov₂ g s)
    {X Y : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hxs : x ∈ s) :
    cov₁ Y x (X x) = cov₂ Y x (X x) := by
  classical
  -- Pair `cov₁ Y x (X x) - cov₂ Y x (X x)` against every tangent vector at `x` via
  -- a smooth global tangent section through that vector.
  apply SmoothRiemannianMetric.eq_of_inner_eq g
  intro ζ
  -- Smooth global tangent section `Z` with `Z x = ζ`.
  obtain ⟨Z, hZx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x ζ
  have hZ : MDiffAt (T% fun y => Z y) x := Z.mdifferentiableAt
  -- Apply the Koszul identity for `cov₁` and `cov₂`.
  have h1 := koszul_identity_on (s := s) hMC₁ hTF₁ hX hY hZ hxs
  have h2 := koszul_identity_on (s := s) hMC₂ hTF₂ hX hY hZ hxs
  -- The right-hand sides are identical, hence the doubled left-hand sides agree.
  have hrhs := h1.trans h2.symm
  have hcancel := mul_left_cancel₀ (a := (2 : ℝ))
    (by norm_num : (2 : ℝ) ≠ 0) hrhs
  -- Replace `Z x` by `ζ`.
  simpa [hZx] using hcancel

/-! ## Global uniqueness on differentiable inputs

The bundled `CovariantDerivative` structure stores a raw function `toFun` defined on
*all* (not necessarily differentiable) sections. The `IsCovariantDerivativeOn`
hypothesis only constrains the values on differentiable sections, so two distinct
bundled covariant derivatives may still differ on non-differentiable inputs.
The Koszul argument therefore yields uniqueness on *differentiable inputs*, which is
the form in which the downstream Levi-Civita-existence file consumes it. -/

/-- **Koszul uniqueness of the Levi-Civita connection.** If two bundled covariant
derivatives `cov₁ cov₂` on the tangent bundle are both torsion-free
(`cov.torsion = 0`) and metric-compatible with respect to the same smooth Riemannian
metric `g`, then they agree, `cov₁.toFun Y x v = cov₂.toFun Y x v`, for every
differentiable section `Y` (`MDiffAt (T% Y) x`), every point `x`, and every tangent
vector `v`. Equality is only claimed on differentiable inputs, since the bundled
`toFun` is unconstrained on non-differentiable sections. -/
theorem koszul_levi_civita_unique_of_torsionFree_metricCompatible
    (cov₁ cov₂ : CovariantDerivative I E (TangentSpace I : M → Type _))
    (htor₁ : cov₁.torsion = 0) (htor₂ : cov₂.torsion = 0)
    (hMC₁ : IsMetricCompatible cov₁ g) (hMC₂ : IsMetricCompatible cov₂ g)
    {Y : Π x : M, TangentSpace I x} {x : M} (hY : MDiffAt (T% Y) x)
    (v : TangentSpace I x) :
    cov₁.toFun Y x v = cov₂.toFun Y x v := by
  classical
  -- Smooth global tangent section `X` with `X x = v`.
  obtain ⟨X, hXx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x v
  have hX : MDiffAt (T% fun y => X y) x := X.mdifferentiableAt
  -- Pull `cov.torsion = 0` into the pointwise torsion-free equation.
  have hTF₁ : ∀ ⦃A B : Π y : M, TangentSpace I y⦄ ⦃y : M⦄,
      MDiffAt (T% A) y → MDiffAt (T% B) y → y ∈ (Set.univ : Set M) →
      cov₁.toFun B y (A y) - cov₁.toFun A y (B y) = VectorField.mlieBracket I A B y := by
    intro A B y hA hB _
    exact (CovariantDerivative.torsion_eq_zero_iff cov₁).mp htor₁ hA hB
  have hTF₂ : ∀ ⦃A B : Π y : M, TangentSpace I y⦄ ⦃y : M⦄,
      MDiffAt (T% A) y → MDiffAt (T% B) y → y ∈ (Set.univ : Set M) →
      cov₂.toFun B y (A y) - cov₂.toFun A y (B y) = VectorField.mlieBracket I A B y := by
    intro A B y hA hB _
    exact (CovariantDerivative.torsion_eq_zero_iff cov₂).mp htor₂ hA hB
  -- Local uniqueness with `s = univ`, applied at the section pair `(X, Y)` and point `x`.
  have hloc : cov₁.toFun Y x (X x) = cov₂.toFun Y x (X x) :=
    koszul_local_uniqueness (s := Set.univ) hTF₁ hTF₂ hMC₁ hMC₂ hX hY trivial
  -- Replace `X x` by `v`.
  simpa [hXx] using hloc

end Connection
end Integral
end DifferentialGeometry
