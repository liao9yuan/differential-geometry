import DifferentialGeometry.PDE.RicciFlow.Pullback.PushforwardVF
import DifferentialGeometry.PDE.RicciFlow.Pullback.Metric
import DifferentialGeometry.PDE.RicciFlow.Pullback.MLieBracketNaturality
import DifferentialGeometry.PDE.RicciFlow.Pullback.PullbackConnection
import DifferentialGeometry.PDE.RicciFlow.Pullback.CovDerivPullbackNaturality
import DifferentialGeometry.Integral.Connection.LeviCivita
import DifferentialGeometry.Integral.Connection.Koszul

/-!
# Pointwise connection-pullback chain rule for the Levi-Civita derivative

For a smooth Riemannian metric `g` on `M` and a smooth diffeomorphism
`Φ : M ≃ₘ⟮I, I⟯ M`, the Levi-Civita connection of the pullback metric `Φ*g`
intertwines with the Levi-Civita connection of `g` through the manifold
derivative of `Φ` and the pushforward of vector fields:

  `dΦ(∇^{Φ*g}_v X) = ∇^g_{dΦ v}(Φ_*X)`.

This is the missing pointwise chain rule that complements
`covariant_derivative_of_pullback_vf_naturality`, which records the
connection-equality `LeviCivita (Φ*g) = pullback_connection_construct g Φ`
as a definitional `rfl` (the bundled identity), without exposing the
pointwise transport of values.

## Proof strategy

We define the unbundled *conjugate* function
`conjCovFun g Φ Y x v := (mfderiv Φ.symm (Φ x))
  ((LeviCivita g).toFun (Φ_* Y) (Φ x) (mfderiv Φ x v))`
and verify it satisfies, on differentiable inputs at a point:

* the torsion-free identity
  `conjCovFun Y x (X x) - conjCovFun X x (Y x) = mlieBracket I X Y x`
  via `LeviCivita_torsion_eq_zero` applied to `(Φ_* X, Φ_* Y)` and
  `mlie_bracket_pullback_naturality`;

* metric compatibility with `pullbackMetric g Φ` via the chain rule for
  `mfderiv` applied to `b ↦ g_{Φ b}((Φ_* Y)(Φ b), (Φ_* Z)(Φ b))` together
  with `LeviCivita_isMetricCompatible`.

`koszul_local_uniqueness` then identifies `conjCovFun` with
`(LeviCivita (Φ*g)).toFun` pointwise on smooth sections, after which
applying `mfderiv Φ x` to the resulting identity collapses the inner
`mfderiv Φ.symm (Φ x)` and yields the claimed chain rule.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle Manifold Set
open scoped Manifold Topology ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open VectorField

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

private lemma infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by decide

/-! ## Auxiliary identities for `Φ` and its derivative -/

/-- Composing the manifold derivative of `Φ` after that of `Φ.symm` at `Φ x` returns the
identity on `T_x M`. The output type `T_x M →L T_x M` is matched by composing in this order. -/
private lemma mfderiv_self_after_symm_at_image
    (Φ : M ≃ₘ⟮I, I⟯ M) (x : M) :
    (mfderiv I I (⇑Φ) x).comp (mfderiv I I (⇑Φ.symm) (Φ x))
      = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  have hΦsymm : MDifferentiableAt I I (⇑Φ.symm) (Φ x) :=
    Φ.symm.mdifferentiable infty_ne_zero (Φ x)
  have hΦ : MDifferentiableAt I I (⇑Φ) (Φ.symm (Φ x)) := by
    have : Φ.symm (Φ x) = x := Φ.symm_apply_apply x
    rw [this]; exact Φ.mdifferentiable infty_ne_zero x
  have hcomp : (⇑Φ) ∘ (⇑Φ.symm) = (id : M → M) := by
    funext z; exact Φ.apply_symm_apply z
  have hchain := mfderiv_comp (Φ x) hΦ hΦsymm
  rw [hcomp, mfderiv_id] at hchain
  -- `hchain : id = (mfderiv Φ (Φ.symm (Φ x))).comp (mfderiv Φ.symm (Φ x))`.
  -- Rewrite `Φ.symm (Φ x) = x`.
  have hsym : Φ.symm (Φ x) = x := Φ.symm_apply_apply x
  -- Substitute hsym in hchain. We need to be careful because Φ.symm (Φ x) appears
  -- inside `mfderiv Φ` as the basepoint, and `TangentSpace I (Φ.symm (Φ x))` is
  -- definitionally `E`, same as `TangentSpace I x`.
  have hΦatx : mfderiv I I (⇑Φ) (Φ.symm (Φ x)) = mfderiv I I (⇑Φ) x := by
    congr 1
  rw [hΦatx] at hchain
  exact hchain.symm

/-- Applied form: `mfderiv Φ x (mfderiv Φ.symm (Φ x) w) = w`. -/
private lemma mfderiv_apply_mfderiv_symm
    (Φ : M ≃ₘ⟮I, I⟯ M) (x : M) (w : TangentSpace I (Φ x)) :
    mfderiv I I (⇑Φ) x (mfderiv I I (⇑Φ.symm) (Φ x) w) = w := by
  have h := mfderiv_self_after_symm_at_image (I := I) Φ x
  have := congrArg (fun f : TangentSpace I x →L[ℝ] TangentSpace I x => f w) h
  -- Goal is over `T_x M ≅ E` so `id` returns `w`.
  -- The displayed coercion needs cleanup.
  simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using this

/-- The reverse direction: `mfderiv Φ.symm (Φ x) (mfderiv Φ x v) = v`. -/
private lemma mfderiv_symm_apply_mfderiv
    (Φ : M ≃ₘ⟮I, I⟯ M) (x : M) (v : TangentSpace I x) :
    mfderiv I I (⇑Φ.symm) (Φ x) (mfderiv I I (⇑Φ) x v) = v := by
  -- Use `mfderiv_symm_comp_self` style computation.
  have hΦ : MDifferentiableAt I I (⇑Φ) x := Φ.mdifferentiable infty_ne_zero x
  have hΦsymm : MDifferentiableAt I I (⇑Φ.symm) (Φ x) :=
    Φ.symm.mdifferentiable infty_ne_zero (Φ x)
  have hcomp : (⇑Φ.symm) ∘ (⇑Φ) = (id : M → M) := by
    funext z; exact Φ.symm_apply_apply z
  have hchain := mfderiv_comp x hΦsymm hΦ
  rw [hcomp, mfderiv_id] at hchain
  -- `hchain : id = (mfderiv Φ.symm (Φ x)).comp (mfderiv Φ x)` (as CLMs `T_x M →L T_x M`).
  have := congrArg (fun f : TangentSpace I x →L[ℝ] TangentSpace I x => f v) hchain.symm
  simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using this

/-- The pushforward of `Y` at `Φ x` equals `mfderiv Φ x (Y x)`, after handling the
`Eq.rec` transport that appears in `Diffeomorph.pushforward`. -/
private lemma pushforward_at_image
    (Φ : M ≃ₘ⟮I, I⟯ M) (Y : ∀ x : M, TangentSpace I x) (x : M) :
    Diffeomorph.pushforward Φ Y (Φ x) = mfderiv I I (⇑Φ) x (Y x) := by
  -- Unfold the definition. The `▸` transports `T_{Φ (Φ.symm (Φ x))}` to `T_{Φ x}`.
  -- Φ.symm (Φ x) = x, so this is morally trivial, but requires `eqRec_heq`.
  change (Φ.apply_symm_apply (Φ x)) ▸
    (mfderiv I I (⇑Φ) (Φ.symm (Φ x))) (Y (Φ.symm (Φ x))) = mfderiv I I (⇑Φ) x (Y x)
  -- We need to show that the RHS equals the LHS after `Eq.rec`.
  -- The basepoint `Φ.symm (Φ x) = x` by `symm_apply_apply`.
  have hbase : Φ.symm (Φ x) = x := Φ.symm_apply_apply x
  -- Equality via `heq` because the dependent type changes.
  refine eq_of_heq ?_
  refine (eqRec_heq (φ := fun z => TangentSpace I z)
    (Φ.apply_symm_apply (Φ x))
    ((mfderiv I I (⇑Φ) (Φ.symm (Φ x))) (Y (Φ.symm (Φ x))))).trans ?_
  -- Goal: HEq ((mfderiv Φ (Φ.symm (Φ x))) (Y (Φ.symm (Φ x)))) ((mfderiv Φ x) (Y x))
  -- Both have type `TangentSpace I _ = E` definitionally. Use that the basepoint equates.
  rw [hbase]

/-! ## The conjugate connection function -/

/-- The conjugate-by-`Φ` of the Levi-Civita connection of `g`. As an unbundled function
of a section and a basepoint with a CLM value, this is
$$
  (\text{conjCovFun}\,g\,\Phi\,Y)(x)\,v
    = \mathrm{d}\Phi^{-1}_{\Phi x}\bigl(\nabla^g_{\mathrm{d}\Phi_x v}(\Phi_*Y)\bigr).
$$
The output type is `TangentSpace I x →L[ℝ] TangentSpace I x`; the inner application
to `Φ_*Y` produces a value in `T_{Φ x} M`, transported back by `mfderiv Φ.symm (Φ x)`.
The CLM is composed as `(mfderiv Φ.symm (Φ x)) ∘ ((LeviCivita g).toFun (Φ_*Y) (Φ x)) ∘
(mfderiv Φ x)`. -/
def conjCovFun
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (Y : ∀ x : M, TangentSpace I x) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  let inner : TangentSpace I (Φ x) →L[ℝ] TangentSpace I x :=
    (mfderiv I I (⇑Φ.symm) (Φ x)).comp
      ((LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ Y) (Φ x))
  inner.comp (mfderiv I I (⇑Φ) x)

@[simp] lemma conjCovFun_apply
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (Y : ∀ x : M, TangentSpace I x) (x : M) (v : TangentSpace I x) :
    conjCovFun g Φ Y x v =
      mfderiv I I (⇑Φ.symm) (Φ x)
        ((LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ Y) (Φ x)
          (mfderiv I I (⇑Φ) x v)) := rfl

/-! ## Pushforward of a differentiable section is differentiable

The pushforward of a manifold-differentiable section `Y` along a smooth diffeomorphism
`Φ` is manifold-differentiable at the image point. We obtain this from
`MDifferentiableAt.mpullback_vectorField` applied to `Φ.symm`, after the identification
`pushforward Φ Y = mpullback Φ.symm Y` (`pushforward_eq_mpullback_symm`). -/

/-- For a diffeomorphism `Φ`, the pushforward of a vector field equals the manifold
pullback of the same vector field by the inverse diffeomorphism. This is the function-level
version of the pointwise lemma `pushforward_eq_mpullback_symm` (which is `private` in
`MLieBracketNaturality.lean`). -/
private lemma pushforward_eq_mpullback_symm_fun
    (Φ : M ≃ₘ⟮I, I⟯ M) (Y : ∀ x : M, TangentSpace I x) :
    (Diffeomorph.pushforward Φ Y : ∀ x : M, TangentSpace I x)
      = (VectorField.mpullback I I (⇑Φ.symm) Y : ∀ x : M, TangentSpace I x) := by
  funext z
  -- Re-derive the proof from `MLieBracketNaturality.lean`.
  have hinv : (mfderiv I I (⇑Φ.symm) z).inverse = mfderiv I I (⇑Φ) (Φ.symm z) := by
    apply ContinuousLinearMap.inverse_eq
    · -- `(mfderiv Φ.symm z).comp (mfderiv Φ (Φ.symm z)) = id` on `T_{Φ.symm z} M`.
      -- This is `mfderiv_symm_comp_self`-style: the inverse-direction chain.
      have hΦ : MDifferentiableAt I I (⇑Φ) (Φ.symm z) :=
        Φ.mdifferentiable infty_ne_zero _
      have hΦsymm : MDifferentiableAt I I (⇑Φ.symm) (Φ (Φ.symm z)) := by
        have hap : Φ (Φ.symm z) = z := Φ.apply_symm_apply z
        rw [hap]; exact Φ.symm.mdifferentiable infty_ne_zero z
      have hcomp : (⇑Φ.symm) ∘ (⇑Φ) = (id : M → M) := by
        funext w; exact Φ.symm_apply_apply w
      have hchain := mfderiv_comp (Φ.symm z) hΦsymm hΦ
      rw [hcomp, mfderiv_id] at hchain
      -- hchain : id = (mfderiv Φ.symm (Φ (Φ.symm z))).comp (mfderiv Φ (Φ.symm z))
      have hap : Φ (Φ.symm z) = z := Φ.apply_symm_apply z
      rw [hap] at hchain
      exact hchain.symm
    · -- `(mfderiv Φ (Φ.symm z)).comp (mfderiv Φ.symm z) = id` on `T_z M`.
      have hΦsymm : MDifferentiableAt I I (⇑Φ.symm) z :=
        Φ.symm.mdifferentiable infty_ne_zero z
      have hΦ : MDifferentiableAt I I (⇑Φ) (Φ.symm z) :=
        Φ.mdifferentiable infty_ne_zero _
      have hcomp : (⇑Φ) ∘ (⇑Φ.symm) = (id : M → M) := by
        funext w; exact Φ.apply_symm_apply w
      have hchain := mfderiv_comp z hΦ hΦsymm
      rw [hcomp, mfderiv_id] at hchain
      exact hchain.symm
  -- Now both sides reduce to the same thing.
  change (Φ.apply_symm_apply z) ▸
      (mfderiv I I (⇑Φ) (Φ.symm z)) (Y (Φ.symm z))
    = (mfderiv I I (⇑Φ.symm) z).inverse (Y (Φ.symm z))
  rw [hinv]
  refine eq_of_heq ?_
  exact eqRec_heq (φ := fun w => TangentSpace I w) (Φ.apply_symm_apply z)
    ((mfderiv I I (⇑Φ) (Φ.symm z)) (Y (Φ.symm z)))

private lemma pushforward_mdiffAt
    (Φ : M ≃ₘ⟮I, I⟯ M) {Y : ∀ x : M, TangentSpace I x} {x : M}
    (hY : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (Y y) : TangentBundle I M)) x) :
    MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (Diffeomorph.pushforward Φ Y y) : TangentBundle I M))
      (Φ x) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  -- Use the equality `pushforward = mpullback ∘ symm` at the function level.
  have hfun_eq := pushforward_eq_mpullback_symm_fun (I := I) Φ Y
  have hY' : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (Y y) : TangentBundle I M))
      (Φ.symm (Φ x)) := by
    rw [Φ.symm_apply_apply]; exact hY
  have hΦsymm_smooth : ContMDiffAt I I (∞ : WithTop ℕ∞) (⇑Φ.symm) (Φ x) :=
    Φ.symm.contMDiffAt
  have hinv : (mfderiv I I (⇑Φ.symm) (Φ x)).IsInvertible := by
    refine ⟨(Diffeomorph.mfderivToContinuousLinearEquiv Φ.symm infty_ne_zero (Φ x)), ?_⟩
    exact Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Φ.symm) (x := Φ x) infty_ne_zero
  have hmn : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    have h1 : (2 : ℕ∞) ≤ ⊤ := le_top
    have h2 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr h1
    convert h2 using 1
  -- Apply `MDifferentiableAt.mpullback_vectorField`.
  have hmpb := MDifferentiableAt.mpullback_vectorField (I := I) (I' := I)
    (V := Y) (f := (⇑Φ.symm)) (x₀ := Φ x) (n := (∞ : WithTop ℕ∞))
    hY' hΦsymm_smooth hinv hmn
  -- Transfer through the function equality (pushforward = mpullback ∘ symm).
  have hfun_total :
      (fun z : M => (TotalSpace.mk' E z (Diffeomorph.pushforward Φ Y z) : TangentBundle I M))
        = (fun z : M => (TotalSpace.mk' E z (VectorField.mpullback I I (⇑Φ.symm) Y z) :
            TangentBundle I M)) := by
    funext z; congr 1
    exact congrFun hfun_eq z
  rw [hfun_total]
  exact hmpb

/-! ## Torsion-free identity for `conjCovFun`

For smooth `X, Y` whose pushforwards along `Φ` are smooth at `Φ x`, the torsion of
`conjCovFun g Φ` at `x` evaluates to the Lie bracket of `X` and `Y` at `x`. The proof
peels off the outer `mfderiv Φ.symm (Φ x)`, applies the torsion-free identity of
`LeviCivita g` at `(Φ_* X, Φ_* Y, Φ x)`, identifies the bracket via
`mlie_bracket_pullback_naturality`, then collapses the doubly-applied
`mfderiv Φ.symm ∘ mfderiv Φ`. -/

private lemma conjCovFun_torsion_free
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    {X Y : ∀ x : M, TangentSpace I x} {x : M}
    (hX : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (X y) : TangentBundle I M)) x)
    (hY : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (Y y) : TangentBundle I M)) x) :
    conjCovFun g Φ Y x (X x) - conjCovFun g Φ X x (Y x)
      = VectorField.mlieBracket I X Y x := by
  -- Step 1: Smoothness of pushforwards `Φ_*X` and `Φ_*Y` at `Φ x`.
  have hPushX := pushforward_mdiffAt (I := I) Φ hX
  have hPushY := pushforward_mdiffAt (I := I) Φ hY
  -- Step 2: Apply torsion-free of `LeviCivita g` at `(Φ_*X, Φ_*Y, Φ x)`.
  have htor_g : (LeviCivita (I := I) g).torsion = 0 :=
    LeviCivita_torsion_eq_zero (I := I) g
  have hTF_g := (CovariantDerivative.torsion_eq_zero_iff (LeviCivita (I := I) g)).mp
    htor_g hPushX hPushY
  -- `hTF_g` :
  --   `(LeviCivita g).toFun (Φ_*Y) (Φ x) ((Φ_*X) (Φ x)) -
  --    (LeviCivita g).toFun (Φ_*X) (Φ x) ((Φ_*Y) (Φ x)) =
  --      mlieBracket I (Φ_*X) (Φ_*Y) (Φ x)`.
  -- Step 3: `(Φ_*X) (Φ x) = mfderiv Φ x (X x)`, ditto for Y.
  have hpfX : Diffeomorph.pushforward Φ X (Φ x) = mfderiv I I (⇑Φ) x (X x) :=
    pushforward_at_image (I := I) Φ X x
  have hpfY : Diffeomorph.pushforward Φ Y (Φ x) = mfderiv I I (⇑Φ) x (Y x) :=
    pushforward_at_image (I := I) Φ Y x
  -- Step 4: Naturality of Lie bracket under pushforward at the image point `Φ x`.
  have hbracket := mlie_bracket_pullback_naturality (I := I) Φ X Y (Φ x)
    (by rw [Φ.symm_apply_apply]; exact hX)
    (by rw [Φ.symm_apply_apply]; exact hY)
  -- `hbracket : mlieBracket I (Φ_*X) (Φ_*Y) (Φ x) = pushforward Φ (mlieBracket I X Y) (Φ x)`.
  have hbracket_pf : Diffeomorph.pushforward Φ (VectorField.mlieBracket I X Y) (Φ x)
      = mfderiv I I (⇑Φ) x ((VectorField.mlieBracket I X Y) x) :=
    pushforward_at_image (I := I) Φ (VectorField.mlieBracket I X Y) x
  rw [hbracket_pf] at hbracket
  -- Step 5: assemble.
  -- LHS = mfderiv Φ.symm (Φ x) (
  --   (LeviCivita g).toFun (Φ_*Y) (Φ x) (mfderiv Φ x (X x)) -
  --   (LeviCivita g).toFun (Φ_*X) (Φ x) (mfderiv Φ x (Y x)))
  -- using linearity of mfderiv Φ.symm (Φ x).
  simp only [conjCovFun_apply]
  -- Substitute pushforward identities for `(Φ_*X) (Φ x)` and `(Φ_*Y) (Φ x)`.
  rw [show (LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ Y) (Φ x)
        (mfderiv I I (⇑Φ) x (X x)) =
      (LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ Y) (Φ x)
        (Diffeomorph.pushforward Φ X (Φ x)) from by rw [hpfX]]
  rw [show (LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ X) (Φ x)
        (mfderiv I I (⇑Φ) x (Y x)) =
      (LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ X) (Φ x)
        (Diffeomorph.pushforward Φ Y (Φ x)) from by rw [hpfY]]
  -- LHS now has shape: `mfderiv Φ.symm (Φ x) A - mfderiv Φ.symm (Φ x) B`
  -- where `A - B = mlieBracket I (Φ_*X) (Φ_*Y) (Φ x)` by `hTF_g`.
  set A := (LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ Y) (Φ x)
    (Diffeomorph.pushforward Φ X (Φ x)) with hA_def
  set B := (LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ X) (Φ x)
    (Diffeomorph.pushforward Φ Y (Φ x)) with hB_def
  have hAB : A - B = VectorField.mlieBracket I (Diffeomorph.pushforward Φ X)
      (Diffeomorph.pushforward Φ Y) (Φ x) := hTF_g
  -- Apply linearity of `mfderiv Φ.symm (Φ x)`.
  calc mfderiv I I (⇑Φ.symm) (Φ x) A - mfderiv I I (⇑Φ.symm) (Φ x) B
      = mfderiv I I (⇑Φ.symm) (Φ x) (A - B) := by
        rw [← ContinuousLinearMap.map_sub]
    _ = mfderiv I I (⇑Φ.symm) (Φ x)
          (VectorField.mlieBracket I (Diffeomorph.pushforward Φ X)
            (Diffeomorph.pushforward Φ Y) (Φ x)) := by rw [hAB]
    _ = mfderiv I I (⇑Φ.symm) (Φ x)
          (mfderiv I I (⇑Φ) x ((VectorField.mlieBracket I X Y) x)) := by rw [hbracket]
    _ = (VectorField.mlieBracket I X Y) x :=
        mfderiv_symm_apply_mfderiv (I := I) Φ x ((VectorField.mlieBracket I X Y) x)

/-! ## Metric compatibility for `conjCovFun`

We show that `conjCovFun g Φ` is metric-compatible with `pullbackMetric g Φ` on
smooth sections at a point. The proof unfolds the pullback inner product, applies
the chain rule for `mfderiv` to the composite scalar function `(g(Φ_*Y, Φ_*Z)) ∘ Φ`,
invokes the metric compatibility of `LeviCivita g`, and reassembles using
`mfderiv_apply_mfderiv_symm` (which collapses the outer `dΦ` against the inner
`dΦ⁻¹` introduced by `conjCovFun`). -/

/-- Pointwise version of `pullbackInner_eval`. -/
private lemma pullbackMetric_inner_eval
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (Y Z : ∀ x : M, TangentSpace I x) (b : M) :
    (Diffeomorph.pullbackMetric g Φ).inner b (Y b) (Z b)
      = g.inner (Φ b) (mfderiv I I (⇑Φ) b (Y b)) (mfderiv I I (⇑Φ) b (Z b)) := by
  change Diffeomorph.pullbackInner g Φ b (Y b) (Z b) = _
  unfold Diffeomorph.pullbackInner
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]

private lemma conjCovFun_metric_compatible
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    {Y Z : ∀ x : M, TangentSpace I x} {x : M}
    (hY : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (Y y) : TangentBundle I M)) x)
    (hZ : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (Z y) : TangentBundle I M)) x)
    (v : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ) (fun b =>
        (Diffeomorph.pullbackMetric g Φ).inner b (Y b) (Z b)) x) v
      = (Diffeomorph.pullbackMetric g Φ).inner x (conjCovFun g Φ Y x v) (Z x)
        + (Diffeomorph.pullbackMetric g Φ).inner x (Y x) (conjCovFun g Φ Z x v) := by
  -- Step 1: Smoothness of pushforwards `Φ_*Y` and `Φ_*Z` at `Φ x`.
  have hPushY := pushforward_mdiffAt (I := I) Φ hY
  have hPushZ := pushforward_mdiffAt (I := I) Φ hZ
  -- Step 2: The scalar function `b ↦ (Φ*g).inner b (Y b) (Z b)` equals
  -- `b ↦ g.inner (Φ b) ((Φ_*Y) (Φ b)) ((Φ_*Z) (Φ b)) ∘ Φ` on `M`.
  have hfun_eq : (fun b : M => (Diffeomorph.pullbackMetric g Φ).inner b (Y b) (Z b))
      = (fun b' : M => g.inner b' (Diffeomorph.pushforward Φ Y b')
          (Diffeomorph.pushforward Φ Z b')) ∘ (⇑Φ) := by
    funext b
    -- LHS = `g.inner (Φ b) (mfderiv Φ b (Y b)) (mfderiv Φ b (Z b))` by `pullbackInner_eval`.
    -- RHS = `g.inner (Φ b) ((Φ_*Y) (Φ b)) ((Φ_*Z) (Φ b))`.
    -- Use `pushforward_at_image`: `(Φ_*Y)(Φ b) = mfderiv Φ b (Y b)`.
    change (Diffeomorph.pullbackMetric g Φ).inner b (Y b) (Z b)
      = g.inner (Φ b) (Diffeomorph.pushforward Φ Y (Φ b))
          (Diffeomorph.pushforward Φ Z (Φ b))
    rw [pullbackMetric_inner_eval, pushforward_at_image, pushforward_at_image]
  -- Step 3: Compute `mfderiv` of the composite via chain rule.
  -- Differentiability of the inner pairing `b' ↦ g.inner b' ((Φ_*Y) b') ((Φ_*Z) b')` at `Φ x`.
  have hg_smooth : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b' => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) b' (g.inner b')) :=
    g.contMDiff
  have hinner_smooth_at_Φx : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun b' : M => g.inner b' (Diffeomorph.pushforward Φ Y b')
          (Diffeomorph.pushforward Φ Z b')) (Φ x) := by
    -- The bilinear-form section applied to two tangent sections is differentiable,
    -- using `ContMDiff.clm_bundle_apply₂`-style reasoning at the point.
    -- We re-derive at the differentiability level.
    have hClmAt : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
        (fun b' => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) b' (g.inner b'))
        (Φ x) :=
      hg_smooth.contMDiffAt.mdifferentiableAt (by simp)
    have h_total :=
      MDifferentiableAt.clm_bundle_apply₂ (b := fun b' : M => b')
        (E₁ := fun b' : M => TangentSpace I b')
        (E₂ := fun b' : M => TangentSpace I b')
        (E₃ := fun _ : M => ℝ)
        (ψ := fun b' : M => g.inner b')
        (v := fun b' : M => Diffeomorph.pushforward Φ Y b')
        (w := fun b' : M => Diffeomorph.pushforward Φ Z b')
        (x := Φ x) hClmAt hPushY hPushZ
    -- `h_total` provides differentiability into the trivial bundle. Extract the scalar.
    -- Convert to `MDifferentiableAt I 𝓘(ℝ, ℝ) ...` via `mdifferentiableAt_section_iff`.
    have h_at_scalar : MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun b' : M =>
          g.inner b' (Diffeomorph.pushforward Φ Y b') (Diffeomorph.pushforward Φ Z b'))
        (Φ x) := by
      -- The trivial-bundle differentiability becomes scalar differentiability via the
      -- standard `contMDiffAt_section` / `mdifferentiableAt_section` route for
      -- `Bundle.Trivial M ℝ`.
      -- Translate via `mdifferentiableAt_totalSpace`.
      rw [mdifferentiableAt_totalSpace] at h_total
      exact h_total.2
    exact h_at_scalar
  have hΦ_smooth_at_x : MDifferentiableAt I I (⇑Φ) x :=
    Φ.mdifferentiable infty_ne_zero x
  have h_chain := mfderiv_comp (I := I) (I' := I) (I'' := 𝓘(ℝ)) x
    hinner_smooth_at_Φx hΦ_smooth_at_x
  -- Apply chain rule: `mfderiv (h ∘ Φ) x = (mfderiv h (Φ x)).comp (mfderiv Φ x)`.
  rw [show (fun b : M => (Diffeomorph.pullbackMetric g Φ).inner b (Y b) (Z b))
        = (fun b' : M => g.inner b' (Diffeomorph.pushforward Φ Y b')
            (Diffeomorph.pushforward Φ Z b')) ∘ (⇑Φ) from hfun_eq]
  rw [h_chain]
  -- Step 4: Metric compatibility of `LeviCivita g` evaluated at `(Φ_*Y, Φ_*Z, Φ x)`.
  have hMC_g : IsMetricCompatible (LeviCivita (I := I) g) g :=
    LeviCivita_isMetricCompatible (I := I) g
  have hMC_at := hMC_g.apply hPushY hPushZ (mfderiv I I (⇑Φ) x v)
  -- `hMC_at` :
  --   `(mfderiv I 𝓘(ℝ) (fun b' => g.inner b' (Φ_*Y b') (Φ_*Z b')) (Φ x)) (mfderiv Φ x v)
  --      = g.inner (Φ x) ((LeviCivita g) (Φ_*Y) (Φ x) (mfderiv Φ x v)) ((Φ_*Z)(Φ x))
  --      + g.inner (Φ x) ((Φ_*Y)(Φ x)) ((LeviCivita g) (Φ_*Z) (Φ x) (mfderiv Φ x v))`
  -- Simplify the LHS-after-chain-rule to match `hMC_at`.
  change (mfderiv I 𝓘(ℝ) (fun b' : M => g.inner b'
        (Diffeomorph.pushforward Φ Y b') (Diffeomorph.pushforward Φ Z b')) (Φ x))
      (mfderiv I I (⇑Φ) x v)
    = (Diffeomorph.pullbackMetric g Φ).inner x (conjCovFun g Φ Y x v) (Z x) +
        (Diffeomorph.pullbackMetric g Φ).inner x (Y x) (conjCovFun g Φ Z x v)
  rw [hMC_at]
  -- Step 5: Convert each RHS term `(pullbackMetric g Φ).inner x A B`
  -- to `g.inner (Φ x) (mfderiv Φ x A) (mfderiv Φ x B)` and identify.
  have hrhs1 : (Diffeomorph.pullbackMetric g Φ).inner x (conjCovFun g Φ Y x v) (Z x)
      = g.inner (Φ x) ((LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ Y) (Φ x)
          (mfderiv I I (⇑Φ) x v)) (Diffeomorph.pushforward Φ Z (Φ x)) := by
    change Diffeomorph.pullbackInner g Φ x (conjCovFun g Φ Y x v) (Z x) = _
    unfold Diffeomorph.pullbackInner
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]
    -- Now LHS: `g.inner (Φ x) (mfderiv Φ x (conjCov Y x v)) (mfderiv Φ x (Z x))`
    -- RHS: `g.inner (Φ x) ((LeviCivita g)(Φ_*Y)(Φ x)(mfderiv Φ x v)) ((Φ_*Z)(Φ x))`
    -- Two equalities under `g.inner (Φ x)`: identify the two pairs.
    have h1 : mfderiv I I (⇑Φ) x (conjCovFun g Φ Y x v)
        = (LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ Y) (Φ x)
            (mfderiv I I (⇑Φ) x v) := by
      simp only [conjCovFun_apply]
      exact mfderiv_apply_mfderiv_symm (I := I) Φ x _
    have h2 : mfderiv I I (⇑Φ) x (Z x) = Diffeomorph.pushforward Φ Z (Φ x) :=
      (pushforward_at_image (I := I) Φ Z x).symm
    rw [h1, h2]
  have hrhs2 : (Diffeomorph.pullbackMetric g Φ).inner x (Y x) (conjCovFun g Φ Z x v)
      = g.inner (Φ x) (Diffeomorph.pushforward Φ Y (Φ x))
          ((LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ Z) (Φ x)
            (mfderiv I I (⇑Φ) x v)) := by
    change Diffeomorph.pullbackInner g Φ x (Y x) (conjCovFun g Φ Z x v) = _
    unfold Diffeomorph.pullbackInner
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]
    have h1 : mfderiv I I (⇑Φ) x (Y x) = Diffeomorph.pushforward Φ Y (Φ x) :=
      (pushforward_at_image (I := I) Φ Y x).symm
    have h2 : mfderiv I I (⇑Φ) x (conjCovFun g Φ Z x v)
        = (LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ Z) (Φ x)
            (mfderiv I I (⇑Φ) x v) := by
      simp only [conjCovFun_apply]
      exact mfderiv_apply_mfderiv_symm (I := I) Φ x _
    rw [h1, h2]
  rw [hrhs1, hrhs2]

/-! ## Pointwise identification of `conjCovFun` with the pullback Levi-Civita

We apply `koszul_local_uniqueness` with `cov₁ = conjCovFun g Φ` and
`cov₂ = (LeviCivita (Φ*g)).toFun` to identify the two on smooth sections at a point.
The universally-quantified torsion-free and metric-compatibility hypotheses for
`conjCovFun` follow from `conjCovFun_torsion_free` and `conjCovFun_metric_compatible`,
applied to each differentiable section in the family. -/

private lemma conjCovFun_eq_LeviCivita_pullback
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    {X Y : ∀ x : M, TangentSpace I x} {x : M}
    (hX : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (X y) : TangentBundle I M)) x)
    (hY : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (Y y) : TangentBundle I M)) x) :
    conjCovFun g Φ Y x (X x)
      = (LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)).toFun Y x (X x) := by
  -- Set up universal torsion-free and metric-compat hypotheses for `conjCovFun`.
  set cov₁ := fun (W : ∀ y : M, TangentSpace I y) (y : M) => conjCovFun g Φ W y with hcov₁_def
  set cov₂ := (LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)).toFun with hcov₂_def
  have hTF₁ : ∀ ⦃A B : ∀ y : M, TangentSpace I y⦄ ⦃y : M⦄,
      MDifferentiableAt I I.tangent
        (fun z : M => (TotalSpace.mk' E z (A z) : TangentBundle I M)) y →
      MDifferentiableAt I I.tangent
        (fun z : M => (TotalSpace.mk' E z (B z) : TangentBundle I M)) y →
      y ∈ (Set.univ : Set M) →
      cov₁ B y (A y) - cov₁ A y (B y) = VectorField.mlieBracket I A B y := by
    intro A B y hA hB _
    exact conjCovFun_torsion_free (I := I) g Φ hA hB
  have hTF₂ : ∀ ⦃A B : ∀ y : M, TangentSpace I y⦄ ⦃y : M⦄,
      MDifferentiableAt I I.tangent
        (fun z : M => (TotalSpace.mk' E z (A z) : TangentBundle I M)) y →
      MDifferentiableAt I I.tangent
        (fun z : M => (TotalSpace.mk' E z (B z) : TangentBundle I M)) y →
      y ∈ (Set.univ : Set M) →
      cov₂ B y (A y) - cov₂ A y (B y) = VectorField.mlieBracket I A B y := by
    intro A B y hA hB _
    exact (CovariantDerivative.torsion_eq_zero_iff _).mp
      (LeviCivita_torsion_eq_zero (I := I) (Diffeomorph.pullbackMetric g Φ)) hA hB
  have hMC₁ : IsMetricCompatibleOn cov₁ (Diffeomorph.pullbackMetric g Φ)
      (Set.univ : Set M) := by
    intro A B y hA hB _ v
    exact conjCovFun_metric_compatible (I := I) g Φ hA hB v
  have hMC₂ : IsMetricCompatibleOn cov₂ (Diffeomorph.pullbackMetric g Φ)
      (Set.univ : Set M) := by
    exact (LeviCivita_isMetricCompatible (I := I) (Diffeomorph.pullbackMetric g Φ))
  -- Apply Koszul local uniqueness.
  exact koszul_local_uniqueness (s := Set.univ) hTF₁ hTF₂ hMC₁ hMC₂ hX hY (Set.mem_univ _)

/-! ## Main theorem -/

/-- **Pointwise connection-pullback chain rule for the Levi-Civita derivative.**

For a smooth Riemannian metric `g`, a smooth diffeomorphism `Φ : M ≃ₘ⟮I, I⟯ M`, a
section `X : ∀ y, T_y M` whose total-space lift is manifold-differentiable at `x`,
and a tangent vector `v ∈ T_x M`,
$$
  \mathrm{d}\Phi_x\bigl(\nabla^{\Phi^*g}_v X\bigr)
    = \nabla^g_{\mathrm{d}\Phi_x v}(\Phi_*X)
$$
where on the left we use `(LeviCivita (pullbackMetric g Φ)).toFun X x v` and on the
right `(LeviCivita g).toFun (pushforward Φ X) (Φ x) (mfderiv Φ x v)`. -/
theorem covariant_derivative_pullback_pointwise
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    {X : ∀ y : M, TangentSpace I y} {x : M} (v : TangentSpace I x)
    (hX : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (X y) : TangentBundle I M)) x) :
    mfderiv I I (⇑Φ) x
        ((LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)).toFun X x v)
      = (LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ X) (Φ x)
          (mfderiv I I (⇑Φ) x v) := by
  -- Step 1: Extend `v` to a smooth global tangent section `V` with `V x = v`.
  obtain ⟨V, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x v
  have hV_mdiff : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (V y) : TangentBundle I M)) x :=
    V.mdifferentiableAt
  -- Step 2: Identify the bundled `LeviCivita (Φ*g)` value at `(X, x, v)` with `conjCov`.
  -- Strategy: apply Koszul uniqueness at the smooth section `V` (with `V x = v`) instead of `v`.
  have hKey : (LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)).toFun X x (V x)
      = conjCovFun g Φ X x (V x) :=
    (conjCovFun_eq_LeviCivita_pullback (I := I) g Φ hV_mdiff hX).symm
  rw [show v = V x from hVx.symm] at *
  -- Step 3: Apply `mfderiv Φ x` to both sides.
  rw [hKey]
  -- Goal: `mfderiv Φ x (conjCov X x (V x)) =
  --         (LeviCivita g).toFun (Φ_*X) (Φ x) (mfderiv Φ x (V x))`
  -- Unfold `conjCov` and use `mfderiv_apply_mfderiv_symm`.
  simp only [conjCovFun_apply]
  exact mfderiv_apply_mfderiv_symm (I := I) Φ x _

end DifferentialGeometry.PDE.RicciFlow.Pullback
