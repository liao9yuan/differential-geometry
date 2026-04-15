import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Vector Field Algebra

Core structures: `DerivationEmbedding`, `AbstractTrace`, `TimeDerivativeData`.
Derived vector field algebra and time derivative properties.
-/

set_option autoImplicit false

-- ============================================================
-- The 3 Core Structures
-- ============================================================

/-- Vector fields embedded into k-derivations of R.
    CRITICAL: Target is `Derivation k R R`, NOT `Derivation R R R`.
    In `Derivation R R R`, `algebraMap R R = id` forces every derivation to zero. -/
structure DerivationEmbedding (k R V : Type*)
    [Field k] [CommRing R] [Algebra k R]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V] where
  embed : V →ₗ[R] Derivation k R R
  embed_injective : Function.Injective embed
  bracket_closed : ∀ X Y : V, ∃ Z : V, embed Z = ⁅embed X, embed Y⁆

/-- Time derivative operator as an R-derivation on time-dependent functions.
    Additivity, Leibniz, dt(constant)=0 are FREE from Mathlib's `Derivation`. -/
structure TimeDerivativeData (R Time : Type*) [CommRing R] where
  dt : Derivation R (Time → R) (Time → R)

-- ============================================================
-- Definitions from DerivationEmbedding
-- ============================================================

section DerivationEmbeddingDefs

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Directional derivative: X(f) := (embed X)(f) -/
def action (emb : DerivationEmbedding k R V) (X : V) (f : R) : R :=
  (emb.embed X) f

/-- Lie bracket: the unique Z such that embed Z = ⁅embed X, embed Y⁆ -/
noncomputable def bracket (emb : DerivationEmbedding k R V) (X Y : V) : V :=
  Classical.choose (emb.bracket_closed X Y)

/-- Specification of bracket: embed (bracket X Y) = ⁅embed X, embed Y⁆ -/
theorem bracket_spec (emb : DerivationEmbedding k R V) (X Y : V) :
    emb.embed (bracket emb X Y) = ⁅emb.embed X, emb.embed Y⁆ :=
  Classical.choose_spec (emb.bracket_closed X Y)

end DerivationEmbeddingDefs

-- ============================================================
-- commutatorEndo: [D_V, L] as R-linear map
-- ============================================================

section CommutatorEndo

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- The commutator [D_V, L] = D_V ∘ L - L ∘ D_V as an R-linear map,
    given D_V satisfies additivity and Leibniz (with respect to D_R : R → R). -/
def commutatorEndo
    (D_R : R → R) (D_V : V → V)
    (h_add : ∀ v w : V, D_V (v + w) = D_V v + D_V w)
    (h_leibniz : ∀ (f : R) (v : V), D_V (f • v) = D_R f • v + f • D_V v)
    (L : V →ₗ[R] V) : V →ₗ[R] V where
  toFun v := D_V (L v) - L (D_V v)
  map_add' v w := by simp only [map_add, h_add]; abel
  map_smul' c v := by
    simp only [RingHom.id_apply, map_smul, h_leibniz, map_add, map_smul]
    simp only [smul_sub]; abel

end CommutatorEndo

-- ============================================================
-- Action theorems from DerivationEmbedding
-- ============================================================

section ActionTheorems

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable (emb : DerivationEmbedding k R V)

theorem action_add_left (X Y : V) (f : R) :
    action emb (X + Y) f = action emb X f + action emb Y f := by
  unfold action; simp [map_add, Derivation.add_apply]

theorem action_smul_left (c : R) (X : V) (f : R) :
    action emb (c • X) f = c * action emb X f := by
  unfold action; simp [map_smul, Derivation.smul_apply, smul_eq_mul]

theorem action_add_right (X : V) (f g : R) :
    action emb X (f + g) = action emb X f + action emb X g := by
  unfold action; exact map_add (emb.embed X) f g

/-- Leibniz rule: X(cf) = X(c)·f + c·X(f) -/
theorem action_smul_right (X : V) (c f : R) :
    action emb X (c * f) = action emb X c * f + c * action emb X f := by
  unfold action
  have h := (emb.embed X).leibniz c f; simp only [smul_eq_mul] at h; rw [h]; ring

/-- Action on k-constants is zero. NOTE: only for c ∈ k, NOT for general c ∈ R! -/
theorem action_algebraMap (X : V) (c : k) :
    action emb X (algebraMap k R c) = 0 :=
  Derivation.map_algebraMap (emb.embed X) c

theorem action_one (X : V) : action emb X (1 : R) = 0 := by
  have := action_algebraMap emb X (1 : k); rwa [map_one] at this

theorem action_zero_left (f : R) : action emb (0 : V) f = 0 := by
  unfold action; simp [map_zero, Derivation.zero_apply]

theorem action_zero_right (X : V) : action emb X (0 : R) = 0 := by
  unfold action; exact map_zero (emb.embed X)

theorem action_neg_right (X : V) (f : R) :
    action emb X (-f) = -action emb X f := by
  unfold action; exact map_neg (emb.embed X) f

theorem action_sub_right (X : V) (f g : R) :
    action emb X (f - g) = action emb X f - action emb X g := by
  unfold action; exact map_sub (emb.embed X) f g

theorem action_neg_left (X : V) (f : R) :
    action emb (-X) f = -action emb X f := by
  unfold action; simp [map_neg, Derivation.neg_apply]

theorem action_sub_left (X Y : V) (f : R) :
    action emb (X - Y) f = action emb X f - action emb Y f := by
  unfold action; simp [map_sub, Derivation.sub_apply]

/-- X(c * f) = c * X(f) when c is a k-constant (correction term vanishes). -/
theorem action_mul_algebraMap (X : V) (c : k) (f : R) :
    action emb X (algebraMap k R c * f) = algebraMap k R c * action emb X f := by
  rw [action_smul_right emb X (algebraMap k R c) f, action_algebraMap emb X c,
      zero_mul, zero_add]

/-- Non-degeneracy: if X and Y have the same action on all functions, they are equal. -/
theorem eq_of_action_eq (X Y : V)
    (h : ∀ f : R, action emb X f = action emb Y f) : X = Y := by
  apply emb.embed_injective; ext f; exact h f

end ActionTheorems

-- ============================================================
-- Bracket theorems
-- ============================================================

section BracketTheorems

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable (emb : DerivationEmbedding k R V)

/-- Action of bracket: [X,Y](f) = X(Y(f)) - Y(X(f)) -/
theorem action_bracket (X Y : V) (f : R) :
    action emb (bracket emb X Y) f =
    action emb X (action emb Y f) - action emb Y (action emb X f) := by
  simp only [action, bracket_spec, Derivation.commutator_apply]

/-- Bracket antisymmetry: [X,Y] = -[Y,X] -/
theorem bracket_antisymm (X Y : V) :
    bracket emb X Y = -bracket emb Y X := by
  apply emb.embed_injective
  rw [map_neg, bracket_spec, bracket_spec]
  exact (lie_skew (emb.embed X) (emb.embed Y)).symm

/-- Bracket additivity (left): [X+Y,Z] = [X,Z] + [Y,Z] -/
theorem bracket_add_left (X Y Z : V) :
    bracket emb (X + Y) Z = bracket emb X Z + bracket emb Y Z := by
  apply emb.embed_injective
  simp only [map_add, bracket_spec]
  exact add_lie (emb.embed X) (emb.embed Y) (emb.embed Z)

/-- Bracket additivity (right): [X,Y+Z] = [X,Y] + [X,Z] -/
theorem bracket_add_right (X Y Z : V) :
    bracket emb X (Y + Z) = bracket emb X Y + bracket emb X Z := by
  apply emb.embed_injective
  simp only [map_add, bracket_spec]
  exact lie_add (emb.embed X) (emb.embed Y) (emb.embed Z)

/-- bracket_smul_left WITH correction term:
    [cX,Y] = c·[X,Y] - Y(c)·X
    The term Y(c) is NOT zero for general c ∈ R. -/
theorem bracket_smul_left (c : R) (X Y : V) :
    bracket emb (c • X) Y = c • bracket emb X Y - action emb Y c • X := by
  apply emb.embed_injective; ext b
  simp only [bracket_spec, Derivation.commutator_apply,
    LinearMap.map_smul, Derivation.coe_smul, Pi.smul_apply, smul_eq_mul,
    map_sub, Derivation.sub_apply]
  unfold action
  have h := (emb.embed Y).leibniz c ((emb.embed X) b)
  simp only [smul_eq_mul] at h; rw [h]; ring

/-- bracket_smul_right: [X,cY] = c·[X,Y] + X(c)·Y -/
theorem bracket_smul_right (c : R) (X Y : V) :
    bracket emb X (c • Y) = c • bracket emb X Y + action emb X c • Y := by
  apply emb.embed_injective; ext b
  simp only [bracket_spec, Derivation.commutator_apply,
    LinearMap.map_smul, Derivation.coe_smul, Pi.smul_apply, smul_eq_mul,
    map_add, Derivation.add_apply]
  unfold action
  have h := (emb.embed X).leibniz c ((emb.embed Y) b)
  simp only [smul_eq_mul] at h; rw [h]; ring

/-- Jacobi identity -/
theorem jacobi_identity (X Y Z : V) :
    bracket emb X (bracket emb Y Z) +
    bracket emb Y (bracket emb Z X) +
    bracket emb Z (bracket emb X Y) = 0 := by
  apply eq_of_action_eq emb; intro f
  simp only [action, map_add, map_sub, map_zero, bracket_spec,
    Derivation.commutator_apply, Derivation.add_apply, Derivation.zero_apply]
  ring

theorem bracket_self (X : V) : bracket emb X X = 0 := by
  apply emb.embed_injective
  rw [bracket_spec, map_zero]
  exact lie_self (emb.embed X)

theorem bracket_zero_left (X : V) : bracket emb 0 X = 0 := by
  apply emb.embed_injective
  rw [bracket_spec, map_zero]
  exact zero_lie (emb.embed X)

theorem bracket_zero_right (X : V) : bracket emb X 0 = 0 := by
  apply emb.embed_injective
  rw [bracket_spec, map_zero]
  exact lie_zero (emb.embed X)

theorem bracket_neg_left (X Y : V) :
    bracket emb (-X) Y = -bracket emb X Y := by
  apply emb.embed_injective
  simp only [map_neg, bracket_spec]
  exact neg_lie (emb.embed X) (emb.embed Y)

theorem bracket_neg_right (X Y : V) :
    bracket emb X (-Y) = -bracket emb X Y := by
  rw [bracket_antisymm emb X (-Y), bracket_neg_left, bracket_antisymm emb Y X]
  simp [neg_neg]

end BracketTheorems

-- ============================================================
-- Time derivative theorems
-- ============================================================

section TimeDerivativeTheorems

variable {R Time : Type*} [CommRing R]
variable (td : TimeDerivativeData R Time)

theorem dt_add (f g : Time → R) : td.dt (f + g) = td.dt f + td.dt g :=
  map_add td.dt f g

/-- dt satisfies Leibniz: dt(fg) = f·dt(g) + g·dt(f) -/
theorem dt_mul (f g : Time → R) :
    td.dt (f * g) = f • td.dt g + g • td.dt f :=
  td.dt.leibniz f g

/-- dt kills time-constant functions -/
theorem t_const_R (c : R) : td.dt (algebraMap R (Time → R) c) = 0 :=
  Derivation.map_algebraMap td.dt c

/-- algebraMap R (Time → R) c t = c is definitionally true -/
theorem time_algebraMap_apply (c : R) (t : Time) :
    algebraMap R (Time → R) c t = c := rfl

theorem dt_sub (f g : Time → R) : td.dt (f - g) = td.dt f - td.dt g :=
  map_sub td.dt f g

theorem dt_neg (f : Time → R) : td.dt (-f) = -td.dt f :=
  map_neg td.dt f

theorem dt_zero : td.dt 0 = 0 :=
  map_zero td.dt

/-- dt commutes with constant R-scalar multiplication -/
theorem dt_smul_const (c : R) (f : Time → R) :
    td.dt (algebraMap R (Time → R) c * f) = algebraMap R (Time → R) c • td.dt f := by
  rw [dt_mul td, t_const_R td c, smul_zero, add_zero]

end TimeDerivativeTheorems

-- ============================================================
-- Connecting Property: SpatialTemporalComm (no AbstractTrace needed)
-- ============================================================

/-- Spatial and temporal derivatives commute:
    dt(X(f(t))) = X(dt(f)(t)) for all X, f, t. -/
def SpatialTemporalComm {k R V Time : Type*}
    [Field k] [CommRing R] [Algebra k R]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    (emb : DerivationEmbedding k R V) (td : TimeDerivativeData R Time) : Prop :=
  ∀ (X : V) (f : Time → R) (t : Time),
    (td.dt (fun s => (emb.embed X) (f s))) t = (emb.embed X) ((td.dt f) t)
