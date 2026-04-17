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

/-- Time derivative operator as an R-derivation on a time function algebra A.
    The algebra A generalizes `Time → R`: for the pure abstract layer, A = Time → R
    with Pi instances; for the SmoothRicciFlow layer, A can be a restricted sub-algebra
    (e.g., smooth-in-time functions, or a jet algebra) where the Derivation axioms
    hold unconditionally.
    `lift` injects `Time → R` into `A`; `eval` projects back (both ring homs).
    `eval ∘ lift = id` (round-trip).
    Additivity, Leibniz, dt(constant)=0 are FREE from Mathlib's `Derivation`. -/
structure TimeDerivativeData (R : Type*) (A : Type*) (Time : Type*)
    [CommRing R] [CommRing A] [Algebra R A] where
  /-- The time derivation on the abstract algebra A. -/
  dt : Derivation R A A
  /-- Lift a time-dependent R-valued function into A (ring homomorphism). -/
  lift : (Time → R) → A
  /-- Evaluate an A-element at a time point (ring homomorphism to Time → R). -/
  eval : A → Time → R
  /-- eval ∘ lift = id (round-trip). -/
  eval_lift : ∀ (f : Time → R) (t : Time), eval (lift f) t = f t
  /-- lift preserves addition. -/
  lift_add : ∀ (f g : Time → R), lift (f + g) = lift f + lift g
  /-- lift preserves multiplication. -/
  lift_mul : ∀ (f g : Time → R), lift (f * g) = lift f * lift g
  /-- lift preserves R-constants (= time-independent functions). -/
  lift_algebraMap : ∀ (c : R), lift (fun _ => c) = algebraMap R A c
  /-- eval preserves addition. -/
  eval_add : ∀ (a b : A) (t : Time), eval (a + b) t = eval a t + eval b t
  /-- eval preserves multiplication. -/
  eval_mul : ∀ (a b : A) (t : Time), eval (a * b) t = eval a t * eval b t
  /-- eval preserves R-constants. -/
  eval_algebraMap : ∀ (c : R) (t : Time), eval (algebraMap R A c) t = c

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

variable {R : Type*} {A : Type*} {Time : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (td : TimeDerivativeData R A Time)

theorem dt_add (f g : A) : td.dt (f + g) = td.dt f + td.dt g :=
  map_add td.dt f g

/-- dt satisfies Leibniz: dt(fg) = f·dt(g) + g·dt(f) -/
theorem dt_mul (f g : A) :
    td.dt (f * g) = f • td.dt g + g • td.dt f :=
  td.dt.leibniz f g

/-- dt kills time-constant functions -/
theorem t_const_R (c : R) : td.dt (algebraMap R A c) = 0 :=
  Derivation.map_algebraMap td.dt c

/-- algebraMap R (Time → R) c t = c is definitionally true (for A = Time → R). -/
theorem time_algebraMap_apply {Time' : Type*} (c : R) (t : Time') :
    algebraMap R (Time' → R) c t = c := rfl

theorem dt_sub (f g : A) : td.dt (f - g) = td.dt f - td.dt g :=
  map_sub td.dt f g

theorem dt_neg (f : A) : td.dt (-f) = -td.dt f :=
  map_neg td.dt f

theorem dt_zero : td.dt 0 = 0 :=
  map_zero td.dt

/-- dt commutes with constant R-scalar multiplication -/
theorem dt_smul_const (c : R) (f : A) :
    td.dt (algebraMap R A c * f) = algebraMap R A c • td.dt f := by
  rw [dt_mul td, t_const_R td c, smul_zero, add_zero]

end TimeDerivativeTheorems

-- ============================================================
-- dt_apply: primary API for applying time derivative to Time → R
-- ============================================================

section DtApply

variable {R : Type*} {A : Type*} {Time : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Apply the time derivative to a `Time → R` function and evaluate at `t`.
    This is the primary API for downstream use:
    `td.dt_apply (fun s => T s vs αs) t` replaces the old `(td.dt (fun s => T s vs αs)) t`. -/
def TimeDerivativeData.dt_apply (td : TimeDerivativeData R A Time)
    (f : Time → R) (t : Time) : R :=
  td.eval (td.dt (td.lift f)) t

theorem TimeDerivativeData.eval_zero (td : TimeDerivativeData R A Time) (t : Time) :
    td.eval 0 t = 0 := by
  have h : (0 : A) = algebraMap R A 0 := by simp
  rw [h, td.eval_algebraMap]

theorem TimeDerivativeData.dt_apply_add (td : TimeDerivativeData R A Time)
    (f g : Time → R) (t : Time) :
    td.dt_apply (f + g) t = td.dt_apply f t + td.dt_apply g t := by
  simp only [TimeDerivativeData.dt_apply, td.lift_add, map_add, td.eval_add]

theorem TimeDerivativeData.dt_apply_const (td : TimeDerivativeData R A Time)
    (c : R) (t : Time) :
    td.dt_apply (fun _ => c) t = 0 := by
  simp only [TimeDerivativeData.dt_apply, td.lift_algebraMap,
    Derivation.map_algebraMap, td.eval_zero]

theorem TimeDerivativeData.dt_apply_mul (td : TimeDerivativeData R A Time)
    (f g : Time → R) (t : Time) :
    td.dt_apply (f * g) t = f t * td.dt_apply g t + g t * td.dt_apply f t := by
  simp only [TimeDerivativeData.dt_apply, td.lift_mul]
  rw [td.dt.leibniz (td.lift f) (td.lift g)]
  simp only [td.eval_add, td.eval_mul, smul_eq_mul, td.eval_lift]

theorem TimeDerivativeData.dt_apply_const_mul (td : TimeDerivativeData R A Time)
    (c : R) (f : Time → R) (t : Time) :
    td.dt_apply (fun s => c * f s) t = c * td.dt_apply f t := by
  have hcf : (fun s => c * f s) = (fun _ => c) * f := by ext s; rfl
  rw [hcf, td.dt_apply_mul, td.dt_apply_const, mul_zero, add_zero]

theorem TimeDerivativeData.dt_apply_neg (td : TimeDerivativeData R A Time)
    (f : Time → R) (t : Time) :
    td.dt_apply (-f) t = -td.dt_apply f t := by
  have h := td.dt_apply_add f (-f) t
  simp only [add_neg_cancel] at h
  have h0 : td.dt_apply 0 t = 0 := by
    change td.dt_apply (fun _ => (0 : R)) t = 0
    exact td.dt_apply_const 0 t
  rw [h0] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem TimeDerivativeData.dt_apply_sub (td : TimeDerivativeData R A Time)
    (f g : Time → R) (t : Time) :
    td.dt_apply (f - g) t = td.dt_apply f t - td.dt_apply g t := by
  have : f - g = f + (-g) := by ext s; simp [sub_eq_add_neg]
  rw [this, td.dt_apply_add, td.dt_apply_neg]; ring

theorem TimeDerivativeData.dt_apply_sum (td : TimeDerivativeData R A Time)
    {ι : Type*} (s : Finset ι) (f : ι → Time → R) (t : Time) :
    td.dt_apply (∑ i ∈ s, f i) t = ∑ i ∈ s, td.dt_apply (f i) t := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    change td.dt_apply (fun _ => (0 : R)) t = 0
    exact td.dt_apply_const 0 t
  | cons a s ha ih =>
    rw [Finset.sum_cons, td.dt_apply_add, ih, Finset.sum_cons]

end DtApply

-- ============================================================
-- Connecting Property: SpatialTemporalComm (no AbstractTrace needed)
-- ============================================================

/-- `DFunLike` instance for Pi types, enabling uniform evaluation via `DFunLike.coe`.
    Used so that `TimeTrComm` can be stated generically
    over an abstract time algebra A with evaluation at time points. -/
instance piDFunLike (R Time : Type*) : DFunLike (Time → R) Time (fun _ => R) where
  coe f := f
  coe_injective' := fun _ _ h => h

/-- Spatial and temporal derivatives commute.
    For any time-dependent function `f : Time → R`,
    `dt_apply (s ↦ X(f s)) t = X(dt_apply f t)`. -/
def SpatialTemporalComm {k R V : Type*} {A Time : Type*}
    [Field k] [CommRing R] [Algebra k R]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    [CommRing A] [Algebra R A]
    (emb : DerivationEmbedding k R V) (td : TimeDerivativeData R A Time) : Prop :=
  ∀ (X : V) (f : Time → R) (t : Time),
    td.dt_apply (fun s => (emb.embed X) (f s)) t = (emb.embed X) (td.dt_apply f t)
