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
    with Pi instances; for smooth-flow layers, A can be a restricted sub-algebra
    (e.g., smooth-in-time functions, or a jet algebra) where the Derivation axioms
    hold on the distinguished class of smooth families.
    `lift` injects `Time → R` into `A`; `eval` projects back.
    The filter-dependent round-trip and closure properties are carried by the
    separate `TimeRegularFam` typeclass so that different family filters (C^∞,
    C^k, piecewise-smooth, open-set-smooth, …) can be plugged in without
    duplicating this structure.
    Additivity, Leibniz, dt(constant)=0 are FREE from Mathlib's `Derivation`. -/
structure TimeDerivativeData (R : Type*) (A : Type*) (Time : Type*)
    [CommRing R] [CommRing A] [Algebra R A] where
  /-- The time derivation on the abstract algebra A. -/
  dt : Derivation R A A
  /-- Lift a time-dependent R-valued function into A. -/
  lift : (Time → R) → A
  /-- Evaluate an A-element at a time point. -/
  eval : A → Time → R
  /-- lift preserves R-constants (= time-independent functions). -/
  lift_algebraMap : ∀ (c : R), lift (fun _ => c) = algebraMap R A c
  /-- eval preserves addition. -/
  eval_add : ∀ (a b : A) (t : Time), eval (a + b) t = eval a t + eval b t
  /-- eval preserves multiplication. -/
  eval_mul : ∀ (a b : A) (t : Time), eval (a * b) t = eval a t * eval b t
  /-- eval preserves R-constants. -/
  eval_algebraMap : ∀ (c : R) (t : Time), eval (algebraMap R A c) t = c

/-- Filter of distinguished "regular-in-time" families plus its conditional
    `lift`/`eval` axioms and closure properties.

    Decoupling this from `TimeDerivativeData` lets us plug different filters
    (full C^∞, finite C^k, piecewise-smooth, open-set-smooth, …) into the
    same time-derivative data without duplicating the structure. Concrete
    realizations register a `TimeRegularFam` instance. -/
class TimeRegularFam {R : Type*} {A : Type*} {Time : Type*}
    [CommRing R] [CommRing A] [Algebra R A]
    (td : TimeDerivativeData R A Time) where
  /-- A predicate identifying "regular-in-time" families. -/
  isSmoothFam : (Time → R) → Prop
  /-- `eval ∘ lift = id` on regular families. -/
  eval_lift : ∀ (f : Time → R), isSmoothFam f → ∀ (t : Time),
    td.eval (td.lift f) t = f t
  /-- lift preserves addition on regular families. -/
  lift_add : ∀ (f g : Time → R), isSmoothFam f → isSmoothFam g →
    td.lift (f + g) = td.lift f + td.lift g
  /-- lift preserves multiplication on regular families. -/
  lift_mul : ∀ (f g : Time → R), isSmoothFam f → isSmoothFam g →
    td.lift (f * g) = td.lift f * td.lift g
  /-- Constants are regular families. -/
  isSmoothFam_const : ∀ (c : R), isSmoothFam (fun _ => c)
  /-- Regular families are closed under addition. -/
  isSmoothFam_add : ∀ (f g : Time → R), isSmoothFam f → isSmoothFam g →
    isSmoothFam (f + g)
  /-- Regular families are closed under multiplication. -/
  isSmoothFam_mul : ∀ (f g : Time → R), isSmoothFam f → isSmoothFam g →
    isSmoothFam (f * g)
  /-- Regular families are closed under negation. -/
  isSmoothFam_neg : ∀ (f : Time → R), isSmoothFam f → isSmoothFam (-f)

-- ============================================================
-- Back-compat wrappers: expose `TimeRegularFam` fields as if
-- they still lived on `TimeDerivativeData` itself.
-- ============================================================

namespace TimeDerivativeData

variable {R A Time : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Filter of distinguished regular-in-time families, read through
    `[TimeRegularFam td]`. This wrapper exists so that existing call-sites
    of the form `td.isSmoothFam f` continue to type-check unchanged. -/
abbrev isSmoothFam (td : TimeDerivativeData R A Time) [TimeRegularFam td] :
    (Time → R) → Prop :=
  TimeRegularFam.isSmoothFam (td := td)

/-- `eval ∘ lift = id` on regular families. -/
theorem eval_lift (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f : Time → R) (hf : td.isSmoothFam f) (t : Time) :
    td.eval (td.lift f) t = f t :=
  TimeRegularFam.eval_lift f hf t

/-- lift preserves addition on regular families. -/
theorem lift_add (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f g : Time → R) (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.lift (f + g) = td.lift f + td.lift g :=
  TimeRegularFam.lift_add f g hf hg

/-- lift preserves multiplication on regular families. -/
theorem lift_mul (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f g : Time → R) (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.lift (f * g) = td.lift f * td.lift g :=
  TimeRegularFam.lift_mul f g hf hg

/-- Constants are regular families. -/
theorem isSmoothFam_const (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (c : R) : td.isSmoothFam (fun _ => c) :=
  TimeRegularFam.isSmoothFam_const (td := td) c

/-- Regular families are closed under addition. -/
theorem isSmoothFam_add (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f g : Time → R) (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.isSmoothFam (f + g) :=
  TimeRegularFam.isSmoothFam_add f g hf hg

/-- Regular families are closed under multiplication. -/
theorem isSmoothFam_mul (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f g : Time → R) (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.isSmoothFam (f * g) :=
  TimeRegularFam.isSmoothFam_mul f g hf hg

/-- Regular families are closed under negation. -/
theorem isSmoothFam_neg (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f : Time → R) (hf : td.isSmoothFam f) :
    td.isSmoothFam (-f) :=
  TimeRegularFam.isSmoothFam_neg f hf

end TimeDerivativeData

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

-- Declare the derived isSmoothFam closure lemmas FIRST (inside the DtApply section)
-- so they are available to `dt_apply_*` proofs below.

theorem TimeDerivativeData.isSmoothFam_sub (td : TimeDerivativeData R A Time)
    [TimeRegularFam td]
    (f g : Time → R) (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.isSmoothFam (f - g) := by
  have heq : f - g = f + (-g) := by ext s; simp [sub_eq_add_neg]
  rw [heq]; exact td.isSmoothFam_add _ _ hf (td.isSmoothFam_neg _ hg)

theorem TimeDerivativeData.isSmoothFam_sum (td : TimeDerivativeData R A Time)
    [TimeRegularFam td]
    {ι : Type*} (s : Finset ι) (f : ι → Time → R)
    (h : ∀ i ∈ s, td.isSmoothFam (f i)) :
    td.isSmoothFam (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    change td.isSmoothFam (fun _ => (0 : R))
    exact td.isSmoothFam_const 0
  | cons a s' _ha ih =>
    rw [Finset.sum_cons]
    have h_head : td.isSmoothFam (f a) := h a (Finset.mem_cons_self _ _)
    have h_tail : ∀ i ∈ s', td.isSmoothFam (f i) :=
      fun i hi => h i (Finset.mem_cons.mpr (Or.inr hi))
    exact td.isSmoothFam_add _ _ h_head (ih h_tail)

theorem TimeDerivativeData.isSmoothFam_const_mul (td : TimeDerivativeData R A Time)
    [TimeRegularFam td]
    (c : R) (f : Time → R) (hf : td.isSmoothFam f) :
    td.isSmoothFam (fun s => c * f s) := by
  have heq : (fun s => c * f s) = (fun _ => c) * f := by ext s; rfl
  rw [heq]; exact td.isSmoothFam_mul _ _ (td.isSmoothFam_const c) hf

theorem TimeDerivativeData.dt_apply_add (td : TimeDerivativeData R A Time)
    [TimeRegularFam td]
    (f g : Time → R) (t : Time)
    (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.dt_apply (f + g) t = td.dt_apply f t + td.dt_apply g t := by
  simp only [TimeDerivativeData.dt_apply, td.lift_add f g hf hg, map_add, td.eval_add]

theorem TimeDerivativeData.dt_apply_const (td : TimeDerivativeData R A Time)
    (c : R) (t : Time) :
    td.dt_apply (fun _ => c) t = 0 := by
  simp only [TimeDerivativeData.dt_apply, td.lift_algebraMap,
    Derivation.map_algebraMap, td.eval_zero]

theorem TimeDerivativeData.dt_apply_mul (td : TimeDerivativeData R A Time)
    [TimeRegularFam td]
    (f g : Time → R) (t : Time)
    (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.dt_apply (f * g) t = f t * td.dt_apply g t + g t * td.dt_apply f t := by
  simp only [TimeDerivativeData.dt_apply, td.lift_mul f g hf hg]
  rw [td.dt.leibniz (td.lift f) (td.lift g)]
  simp only [td.eval_add, td.eval_mul, smul_eq_mul, td.eval_lift f hf, td.eval_lift g hg]

theorem TimeDerivativeData.dt_apply_const_mul (td : TimeDerivativeData R A Time)
    [TimeRegularFam td]
    (c : R) (f : Time → R) (t : Time) (hf : td.isSmoothFam f) :
    td.dt_apply (fun s => c * f s) t = c * td.dt_apply f t := by
  have hcf : (fun s => c * f s) = (fun _ => c) * f := by ext s; rfl
  rw [hcf, td.dt_apply_mul _ _ _ (td.isSmoothFam_const c) hf,
      td.dt_apply_const, mul_zero, add_zero]

theorem TimeDerivativeData.dt_apply_neg (td : TimeDerivativeData R A Time)
    [TimeRegularFam td]
    (f : Time → R) (t : Time) (hf : td.isSmoothFam f) :
    td.dt_apply (-f) t = -td.dt_apply f t := by
  have h := td.dt_apply_add f (-f) t hf (td.isSmoothFam_neg f hf)
  simp only [add_neg_cancel] at h
  have h0 : td.dt_apply 0 t = 0 := by
    change td.dt_apply (fun _ => (0 : R)) t = 0
    exact td.dt_apply_const 0 t
  rw [h0] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem TimeDerivativeData.dt_apply_sub (td : TimeDerivativeData R A Time)
    [TimeRegularFam td]
    (f g : Time → R) (t : Time)
    (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.dt_apply (f - g) t = td.dt_apply f t - td.dt_apply g t := by
  have heq : f - g = f + (-g) := by ext s; simp [sub_eq_add_neg]
  rw [heq, td.dt_apply_add _ _ _ hf (td.isSmoothFam_neg g hg),
      td.dt_apply_neg _ _ hg]; ring

theorem TimeDerivativeData.dt_apply_sum (td : TimeDerivativeData R A Time)
    [TimeRegularFam td]
    {ι : Type*} (s : Finset ι) (f : ι → Time → R) (t : Time)
    (hfs : ∀ i ∈ s, td.isSmoothFam (f i)) :
    td.dt_apply (∑ i ∈ s, f i) t = ∑ i ∈ s, td.dt_apply (f i) t := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    change td.dt_apply (fun _ => (0 : R)) t = 0
    exact td.dt_apply_const 0 t
  | cons a s' _ha ih =>
    have h_head : td.isSmoothFam (f a) := hfs a (Finset.mem_cons_self _ _)
    have h_tail : ∀ i ∈ s', td.isSmoothFam (f i) :=
      fun i hi => hfs i (Finset.mem_cons.mpr (Or.inr hi))
    have h_tail_sum : td.isSmoothFam (∑ i ∈ s', f i) :=
      td.isSmoothFam_sum s' f h_tail
    rw [Finset.sum_cons, td.dt_apply_add _ _ _ h_head h_tail_sum, ih h_tail,
        Finset.sum_cons]

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

/-- Spatial and temporal derivatives commute on smooth families.
    For any vector field `X` and smooth time-dependent function `f : Time → R`,
    `dt_apply (s ↦ X(f s)) t = X(dt_apply f t)`. The `isSmoothFam f` hypothesis
    is required because in concrete realizations `lift` only honors addition/
    multiplication on the distinguished smooth class, and the relevant Schwarz-type
    identities are only guaranteed there. -/
def SpatialTemporalComm {k R V : Type*} {A Time : Type*}
    [Field k] [CommRing R] [Algebra k R]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    [CommRing A] [Algebra R A]
    (emb : DerivationEmbedding k R V) (td : TimeDerivativeData R A Time)
    [TimeRegularFam td] : Prop :=
  ∀ (X : V) (f : Time → R) (t : Time), td.isSmoothFam f →
    td.dt_apply (fun s => (emb.embed X) (f s)) t = (emb.embed X) (td.dt_apply f t)

-- ============================================================
-- Two-time regular families and the diagonal chain rule
-- ============================================================

/-- Two-time smoothness extension of `TimeRegularFam`.
    Carries an abstract predicate `isSmoothFam2` on families of type
    `Time × Time → R`, with closure under algebra operations, single-time
    embeddings, and projections to single-time smoothness. The distinguished
    axiom `dt_apply_diag_leibniz` captures the Leibniz rule for the diagonal
    of a two-time smooth family: it is the synthetic-level statement of the
    classical identity
    `deriv (τ ↦ G(τ, τ)) t = deriv (τ ↦ G(τ, t)) t + deriv (τ ↦ G(t, τ)) t`
    expressed via `dt_apply`. Decoupling this from `TimeRegularFam` lets
    concrete realizations register a separate two-time smooth class (C^∞,
    C^k, piecewise-smooth, …) without affecting the one-time data. -/
class TimeRegularFam2 {R : Type*} {A : Type*} {Time : Type*}
    [CommRing R] [CommRing A] [Algebra R A]
    (td : TimeDerivativeData R A Time) [TimeRegularFam td] where
  /-- Two-time smooth-family predicate. -/
  isSmoothFam2 : (Time × Time → R) → Prop
  /-- Closure: constants are 2-smooth. -/
  isSmoothFam2_const : ∀ c, isSmoothFam2 (fun _ => c)
  /-- Closure: pointwise addition. -/
  isSmoothFam2_add : ∀ f g, isSmoothFam2 f → isSmoothFam2 g → isSmoothFam2 (f + g)
  /-- Closure: pointwise multiplication. -/
  isSmoothFam2_mul : ∀ f g, isSmoothFam2 f → isSmoothFam2 g → isSmoothFam2 (f * g)
  /-- Closure: pointwise negation. -/
  isSmoothFam2_neg : ∀ f, isSmoothFam2 f → isSmoothFam2 (-f)
  /-- Embed a 1-smooth family depending only on the first coordinate. -/
  isSmoothFam2_of_single_fst : ∀ f, td.isSmoothFam f → isSmoothFam2 (fun p => f p.1)
  /-- Embed a 1-smooth family depending only on the second coordinate. -/
  isSmoothFam2_of_single_snd : ∀ f, td.isSmoothFam f → isSmoothFam2 (fun p => f p.2)
  /-- The diagonal `τ ↦ G(τ, τ)` is 1-smooth. -/
  diag_isSmoothFam : ∀ G, isSmoothFam2 G → td.isSmoothFam (fun τ => G (τ, τ))
  /-- The left-frozen slice `τ ↦ G(τ, τ₀)` is 1-smooth. -/
  slice_left_isSmoothFam : ∀ G τ₀, isSmoothFam2 G → td.isSmoothFam (fun τ => G (τ, τ₀))
  /-- The right-frozen slice `τ ↦ G(τ₀, τ)` is 1-smooth. -/
  slice_right_isSmoothFam : ∀ G τ₀, isSmoothFam2 G → td.isSmoothFam (fun τ => G (τ₀, τ))
  /-- **Diagonal chain rule.** Given a 2-smooth family `G`,
      `dt_apply (τ ↦ G(τ,τ)) t = dt_apply (τ ↦ G(τ,t)) t + dt_apply (τ ↦ G(t,τ)) t`. -/
  dt_apply_diag_leibniz : ∀ G (t : Time), isSmoothFam2 G →
      td.dt_apply (fun τ => G (τ, τ)) t =
      td.dt_apply (fun τ => G (τ, t)) t + td.dt_apply (fun τ => G (t, τ)) t

/-- Subtraction closure for 2-time smooth families, derived from `isSmoothFam2_add`
    and `isSmoothFam2_neg`. Uses the pointwise identity `f - g = f + (-g)`. -/
theorem TimeRegularFam2.isSmoothFam2_sub
    {R : Type*} {A : Type*} {Time : Type*}
    [CommRing R] [CommRing A] [Algebra R A]
    {td : TimeDerivativeData R A Time} [TimeRegularFam td] [TimeRegularFam2 td]
    (f g : Time × Time → R)
    (hf : TimeRegularFam2.isSmoothFam2 (td := td) f)
    (hg : TimeRegularFam2.isSmoothFam2 (td := td) g) :
    TimeRegularFam2.isSmoothFam2 (td := td) (f - g) := by
  have h_eq : f - g = f + (-g) := by
    funext p; simp [sub_eq_add_neg]
  rw [h_eq]
  exact TimeRegularFam2.isSmoothFam2_add _ _ hf (TimeRegularFam2.isSmoothFam2_neg _ hg)
