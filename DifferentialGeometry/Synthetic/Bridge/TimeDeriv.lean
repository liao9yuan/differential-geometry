import DifferentialGeometry.Synthetic.Algebra.VectorFieldAlgebra
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# Bridge Layer: Time Derivative via Bare Jet Sequences

Constructs a concrete `TimeDerivativeData R (JetFun R) ℝ` using bare jet sequences
(no smoothness/HasDerivAt constraint between jets).

## Design

`JetFun R` wraps `ℕ → ℝ → R` — a sequence of functions `ℝ → R` indexed by jet level.
- Jet 0 is the value, jet n is the "n-th time derivative" (no constraint enforced).
- Addition: pointwise.
- Multiplication: Leibniz formula `(f * g) n t = Σ C(n,k) f(k)(t) * g(n-k)(t)`.
- `dt`: jet shift `(dt a) n t = a (n+1) t`.
- `lift f`: jet 0 = f, higher jets = 0.
- `eval a t`: `a 0 t`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open BigOperators

-- ============================================================
-- JetFun: bare jet sequence (wrapped to avoid Pi instance conflicts)
-- ============================================================

/-- Bare jet sequence: wraps `ℕ → ℝ → R`. No smoothness constraint.
    Jet n represents the n-th time derivative. -/
structure JetFun (R : Type*) where
  jet : ℕ → ℝ → R

namespace JetFun

variable {R : Type*} [CommRing R]

@[ext] theorem ext {a b : JetFun R} (h : ∀ n t, a.jet n t = b.jet n t) : a = b := by
  cases a; cases b; congr; funext n t; exact h n t

-- ============================================================
-- Ring operations
-- ============================================================

instance : Zero (JetFun R) where zero := ⟨fun _ _ => 0⟩
instance : Add (JetFun R) where add f g := ⟨fun n t => f.jet n t + g.jet n t⟩
instance : Neg (JetFun R) where neg f := ⟨fun n t => -(f.jet n t)⟩
instance : Sub (JetFun R) where sub f g := ⟨fun n t => f.jet n t - g.jet n t⟩

instance : One (JetFun R) where
  one := ⟨fun n _ => if n = 0 then 1 else 0⟩

/-- Leibniz multiplication: `(f * g).jet n t = Σ_{k=0}^{n} C(n,k) f.jet(k)(t) g.jet(n-k)(t)`. -/
instance : Mul (JetFun R) where
  mul f g := ⟨fun n t =>
    ∑ k ∈ Finset.range (n + 1), (n.choose k : R) * f.jet k t * g.jet (n - k) t⟩

instance : NatCast (JetFun R) where
  natCast m := ⟨fun n _ => if n = 0 then (m : R) else 0⟩

instance : IntCast (JetFun R) where
  intCast m := ⟨fun n _ => if n = 0 then (m : R) else 0⟩

-- ============================================================
-- Simp lemmas
-- ============================================================

@[simp] theorem zero_jet (n : ℕ) (t : ℝ) : (0 : JetFun R).jet n t = 0 := rfl
@[simp] theorem one_jet_zero (t : ℝ) : (1 : JetFun R).jet 0 t = 1 := rfl
@[simp] theorem one_jet_succ (n : ℕ) (t : ℝ) : (1 : JetFun R).jet (n + 1) t = 0 := by
  show (if n + 1 = 0 then (1 : R) else 0) = 0; simp
@[simp] theorem add_jet (f g : JetFun R) (n : ℕ) (t : ℝ) :
    (f + g).jet n t = f.jet n t + g.jet n t := rfl
@[simp] theorem neg_jet (f : JetFun R) (n : ℕ) (t : ℝ) :
    (-f).jet n t = -(f.jet n t) := rfl
@[simp] theorem sub_jet (f g : JetFun R) (n : ℕ) (t : ℝ) :
    (f - g).jet n t = f.jet n t - g.jet n t := rfl
@[simp] theorem mul_jet (f g : JetFun R) (n : ℕ) (t : ℝ) :
    (f * g).jet n t = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : R) * f.jet k t * g.jet (n - k) t := rfl

-- ============================================================
-- CommRing helper lemmas
-- ============================================================

private theorem mul_comm_jet (f g : JetFun R) (n : ℕ) (t : ℝ) :
    (f * g).jet n t = (g * f).jet n t := by
  simp only [mul_jet]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
  rw [show n - (n + 1 - 1 - k) = k from by omega,
      show n + 1 - 1 - k = n - k from by omega, Nat.choose_symm hk']
  ring

private theorem one_mul_jet (f : JetFun R) (n : ℕ) (t : ℝ) :
    (1 * f).jet n t = f.jet n t := by
  simp only [mul_jet]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]
  · simp
  · intro k _ hk0
    have : (1 : JetFun R).jet k t = 0 := by
      show (if k = 0 then (1 : R) else 0) = 0; simp [hk0]
    simp [this]

private theorem left_distrib_jet (a b c : JetFun R) (n : ℕ) (t : ℝ) :
    (a * (b + c)).jet n t = (a * b + a * c).jet n t := by
  simp only [mul_jet, add_jet]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _; ring

-- ============================================================
-- mul_assoc via Nat.choose_mul (Vandermonde identity)
-- ============================================================

private theorem mul_assoc_jet (a b c : JetFun R) (n : ℕ) (t : ℝ) :
    (a * b * c).jet n t = (a * (b * c)).jet n t := by
  simp only [mul_jet]
  -- Both sides equal ∑_{i+l≤n} C(n,i)*C(n-i,l) * a_i * b_l * c_{n-i-l}
  -- via Vandermonde: C(n,j)*C(j,i) = C(n,i)*C(n-i,j-i)
  -- Use sigma type for the canonical form
  set S₁ := (Finset.range (n + 1)).sigma (fun j => Finset.range (j + 1))
  set S₂ := (Finset.range (n + 1)).sigma (fun i => Finset.range (n - i + 1))
  trans (∑ p ∈ S₂,
    (n.choose p.1 : R) * ((n - p.1).choose p.2 : R) * a.jet p.1 t *
      b.jet p.2 t * c.jet (n - p.1 - p.2) t)
  · -- LHS → canonical double sum
    conv_lhs => arg 2; ext j; rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_sigma']
    apply Finset.sum_nbij'
      (fun (p : Σ _, ℕ) => (⟨p.2, p.1 - p.2⟩ : Σ _, ℕ))
      (fun (p : Σ _, ℕ) => (⟨p.1 + p.2, p.1⟩ : Σ _, ℕ))
    · intro ⟨j, i⟩ hp
      simp only [S₁, S₂, Finset.mem_sigma, Finset.mem_range] at hp ⊢; omega
    · intro ⟨k, l⟩ hq
      simp only [S₁, S₂, Finset.mem_sigma, Finset.mem_range] at hq ⊢; omega
    · intro ⟨j, i⟩ hp
      simp only [S₁, Finset.mem_sigma, Finset.mem_range] at hp
      simp only [Sigma.eta]; ext <;> simp <;> omega
    · intro ⟨k, l⟩ hq
      simp only [S₂, Finset.mem_sigma, Finset.mem_range] at hq
      simp only [Sigma.eta]; ext <;> simp <;> omega
    · intro ⟨j, i⟩ hp
      simp only [S₁, Finset.mem_sigma, Finset.mem_range] at hp
      have hij : i ≤ j := by omega
      have h_choose : (n.choose j : R) * (j.choose i : R) =
          (n.choose i : R) * ((n - i).choose (j - i) : R) := by
        have h := Nat.choose_mul hij (n := n)
        rw [← Nat.cast_mul, ← Nat.cast_mul, h]
      simp only [Sigma.fst, Sigma.snd]
      rw [show n - j = n - i - (j - i) from by omega]
      calc ↑(n.choose j) * (↑(j.choose i) * a.jet i t * b.jet (j - i) t) *
              c.jet (n - i - (j - i)) t
          = (↑(n.choose j) * ↑(j.choose i)) * a.jet i t * b.jet (j - i) t *
              c.jet (n - i - (j - i)) t := by ring
        _ = (↑(n.choose i) * ↑((n - i).choose (j - i))) * a.jet i t * b.jet (j - i) t *
              c.jet (n - i - (j - i)) t := by rw [h_choose]
        _ = ↑(n.choose i) * ↑((n - i).choose (j - i)) * a.jet i t * b.jet (j - i) t *
              c.jet (n - i - (j - i)) t := by ring
  · -- canonical → RHS
    symm
    conv_lhs => arg 2; ext k; rw [Finset.mul_sum]
    rw [Finset.sum_sigma']
    apply Finset.sum_congr rfl; intro ⟨k, l⟩ hq
    simp only [S₂, Finset.mem_sigma, Finset.mem_range] at hq
    ring

-- ============================================================
-- CommRing instance
-- ============================================================

instance : CommRing (JetFun R) where
  add_assoc a b c := by ext n t; simp [add_assoc]
  zero_add a := by ext n t; simp
  add_zero a := by ext n t; simp
  add_comm a b := by ext n t; simp [add_comm]
  mul_assoc a b c := by ext n t; exact mul_assoc_jet a b c n t
  one_mul a := by ext n t; exact one_mul_jet a n t
  mul_one a := by ext n t; rw [mul_comm_jet]; exact one_mul_jet a n t
  mul_comm a b := by ext n t; exact mul_comm_jet a b n t
  left_distrib a b c := by ext n t; exact left_distrib_jet a b c n t
  right_distrib a b c := by
    ext n t
    have h1 := mul_comm_jet (a + b) c n t
    have h2 := left_distrib_jet c a b n t
    have h3 := mul_comm_jet c a n t
    have h4 := mul_comm_jet c b n t
    simp only [mul_jet, add_jet] at h1 h2 h3 h4 ⊢
    rw [h1, h2, h3, h4]
  zero_mul a := by ext n t; simp [Finset.sum_const_zero]
  mul_zero a := by ext n t; simp [Finset.sum_const_zero]
  sub_eq_add_neg a b := by ext n t; simp [sub_eq_add_neg]
  neg_add_cancel a := by ext n t; simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  natCast_zero := by ext n t; simp [NatCast.natCast, Zero.zero]
  natCast_succ m := by
    ext n t; show (if n = 0 then ((m + 1 : ℕ) : R) else 0) =
      (if n = 0 then (m : R) else 0) + (if n = 0 then (1 : R) else 0)
    by_cases h : n = 0 <;> simp [h, Nat.cast_succ]
  intCast_ofNat m := by
    ext n t; show (if n = 0 then ((m : ℤ) : R) else 0) = (if n = 0 then (m : R) else 0)
    by_cases h : n = 0 <;> simp [h]
  intCast_negSucc m := by
    ext n t; show (if n = 0 then ((Int.negSucc m : ℤ) : R) else 0) =
      -(if n = 0 then ((m + 1 : ℕ) : R) else 0)
    by_cases h : n = 0 <;> simp [h, Int.negSucc_eq]

-- ============================================================
-- SMul and Algebra
-- ============================================================

instance : SMul R (JetFun R) where
  smul c f := ⟨fun n t => c * f.jet n t⟩

@[simp] theorem smul_jet (c : R) (f : JetFun R) (n : ℕ) (t : ℝ) :
    (c • f).jet n t = c * f.jet n t := rfl

/-- Embed a constant into JetFun: jet 0 = c, higher jets = 0. -/
def const (c : R) : JetFun R := ⟨fun n _ => if n = 0 then c else 0⟩

@[simp] theorem const_jet_zero (c : R) (t : ℝ) : (const c).jet 0 t = c := rfl
@[simp] theorem const_jet_succ (c : R) (n : ℕ) (t : ℝ) :
    (const c).jet (n + 1) t = 0 := by simp [const]

private theorem const_mul_eq (c : R) (f : JetFun R) :
    const c * f = c • f := by
  ext n t; simp only [mul_jet, smul_jet]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]
  · simp [const]
  · intro k _ hk0; simp [const, hk0]

def constRingHom : R →+* JetFun R where
  toFun := const
  map_one' := by
    ext n t; cases n with
    | zero => simp [const]
    | succ n => simp [const]
  map_mul' a b := by
    ext n t; simp only [mul_jet, const]
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]
    · simp
    · intro k _ hk0; simp [hk0]
  map_zero' := by
    ext n t; cases n with
    | zero => simp [const]
    | succ n => simp [const]
  map_add' a b := by
    ext n t; cases n with
    | zero => simp [const]
    | succ n => simp [const]

instance : Algebra R (JetFun R) where
  algebraMap := constRingHom
  commutes' c f := by ext n t; exact mul_comm_jet (const c) f n t
  smul_def' c f := by
    ext n t; simp only [smul_jet]
    have := const_mul_eq c f
    exact (congr_arg (fun x => x.jet n t) this.symm)

-- ============================================================
-- lift, eval, dt
-- ============================================================

/-- Lift a time-dependent function into JetFun: jet 0 = f, higher jets = 0. -/
def lift (f : ℝ → R) : JetFun R := ⟨fun n t => if n = 0 then f t else 0⟩

/-- Evaluate a JetFun at a time point (project to jet 0). -/
def eval (a : JetFun R) (t : ℝ) : R := a.jet 0 t

/-- Time derivative: shift the jet sequence by one. -/
def dt (a : JetFun R) : JetFun R := ⟨fun n t => a.jet (n + 1) t⟩

@[simp] theorem lift_jet_zero (f : ℝ → R) (t : ℝ) : (lift f).jet 0 t = f t := rfl
@[simp] theorem lift_jet_succ (f : ℝ → R) (n : ℕ) (t : ℝ) :
    (lift f).jet (n + 1) t = 0 := by simp [lift]
@[simp] theorem eval_eq (a : JetFun R) (t : ℝ) : eval a t = a.jet 0 t := rfl
@[simp] theorem dt_jet (a : JetFun R) (n : ℕ) (t : ℝ) : (dt a).jet n t = a.jet (n + 1) t := rfl

-- ============================================================
-- TimeDerivativeData axioms
-- ============================================================

theorem eval_lift (f : ℝ → R) (t : ℝ) : eval (lift f) t = f t := rfl

theorem lift_add (f g : ℝ → R) : lift (f + g) = lift f + lift g := by
  ext n t; simp [lift]; by_cases h : n = 0 <;> simp [h]

theorem lift_mul (f g : ℝ → R) : lift (f * g) = lift f * lift g := by
  ext n t; simp only [mul_jet, lift]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]
  · simp
  · intro k _ hk0; simp [hk0]

theorem lift_algebraMap (c : R) :
    lift (fun _ => c) = algebraMap R (JetFun R) c := by
  change lift (fun _ => c) = constRingHom c
  ext n t; cases n with
  | zero => rfl
  | succ n => rfl

theorem eval_add (a b : JetFun R) (t : ℝ) :
    eval (a + b) t = eval a t + eval b t := rfl

theorem eval_mul (a b : JetFun R) (t : ℝ) :
    eval (a * b) t = eval a t * eval b t := by simp

theorem eval_algebraMap (c : R) (t : ℝ) :
    eval (algebraMap R (JetFun R) c) t = c := rfl

-- ============================================================
-- dt is a Derivation
-- ============================================================

private theorem dt_map_add (f g : JetFun R) : dt (f + g) = dt f + dt g := by
  ext n t; simp [dt]

private theorem dt_map_smul (c : R) (f : JetFun R) : dt (c • f) = c • dt f := by
  ext n t; simp [dt]

/-- The Leibniz rule for dt, proved via Pascal's rule on binomial coefficients. -/
private theorem dt_leibniz (f g : JetFun R) :
    dt (f * g) = f * dt g + g * dt f := by
  ext n t
  simp only [dt_jet, mul_jet, add_jet]
  -- Normalize n-k+1 → n+1-k in the RHS sums (equal for k ≤ n)
  have hnorm₁ : ∀ k ∈ Finset.range (n + 1),
      (n.choose k : R) * f.jet k t * g.jet (n - k + 1) t =
      (n.choose k : R) * f.jet k t * g.jet (n + 1 - k) t := by
    intro k hk
    have : k ≤ n := by have := Finset.mem_range.mp hk; omega
    rw [show n - k + 1 = n + 1 - k from by omega]
  have hnorm₂ : ∀ k ∈ Finset.range (n + 1),
      (n.choose k : R) * g.jet k t * f.jet (n - k + 1) t =
      (n.choose k : R) * g.jet k t * f.jet (n + 1 - k) t := by
    intro k hk
    have : k ≤ n := by have := Finset.mem_range.mp hk; omega
    rw [show n - k + 1 = n + 1 - k from by omega]
  rw [Finset.sum_congr rfl hnorm₁, Finset.sum_congr rfl hnorm₂]
  -- Now both sides use n+1-k. Peel LHS boundary terms.
  rw [Finset.sum_range_succ'
    (fun k => ((n + 1).choose k : R) * f.jet k t * g.jet (n + 1 - k) t)]
  rw [Finset.sum_range_succ
    (fun k => ((n + 1).choose (k + 1) : R) * f.jet (k + 1) t * g.jet (n + 1 - (k + 1)) t)]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.choose_self, Nat.sub_self]
  -- Pascal: C(n+1,k+1) = C(n,k) + C(n,k+1)
  have pascal : ∀ k ∈ Finset.range n,
      ((n + 1).choose (k + 1) : R) * f.jet (k + 1) t * g.jet (n + 1 - (k + 1)) t =
      (n.choose k : R) * f.jet (k + 1) t * g.jet (n + 1 - (k + 1)) t +
      (n.choose (k + 1) : R) * f.jet (k + 1) t * g.jet (n + 1 - (k + 1)) t := by
    intro k _; rw [← add_mul, ← add_mul]; congr 1; congr 1
    push_cast [Nat.choose_succ_succ n k]; ring
  rw [Finset.sum_congr rfl pascal, Finset.sum_add_distrib]
  -- Peel RHS sums to match
  conv_rhs =>
    lhs; rw [Finset.sum_range_succ'
      (fun k => (n.choose k : R) * f.jet k t * g.jet (n + 1 - k) t)]
  conv_rhs =>
    rhs; rw [Finset.sum_range_succ'
      (fun k => (n.choose k : R) * g.jet k t * f.jet (n + 1 - k) t)]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul,
    show n + 1 - 0 = n + 1 from by omega]
  -- Both sides now have matching boundary terms + two inner sums over range n.
  -- The C(n,k+1) sums in LHS and first RHS match.
  -- Need: C(n,k) sum (LHS) = reflected C(n,k+1) sum (second RHS inner)
  suffices h_sum :
      ∑ k ∈ Finset.range n,
        (n.choose k : R) * f.jet (k + 1) t * g.jet (n + 1 - (k + 1)) t =
      ∑ k ∈ Finset.range n,
        (n.choose (k + 1) : R) * g.jet (k + 1) t * f.jet (n + 1 - (k + 1)) t by
    rw [h_sum]; ring
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k < n := Finset.mem_range.mp hk
  -- After reflection: index is n-1-k. Goal has choose (n-(k+1)) and jet (n-(k+1)+1)
  -- Need: C(n, n-(k+1)) = C(n, k+1) and index arithmetic
  conv_lhs =>
    rw [show n - 1 - k = n - (k + 1) from by omega]
  rw [show n.choose (n - (k + 1)) = n.choose (k + 1) from
        Nat.choose_symm (by omega),
      show n - (k + 1) + 1 = n - k from by omega,
      show n + 1 - (n - k) = k + 1 from by omega,
      show n - k = n + 1 - (k + 1) from by omega]
  ring

private theorem dt_one : dt (1 : JetFun R) = 0 := by
  ext n t; simp [dt]

/-- The time derivation on JetFun as a `Derivation`. -/
def timeDeriv : Derivation R (JetFun R) (JetFun R) where
  toLinearMap :=
    { toFun := dt
      map_add' := dt_map_add
      map_smul' := dt_map_smul }
  leibniz' f g := by
    show dt (f * g) = f * dt g + g * dt f
    exact dt_leibniz f g
  map_one_eq_zero' := dt_one

-- ============================================================
-- Package: TimeDerivativeData
-- ============================================================

/-- The concrete `TimeDerivativeData` for any `CommRing R`.
    The algebra is `JetFun R` (bare jet sequences) with the Leibniz product.
    The derivation is jet-shifting: `(dt a).jet n t = a.jet (n+1) t`.
    `lift`/`eval` embed and project at jet level 0. -/
def concreteTimeDerivativeData : TimeDerivativeData R (JetFun R) ℝ where
  dt := timeDeriv
  lift := lift
  eval := eval
  eval_lift := eval_lift
  lift_add := lift_add
  lift_mul := lift_mul
  lift_algebraMap := lift_algebraMap
  eval_add := eval_add
  eval_mul := eval_mul
  eval_algebraMap := eval_algebraMap

end JetFun
