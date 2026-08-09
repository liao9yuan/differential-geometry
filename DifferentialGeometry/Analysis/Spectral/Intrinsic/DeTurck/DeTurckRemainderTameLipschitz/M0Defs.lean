import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Order-zero index-algebra definitions (`M0Abstract.Defs`)

Chunk of `DeTurckRemainderTameLipschitz`, split out of the former
46927-line monolith (no longer elaborable in a single Lean
process).  Every declaration is verbatim.  Chunk map, dependency
graph and measured peaks: `DeTurckRemainderTameLipschitz.md`.
-/

noncomputable section

open scoped BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

section

set_option linter.style.setOption false

set_option backward.isDefEq.respectTransparency false

set_option linter.style.setOption false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1600000

set_option synthInstance.maxHeartbeats 1600000

set_option linter.unusedSectionVars false

section M0AbstractLayer

set_option linter.style.setOption false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 3200000

namespace M0Abstract

variable {n : ℕ}

section Defs

variable (ig cg : Fin n → Fin n → ℝ)
variable (dg gb : Fin n → Fin n → Fin n → ℝ)
variable (dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
variable (dig : Fin n → Fin n → Fin n → ℝ)
variable (ga1 ga0 gbg : Fin n → Fin n → Fin n → ℝ)
variable (dga1 dga0 dgbg : Fin n → Fin n → Fin n → Fin n → ℝ)
variable (f : Fin n → Fin n → ℝ)
variable (f3 : Fin n → Fin n → Fin n → ℝ)

def p1B (i j : Fin n) : ℝ :=
  (- ∑ ρ, (∑ a, ∑ b, (dig i a b * (ga1 a b ρ - ga0 a b ρ) +
      ig a b * (dga1 i a b ρ - dga0 i a b ρ)) +
    ∑ σ, ga0 i σ ρ * (∑ a, ∑ b, ig a b * (ga1 a b σ - ga0 a b σ))) * f ρ j) +
  (- ∑ ρ, (∑ a, ∑ b, (dig j a b * (ga1 a b ρ - ga0 a b ρ) +
      ig a b * (dga1 j a b ρ - dga0 j a b ρ)) +
    ∑ σ, ga0 j σ ρ * (∑ a, ∑ b, ig a b * (ga1 a b σ - ga0 a b σ))) * f i ρ)

def p2B (i j : Fin n) : ℝ :=
  2 * ∑ ρ, ∑ σ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) *
    ((ga1 i j σ - ga0 i j σ) * f ρ σ)

private def p3B (i j : Fin n) : ℝ :=
  2 * (∑ a, ∑ p, ∑ b, ∑ q, ∑ ρ, ∑ k,
      ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
        ((ga1 a b k - gbg a b k) * cg k j)))) +
    ∑ a, ∑ p, ∑ b, ∑ q, ∑ ρ, ∑ k,
      ig a p * (ig b q * ((ga1 j p ρ - ga0 j p ρ) * (f ρ q *
        ((ga1 a b k - gbg a b k) * cg k i)))))

def p4B (i j : Fin n) : ℝ :=
  (- ∑ m, ∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) *
      ((ga1 m i ρ - ga0 m i ρ) * f ρ j)) +
  (- ∑ m, ∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) *
      ((ga1 m j ρ - ga0 m j ρ) * f i ρ))

def rchB (l i j ρ : Fin n) : ℝ :=
  dga0 i l j ρ - dga0 j l i ρ + ∑ c, (ga0 i c ρ * ga0 l j c - ga0 j c ρ * ga0 l i c)

def p5B (i j : Fin n) : ℝ :=
  -(∑ m, ∑ ml, ig m ml * ∑ ρ, rchB ga0 dga0 ml i j ρ * f ρ m)

def nscB (i p : Fin n) : ℝ :=
  ∑ m, (∑ a, ∑ b, ig a b * (ga1 a b m - ga0 a b m)) * (ga1 i m p - ga0 i m p) -
    ∑ m, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) * (ga1 i m p - ga0 i m p) -
    ((∑ a, ∑ b, (dig i a b * (ga1 a b p - ga0 a b p) +
        ig a b * (dga1 i a b p - dga0 i a b p))) +
      ∑ m, ga1 i m p * (∑ a, ∑ b, ig a b * (ga1 a b m - ga0 a b m)))

def insertB (i j : Fin n) : ℝ :=
  (∑ p, nscB ig dig ga1 ga0 gbg dga1 dga0 i p * f p j) +
    (∑ p, nscB ig dig ga1 ga0 gbg dga1 dga0 j p * f i p)

private lemma a1_ga1_symm
    (hgb : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgs : ∀ m a b, dg m a b = dg m b a)
    (hga1 : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (a b k : Fin n) : ga1 a b k = ga1 b a k := by
  rw [hga1, hga1]
  refine congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) (Finset.sum_congr rfl (fun l _ => ?_))
  rw [hgb, hgb, hdgs a l b, hdgs b l a, hdgs l a b]
  ring

theorem stageA1
    (hgb : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgs : ∀ m a b, dg m a b = dg m b a)
    (hga1 : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (i j : Fin n) :
    insertB ig dig ga1 ga0 gbg dga1 dga0 f i j =
      p1B ig dig ga1 ga0 dga1 dga0 f i j + p4B ig ga1 ga0 gbg f i j := by
  have hga1s : ∀ a b k, ga1 a b k = ga1 b a k :=
    a1_ga1_symm ig dg gb ga1 hgb hdgs hga1
  have hhalf : ∀ (u : Fin n) (F : Fin n → ℝ),
      (∑ p, nscB ig dig ga1 ga0 gbg dga1 dga0 u p * F p) =
        (- ∑ ρ, (∑ a, ∑ b, (dig u a b * (ga1 a b ρ - ga0 a b ρ) +
            ig a b * (dga1 u a b ρ - dga0 u a b ρ)) +
          ∑ σ, ga0 u σ ρ * (∑ a, ∑ b, ig a b * (ga1 a b σ - ga0 a b σ))) * F ρ) +
        (- ∑ m, ∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) *
            ((ga1 m u ρ - ga0 m u ρ) * F ρ)) := by
    intro u F
    have hswap2 : (∑ m, ∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) *
        ((ga1 m u ρ - ga0 m u ρ) * F ρ)) =
        ∑ ρ, (∑ m, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) *
          (ga1 u m ρ - ga0 u m ρ)) * F ρ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [hga1s m u ρ, hga0s m u ρ]
      ring
    have hcomb : (- ∑ ρ, (∑ a, ∑ b, (dig u a b * (ga1 a b ρ - ga0 a b ρ) +
          ig a b * (dga1 u a b ρ - dga0 u a b ρ)) +
        ∑ σ, ga0 u σ ρ * (∑ a, ∑ b, ig a b * (ga1 a b σ - ga0 a b σ))) * F ρ) +
        (- ∑ ρ, (∑ m, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) *
          (ga1 u m ρ - ga0 u m ρ)) * F ρ) =
      ∑ ρ, (((-((∑ a, ∑ b, (dig u a b * (ga1 a b ρ - ga0 a b ρ) +
          ig a b * (dga1 u a b ρ - dga0 u a b ρ)) +
        ∑ σ, ga0 u σ ρ * (∑ a, ∑ b, ig a b * (ga1 a b σ - ga0 a b σ)))))
        + (-(∑ m, (∑ a, ∑ b, ig a b * (ga1 a b m - gbg a b m)) *
          (ga1 u m ρ - ga0 u m ρ)))) * F ρ) := by
      rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      ring
    rw [hswap2, hcomb]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    refine congrArg (fun t : ℝ => t * F p) ?_
    rw [nscB]
    have hkey : (∑ m, ga1 u m p * (∑ a, ∑ b, ig a b * (ga1 a b m - ga0 a b m))) -
        (∑ m, (∑ a, ∑ b, ig a b * (ga1 a b m - ga0 a b m)) * (ga1 u m p - ga0 u m p)) =
        ∑ σ, ga0 u σ p * (∑ a, ∑ b, ig a b * (ga1 a b σ - ga0 a b σ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
    linarith [hkey]
  rw [insertB, hhalf i (fun p => f p j), hhalf j (fun p => f i p)]
  rw [p1B, p4B]
  ring

def vbB (i j : Fin n) : ℝ :=
  2 * ∑ k, ∑ l, ig k l *
    ((∑ c, (ga1 j i c - ga0 j i c) * cg c l) *
      (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k))

private lemma collapse_sum (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1:ℝ) else 0)
    (higs : ∀ a b, ig a b = ig b a) (hcgs : ∀ a b, cg a b = cg b a)
    (X : Fin n → ℝ) (c : Fin n) :
    (∑ k, (∑ l, ig k l * cg c l) * X k) = X c := by
  have hone : ∀ k, (∑ l, ig k l * cg c l) = if k = c then (1:ℝ) else 0 := by
    intro k
    rw [show (∑ l, ig k l * cg c l) = ∑ l, cg l c * ig l k from
      Finset.sum_congr rfl (fun l _ => by rw [higs k l, hcgs c l]; ring)]
    exact hcol k c
  rw [Finset.sum_congr rfl (fun k _ => by rw [hone k])]
  rw [Finset.sum_eq_single c]
  · rw [if_pos rfl, one_mul]
  · intro k _ hk
    rw [if_neg hk, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem stageA2
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1:ℝ) else 0)
    (higs : ∀ a b, ig a b = ig b a) (hcgs : ∀ a b, cg a b = cg b a)
    (hgb : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgs : ∀ m a b, dg m a b = dg m b a)
    (hga1 : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (i j : Fin n) :
    vbB ig cg ga1 ga0 f i j = p2B ig ga1 ga0 f i j := by
  have hga1s : ∀ a b k, ga1 a b k = ga1 b a k :=
    a1_ga1_symm ig dg gb ga1 hgb hdgs hga1
  rw [vbB, p2B]
  refine congrArg (fun t : ℝ => 2 * t) ?_
  have hstep1 : (∑ k, ∑ l, ig k l *
      ((∑ c, (ga1 j i c - ga0 j i c) * cg c l) *
        (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k))) =
    ∑ c, (ga1 j i c - ga0 j i c) *
      ∑ k, (∑ l, ig k l * cg c l) *
        (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k) := by
    have h1 : ∀ k, (∑ l, ig k l *
        ((∑ c, (ga1 j i c - ga0 j i c) * cg c l) *
          (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k))) =
        ∑ c, ∑ l, (ga1 j i c - ga0 j i c) *
          ((ig k l * cg c l) *
            (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k)) := by
      intro k
      have h2 : ∀ l, ig k l *
          ((∑ c, (ga1 j i c - ga0 j i c) * cg c l) *
            (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k)) =
          ∑ c, (ga1 j i c - ga0 j i c) *
            ((ig k l * cg c l) *
              (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k)) := by
        intro l
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        ring
      rw [Finset.sum_congr rfl (fun l _ => h2 l)]
      exact Finset.sum_comm
    rw [Finset.sum_congr rfl (fun k _ => h1 k)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_mul, Finset.mul_sum]
  rw [hstep1]
  have hstep2 : (∑ c, (ga1 j i c - ga0 j i c) *
      ∑ k, (∑ l, ig k l * cg c l) *
        (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k)) =
      ∑ c, (ga1 j i c - ga0 j i c) *
        (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ c) :=
    Finset.sum_congr rfl (fun c _ => by
      rw [collapse_sum ig cg hcol higs hcgs
        (fun k => (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ k)) c])
  rw [hstep2]
  have hdist : (∑ c, (ga1 j i c - ga0 j i c) *
      (∑ ρ, (∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ c)) =
      ∑ c, ∑ ρ, (ga1 j i c - ga0 j i c) *
        ((∑ a, ∑ b, ig a b * (ga1 a b ρ - ga0 a b ρ)) * f ρ c) :=
    Finset.sum_congr rfl (fun c _ => Finset.mul_sum _ _ _)
  rw [hdist, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [hga1s j i σ, hga0s j i σ]
  ring

def amixHalfB (i j : Fin n) : ℝ :=
  ∑ m, ∑ ml, ig m ml *
    (∑ a, ∑ al, ig a al *
      ((∑ k, ∑ kl, ig k kl *
        (f k ml * (∑ c, (ga1 al i c - ga0 al i c) * cg c kl))) *
        (∑ d, (ga1 m a d - gbg m a d) * cg d j)))

def p3HalfB (i j : Fin n) : ℝ :=
  ∑ a, ∑ p, ∑ b, ∑ q, ∑ ρ, ∑ k,
    ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
      ((ga1 a b k - gbg a b k) * cg k j))))

theorem stageA3
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1:ℝ) else 0)
    (higs : ∀ a b, ig a b = ig b a) (hcgs : ∀ a b, cg a b = cg b a)
    (hgb : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgs : ∀ m a b, dg m a b = dg m b a)
    (hga1 : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (i j : Fin n) :
    amixHalfB ig cg ga1 ga0 gbg f i j = p3HalfB ig cg ga1 ga0 gbg f i j := by
  have hga1s : ∀ a b k, ga1 a b k = ga1 b a k :=
    a1_ga1_symm ig dg gb ga1 hgb hdgs hga1
  have hinner : ∀ ml al : Fin n,
      (∑ k, ∑ kl, ig k kl *
        (f k ml * (∑ c, (ga1 al i c - ga0 al i c) * cg c kl))) =
      ∑ c, (ga1 al i c - ga0 al i c) * f c ml := by
    intro ml al
    have h1 : ∀ k, (∑ kl, ig k kl *
        (f k ml * (∑ c, (ga1 al i c - ga0 al i c) * cg c kl))) =
        ∑ c, (ga1 al i c - ga0 al i c) * ((∑ kl, ig k kl * cg c kl) * f k ml) := by
      intro k
      have h2 : ∀ kl, ig k kl *
          (f k ml * (∑ c, (ga1 al i c - ga0 al i c) * cg c kl)) =
          ∑ c, (ga1 al i c - ga0 al i c) * ((ig k kl * cg c kl) * f k ml) := by
        intro kl
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        ring
      rw [Finset.sum_congr rfl (fun kl _ => h2 kl), Finset.sum_comm]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun k _ => h1 k), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [← Finset.mul_sum]
    refine congrArg (fun t : ℝ => (ga1 al i c - ga0 al i c) * t) ?_
    exact collapse_sum ig cg hcol higs hcgs (fun k => f k ml) c
  have hmid : amixHalfB ig cg ga1 ga0 gbg f i j =
      ∑ m, ∑ ml, ig m ml *
        (∑ a, ∑ al, ig a al *
          ((∑ c, (ga1 al i c - ga0 al i c) * f c ml) *
            (∑ d, (ga1 m a d - gbg m a d) * cg d j))) := by
    rw [amixHalfB]
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => ?_))
    refine congrArg (fun t : ℝ => ig m ml * t) ?_
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun al _ => ?_))
    refine congrArg (fun t : ℝ => ig a al * t) ?_
    rw [hinner ml al]
  rw [hmid, p3HalfB]
  have hL : (∑ m, ∑ ml, ig m ml *
      (∑ a, ∑ al, ig a al *
        ((∑ c, (ga1 al i c - ga0 al i c) * f c ml) *
          (∑ d, (ga1 m a d - gbg m a d) * cg d j)))) =
      ∑ m, ∑ ml, ∑ a, ∑ al, ∑ c, ∑ d,
        ig m ml * (ig a al * (((ga1 al i c - ga0 al i c) * f c ml) *
          ((ga1 m a d - gbg m a d) * cg d j))) := by
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => ?_))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun al _ => ?_)
    have hprod : (∑ c, (ga1 al i c - ga0 al i c) * f c ml) *
        (∑ d, (ga1 m a d - gbg m a d) * cg d j) =
        ∑ c, ∑ d, ((ga1 al i c - ga0 al i c) * f c ml) *
          ((ga1 m a d - gbg m a d) * cg d j) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Finset.mul_sum]
    rw [hprod, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
  have hR : (∑ a, ∑ p, ∑ b, ∑ q, ∑ ρ, ∑ k,
      ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
        ((ga1 a b k - gbg a b k) * cg k j))))) =
      ∑ b, ∑ q, ∑ a, ∑ p, ∑ ρ, ∑ k,
        ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
          ((ga1 a b k - gbg a b k) * cg k j)))) := by
    rw [show (∑ a, ∑ p, ∑ b, ∑ q, ∑ ρ, ∑ k,
        ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
          ((ga1 a b k - gbg a b k) * cg k j))))) =
      ∑ a, ∑ b, ∑ p, ∑ q, ∑ ρ, ∑ k,
        ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
          ((ga1 a b k - gbg a b k) * cg k j)))) from
      Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [show (∑ a, ∑ p, ∑ q, ∑ ρ, ∑ k,
        ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
          ((ga1 a b k - gbg a b k) * cg k j))))) =
      ∑ a, ∑ q, ∑ p, ∑ ρ, ∑ k,
        ig a p * (ig b q * ((ga1 i p ρ - ga0 i p ρ) * (f ρ q *
          ((ga1 a b k - gbg a b k) * cg k j)))) from
      Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
  rw [hL, hR]
  rw [show (∑ m, ∑ ml, ∑ a, ∑ al, ∑ c, ∑ d,
      ig m ml * (ig a al * (((ga1 al i c - ga0 al i c) * f c ml) *
        ((ga1 m a d - gbg m a d) * cg d j)))) =
    ∑ m, ∑ ml, ∑ a, ∑ al, ∑ c, ∑ d,
      ig a al * (ig m ml * ((ga1 i al c - ga0 i al c) * (f c ml *
        ((ga1 a m d - gbg a m d) * cg d j)))) from by
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => ?_))
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun al _ => ?_))
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
    rw [hga1s al i c, hga0s al i c, hga1s m a d, hgbgs m a d]
    ring]

theorem nf_p5 (higs : ∀ a b, ig a b = ig b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (i j : Fin n) :
    p5B ig ga0 dga0 f i j =
      (-(∑ a, ∑ b, ∑ c, dga0 i j a b * f b c * ig a c))
      + (∑ a, ∑ b, ∑ c, dga0 j i a b * f b c * ig a c)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d c * ig b d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c d * ga0 j d a * ig b c) := by
  rw [p5B]
  have hcomb : ∀ m ml : Fin n, ig m ml * ∑ ρ, rchB ga0 dga0 ml i j ρ * f ρ m =
      ∑ ρ, ((ig m ml * (dga0 i ml j ρ * f ρ m) - ig m ml * (dga0 j ml i ρ * f ρ m))
        + ∑ c, (ig m ml * (ga0 i c ρ * (ga0 ml j c * f ρ m))
            - ig m ml * (ga0 j c ρ * (ga0 ml i c * f ρ m)))) := by
    intro m ml
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    rw [rchB]
    rw [show (dga0 i ml j ρ - dga0 j ml i ρ +
        ∑ c, (ga0 i c ρ * ga0 ml j c - ga0 j c ρ * ga0 ml i c)) * f ρ m =
      (dga0 i ml j ρ * f ρ m - dga0 j ml i ρ * f ρ m)
        + ∑ c, (ga0 i c ρ * ga0 ml j c - ga0 j c ρ * ga0 ml i c) * f ρ m from by
      rw [add_mul, sub_mul, Finset.sum_mul]]
    rw [mul_add, Finset.mul_sum]
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) (by ring)
      (Finset.sum_congr rfl (fun c _ => by ring))
  rw [Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => hcomb m ml))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h1 : (∑ m, ∑ ml, ∑ ρ, ig m ml * (dga0 i ml j ρ * f ρ m)) =
      ∑ a, ∑ b, ∑ c, dga0 i j a b * f b c * ig a c := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ml _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ρ _ => Finset.sum_congr rfl (fun m _ => ?_))
    rw [hdga0s i ml j ρ, higs m ml]
    ring
  have h2 : (∑ m, ∑ ml, ∑ ρ, ig m ml * (dga0 j ml i ρ * f ρ m)) =
      ∑ a, ∑ b, ∑ c, dga0 j i a b * f b c * ig a c := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ml _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ρ _ => Finset.sum_congr rfl (fun m _ => ?_))
    rw [hdga0s j ml i ρ, higs m ml]
    ring
  have h3 : (∑ m, ∑ ml, ∑ ρ, ∑ c, ig m ml * (ga0 i c ρ * (ga0 ml j c * f ρ m))) =
      ∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d c * ig b d := by
    rw [Finset.sum_congr rfl (fun m (_ : m ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ρ _ => Finset.sum_congr rfl (fun m _ => ?_))
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun ml _ => ?_))
    rw [hga0s ml j c, higs m ml]
    ring
  have h4 : (∑ m, ∑ ml, ∑ ρ, ∑ c, ig m ml * (ga0 j c ρ * (ga0 ml i c * f ρ m))) =
      ∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c d * ga0 j d a * ig b c := by
    rw [Finset.sum_congr rfl (fun m (_ : m ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ρ _ => Finset.sum_congr rfl (fun m _ =>
      Finset.sum_congr rfl (fun ml _ => Finset.sum_congr rfl (fun c _ => ?_))))
    rw [hga0s ml i c, higs m ml]
    ring
  rw [h1, h2, h3, h4]
  ring
def r4F (a b c d : Fin n) : ℝ :=
  (((- ∑ r, dga0 a c b r * f r d) + (- ∑ r, dga0 a d b r * f c r)) +
      ((- ∑ r, ga0 c b r * f3 a r d) + (- ∑ r, ga0 d b r * f3 a c r))) +
    ((- ∑ r, ga0 a b r * (f3 r c d +
        ((- ∑ t, ga0 r c t * f t d) + (- ∑ t, ga0 r d t * f c t)))) +
      ((- ∑ r, ga0 a c r * (f3 b r d +
          ((- ∑ t, ga0 b r t * f t d) + (- ∑ t, ga0 b d t * f r t)))) +
        (- ∑ r, ga0 a d r * (f3 b c r +
          ((- ∑ t, ga0 b c t * f t r) + (- ∑ t, ga0 b r t * f c t))))))

def r4pfB (d a b c : Fin n) : ℝ :=
  - ∑ r, (ga0 a b r * f3 d r c + ga0 a c r * f3 d b r + ga0 d a r * f3 r b c +
      ga0 d b r * f3 a r c + ga0 d c r * f3 a b r)

private def r4hB (a b c d : Fin n) : ℝ :=
  ((- ∑ r, dga0 a c b r * f r d) + (- ∑ r, dga0 a d b r * f c r)) +
    ((∑ r, ∑ t, ga0 a b r * (ga0 r c t * f t d)) +
      (∑ r, ∑ t, ga0 a b r * (ga0 r d t * f c t)) +
      (∑ r, ∑ t, ga0 a c r * (ga0 b r t * f t d)) +
      (∑ r, ∑ t, ga0 a c r * (ga0 b d t * f r t)) +
      (∑ r, ∑ t, ga0 a d r * (ga0 b c t * f t r)) +
      (∑ r, ∑ t, ga0 a d r * (ga0 b r t * f c t)))

def t2F (i j : Fin n) : ℝ :=
  ∑ k1, ∑ l, ig k1 l * (r4F ga0 dga0 f f3 i l j k1 + r4F ga0 dga0 f f3 j l i k1 -
    r4F ga0 dga0 f f3 i j l k1)

def tpfF (i j : Fin n) : ℝ :=
  ∑ k1, ∑ l, ig k1 l * (r4pfB ga0 f3 i l j k1 + r4pfB ga0 f3 j l i k1 -
    r4pfB ga0 f3 i j l k1)

private lemma b1_r4_split (hga0s : ∀ a b k, ga0 a b k = ga0 b a k) (a b c d : Fin n) :
    r4F ga0 dga0 f f3 a b c d - r4pfB ga0 f3 a b c d = r4hB ga0 dga0 f a b c d := by
  rw [r4F, r4pfB, r4hB]
  have e1 : (∑ r, ga0 a b r * (f3 r c d +
      ((- ∑ t, ga0 r c t * f t d) + (- ∑ t, ga0 r d t * f c t)))) =
      (∑ r, ga0 a b r * f3 r c d) - (∑ r, ∑ t, ga0 a b r * (ga0 r c t * f t d)) -
        (∑ r, ∑ t, ga0 a b r * (ga0 r d t * f c t)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [mul_add, mul_add, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have e2 : (∑ r, ga0 a c r * (f3 b r d +
      ((- ∑ t, ga0 b r t * f t d) + (- ∑ t, ga0 b d t * f r t)))) =
      (∑ r, ga0 a c r * f3 b r d) - (∑ r, ∑ t, ga0 a c r * (ga0 b r t * f t d)) -
        (∑ r, ∑ t, ga0 a c r * (ga0 b d t * f r t)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [mul_add, mul_add, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have e3 : (∑ r, ga0 a d r * (f3 b c r +
      ((- ∑ t, ga0 b c t * f t r) + (- ∑ t, ga0 b r t * f c t)))) =
      (∑ r, ga0 a d r * f3 b c r) - (∑ r, ∑ t, ga0 a d r * (ga0 b c t * f t r)) -
        (∑ r, ∑ t, ga0 a d r * (ga0 b r t * f c t)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [mul_add, mul_add, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  rw [e1, e2, e3]
  have hpf : (∑ r, (ga0 b c r * f3 a r d + ga0 b d r * f3 a c r + ga0 a b r * f3 r c d +
      ga0 a c r * f3 b r d + ga0 a d r * f3 b c r)) =
      (∑ r, ga0 c b r * f3 a r d) + (∑ r, ga0 d b r * f3 a c r) +
        (∑ r, ga0 a b r * f3 r c d) + (∑ r, ga0 a c r * f3 b r d) +
        (∑ r, ga0 a d r * f3 b c r) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [hga0s c b r, hga0s d b r]
  rw [hpf]
  ring

private lemma b1_block (hga0s : ∀ a b k, ga0 a b k = ga0 b a k) (i j : Fin n) :
    t2F ig ga0 dga0 f f3 i j - tpfF ig ga0 f3 i j =
      ∑ k1, ∑ l, ig k1 l * (r4hB ga0 dga0 f i l j k1 + r4hB ga0 dga0 f j l i k1 -
        r4hB ga0 dga0 f i j l k1) := by
  rw [t2F, tpfF, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k1 _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [← mul_sub]
  refine congrArg (fun t : ℝ => ig k1 l * t) ?_
  rw [show r4F ga0 dga0 f f3 i l j k1 + r4F ga0 dga0 f f3 j l i k1 -
      r4F ga0 dga0 f f3 i j l k1 -
      (r4pfB ga0 f3 i l j k1 + r4pfB ga0 f3 j l i k1 - r4pfB ga0 f3 i j l k1) =
    (r4F ga0 dga0 f f3 i l j k1 - r4pfB ga0 f3 i l j k1) +
      (r4F ga0 dga0 f f3 j l i k1 - r4pfB ga0 f3 j l i k1) -
      (r4F ga0 dga0 f f3 i j l k1 - r4pfB ga0 f3 i j l k1) from by ring]
  rw [b1_r4_split ga0 dga0 f f3 hga0s i l j k1, b1_r4_split ga0 dga0 f f3 hga0s j l i k1,
    b1_r4_split ga0 dga0 f f3 hga0s i j l k1]

theorem nf_T2h
    (higs : ∀ a b, ig a b = ig b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hfs : ∀ a b, f a b = f b a)
    (i j : Fin n) :
    t2F ig ga0 dga0 f f3 i j - tpfF ig ga0 f3 i j =
      (∑ a, ∑ b, ∑ c, dga0 i j a b * f b c * ig a c)
      + (-(∑ a, ∑ b, ∑ c, dga0 i a b c * f j c * ig a b))
      + (-(∑ a, ∑ b, ∑ c, dga0 j i a b * f b c * ig a c))
      + (-(∑ a, ∑ b, ∑ c, dga0 j a b c * f i c * ig a b))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b c * ga0 c d a * ig b d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b c * ga0 c d a * ig b d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d c * ig b d)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c d * ga0 j d a * ig b c)) := by
  rw [b1_block ig ga0 dga0 f f3 hga0s i j]
  have hcomb : ∀ k1 l : Fin n, ig k1 l * (r4hB ga0 dga0 f i l j k1 +
      r4hB ga0 dga0 f j l i k1 - r4hB ga0 dga0 f i j l k1) =
      -(ig k1 l * (∑ r, dga0 i j l r * f r k1))
          - ig k1 l * (∑ r, dga0 i k1 l r * f j r)
          + ig k1 l * (∑ r, ∑ t, ga0 i l r * (ga0 r j t * f t k1))
          + ig k1 l * (∑ r, ∑ t, ga0 i l r * (ga0 r k1 t * f j t))
          + ig k1 l * (∑ r, ∑ t, ga0 i j r * (ga0 l r t * f t k1))
          + ig k1 l * (∑ r, ∑ t, ga0 i j r * (ga0 l k1 t * f r t))
          + ig k1 l * (∑ r, ∑ t, ga0 i k1 r * (ga0 l j t * f t r))
          + ig k1 l * (∑ r, ∑ t, ga0 i k1 r * (ga0 l r t * f j t))
          - ig k1 l * (∑ r, dga0 j i l r * f r k1)
          - ig k1 l * (∑ r, dga0 j k1 l r * f i r)
          + ig k1 l * (∑ r, ∑ t, ga0 j l r * (ga0 r i t * f t k1))
          + ig k1 l * (∑ r, ∑ t, ga0 j l r * (ga0 r k1 t * f i t))
          + ig k1 l * (∑ r, ∑ t, ga0 j i r * (ga0 l r t * f t k1))
          + ig k1 l * (∑ r, ∑ t, ga0 j i r * (ga0 l k1 t * f r t))
          + ig k1 l * (∑ r, ∑ t, ga0 j k1 r * (ga0 l i t * f t r))
          + ig k1 l * (∑ r, ∑ t, ga0 j k1 r * (ga0 l r t * f i t))
          + ig k1 l * (∑ r, dga0 i l j r * f r k1)
          + ig k1 l * (∑ r, dga0 i k1 j r * f l r)
          - ig k1 l * (∑ r, ∑ t, ga0 i j r * (ga0 r l t * f t k1))
          - ig k1 l * (∑ r, ∑ t, ga0 i j r * (ga0 r k1 t * f l t))
          - ig k1 l * (∑ r, ∑ t, ga0 i l r * (ga0 j r t * f t k1))
          - ig k1 l * (∑ r, ∑ t, ga0 i l r * (ga0 j k1 t * f r t))
          - ig k1 l * (∑ r, ∑ t, ga0 i k1 r * (ga0 j l t * f t r))
          - ig k1 l * (∑ r, ∑ t, ga0 i k1 r * (ga0 j r t * f l t)) := by
    intro k1 l
    simp only [r4hB]
    ring
  rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun l _ => hcomb k1 l))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have ht1 : (∑ k1, ∑ l, ig k1 l * (∑ r, dga0 i j l r * f r k1)) =
      (∑ a, ∑ b, ∑ c, dga0 i j a b * f b c * ig a c) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun k1 _ => ?_)))
    rw [higs k1 l]
    ring

  have ht2 : (∑ k1, ∑ l, ig k1 l * (∑ r, dga0 i k1 l r * f j r)) =
      (∑ a, ∑ b, ∑ c, dga0 i a b c * f j c * ig a b) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => ?_)))
    ring

  have ht3 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i l r * (ga0 r j t * f t k1))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c d * ga0 j d a * ig b c) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => ?_))))
    rw [hga0s r j t]
    ring

  have ht4 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i l r * (ga0 r k1 t * f j t))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b c * ga0 c d a * ig b d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun k1 _ => ?_))))
    rw [higs k1 l]
    ring

  have ht5 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i j r * (ga0 l r t * f t k1))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j c * ga0 c d a * ig b d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun l _ => ?_))))
    rw [hga0s l r t]
    ring

  have ht6 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i j r * (ga0 l k1 t * f r t))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun l _ => ?_))))
    rw [hga0s l k1 t]
    ring

  have ht7 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i k1 r * (ga0 l j t * f t r))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun l _ => ?_))))
    rw [hga0s l j t, hfs t r]
    ring

  have ht8 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i k1 r * (ga0 l r t * f j t))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b c * ga0 c d a * ig b d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun l _ => ?_))))
    rw [hga0s l r t]
    ring

  have ht9 : (∑ k1, ∑ l, ig k1 l * (∑ r, dga0 j i l r * f r k1)) =
      (∑ a, ∑ b, ∑ c, dga0 j i a b * f b c * ig a c) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun k1 _ => ?_)))
    rw [higs k1 l]
    ring

  have ht10 : (∑ k1, ∑ l, ig k1 l * (∑ r, dga0 j k1 l r * f i r)) =
      (∑ a, ∑ b, ∑ c, dga0 j a b c * f i c * ig a b) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => ?_)))
    ring

  have ht11 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 j l r * (ga0 r i t * f t k1))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d c * ig b d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun l _ => ?_))))
    rw [hga0s r i t]
    ring

  have ht12 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 j l r * (ga0 r k1 t * f i t))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b c * ga0 c d a * ig b d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun k1 _ => ?_))))
    rw [higs k1 l]
    ring

  have ht13 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 j i r * (ga0 l r t * f t k1))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j c * ga0 c d a * ig b d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun l _ => ?_))))
    rw [hga0s j i r, hga0s l r t]
    ring

  have ht14 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 j i r * (ga0 l k1 t * f r t))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun l _ => ?_))))
    rw [hga0s j i r, hga0s l k1 t]
    ring

  have ht15 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 j k1 r * (ga0 l i t * f t r))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k1 _ => ?_))))
    rw [higs k1 l, hga0s l i t]
    ring

  have ht16 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 j k1 r * (ga0 l r t * f i t))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b c * ga0 c d a * ig b d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun l _ => ?_))))
    rw [hga0s l r t]
    ring

  have ht17 : (∑ k1, ∑ l, ig k1 l * (∑ r, dga0 i l j r * f r k1)) =
      (∑ a, ∑ b, ∑ c, dga0 i j a b * f b c * ig a c) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun k1 _ => ?_)))
    rw [higs k1 l, hdga0s i l j r]
    ring

  have ht18 : (∑ k1, ∑ l, ig k1 l * (∑ r, dga0 i k1 j r * f l r)) =
      (∑ a, ∑ b, ∑ c, dga0 i j a b * f b c * ig a c) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun l _ => ?_)))
    rw [hdga0s i k1 j r, hfs l r]
    ring

  have ht19 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i j r * (ga0 r l t * f t k1))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j c * ga0 c d a * ig b d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun l _ => ?_))))
    ring

  have ht20 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i j r * (ga0 r k1 t * f l t))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j c * ga0 c d a * ig b d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun k1 _ => ?_))))
    rw [higs k1 l, hfs l t]
    ring

  have ht21 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i l r * (ga0 j r t * f t k1))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c d * ga0 j d a * ig b c) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => ?_))))
    ring

  have ht22 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i l r * (ga0 j k1 t * f r t))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k1 _ => ?_))))
    rw [higs k1 l]
    ring

  have ht23 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i k1 r * (ga0 j l t * f t r))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun l _ => ?_))))
    rw [hfs t r]
    ring

  have ht24 : (∑ k1, ∑ l, ig k1 l * (∑ r, ∑ t, ga0 i k1 r * (ga0 j r t * f l t))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c d * ga0 j d a * ig b c) := by
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ _))]
    rw [Finset.sum_congr rfl (fun k1 (_ : k1 ∈ Finset.univ) => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => Finset.mul_sum _ _ _)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun r _ => ?_))))
    rw [higs k1 l, hfs l t]
    ring
  rw [ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10, ht11, ht12, ht13, ht14, ht15,
    ht16, ht17, ht18, ht19, ht20, ht21, ht22, ht23, ht24]
  ring

end Defs

end M0Abstract

end M0AbstractLayer
end

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
