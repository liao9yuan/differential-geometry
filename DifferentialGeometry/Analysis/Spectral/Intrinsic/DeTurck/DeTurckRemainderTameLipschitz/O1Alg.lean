import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Order-one index-algebra normal forms (`O1Abstract`)

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

namespace O1Abstract

variable {n : ℕ}

private lemma o1_sum_ite (g : Fin n → ℝ) (p : Fin n) :
    (∑ q : Fin n, g q * (if p = q then (1 : ℝ) else 0)) = g p := by
  rw [Finset.sum_eq_single p]
  · rw [if_pos rfl, mul_one]
  · intro q _ hq
    rw [if_neg (fun h => hq h.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ p) h

private lemma o1_sink4 (F : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n, ∑ q : Fin n, F k₁ p l₁ m q)
    = ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n, ∑ q : Fin n, ∑ k₁ : Fin n, F k₁ p l₁ m q := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l₁ _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_comm]

private lemma o1_sink4mid (F : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n, ∑ q : Fin n, F k₁ p l₁ m q)
    = ∑ k₁ : Fin n, ∑ p : Fin n, ∑ m : Fin n, ∑ q : Fin n, ∑ l₁ : Fin n, F k₁ p l₁ m q := by
  refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_comm]

section Collapses

variable (ig cg : Fin n → Fin n → ℝ)

private lemma o1_col2
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a) (p q : Fin n) :
    (∑ k : Fin n, ig k p * cg q k) = if p = q then (1 : ℝ) else 0 := by
  rw [show (∑ k : Fin n, ig k p * cg q k) = ∑ k : Fin n, cg k q * ig k p from
    Finset.sum_congr rfl (fun k _ => by rw [hcgs q k]; ring)]
  exact hcol p q

private lemma o1_col3
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (higs : ∀ a b : Fin n, ig a b = ig b a) (q c : Fin n) :
    (∑ l : Fin n, ig q l * cg l c) = if q = c then (1 : ℝ) else 0 := by
  rw [show (∑ l : Fin n, ig q l * cg l c) = ∑ l : Fin n, cg l c * ig l q from
    Finset.sum_congr rfl (fun l _ => by rw [higs q l]; ring)]
  exact hcol q c

private lemma o1_col4
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a) (l m : Fin n) :
    (∑ c : Fin n, cg l c * ig c m) = if m = l then (1 : ℝ) else 0 := by
  rw [show (∑ c : Fin n, cg l c * ig c m) = ∑ c : Fin n, cg c l * ig c m from
    Finset.sum_congr rfl (fun c _ => by rw [hcgs l c])]
  exact hcol m l

end Collapses

section QuadCollapse

variable (ig cg : Fin n → Fin n → ℝ) (g1 g0 : Fin n → Fin n → Fin n → ℝ)
    (X : Fin n → Fin n → ℝ)

private lemma o1_quadAC
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a) (v : Fin n) :
    (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
      ig k₁ p * (ig l₁ m * (X m p * (∑ q : Fin n, (g1 l₁ v q - g0 l₁ v q) * cg q k₁))))
    = (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a v c * X b c))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a v c * X b c)) := by
  have hpt : ∀ k₁ p l₁ m : Fin n,
      ig k₁ p * (ig l₁ m * (X m p * (∑ q : Fin n, (g1 l₁ v q - g0 l₁ v q) * cg q k₁)))
      = ∑ q : Fin n,
          (ig l₁ m * ((g1 l₁ v q - g0 l₁ v q) * X m p)) * (ig k₁ p * cg q k₁) := by
    intro k₁ p l₁ m
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  rw [Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
    Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => hpt k₁ p l₁ m))))]
  rw [o1_sink4 (fun k₁ p l₁ m q =>
    (ig l₁ m * ((g1 l₁ v q - g0 l₁ v q) * X m p)) * (ig k₁ p * cg q k₁))]
  have hcolpt : ∀ p l₁ m q : Fin n,
      (∑ k₁ : Fin n,
        (ig l₁ m * ((g1 l₁ v q - g0 l₁ v q) * X m p)) * (ig k₁ p * cg q k₁))
      = (ig l₁ m * ((g1 l₁ v q - g0 l₁ v q) * X m p)) * (if p = q then (1 : ℝ) else 0) := by
    intro p l₁ m q
    rw [← Finset.mul_sum, o1_col2 ig cg hcol hcgs p q]
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun l₁ _ =>
    Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun q _ => hcolpt p l₁ m q))))]
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun l₁ _ =>
    Finset.sum_congr rfl (fun m _ =>
      o1_sum_ite (fun q => ig l₁ m * ((g1 l₁ v q - g0 l₁ v q) * X m p)) p)))]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun l₁ _ => Finset.sum_comm)]
  rw [show (∑ l₁ : Fin n, ∑ m : Fin n, ∑ p : Fin n,
      ig l₁ m * ((g1 l₁ v p - g0 l₁ v p) * X m p))
    = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
        (ig a b * (g1 a v c * X b c) - ig a b * (g0 a v c * X b c)) from
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun c _ => by ring)))]
  simp only [Finset.sum_sub_distrib]

private lemma o1_quadB
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a) (v : Fin n) :
    (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
      ig k₁ p * (ig l₁ m * (X m p * (∑ q : Fin n, (g1 k₁ v q - g0 k₁ v q) * cg q l₁))))
    = (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a v c * X c b))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a v c * X c b)) := by
  have hpt : ∀ k₁ p l₁ m : Fin n,
      ig k₁ p * (ig l₁ m * (X m p * (∑ q : Fin n, (g1 k₁ v q - g0 k₁ v q) * cg q l₁)))
      = ∑ q : Fin n,
          (ig k₁ p * ((g1 k₁ v q - g0 k₁ v q) * X m p)) * (ig l₁ m * cg q l₁) := by
    intro k₁ p l₁ m
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  rw [Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
    Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => hpt k₁ p l₁ m))))]
  rw [o1_sink4mid (fun k₁ p l₁ m q =>
    (ig k₁ p * ((g1 k₁ v q - g0 k₁ v q) * X m p)) * (ig l₁ m * cg q l₁))]
  have hcolpt : ∀ k₁ p m q : Fin n,
      (∑ l₁ : Fin n,
        (ig k₁ p * ((g1 k₁ v q - g0 k₁ v q) * X m p)) * (ig l₁ m * cg q l₁))
      = (ig k₁ p * ((g1 k₁ v q - g0 k₁ v q) * X m p)) * (if m = q then (1 : ℝ) else 0) := by
    intro k₁ p m q
    rw [← Finset.mul_sum, o1_col2 ig cg hcol hcgs m q]
  rw [Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
    Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun q _ => hcolpt k₁ p m q))))]
  rw [Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
    Finset.sum_congr rfl (fun m _ =>
      o1_sum_ite (fun q => ig k₁ p * ((g1 k₁ v q - g0 k₁ v q) * X m p)) m)))]
  rw [show (∑ k₁ : Fin n, ∑ p : Fin n, ∑ m : Fin n,
      ig k₁ p * ((g1 k₁ v m - g0 k₁ v m) * X m p))
    = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
        (ig a b * (g1 a v c * X c b) - ig a b * (g0 a v c * X c b)) from
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun c _ => by ring)))]
  simp only [Finset.sum_sub_distrib]

end QuadCollapse

end O1Abstract

namespace O1Abstract

variable {n : ℕ}

private lemma o1_sum_ite2 (g : Fin n → ℝ) (p : Fin n) :
    (∑ q : Fin n, (if q = p then (1 : ℝ) else 0) * g q) = g p := by
  rw [Finset.sum_eq_single p]
  · rw [if_pos rfl, one_mul]
  · intro q _ hq
    rw [if_neg hq, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ p) h

section EFshapes

variable (ig : Fin n → Fin n → ℝ) (g1 g0 : Fin n → Fin n → Fin n → ℝ)
    (f3 : Fin n → Fin n → Fin n → ℝ)

private lemma o1_pullE (u v : Fin n) :
    (∑ k : Fin n, ∑ p : Fin n, ig k p * (∑ q : Fin n, (g1 u v q - g0 u v q) * f3 p q k))
    = (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g1 u v q * f3 p q k))
      - (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g0 u v q * f3 p q k)) := by
  rw [show (∑ k : Fin n, ∑ p : Fin n, ig k p * (∑ q : Fin n, (g1 u v q - g0 u v q) * f3 p q k))
      = ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n,
          (ig k p * (g1 u v q * f3 p q k) - ig k p * (g0 u v q * f3 p q k)) from
    Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun p _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun q _ => by ring)))]
  simp only [Finset.sum_sub_distrib]

private lemma o1_pullF (u v : Fin n) :
    (∑ k : Fin n, ∑ p : Fin n, ig k p * (∑ q : Fin n, (g1 u v q - g0 u v q) * f3 q p k))
    = (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g1 u v q * f3 q p k))
      - (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g0 u v q * f3 q p k)) := by
  rw [show (∑ k : Fin n, ∑ p : Fin n, ig k p * (∑ q : Fin n, (g1 u v q - g0 u v q) * f3 q p k))
      = ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n,
          (ig k p * (g1 u v q * f3 q p k) - ig k p * (g0 u v q * f3 q p k)) from
    Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun p _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun q _ => by ring)))]
  simp only [Finset.sum_sub_distrib]

private lemma o1_swapE (ga : Fin n → Fin n → Fin n → ℝ)
    (hgas : ∀ a b k : Fin n, ga a b k = ga b a k) (u v : Fin n) :
    (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (ga u v q * f3 p q k))
    = ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (ga v u q * f3 p q k) :=
  Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun p _ =>
    Finset.sum_congr rfl (fun q _ => by rw [hgas u v q])))

private lemma o1_swapF (ga : Fin n → Fin n → Fin n → ℝ)
    (hgas : ∀ a b k : Fin n, ga a b k = ga b a k) (u v : Fin n) :
    (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (ga u v q * f3 q p k))
    = ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (ga v u q * f3 q p k) :=
  Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun p _ =>
    Finset.sum_congr rfl (fun q _ => by rw [hgas u v q])))

private lemma o1_vf0exp (u v : Fin n) :
    (∑ w : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * (g1 a b w - g0 a b w)) * f3 u v w)
    = (∑ a : Fin n, ∑ b : Fin n, ∑ w : Fin n, ig a b * (g1 a b w * f3 u v w))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ w : Fin n, ig a b * (g0 a b w * f3 u v w)) := by
  rw [show (∑ w : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * (g1 a b w - g0 a b w)) * f3 u v w)
      = ∑ w : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          (ig a b * (g1 a b w * f3 u v w) - ig a b * (g0 a b w * f3 u v w)) from
    Finset.sum_congr rfl (fun w _ => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun a _ => by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun b _ => by ring)))]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  simp only [Finset.sum_sub_distrib]

end EFshapes

section DerivedHyps

private lemma o1_hgb2 (ig cg : Fin n → Fin n → ℝ) (gb g1 : Fin n → Fin n → Fin n → ℝ)
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a)
    (hga1 : ∀ a b k : Fin n, g1 a b k = (1 / 2 : ℝ) * ∑ l : Fin n, ig k l * gb a b l)
    (a b l : Fin n) :
    gb a b l = 2 * ∑ c : Fin n, cg l c * g1 a b c := by
  have h1 : (∑ c : Fin n, cg l c * g1 a b c)
      = ∑ c : Fin n, ∑ m : Fin n, (cg l c * ig c m) * ((1 / 2 : ℝ) * gb a b m) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [hga1 a b c, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  have h2 : (∑ c : Fin n, ∑ m : Fin n, (cg l c * ig c m) * ((1 / 2 : ℝ) * gb a b m))
      = ∑ m : Fin n, (if m = l then (1 : ℝ) else 0) * ((1 / 2 : ℝ) * gb a b m) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← Finset.sum_mul, o1_col4 ig cg hcol hcgs l m]
  rw [h1, h2, o1_sum_ite2 (fun m => (1 / 2 : ℝ) * gb a b m) l]
  ring

private lemma o1_hdg2 (ig cg : Fin n → Fin n → ℝ) (dg gb g1 : Fin n → Fin n → Fin n → ℝ)
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a)
    (hgbdef : ∀ a b l : Fin n, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgs : ∀ m a b : Fin n, dg m a b = dg m b a)
    (hga1 : ∀ a b k : Fin n, g1 a b k = (1 / 2 : ℝ) * ∑ l : Fin n, ig k l * gb a b l)
    (m u v : Fin n) :
    dg m u v = (∑ c : Fin n, cg v c * g1 m u c) + (∑ c : Fin n, cg u c * g1 m v c) := by
  have h1 : dg m u v = (1 / 2 : ℝ) * (gb m u v + gb m v u) := by
    rw [hgbdef m u v, hgbdef m v u, hdgs m v u, hdgs u v m, hdgs v u m]
    ring
  rw [h1, o1_hgb2 ig cg gb g1 hcol hcgs hga1 m u v,
    o1_hgb2 ig cg gb g1 hcol hcgs hga1 m v u]
  ring

private lemma o1_hdig2 (ig cg : Fin n → Fin n → ℝ) (dg gb dig g1 : Fin n → Fin n → Fin n → ℝ)
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a)
    (hgbdef : ∀ a b l : Fin n, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgs : ∀ m a b : Fin n, dg m a b = dg m b a)
    (hga1 : ∀ a b k : Fin n, g1 a b k = (1 / 2 : ℝ) * ∑ l : Fin n, ig k l * gb a b l)
    (hdig : ∀ m a b : Fin n, dig m a b
      = -(∑ x : Fin n, ∑ y : Fin n, ig a x * ig y b * dg m x y))
    (m a b : Fin n) :
    dig m a b = -(∑ p : Fin n, (ig a p * g1 m p b + ig p b * g1 m p a)) := by
  have hsub : ∀ x y : Fin n, ig a x * ig y b * dg m x y
      = (∑ c : Fin n, (ig a x * g1 m x c) * (cg y c * ig y b))
        + ∑ c : Fin n, (ig y b * g1 m y c) * (ig a x * cg x c) := by
    intro x y
    rw [o1_hdg2 ig cg dg gb g1 hcol hcgs hgbdef hdgs hga1 m x y]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl (fun c _ => by ring)
    · exact Finset.sum_congr rfl (fun c _ => by ring)
  have h0 : (∑ x : Fin n, ∑ y : Fin n, ig a x * ig y b * dg m x y)
      = (∑ x : Fin n, ∑ y : Fin n, ∑ c : Fin n, (ig a x * g1 m x c) * (cg y c * ig y b))
        + ∑ x : Fin n, ∑ y : Fin n, ∑ c : Fin n, (ig y b * g1 m y c) * (ig a x * cg x c) := by
    rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hsub x y))]
    simp only [Finset.sum_add_distrib]
  have hP1 : (∑ x : Fin n, ∑ y : Fin n, ∑ c : Fin n, (ig a x * g1 m x c) * (cg y c * ig y b))
      = ∑ p : Fin n, ig a p * g1 m p b := by
    have e1 : ∀ x : Fin n,
        (∑ y : Fin n, ∑ c : Fin n, (ig a x * g1 m x c) * (cg y c * ig y b))
        = ∑ c : Fin n, (ig a x * g1 m x c) * (if b = c then (1 : ℝ) else 0) := by
      intro x
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [← Finset.mul_sum, hcol b c]
    rw [Finset.sum_congr rfl (fun x _ => e1 x)]
    exact Finset.sum_congr rfl (fun x _ => o1_sum_ite (fun c => ig a x * g1 m x c) b)
  have hP2 : (∑ x : Fin n, ∑ y : Fin n, ∑ c : Fin n, (ig y b * g1 m y c) * (ig a x * cg x c))
      = ∑ p : Fin n, ig p b * g1 m p a := by
    have e2 : ∀ y c : Fin n, (∑ x : Fin n, (ig y b * g1 m y c) * (ig a x * cg x c))
        = (ig y b * g1 m y c) * (if a = c then (1 : ℝ) else 0) := by
      intro y c
      rw [← Finset.mul_sum, o1_col3 ig cg hcol higs a c]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun y _ => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun c _ => e2 y c))]
    exact Finset.sum_congr rfl (fun y _ => o1_sum_ite (fun c => ig y b * g1 m y c) a)
  rw [hdig m a b, h0, hP1, hP2, ← Finset.sum_add_distrib]

end DerivedHyps

end O1Abstract

namespace O1Abstract

variable {n : ℕ}

private lemma o1_neg_push (c d : ℝ) (P : Fin n → Fin n → ℝ) :
    c * ((-(∑ q : Fin n, ∑ p : Fin n, P q p)) * d)
    = ∑ q : Fin n, ∑ p : Fin n, -(P q p * (d * c)) := by
  rw [show c * ((-(∑ q : Fin n, ∑ p : Fin n, P q p)) * d)
      = -((∑ q : Fin n, ∑ p : Fin n, P q p) * (d * c)) from by ring]
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]

private lemma o1_neg_push1 (t : ℝ) (P : Fin n → Fin n → ℝ) :
    (-(∑ q : Fin n, ∑ p : Fin n, P q p)) * t
    = ∑ q : Fin n, ∑ p : Fin n, -(P q p * t) := by
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]

private lemma o1_sum_ite' (g : Fin n → ℝ) (p : Fin n) :
    (∑ q : Fin n, g q * (if q = p then (1 : ℝ) else 0)) = g p := by
  rw [Finset.sum_eq_single p]
  · rw [if_pos rfl, mul_one]
  · intro q _ hq
    rw [if_neg hq, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ p) h

private lemma o1_neg_push3 (c d : ℝ) (X : Fin n → ℝ) :
    c * (d * (-(∑ q : Fin n, X q))) = ∑ q : Fin n, -(X q * (d * c)) := by
  rw [show c * (d * (-(∑ q : Fin n, X q))) = -((∑ q : Fin n, X q) * (d * c)) from by ring]
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]

section RQ3

variable (ig cg : Fin n → Fin n → ℝ) (g1 g0 f3 : Fin n → Fin n → Fin n → ℝ)

private lemma o1_rq3
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hf3s : ∀ d a b : Fin n, f3 d a b = f3 d b a) (u v : Fin n) :
    (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n,
      (-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u p q * ig q b)) * (g1 a b k - g0 a b k)))
    = -(∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
        ig k₁ p * (ig l₁ m * (f3 u m p * (∑ q : Fin n, (g1 k₁ l₁ q - g0 k₁ l₁ q) * cg q v)))) := by
  have hflat : (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n,
      (-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u p q * ig q b)) * (g1 a b k - g0 a b k)))
      = ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ q : Fin n, ∑ p : Fin n,
          -((ig a p * f3 u p q * ig q b) * ((g1 a b k - g0 a b k) * cg k v)) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    exact o1_neg_push (cg k v) (g1 a b k - g0 a b k) (fun q p => ig a p * f3 u p q * ig q b)
  rw [hflat]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun q _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  have hrhs : (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
      ig k₁ p * (ig l₁ m * (f3 u m p * (∑ q : Fin n, (g1 k₁ l₁ q - g0 k₁ l₁ q) * cg q v))))
      = ∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n, ∑ q : Fin n,
          ig k₁ p * (ig l₁ m * (f3 u m p * ((g1 k₁ l₁ q - g0 k₁ l₁ q) * cg q v))) := by
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [hrhs]
  simp only [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ =>
    Finset.sum_congr rfl (fun x3 _ => Finset.sum_congr rfl (fun x4 _ =>
      Finset.sum_congr rfl (fun x5 _ => ?_)))))
  rw [higs x4 x3, hf3s u x2 x4]
  ring

end RQ3

section RG7

variable (ig cg : Fin n → Fin n → ℝ) (gb g1 f3 : Fin n → Fin n → Fin n → ℝ)

private lemma o1_rg7
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hgb2 : ∀ a b l : Fin n, gb a b l = 2 * ∑ c : Fin n, cg l c * g1 a b c)
    (u v : Fin n) :
    (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
      ∑ l : Fin n, (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u p q * ig q l)) * gb a b l)))
    = -(∑ a : Fin n, ∑ b : Fin n, ∑ w : Fin n, ig a b * (g1 a b w * f3 u v w)) := by
  have hinner : ∀ k a b : Fin n,
      ((1 / 2 : ℝ) * ∑ l : Fin n,
        (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u p q * ig q l)) * gb a b l)
      = -(∑ q : Fin n, (∑ p : Fin n, ig k p * f3 u p q) * g1 a b q) := by
    intro k a b
    have hpt1 : ∀ l : Fin n,
        (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u p q * ig q l)) * gb a b l
        = ∑ c : Fin n, ∑ q : Fin n, ∑ p : Fin n,
            ((-2 : ℝ) * ((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c) := by
      intro l
      rw [hgb2 a b l]
      rw [show (2 : ℝ) * ∑ c : Fin n, cg l c * g1 a b c
          = ∑ c : Fin n, 2 * (cg l c * g1 a b c) from Finset.mul_sum _ _ _]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [o1_neg_push1 (2 * (cg l c * g1 a b c)) (fun q p => ig k p * f3 u p q * ig q l)]
      refine Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => ?_))
      ring
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun l _ => congrArg (HMul.hMul (1 / 2 : ℝ)) (hpt1 l))]
    have hro : (∑ l : Fin n, (1 / 2 : ℝ) * ∑ c : Fin n, ∑ q : Fin n, ∑ p : Fin n,
        ((-2 : ℝ) * ((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c))
        = ∑ c : Fin n, ∑ q : Fin n, ∑ p : Fin n, ∑ l : Fin n,
            (1 / 2 : ℝ) * (((-2 : ℝ) * ((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c)) := by
      rw [show (∑ l : Fin n, (1 / 2 : ℝ) * ∑ c : Fin n, ∑ q : Fin n, ∑ p : Fin n,
          ((-2 : ℝ) * ((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c))
          = ∑ l : Fin n, ∑ c : Fin n, ∑ q : Fin n, ∑ p : Fin n,
              (1 / 2 : ℝ) * (((-2 : ℝ) * ((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c)) from
        Finset.sum_congr rfl (fun l _ => by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun q _ => ?_)
          rw [Finset.mul_sum])]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [Finset.sum_comm]
    rw [hro]
    have hcolstep : ∀ c q p : Fin n,
        (∑ l : Fin n, (1 / 2 : ℝ) *
          (((-2 : ℝ) * ((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c)))
        = (-((ig k p * f3 u p q) * g1 a b c)) * (if q = c then (1 : ℝ) else 0) := by
      intro c q p
      rw [show (∑ l : Fin n, (1 / 2 : ℝ) *
          (((-2 : ℝ) * ((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c)))
          = ∑ l : Fin n, (-((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c) from
        Finset.sum_congr rfl (fun l _ => by ring)]
      rw [← Finset.mul_sum, o1_col3 ig cg hcol higs q c]
    rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun q _ =>
      Finset.sum_congr rfl (fun p _ => hcolstep c q p)))]
    have hite : (∑ c : Fin n, ∑ q : Fin n, ∑ p : Fin n,
        (-((ig k p * f3 u p q) * g1 a b c)) * (if q = c then (1 : ℝ) else 0))
        = ∑ q : Fin n, ∑ p : Fin n, -((ig k p * f3 u p q) * g1 a b q) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      exact o1_sum_ite (fun c => -((ig k p * f3 u p q) * g1 a b c)) q
    rw [hite]
    rw [show (∑ q : Fin n, ∑ p : Fin n, -((ig k p * f3 u p q) * g1 a b q))
        = ∑ q : Fin n, -((∑ p : Fin n, ig k p * f3 u p q) * g1 a b q) from
      Finset.sum_congr rfl (fun q _ => by
        rw [Finset.sum_neg_distrib, ← Finset.sum_mul])]
    rw [← Finset.sum_neg_distrib]
  rw [Finset.sum_congr rfl (fun k _ => congrArg (HMul.hMul (cg k v))
    (Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      congrArg (HMul.hMul (ig a b)) (hinner k a b)))))]
  have hflat2 : (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n,
      ig a b * (-(∑ q : Fin n, (∑ p : Fin n, ig k p * f3 u p q) * g1 a b q))))
      = ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ q : Fin n, ∑ p : Fin n,
          (-((f3 u p q * (ig a b * g1 a b q))) * (cg k v * ig k p)) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [o1_neg_push3 (cg k v) (ig a b)
      (fun q => (∑ p : Fin n, ig k p * f3 u p q) * g1 a b q)]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [show -((∑ p : Fin n, ig k p * f3 u p q) * g1 a b q * (ig a b * cg k v))
        = ∑ p : Fin n, -((f3 u p q * (ig a b * g1 a b q)) * (cg k v * ig k p)) from by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun p _ => by ring)]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [hflat2]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun q _ => Finset.sum_comm)))]
  have hcolk : ∀ a b q p : Fin n,
      (∑ k : Fin n, (-((f3 u p q * (ig a b * g1 a b q))) * (cg k v * ig k p)))
      = (-((f3 u p q * (ig a b * g1 a b q)))) * (if p = v then (1 : ℝ) else 0) := by
    intro a b q p
    rw [← Finset.mul_sum, hcol p v]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => hcolk a b q p))))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun q _ =>
      o1_sum_ite' (fun p => -((f3 u p q * (ig a b * g1 a b q)))) v)))]
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ q : Fin n, -((f3 u v q * (ig a b * g1 a b q))))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ q : Fin n, -(ig a b * (g1 a b q * f3 u v q)) from
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun q _ => by ring)))]
  simp only [Finset.sum_neg_distrib]

end RG7

end O1Abstract

namespace O1Abstract

variable {n : ℕ}

private lemma o1_neg_push1d (t : ℝ) (P : Fin n → ℝ) :
    (-(∑ p : Fin n, P p)) * t = ∑ p : Fin n, -(P p * t) := by
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]

private lemma o1_sum3_add (F G : Fin n → Fin n → Fin n → ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, F a b c)
      + (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, G a b c)
    = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, (F a b c + G a b c) := by
  simp only [Finset.sum_add_distrib]

private lemma o1_abswap3 (H : Fin n → Fin n → Fin n → ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n, H a b p)
    = ∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n, H b a p :=
  Finset.sum_comm

private lemma o1_abswap5 (H : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, H k a b l p)
    = ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, H k b a l p :=
  Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)

section RF1

variable (ig cg : Fin n → Fin n → ℝ) (dig g1 f3 : Fin n → Fin n → Fin n → ℝ)

private lemma o1_rf1a
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hf3s : ∀ d a b : Fin n, f3 d a b = f3 d b a)
    (hg1s : ∀ a b k : Fin n, g1 a b k = g1 b a k)
    (hdig2 : ∀ m a b : Fin n, dig m a b
      = -(∑ p : Fin n, (ig a p * g1 m p b + ig p b * g1 m p a)))
    (u v : Fin n) :
    (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n, dig u a b * ((1 / 2 : ℝ) *
      ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b))))
    = -(∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a u c * f3 b v c))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a u c * f3 c v b))
      + (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a u c * f3 v b c)) := by
  have hflat : (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n, dig u a b * ((1 / 2 : ℝ) *
      ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b))))
      = ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n,
          (dig u a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * (cg k v * ig k l) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [hflat]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
  have hcolk : ∀ a b l : Fin n,
      (∑ k : Fin n,
        (dig u a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * (cg k v * ig k l))
      = (dig u a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b)))
          * (if l = v then (1 : ℝ) else 0) := by
    intro a b l
    rw [← Finset.mul_sum, hcol l v]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun l _ => hcolk a b l)))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    o1_sum_ite' (fun l => dig u a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) v))]
  have h2 : ∀ a b : Fin n,
      dig u a b * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b))
      = ∑ p : Fin n,
          (-((ig a p * g1 u p b) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b)))
           + -((ig p b * g1 u p a) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b)))) := by
    intro a b
    rw [hdig2 u a b, o1_neg_push1d ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b))
      (fun p => ig a p * g1 u p b + ig p b * g1 u p a)]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => h2 a b))]
  simp only [Finset.sum_add_distrib]
  have hmerge : (∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n,
      -((ig p b * g1 u p a) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b))))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n,
          -((ig a p * g1 u p b) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b))) := by
    rw [o1_abswap3 (fun a b p =>
      -((ig p b * g1 u p a) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b))))]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun p _ => ?_)))
    rw [higs p a, hf3s v b a]
    ring
  rw [hmerge]
  rw [o1_sum3_add
    (fun a b p => -((ig a p * g1 u p b) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b))))
    (fun a b p => -((ig a p * g1 u p b) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b))))]
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n,
      (-((ig a p * g1 u p b) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b)))
       + -((ig a p * g1 u p b) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b)))))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n,
          ((-((ig a p * g1 u p b) * f3 a v b) + -((ig a p * g1 u p b) * f3 b v a))
           + (ig a p * g1 u p b) * f3 v a b) from
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun p _ => by ring)))]
  simp only [Finset.sum_add_distrib]
  have hT1 : (∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n, -((ig a p * g1 u p b) * f3 a v b))
      = -(∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a u c * f3 b v c)) := by
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [show (∑ p : Fin n, ∑ a : Fin n, ∑ b : Fin n, -((ig a p * g1 u p b) * f3 a v b))
        = ∑ p : Fin n, ∑ a : Fin n, ∑ b : Fin n, -(ig p a * (g1 p u b * f3 a v b)) from
      Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun a _ =>
        Finset.sum_congr rfl (fun b _ => by rw [higs a p, hg1s u p b]; ring)))]
    simp only [Finset.sum_neg_distrib]
  have hT2 : (∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n, -((ig a p * g1 u p b) * f3 b v a))
      = -(∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a u c * f3 c v b)) := by
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [show (∑ p : Fin n, ∑ a : Fin n, ∑ b : Fin n, -((ig a p * g1 u p b) * f3 b v a))
        = ∑ p : Fin n, ∑ a : Fin n, ∑ b : Fin n, -(ig p a * (g1 p u b * f3 b v a)) from
      Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun a _ =>
        Finset.sum_congr rfl (fun b _ => by rw [higs a p, hg1s u p b]; ring)))]
    simp only [Finset.sum_neg_distrib]
  have hT3 : (∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n, (ig a p * g1 u p b) * f3 v a b)
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a u c * f3 v b c) := by
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun a _ =>
      Finset.sum_congr rfl (fun b _ => by rw [higs a p, hg1s u p b]; ring)))
  rw [hT1, hT2, hT3]
  ring

end RF1

end O1Abstract

namespace O1Abstract

variable {n : ℕ}

private lemma o1_const_pull3 (c : ℝ) (X : Fin n → Fin n → Fin n → ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, c * X a b l)
    = c * ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, X a b l := by
  simp only [← Finset.mul_sum]

private lemma o1_const_pull5 (c : ℝ) (X : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n, c * X a b l p k)
    = c * ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n, X a b l p k := by
  simp only [← Finset.mul_sum]

private lemma o1_ftriple3 (f3 : Fin n → Fin n → Fin n → ℝ) (W : Fin n → Fin n → Fin n → ℝ)
    (hW : ∀ a b l : Fin n, W a b l = W b a l) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, W a b l * (f3 a l b + f3 b l a - f3 l a b))
    = 2 * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, W a b l * f3 a l b)
      - (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, W a b l * f3 l a b) := by
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, W a b l * (f3 a l b + f3 b l a - f3 l a b))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n,
          ((W a b l * f3 a l b + W a b l * f3 b l a) - W a b l * f3 l a b) from
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => by ring)))]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hAB : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, W a b l * f3 b l a)
      = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, W a b l * f3 a l b := by
    rw [o1_abswap3 (fun a b l => W a b l * f3 b l a)]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => ?_)))
    rw [hW b a l]
  rw [hAB]
  ring

private lemma o1_ftriple5 (f3 : Fin n → Fin n → Fin n → ℝ)
    (W : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ)
    (hW : ∀ a b l p k : Fin n, W a b l p k = W b a l p k) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
      W a b l p k * (f3 a l b + f3 b l a - f3 l a b))
    = 2 * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        W a b l p k * f3 a l b)
      - (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        W a b l p k * f3 l a b) := by
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
      W a b l p k * (f3 a l b + f3 b l a - f3 l a b))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          ((W a b l p k * f3 a l b + W a b l p k * f3 b l a) - W a b l p k * f3 l a b) from
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun k _ => by ring)))))]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hAB : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
      W a b l p k * f3 b l a)
      = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          W a b l p k * f3 a l b := by
    rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        W a b l p k * f3 b l a)
        = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
            W b a l p k * f3 a l b from Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun k _ => ?_)))))
    rw [hW b a l p k]
  rw [hAB]
  ring

end O1Abstract

namespace O1Abstract

variable {n : ℕ}

section RF1B

variable (ig cg : Fin n → Fin n → ℝ) (dig g1 f3 : Fin n → Fin n → Fin n → ℝ)

private lemma o1_rf1b
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hdig2 : ∀ m a b : Fin n, dig m a b
      = -(∑ p : Fin n, (ig a p * g1 m p b + ig p b * g1 m p a)))
    (u v : Fin n) :
    (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
      ∑ l : Fin n, dig u k l * (f3 a l b + f3 b l a - f3 l a b))))
    = -(∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g1 u v q * f3 p q k))
      + (1 / 2 : ℝ) * (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g1 u v q * f3 q p k))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          ig a b * (ig p l * (f3 a l b * (g1 u p k * cg k v))))
      + (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          ig a b * (ig p l * (f3 l a b * (g1 u p k * cg k v)))) := by
  have hflat : (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
      ∑ l : Fin n, dig u k l * (f3 a l b + f3 b l a - f3 l a b))))
      = ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n,
          ((-((ig a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * g1 u p l))
              * (cg k v * ig k p)
           + -(ig a b * (ig p l * ((1 / 2 : ℝ) *
              ((f3 a l b + f3 b l a - f3 l a b) * (g1 u p k * cg k v)))))) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hdig2 u k l, o1_neg_push1d (f3 a l b + f3 b l a - f3 l a b)
      (fun p => ig k p * g1 u p l + ig p l * g1 u p k)]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [hflat]
  simp only [Finset.sum_add_distrib]
  have hS1 : (∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n,
      (-((ig a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * g1 u p l))
        * (cg k v * ig k p))
      = -(∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g1 u v q * f3 p q k))
        + (1 / 2 : ℝ) * (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n,
            ig k p * (g1 u v q * f3 q p k)) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => Finset.sum_comm)))]
    have hck : ∀ a b l p : Fin n,
        (∑ k : Fin n,
          (-((ig a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * g1 u p l))
            * (cg k v * ig k p))
        = (-((ig a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * g1 u p l))
            * (if p = v then (1 : ℝ) else 0) := by
      intro a b l p
      rw [← Finset.mul_sum, hcol p v]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun p _ => hck a b l p))))]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => o1_sum_ite' (fun p =>
        -((ig a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * g1 u p l)) v)))]
    rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n,
        -((ig a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * g1 u v l))
        = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n,
            (-((1 / 2 : ℝ) * (ig a b * g1 u v l))) * (f3 a l b + f3 b l a - f3 l a b) from
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
        Finset.sum_congr rfl (fun l _ => by ring)))]
    rw [o1_ftriple3 f3 (fun a b l => -((1 / 2 : ℝ) * (ig a b * g1 u v l)))
      (fun a b l => by
        show -((1 / 2 : ℝ) * (ig a b * g1 u v l)) = -((1 / 2 : ℝ) * (ig b a * g1 u v l))
        rw [higs a b])]
    have hE : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n,
        (-((1 / 2 : ℝ) * (ig a b * g1 u v l))) * f3 a l b)
        = (-(1 / 2 : ℝ)) * (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n,
            ig k p * (g1 u v q * f3 p q k)) := by
      rw [Finset.sum_comm]
      rw [show (∑ b : Fin n, ∑ a : Fin n, ∑ l : Fin n,
          (-((1 / 2 : ℝ) * (ig a b * g1 u v l))) * f3 a l b)
          = ∑ b : Fin n, ∑ a : Fin n, ∑ l : Fin n,
              (-(1 / 2 : ℝ)) * (ig b a * (g1 u v l * f3 a l b)) from
        Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ =>
          Finset.sum_congr rfl (fun l _ => by rw [higs a b]; ring)))]
      rw [o1_const_pull3]
    have hF : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n,
        (-((1 / 2 : ℝ) * (ig a b * g1 u v l))) * f3 l a b)
        = (-(1 / 2 : ℝ)) * (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n,
            ig k p * (g1 u v q * f3 q p k)) := by
      rw [Finset.sum_comm]
      rw [show (∑ b : Fin n, ∑ a : Fin n, ∑ l : Fin n,
          (-((1 / 2 : ℝ) * (ig a b * g1 u v l))) * f3 l a b)
          = ∑ b : Fin n, ∑ a : Fin n, ∑ l : Fin n,
              (-(1 / 2 : ℝ)) * (ig b a * (g1 u v l * f3 l a b)) from
        Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ =>
          Finset.sum_congr rfl (fun l _ => by rw [higs a b]; ring)))]
      rw [o1_const_pull3]
    rw [hE, hF]
    ring
  have hS2 : (∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n,
      -(ig a b * (ig p l * ((1 / 2 : ℝ) *
        ((f3 a l b + f3 b l a - f3 l a b) * (g1 u p k * cg k v))))))
      = -(∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          ig a b * (ig p l * (f3 a l b * (g1 u p k * cg k v))))
        + (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          ig a b * (ig p l * (f3 l a b * (g1 u p k * cg k v)))) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => Finset.sum_comm)))]
    rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        -(ig a b * (ig p l * ((1 / 2 : ℝ) *
          ((f3 a l b + f3 b l a - f3 l a b) * (g1 u p k * cg k v))))))
        = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
            (-((1 / 2 : ℝ) * (ig a b * (ig p l * (g1 u p k * cg k v)))))
              * (f3 a l b + f3 b l a - f3 l a b) from
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
        Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun p _ =>
          Finset.sum_congr rfl (fun k _ => by ring)))))]
    rw [o1_ftriple5 f3
      (fun a b l p k => -((1 / 2 : ℝ) * (ig a b * (ig p l * (g1 u p k * cg k v)))))
      (fun a b l p k => by
        show -((1 / 2 : ℝ) * (ig a b * (ig p l * (g1 u p k * cg k v))))
          = -((1 / 2 : ℝ) * (ig b a * (ig p l * (g1 u p k * cg k v))))
        rw [higs a b])]
    have hR1 : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        (-((1 / 2 : ℝ) * (ig a b * (ig p l * (g1 u p k * cg k v))))) * f3 a l b)
        = (-(1 / 2 : ℝ)) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
            ig a b * (ig p l * (f3 a l b * (g1 u p k * cg k v)))) := by
      rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          (-((1 / 2 : ℝ) * (ig a b * (ig p l * (g1 u p k * cg k v))))) * f3 a l b)
          = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
              (-(1 / 2 : ℝ)) * (ig a b * (ig p l * (f3 a l b * (g1 u p k * cg k v)))) from
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
          Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun p _ =>
            Finset.sum_congr rfl (fun k _ => by ring)))))]
      rw [o1_const_pull5]
    have hR2 : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        (-((1 / 2 : ℝ) * (ig a b * (ig p l * (g1 u p k * cg k v))))) * f3 l a b)
        = (-(1 / 2 : ℝ)) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
            ig a b * (ig p l * (f3 l a b * (g1 u p k * cg k v)))) := by
      rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          (-((1 / 2 : ℝ) * (ig a b * (ig p l * (g1 u p k * cg k v))))) * f3 l a b)
          = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
              (-(1 / 2 : ℝ)) * (ig a b * (ig p l * (f3 l a b * (g1 u p k * cg k v)))) from
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
          Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun p _ =>
            Finset.sum_congr rfl (fun k _ => by ring)))))]
      rw [o1_const_pull5]
    rw [hR1, hR2]
    ring
  rw [hS1, hS2]
  ring

end RF1B

private lemma o1_mul_sum_sum (x y : ℝ) (A B : Fin n → ℝ) :
    (x * (y * ∑ l : Fin n, A l)) * (∑ c : Fin n, B c)
    = ∑ l : Fin n, ∑ c : Fin n, (y * (x * B c)) * A l := by
  rw [show (x * (y * ∑ l : Fin n, A l)) * (∑ c : Fin n, B c)
      = (∑ l : Fin n, A l) * (∑ c : Fin n, B c) * (x * y) from by ring]
  rw [Finset.sum_mul_sum]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun c _ => by ring)

section RLVF

variable (ig cg : Fin n → Fin n → ℝ) (dg g1 f3 : Fin n → Fin n → Fin n → ℝ)

private lemma o1_rlvf
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a)
    (hg1s : ∀ a b k : Fin n, g1 a b k = g1 b a k)
    (hdg2 : ∀ m a b : Fin n, dg m a b
      = (∑ c : Fin n, cg b c * g1 m a c) + (∑ c : Fin n, cg a c * g1 m b c))
    (u v : Fin n) :
    (∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
      ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b))) * dg k u v)
    = (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        ig a b * (ig p l * (f3 a l b * (g1 u p k * cg k v))))
      + (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        ig a b * (ig p l * (f3 a l b * (g1 v p k * cg k u))))
      - (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        ig a b * (ig p l * (f3 l a b * (g1 u p k * cg k v))))
      - (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        ig a b * (ig p l * (f3 l a b * (g1 v p k * cg k u)))) := by
  have hsplit : (∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
      ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b))) * dg k u v)
      = (∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
          ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
            * (∑ c : Fin n, cg v c * g1 k u c))
        + ∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
              * (∑ c : Fin n, cg u c * g1 k v c) := by
    rw [show (∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
        ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b))) * dg k u v)
        = ∑ k : Fin n, ((∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
              * (∑ c : Fin n, cg v c * g1 k u c)
           + (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
              * (∑ c : Fin n, cg u c * g1 k v c)) from
      Finset.sum_congr rfl (fun k _ => by rw [hdg2 k u v, mul_add])]
    rw [Finset.sum_add_distrib]
  rw [hsplit]
  have hhalf : ∀ u' v' : Fin n,
      (∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
        ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
          * (∑ c : Fin n, cg v' c * g1 k u' c))
      = (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          ig a b * (ig p l * (f3 a l b * (g1 u' p k * cg k v'))))
        - (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          ig a b * (ig p l * (f3 l a b * (g1 u' p k * cg k v')))) := by
    intro u' v'
    have hflat : (∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
        ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
          * (∑ c : Fin n, cg v' c * g1 k u' c))
        = ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ c : Fin n,
            ((1 / 2 : ℝ) * (ig a b * (ig k l * (cg v' c * g1 k u' c))))
              * (f3 a l b + f3 b l a - f3 l a b) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [o1_mul_sum_sum (ig a b) (1 / 2 : ℝ)
        (fun l => ig k l * (f3 a l b + f3 b l a - f3 l a b))
        (fun c => cg v' c * g1 k u' c)]
      refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun c _ => ?_))
      ring
    rw [hflat]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
    rw [o1_ftriple5 f3
      (fun a b l k c => (1 / 2 : ℝ) * (ig a b * (ig k l * (cg v' c * g1 k u' c))))
      (fun a b l k c => by
        show (1 / 2 : ℝ) * (ig a b * (ig k l * (cg v' c * g1 k u' c)))
          = (1 / 2 : ℝ) * (ig b a * (ig k l * (cg v' c * g1 k u' c)))
        rw [higs a b])]
    have hB1 : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ k : Fin n, ∑ c : Fin n,
        ((1 / 2 : ℝ) * (ig a b * (ig k l * (cg v' c * g1 k u' c)))) * f3 a l b)
        = (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
            ig a b * (ig p l * (f3 a l b * (g1 u' p k * cg k v')))) := by
      rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ k : Fin n, ∑ c : Fin n,
          ((1 / 2 : ℝ) * (ig a b * (ig k l * (cg v' c * g1 k u' c)))) * f3 a l b)
          = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ k : Fin n, ∑ c : Fin n,
              (1 / 2 : ℝ) * (ig a b * (ig k l * (f3 a l b * (g1 u' k c * cg c v')))) from
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
          Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ =>
            Finset.sum_congr rfl (fun c _ => by
              rw [hcgs v' c, hg1s k u' c]; ring)))))]
      rw [o1_const_pull5]
    have hB2 : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ k : Fin n, ∑ c : Fin n,
        ((1 / 2 : ℝ) * (ig a b * (ig k l * (cg v' c * g1 k u' c)))) * f3 l a b)
        = (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
            ig a b * (ig p l * (f3 l a b * (g1 u' p k * cg k v')))) := by
      rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ k : Fin n, ∑ c : Fin n,
          ((1 / 2 : ℝ) * (ig a b * (ig k l * (cg v' c * g1 k u' c)))) * f3 l a b)
          = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ k : Fin n, ∑ c : Fin n,
              (1 / 2 : ℝ) * (ig a b * (ig k l * (f3 l a b * (g1 u' k c * cg c v')))) from
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
          Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ =>
            Finset.sum_congr rfl (fun c _ => by
              rw [hcgs v' c, hg1s k u' c]; ring)))))]
      rw [o1_const_pull5]
    rw [hB1, hB2]
    ring
  rw [hhalf u v, hhalf v u]
  ring

end RLVF

end O1Abstract

namespace O1Abstract

variable {n : ℕ}

section Tail

variable (ig : Fin n → Fin n → ℝ) (g0 f3 : Fin n → Fin n → Fin n → ℝ)

private lemma o1_tail
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hg0s : ∀ a b k : Fin n, g0 a b k = g0 b a k)
    (hf3s : ∀ d a b : Fin n, f3 d a b = f3 d b a)
    (i j : Fin n) :
    (∑ k₁ : Fin n, ∑ l : Fin n, ig k₁ l *
      ((-(∑ r : Fin n, (g0 l j r * f3 i r k₁ + g0 l k₁ r * f3 i j r + g0 i l r * f3 r j k₁
          + g0 i j r * f3 l r k₁ + g0 i k₁ r * f3 l j r)))
       + (-(∑ r : Fin n, (g0 l i r * f3 j r k₁ + g0 l k₁ r * f3 j i r + g0 j l r * f3 r i k₁
          + g0 j i r * f3 l r k₁ + g0 j k₁ r * f3 l i r)))
       - (-(∑ r : Fin n, (g0 j l r * f3 i r k₁ + g0 j k₁ r * f3 i l r + g0 i j r * f3 r l k₁
          + g0 i l r * f3 j r k₁ + g0 i k₁ r * f3 j l r)))))
    = (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 i b c))
      + (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 j b c))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 c j b))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 c i b))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 b j c))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 b i c))
      - 2 * (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g0 i j q * f3 p q k))
      + (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g0 i j q * f3 q p k))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ w : Fin n, ig a b * (g0 a b w * f3 i j w))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ w : Fin n, ig a b * (g0 a b w * f3 j i w)) := by
  have hcomb : ∀ k₁ l : Fin n, ig k₁ l *
      ((-(∑ r : Fin n, (g0 l j r * f3 i r k₁ + g0 l k₁ r * f3 i j r + g0 i l r * f3 r j k₁
          + g0 i j r * f3 l r k₁ + g0 i k₁ r * f3 l j r)))
       + (-(∑ r : Fin n, (g0 l i r * f3 j r k₁ + g0 l k₁ r * f3 j i r + g0 j l r * f3 r i k₁
          + g0 j i r * f3 l r k₁ + g0 j k₁ r * f3 l i r)))
       - (-(∑ r : Fin n, (g0 j l r * f3 i r k₁ + g0 j k₁ r * f3 i l r + g0 i j r * f3 r l k₁
          + g0 i l r * f3 j r k₁ + g0 i k₁ r * f3 j l r))))
      = ∑ r : Fin n,
          (((ig k₁ l * (g0 j l r * f3 i r k₁) + ig k₁ l * (g0 j k₁ r * f3 i l r)
              + ig k₁ l * (g0 i j r * f3 r l k₁) + ig k₁ l * (g0 i l r * f3 j r k₁)
              + ig k₁ l * (g0 i k₁ r * f3 j l r))
            - (ig k₁ l * (g0 l j r * f3 i r k₁) + ig k₁ l * (g0 l k₁ r * f3 i j r)
              + ig k₁ l * (g0 i l r * f3 r j k₁) + ig k₁ l * (g0 i j r * f3 l r k₁)
              + ig k₁ l * (g0 i k₁ r * f3 l j r)))
           - (ig k₁ l * (g0 l i r * f3 j r k₁) + ig k₁ l * (g0 l k₁ r * f3 j i r)
              + ig k₁ l * (g0 j l r * f3 r i k₁) + ig k₁ l * (g0 j i r * f3 l r k₁)
              + ig k₁ l * (g0 j k₁ r * f3 l i r))) := by
    intro k₁ l
    rw [show ∀ P Q R : Fin n → ℝ, (-(∑ r : Fin n, P r)) + (-(∑ r : Fin n, Q r))
        - (-(∑ r : Fin n, R r)) = (∑ r : Fin n, R r) - (∑ r : Fin n, P r) - (∑ r : Fin n, Q r)
      from fun P Q R => by ring]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    ring
  rw [Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => hcomb k₁ l))]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hp1 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 l j r * f3 i r k₁))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 i b c) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l, hf3s i r k₁])))
  have hp2 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 l k₁ r * f3 i j r))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ w : Fin n, ig a b * (g0 a b w * f3 i j w) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l])))
  have hp3 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 i l r * f3 r j k₁))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 c j b) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l, hg0s i l r])))
  have hp4 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 i j r * f3 l r k₁))
      = ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g0 i j q * f3 p q k) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ =>
      Finset.sum_congr rfl (fun r _ => by ring)))
  have hp5 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 i k₁ r * f3 l j r))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 b j c) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ =>
      Finset.sum_congr rfl (fun r _ => by rw [hg0s i k₁ r])))
  have hq1 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 l i r * f3 j r k₁))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 j b c) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l, hf3s j r k₁])))
  have hq2 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 l k₁ r * f3 j i r))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ w : Fin n, ig a b * (g0 a b w * f3 j i w) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l])))
  have hq3 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 j l r * f3 r i k₁))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 c i b) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l, hg0s j l r])))
  have hq4 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 j i r * f3 l r k₁))
      = ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g0 i j q * f3 p q k) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ =>
      Finset.sum_congr rfl (fun r _ => by rw [hg0s j i r])))
  have hq5 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 j k₁ r * f3 l i r))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 b i c) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ =>
      Finset.sum_congr rfl (fun r _ => by rw [hg0s j k₁ r])))
  have hr1 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 j l r * f3 i r k₁))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 i b c) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l, hg0s j l r, hf3s i r k₁])))
  have hr2 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 j k₁ r * f3 i l r))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 i b c) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ =>
      Finset.sum_congr rfl (fun r _ => by rw [hg0s j k₁ r])))
  have hr3 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 i j r * f3 r l k₁))
      = ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g0 i j q * f3 q p k) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ =>
      Finset.sum_congr rfl (fun r _ => by ring)))
  have hr4 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 i l r * f3 j r k₁))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 j b c) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l, hg0s i l r, hf3s j r k₁])))
  have hr5 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 i k₁ r * f3 j l r))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 j b c) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ =>
      Finset.sum_congr rfl (fun r _ => by rw [hg0s i k₁ r])))
  rw [hp1, hp2, hp3, hp4, hp5, hq1, hq2, hq3, hq4, hq5, hr1, hr2, hr3, hr4, hr5]
  ring

end Tail

end O1Abstract

namespace O1Abstract

variable {n : ℕ}

set_option maxHeartbeats 3200000 in
lemma o1_master (ig cg : Fin n → Fin n → ℝ)
    (dg gb dig g1 g0 gbg f3 : Fin n → Fin n → Fin n → ℝ) (w1 : Fin n → ℝ)
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a)
    (hf3s : ∀ d a b : Fin n, f3 d a b = f3 d b a)
    (hg1s : ∀ a b k : Fin n, g1 a b k = g1 b a k)
    (hg0s : ∀ a b k : Fin n, g0 a b k = g0 b a k)
    (hgbdef : ∀ a b l : Fin n, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgs : ∀ m a b : Fin n, dg m a b = dg m b a)
    (hga1 : ∀ a b k : Fin n, g1 a b k = (1 / 2 : ℝ) * ∑ l : Fin n, ig k l * gb a b l)
    (hdig : ∀ m a b : Fin n, dig m a b
      = -(∑ x : Fin n, ∑ y : Fin n, ig a x * ig y b * dg m x y))
    (i j : Fin n) :
    ((∑ w : Fin n, w1 w * f3 w i j)
      + ((∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 i m p * (∑ q : Fin n, (g1 l₁ j q - g0 l₁ j q) * cg q k₁))))
        - (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 i m p * (∑ q : Fin n, (g1 k₁ l₁ q - gbg k₁ l₁ q) * cg q j))))
        - (∑ w : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * (g1 a b w - g0 a b w)) * f3 i j w)
        - (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 m j p * (∑ q : Fin n, (g1 k₁ i q - g0 k₁ i q) * cg q l₁))))
        - (∑ k₁ : Fin n, ∑ p : Fin n,
            ig k₁ p * (∑ q : Fin n, (g1 j i q - g0 j i q) * f3 p q k₁))
        - (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 m j p * (∑ q : Fin n, (g1 l₁ i q - g0 l₁ i q) * cg q k₁)))))
      + ((∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 j m p * (∑ q : Fin n, (g1 l₁ i q - g0 l₁ i q) * cg q k₁))))
        - (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 j m p * (∑ q : Fin n, (g1 k₁ l₁ q - gbg k₁ l₁ q) * cg q i))))
        - (∑ w : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * (g1 a b w - g0 a b w)) * f3 j i w)
        - (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 m i p * (∑ q : Fin n, (g1 k₁ j q - g0 k₁ j q) * cg q l₁))))
        - (∑ k₁ : Fin n, ∑ p : Fin n,
            ig k₁ p * (∑ q : Fin n, (g1 i j q - g0 i j q) * f3 p q k₁))
        - (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 m i p * (∑ q : Fin n, (g1 l₁ j q - g0 l₁ j q) * cg q k₁)))))
      + (∑ k₁ : Fin n, ∑ p : Fin n,
          ig k₁ p * (∑ q : Fin n, (g1 j i q - g0 j i q) * f3 q p k₁)))
    + (∑ k₁ : Fin n, ∑ l : Fin n, ig k₁ l *
        ((-(∑ r : Fin n, (g0 l j r * f3 i r k₁ + g0 l k₁ r * f3 i j r + g0 i l r * f3 r j k₁
            + g0 i j r * f3 l r k₁ + g0 i k₁ r * f3 l j r)))
         + (-(∑ r : Fin n, (g0 l i r * f3 j r k₁ + g0 l k₁ r * f3 j i r + g0 j l r * f3 r i k₁
            + g0 j i r * f3 l r k₁ + g0 j k₁ r * f3 l i r)))
         - (-(∑ r : Fin n, (g0 j l r * f3 i r k₁ + g0 j k₁ r * f3 i l r + g0 i j r * f3 r l k₁
            + g0 i l r * f3 j r k₁ + g0 i k₁ r * f3 j l r)))))
    = ((∑ k : Fin n, cg k j *
          ((∑ a : Fin n, ∑ b : Fin n, dig i a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
           + ∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, dig i k l * (f3 a l b + f3 b l a - f3 l a b))))
      + ∑ k : Fin n, cg i k *
          ((∑ a : Fin n, ∑ b : Fin n, dig j a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
           + ∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, dig j k l * (f3 a l b + f3 b l a - f3 l a b))))
    + ((∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
          ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b))) * dg k i j)
      + (∑ k : Fin n, w1 k * f3 k i j)
      + (∑ k : Fin n, cg k j * (∑ a : Fin n, ∑ b : Fin n,
          ((-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 i p q * ig q b)) * (g1 a b k - gbg a b k)
           + ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
              (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 i p q * ig q l)) * gb a b l))))
      + (∑ k : Fin n, cg i k * (∑ a : Fin n, ∑ b : Fin n,
          ((-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 j p q * ig q b)) * (g1 a b k - gbg a b k)
           + ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
              (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 j p q * ig q l)) * gb a b l))))) := by
  have hgb2 := o1_hgb2 ig cg gb g1 hcol hcgs hga1
  have hdg2 := o1_hdg2 ig cg dg gb g1 hcol hcgs hgbdef hdgs hga1
  have hdig2 := o1_hdig2 ig cg dg gb dig g1 hcol higs hcgs hgbdef hdgs hga1 hdig
  have hT2 := o1_quadAC ig cg g1 g0 (fun m p => f3 i m p) hcol hcgs j
  have hT5 := o1_quadB ig cg g1 g0 (fun m p => f3 m j p) hcol hcgs i
  have hT7 := o1_quadAC ig cg g1 g0 (fun m p => f3 m j p) hcol hcgs i
  have hT8 := o1_quadAC ig cg g1 g0 (fun m p => f3 j m p) hcol hcgs i
  have hT11 := o1_quadB ig cg g1 g0 (fun m p => f3 m i p) hcol hcgs j
  have hT13 := o1_quadAC ig cg g1 g0 (fun m p => f3 m i p) hcol hcgs j
  have hT4 := o1_vf0exp ig g1 g0 f3 i j
  have hT10 := o1_vf0exp ig g1 g0 f3 j i
  have hT6 := (o1_pullE ig g1 g0 f3 j i).trans
    (congrArg₂ (· - ·) (o1_swapE ig f3 g1 hg1s j i) (o1_swapE ig f3 g0 hg0s j i))
  have hT12 := o1_pullE ig g1 g0 f3 i j
  have hT14 := (o1_pullF ig g1 g0 f3 j i).trans
    (congrArg₂ (· - ·) (o1_swapF ig f3 g1 hg1s j i) (o1_swapF ig f3 g0 hg0s j i))
  have hTail := o1_tail ig g0 f3 higs hg0s hf3s i j
  have hFRsplit : ∀ u' v' : Fin n,
      (∑ k : Fin n, cg k v' *
        ((∑ a : Fin n, ∑ b : Fin n, dig u' a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
         + ∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, dig u' k l * (f3 a l b + f3 b l a - f3 l a b))))
      = (∑ k : Fin n, cg k v' * (∑ a : Fin n, ∑ b : Fin n, dig u' a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b))))
        + ∑ k : Fin n, cg k v' * (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, dig u' k l * (f3 a l b + f3 b l a - f3 l a b))) := by
    intro u' v'
    rw [show (∑ k : Fin n, cg k v' *
        ((∑ a : Fin n, ∑ b : Fin n, dig u' a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
         + ∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, dig u' k l * (f3 a l b + f3 b l a - f3 l a b))))
        = ∑ k : Fin n,
            (cg k v' * (∑ a : Fin n, ∑ b : Fin n, dig u' a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
             + cg k v' * (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, dig u' k l * (f3 a l b + f3 b l a - f3 l a b)))) from
      Finset.sum_congr rfl (fun k _ => mul_add _ _ _)]
    rw [Finset.sum_add_distrib]
  have hCDsplit : ∀ u' v' : Fin n,
      (∑ k : Fin n, cg k v' * (∑ a : Fin n, ∑ b : Fin n,
        ((-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u' p q * ig q b)) * (g1 a b k - gbg a b k)
         + ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
            (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u' p q * ig q l)) * gb a b l))))
      = (∑ k : Fin n, cg k v' * (∑ a : Fin n, ∑ b : Fin n,
          (-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u' p q * ig q b)) * (g1 a b k - gbg a b k)))
        + ∑ k : Fin n, cg k v' * (∑ a : Fin n, ∑ b : Fin n,
            ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
              (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u' p q * ig q l)) * gb a b l)) := by
    intro u' v'
    rw [show (∑ k : Fin n, cg k v' * (∑ a : Fin n, ∑ b : Fin n,
        ((-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u' p q * ig q b)) * (g1 a b k - gbg a b k)
         + ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
            (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u' p q * ig q l)) * gb a b l))))
        = ∑ k : Fin n,
            (cg k v' * (∑ a : Fin n, ∑ b : Fin n,
              (-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u' p q * ig q b)) * (g1 a b k - gbg a b k))
             + cg k v' * (∑ a : Fin n, ∑ b : Fin n,
                ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
                  (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u' p q * ig q l)) * gb a b l))) from
      Finset.sum_congr rfl (fun k _ => by
        rw [show (∑ a : Fin n, ∑ b : Fin n,
            ((-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u' p q * ig q b)) * (g1 a b k - gbg a b k)
             + ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
                (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u' p q * ig q l)) * gb a b l)))
            = (∑ a : Fin n, ∑ b : Fin n,
                (-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u' p q * ig q b)) * (g1 a b k - gbg a b k))
              + ∑ a : Fin n, ∑ b : Fin n,
                  ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
                    (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u' p q * ig q l)) * gb a b l) from by
          simp only [Finset.sum_add_distrib]]
        rw [mul_add])]
    rw [Finset.sum_add_distrib]
  have hflipFR : (∑ k : Fin n, cg i k *
      ((∑ a : Fin n, ∑ b : Fin n, dig j a b * ((1 / 2 : ℝ) *
          ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
       + ∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
          ∑ l : Fin n, dig j k l * (f3 a l b + f3 b l a - f3 l a b))))
      = ∑ k : Fin n, cg k i *
          ((∑ a : Fin n, ∑ b : Fin n, dig j a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
           + ∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, dig j k l * (f3 a l b + f3 b l a - f3 l a b))) :=
    Finset.sum_congr rfl (fun k _ => by rw [hcgs i k])
  have hflipCD : (∑ k : Fin n, cg i k * (∑ a : Fin n, ∑ b : Fin n,
      ((-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 j p q * ig q b)) * (g1 a b k - gbg a b k)
       + ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
          (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 j p q * ig q l)) * gb a b l))))
      = ∑ k : Fin n, cg k i * (∑ a : Fin n, ∑ b : Fin n,
          ((-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 j p q * ig q b)) * (g1 a b k - gbg a b k)
           + ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
              (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 j p q * ig q l)) * gb a b l))) :=
    Finset.sum_congr rfl (fun k _ => by rw [hcgs i k])
  rw [hflipFR, hflipCD]
  rw [hFRsplit i j, hFRsplit j i, hCDsplit i j, hCDsplit j i]
  rw [o1_rf1a ig cg dig g1 f3 hcol higs hf3s hg1s hdig2 i j]
  rw [o1_rf1a ig cg dig g1 f3 hcol higs hf3s hg1s hdig2 j i]
  rw [o1_rf1b ig cg dig g1 f3 hcol higs hdig2 i j]
  rw [o1_rf1b ig cg dig g1 f3 hcol higs hdig2 j i]
  rw [o1_rlvf ig cg dg g1 f3 higs hcgs hg1s hdg2 i j]
  rw [o1_rq3 ig cg g1 gbg f3 higs hf3s i j]
  rw [o1_rq3 ig cg g1 gbg f3 higs hf3s j i]
  rw [o1_rg7 ig cg gb g1 f3 hcol higs hgb2 i j]
  rw [o1_rg7 ig cg gb g1 f3 hcol higs hgb2 j i]
  rw [o1_swapE ig f3 g1 hg1s j i, o1_swapF ig f3 g1 hg1s j i]
  rw [hT2, hT5, hT7, hT8, hT11, hT13, hT4, hT10, hT6, hT12, hT14, hTail]
  ring

end O1Abstract

end

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
