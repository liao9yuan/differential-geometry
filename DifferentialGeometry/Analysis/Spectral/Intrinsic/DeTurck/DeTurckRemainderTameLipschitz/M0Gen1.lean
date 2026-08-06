import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.M0Defs

/-!
# Order-zero index-algebra normal forms, part 1

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

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace M0Abstract

section Gen

lemma m0_collapse {n : ℕ} (ig cg : Fin n → Fin n → ℝ)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (X : Fin n → ℝ) (e : Fin n) :
    (∑ u, ∑ d, cg d e * ig d u * X u) = X e := by
  have h1 : ∀ u : Fin n, (∑ d, cg d e * ig d u * X u) =
      (if u = e then (1 : ℝ) else 0) * X u := by
    intro u
    rw [← Finset.sum_mul, hcol u e]
  rw [Finset.sum_congr rfl (fun u _ => h1 u)]
  rw [Finset.sum_eq_single e]
  · rw [if_pos rfl, one_mul]
  · intro b _ hb
    rw [if_neg hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ e) h

private lemma m0_collapse2 {n : ℕ} (ig cg : Fin n → Fin n → ℝ)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (X : Fin n → ℝ) (e : Fin n) :
    (∑ w, ∑ d, cg d w * ig d e * X w) = X e := by
  have h1 : ∀ w : Fin n, (∑ d, cg d w * ig d e * X w) =
      (if e = w then (1 : ℝ) else 0) * X w := by
    intro w
    rw [← Finset.sum_mul, hcol e w]
  rw [Finset.sum_congr rfl (fun w _ => h1 w)]
  rw [Finset.sum_eq_single e]
  · rw [if_pos rfl, one_mul]
  · intro b _ hb
    rw [if_neg (fun h => hb h.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ e) h

noncomputable def r3B {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (a b c : Fin n) : ℝ :=
  -(∑ r, ga0 a b r * f r c) + (-(∑ r, ga0 a c r * f b r))

noncomputable def chrCorrF {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (a b k : Fin n) : ℝ :=
  (1 / 2 : ℝ) * (∑ l, (-(∑ q, ∑ p, ig k p * f p q * ig q l)) * gb a b l)

noncomputable def wcF {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (k : Fin n) : ℝ :=
  ∑ a, ∑ b, ((-(∑ q, ∑ p, ig a p * f p q * ig q b)) * (ga1 a b k - gbg a b k) + ig a b * chrCorrF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb a b k)

noncomputable def dvfbF {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (m k : Fin n) : ℝ :=
  ∑ a, ∑ b, (dig m a b * (ga1 a b k - gbg a b k) + ig a b * (dga1 m a b k - dgbg m a b k))

noncomputable def d0F {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (m k : Fin n) : ℝ :=
  ∑ a, ∑ b, ((-(∑ q, ∑ p, (dig m a p * f p q * ig q b + ig a p * f p q * dig m q b))) * (ga1 a b k - gbg a b k) + (-(∑ q, ∑ p, ig a p * f p q * ig q b)) * (dga1 m a b k - dgbg m a b k) + dig m a b * chrCorrF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb a b k + ig a b * ((1 / 2 : ℝ) * (∑ l, ((-(∑ q, ∑ p, (dig m k p * f p q * ig q l + ig k p * f p q * dig m q l))) * gb a b l + (-(∑ q, ∑ p, ig k p * f p q * ig q l)) * dgb m a b l))))

noncomputable def O0F {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  (∑ k, wcF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb k * dg k i j) + (∑ k, f k j * dvfbF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i k) + (∑ k, f i k * dvfbF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb j k) + (∑ k, cg k j * d0F ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i k) + (∑ k, cg i k * d0F ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb j k)

noncomputable def vfbF {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (k : Fin n) : ℝ :=
  ∑ a, ∑ b, ig a b * (ga1 a b k - gbg a b k)

noncomputable def covAF {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (a m k p : Fin n) : ℝ :=
  dga1 a k m p - dgbg a k m p + (∑ c, ga1 a c p * (ga1 k m c - gbg k m c)) - (∑ c, ga1 a m c * (ga1 k c p - gbg k c p)) - (∑ c, ga1 a k c * (ga1 c m p - gbg c m p))

noncomputable def covWF {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (a p : Fin n) : ℝ :=
  dvfbF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb a p + (∑ c, ga1 a c p * vfbF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb c)

noncomputable def V0F {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  -(∑ m, ∑ ml, ig m ml * (∑ k, ∑ kl, ig k kl * (((∑ p, covAF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i m k p * cg p j) + (∑ p, covAF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb j m k p * cg p i)) * f ml kl))) + ((∑ p, covWF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i p * f p j) + (∑ p, covWF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb j p * f i p))

noncomputable def D1RF {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  (∑ w, vfbF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb w * r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb w i j) + ((∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m * (r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i m p * (∑ q, (ga1 l1 j q - ga0 l1 j q) * cg q k1)))) - (∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m * (r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i m p * (∑ q, (ga1 k1 l1 q - gbg k1 l1 q) * cg q j)))) - (∑ w, (∑ a, ∑ b, ig a b * (ga1 a b w - ga0 a b w)) * r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i j w) - (∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m * (r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb m j p * (∑ q, (ga1 k1 i q - ga0 k1 i q) * cg q l1)))) - (∑ k1, ∑ p, ig k1 p * (∑ q, (ga1 j i q - ga0 j i q) * r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb p q k1)) - (∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m * (r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb m j p * (∑ q, (ga1 l1 i q - ga0 l1 i q) * cg q k1))))) + ((∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m * (r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb j m p * (∑ q, (ga1 l1 i q - ga0 l1 i q) * cg q k1)))) - (∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m * (r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb j m p * (∑ q, (ga1 k1 l1 q - gbg k1 l1 q) * cg q i)))) - (∑ w, (∑ a, ∑ b, ig a b * (ga1 a b w - ga0 a b w)) * r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb j i w) - (∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m * (r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb m i p * (∑ q, (ga1 k1 j q - ga0 k1 j q) * cg q l1)))) - (∑ k1, ∑ p, ig k1 p * (∑ q, (ga1 i j q - ga0 i j q) * r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb p q k1)) - (∑ k1, ∑ p, ∑ l1, ∑ m, ig k1 p * (ig l1 m * (r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb m i p * (∑ q, (ga1 l1 j q - ga0 l1 j q) * cg q k1))))) + (∑ k1, ∑ p, ig k1 p * (∑ q, (ga1 j i q - ga0 j i q) * r3B ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb q p k1))

private lemma nf_p1B_h1 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, dig i b1 b2 * ga1 b1 b2 b0 * f b0 j) =
      (∑ a, ∑ b, ∑ c, dig i a b * f j c * ga1 a b c) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  rw [hfs c j]
  try ring

private lemma nf_p1B_h2 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, dig i b1 b2 * ga0 b1 b2 b0 * f b0 j) =
      (∑ a, ∑ b, ∑ c, dig i a b * f j c * ga0 a b c) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  rw [hfs c j]
  try ring

private lemma nf_p1B_h3 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ig b1 b2 * dga1 i b1 b2 b0 * f b0 j) =
      (∑ a, ∑ b, ∑ c, dga1 i a b c * f j c * ig a b) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  rw [hfs c j]
  try ring

private lemma nf_p1B_h4 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ig b1 b2 * dga0 i b1 b2 b0 * f b0 j) =
      (∑ a, ∑ b, ∑ c, dga0 i a b c * f j c * ig a b) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  rw [hfs c j]
  try ring

private lemma nf_p1B_h5 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b3, ∑ b4, ∑ b5, ga0 i b3 b0 * (ig b4 b5 * ga1 b4 b5 b3) * f b0 j) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * ga1 c d b * ig c d) := by
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hfs a j]
  try ring

private lemma nf_p1B_h6 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b3, ∑ b4, ∑ b5, ga0 i b3 b0 * (ig b4 b5 * ga0 b4 b5 b3) * f b0 j) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * ga0 c d b * ig c d) := by
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hfs a j]
  try ring

private lemma nf_p1B_h7 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b6, ∑ b7, ∑ b8, dig j b7 b8 * ga1 b7 b8 b6 * f i b6) =
      (∑ a, ∑ b, ∑ c, dig j a b * f i c * ga1 a b c) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  ring

private lemma nf_p1B_h8 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b6, ∑ b7, ∑ b8, dig j b7 b8 * ga0 b7 b8 b6 * f i b6) =
      (∑ a, ∑ b, ∑ c, dig j a b * f i c * ga0 a b c) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  ring

private lemma nf_p1B_h9 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b6, ∑ b7, ∑ b8, ig b7 b8 * dga1 j b7 b8 b6 * f i b6) =
      (∑ a, ∑ b, ∑ c, dga1 j a b c * f i c * ig a b) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  ring

private lemma nf_p1B_h10 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b6, ∑ b7, ∑ b8, ig b7 b8 * dga0 j b7 b8 b6 * f i b6) =
      (∑ a, ∑ b, ∑ c, dga0 j a b c * f i c * ig a b) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  ring

private lemma nf_p1B_h11 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b6, ∑ b9, ∑ b10, ∑ b11, ga0 j b9 b6 * (ig b10 b11 * ga1 b10 b11 b9) * f i b6) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * ga1 c d b * ig c d) := by
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

private lemma nf_p1B_h12 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b6, ∑ b9, ∑ b10, ∑ b11, ga0 j b9 b6 * (ig b10 b11 * ga0 b10 b11 b9) * f i b6) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * ga0 c d b * ig c d) := by
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

lemma nf_p1B {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    p1B ig dig ga1 ga0 dga1 dga0 f i j =
      (∑ a, ∑ b, ∑ c, dga0 i a b c * f j c * ig a b)
      + (∑ a, ∑ b, ∑ c, dga0 j a b c * f i c * ig a b)
      + (-(∑ a, ∑ b, ∑ c, dga1 i a b c * f j c * ig a b))
      + (-(∑ a, ∑ b, ∑ c, dga1 j a b c * f i c * ig a b))
      + (∑ a, ∑ b, ∑ c, dig i a b * f j c * ga0 a b c)
      + (-(∑ a, ∑ b, ∑ c, dig i a b * f j c * ga1 a b c))
      + (∑ a, ∑ b, ∑ c, dig j a b * f i c * ga0 a b c)
      + (-(∑ a, ∑ b, ∑ c, dig j a b * f i c * ga1 a b c))
      + (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * ga0 c d b * ig c d)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * ga1 c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * ga0 c d b * ig c d)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * ga1 c d b * ig c d)) := by
  have h1 : p1B ig dig ga1 ga0 dga1 dga0 f i j =
      -((∑ b0, ∑ b1, ∑ b2, dig i b1 b2 * ga1 b1 b2 b0 * f b0 j) - (∑ b0, ∑ b1, ∑ b2, dig i b1 b2 * ga0 b1 b2 b0 * f b0 j) + ((∑ b0, ∑ b1, ∑ b2, ig b1 b2 * dga1 i b1 b2 b0 * f b0 j) - (∑ b0, ∑ b1, ∑ b2, ig b1 b2 * dga0 i b1 b2 b0 * f b0 j)) + ((∑ b0, ∑ b3, ∑ b4, ∑ b5, ga0 i b3 b0 * (ig b4 b5 * ga1 b4 b5 b3) * f b0 j) - (∑ b0, ∑ b3, ∑ b4, ∑ b5, ga0 i b3 b0 * (ig b4 b5 * ga0 b4 b5 b3) * f b0 j))) + (-((∑ b6, ∑ b7, ∑ b8, dig j b7 b8 * ga1 b7 b8 b6 * f i b6) - (∑ b6, ∑ b7, ∑ b8, dig j b7 b8 * ga0 b7 b8 b6 * f i b6) + ((∑ b6, ∑ b7, ∑ b8, ig b7 b8 * dga1 j b7 b8 b6 * f i b6) - (∑ b6, ∑ b7, ∑ b8, ig b7 b8 * dga0 j b7 b8 b6 * f i b6)) + ((∑ b6, ∑ b9, ∑ b10, ∑ b11, ga0 j b9 b6 * (ig b10 b11 * ga1 b10 b11 b9) * f i b6) - (∑ b6, ∑ b9, ∑ b10, ∑ b11, ga0 j b9 b6 * (ig b10 b11 * ga0 b10 b11 b9) * f i b6)))) := by
    simp only [p1B]
    simp (config := { maxSteps := 10000000 }) only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    try ring
  have h2 : -((∑ b0, ∑ b1, ∑ b2, dig i b1 b2 * ga1 b1 b2 b0 * f b0 j) - (∑ b0, ∑ b1, ∑ b2, dig i b1 b2 * ga0 b1 b2 b0 * f b0 j) + ((∑ b0, ∑ b1, ∑ b2, ig b1 b2 * dga1 i b1 b2 b0 * f b0 j) - (∑ b0, ∑ b1, ∑ b2, ig b1 b2 * dga0 i b1 b2 b0 * f b0 j)) + ((∑ b0, ∑ b3, ∑ b4, ∑ b5, ga0 i b3 b0 * (ig b4 b5 * ga1 b4 b5 b3) * f b0 j) - (∑ b0, ∑ b3, ∑ b4, ∑ b5, ga0 i b3 b0 * (ig b4 b5 * ga0 b4 b5 b3) * f b0 j))) + (-((∑ b6, ∑ b7, ∑ b8, dig j b7 b8 * ga1 b7 b8 b6 * f i b6) - (∑ b6, ∑ b7, ∑ b8, dig j b7 b8 * ga0 b7 b8 b6 * f i b6) + ((∑ b6, ∑ b7, ∑ b8, ig b7 b8 * dga1 j b7 b8 b6 * f i b6) - (∑ b6, ∑ b7, ∑ b8, ig b7 b8 * dga0 j b7 b8 b6 * f i b6)) + ((∑ b6, ∑ b9, ∑ b10, ∑ b11, ga0 j b9 b6 * (ig b10 b11 * ga1 b10 b11 b9) * f i b6) - (∑ b6, ∑ b9, ∑ b10, ∑ b11, ga0 j b9 b6 * (ig b10 b11 * ga0 b10 b11 b9) * f i b6)))) =
      (∑ a, ∑ b, ∑ c, dga0 i a b c * f j c * ig a b)
      + (∑ a, ∑ b, ∑ c, dga0 j a b c * f i c * ig a b)
      + (-(∑ a, ∑ b, ∑ c, dga1 i a b c * f j c * ig a b))
      + (-(∑ a, ∑ b, ∑ c, dga1 j a b c * f i c * ig a b))
      + (∑ a, ∑ b, ∑ c, dig i a b * f j c * ga0 a b c)
      + (-(∑ a, ∑ b, ∑ c, dig i a b * f j c * ga1 a b c))
      + (∑ a, ∑ b, ∑ c, dig j a b * f i c * ga0 a b c)
      + (-(∑ a, ∑ b, ∑ c, dig j a b * f i c * ga1 a b c))
      + (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * ga0 c d b * ig c d)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * ga1 c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * ga0 c d b * ig c d)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * ga1 c d b * ig c d)) := by
    linear_combination - nf_p1B_h1 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_p1B_h2 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_p1B_h3 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_p1B_h4 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_p1B_h5 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_p1B_h6 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_p1B_h7 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_p1B_h8 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_p1B_h9 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_p1B_h10 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_p1B_h11 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_p1B_h12 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
  exact h1.trans h2

private lemma nf_p2B_h1 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, (2 : ℝ) * (ig b2 b3 * ga1 b2 b3 b0 * (ga1 i j b1 * f b0 b1))) =
      (2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga1 i j a * ga1 c d b * ig c d) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hfs b a]
  try ring

private lemma nf_p2B_h2 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, (2 : ℝ) * (ig b2 b3 * ga0 b2 b3 b0 * (ga1 i j b1 * f b0 b1))) =
      (2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 c d a * ga1 i j b * ig c d) := by
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

private lemma nf_p2B_h3 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, (2 : ℝ) * (ig b2 b3 * ga1 b2 b3 b0 * (ga0 i j b1 * f b0 b1))) =
      (2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga1 c d b * ig c d) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hfs b a]
  try ring

private lemma nf_p2B_h4 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, (2 : ℝ) * (ig b2 b3 * ga0 b2 b3 b0 * (ga0 i j b1 * f b0 b1))) =
      (2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hfs b a]
  try ring

lemma nf_p2B {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    p2B ig ga1 ga0 f i j =
      ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga1 c d b * ig c d))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 c d a * ga1 i j b * ig c d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga1 i j a * ga1 c d b * ig c d)) := by
  have h1 : p2B ig ga1 ga0 f i j =
      (∑ b0, ∑ b1, ∑ b2, ∑ b3, (2 : ℝ) * (ig b2 b3 * ga1 b2 b3 b0 * (ga1 i j b1 * f b0 b1))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, (2 : ℝ) * (ig b2 b3 * ga0 b2 b3 b0 * (ga1 i j b1 * f b0 b1))) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, (2 : ℝ) * (ig b2 b3 * ga1 b2 b3 b0 * (ga0 i j b1 * f b0 b1))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, (2 : ℝ) * (ig b2 b3 * ga0 b2 b3 b0 * (ga0 i j b1 * f b0 b1)))) := by
    simp only [p2B]
    simp (config := { maxSteps := 10000000 }) only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    try ring
  have h2 : (∑ b0, ∑ b1, ∑ b2, ∑ b3, (2 : ℝ) * (ig b2 b3 * ga1 b2 b3 b0 * (ga1 i j b1 * f b0 b1))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, (2 : ℝ) * (ig b2 b3 * ga0 b2 b3 b0 * (ga1 i j b1 * f b0 b1))) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, (2 : ℝ) * (ig b2 b3 * ga1 b2 b3 b0 * (ga0 i j b1 * f b0 b1))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, (2 : ℝ) * (ig b2 b3 * ga0 b2 b3 b0 * (ga0 i j b1 * f b0 b1)))) =
      ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga1 c d b * ig c d))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 c d a * ga1 i j b * ig c d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga1 i j a * ga1 c d b * ig c d)) := by
    linear_combination nf_p2B_h1 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_p2B_h2 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_p2B_h3 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_p2B_h4 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
  exact h1.trans h2

private lemma nf_p3h_h1 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 i b1 b4 * (f b4 b3 * (ga1 b0 b2 b5 * cg b5 j))))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d b * ga1 e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r d, higs e c, hga1s r e a, hcgs a j]
  try ring

private lemma nf_p3h_h2 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 i b1 b4 * (f b4 b3 * (gbg b0 b2 b5 * cg b5 j))))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d b * gbg e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r d, higs e c, hgbgs r e a, hcgs a j]
  try ring

private lemma nf_p3h_h3 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga0 i b1 b4 * (f b4 b3 * (ga1 b0 b2 b5 * cg b5 j))))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga0 i d b * ga1 e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r d, higs e c, hga1s r e a, hcgs a j]
  try ring

private lemma nf_p3h_h4 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga0 i b1 b4 * (f b4 b3 * (gbg b0 b2 b5 * cg b5 j))))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga0 i d b * gbg e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r d, higs e c, hgbgs r e a, hcgs a j]
  try ring

lemma nf_p3h {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    p3HalfB ig cg ga1 ga0 gbg f i j =
      (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga0 i d b * ga1 e r a * ig c e * ig d r))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga0 i d b * gbg e r a * ig c e * ig d r)
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d b * ga1 e r a * ig c e * ig d r)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d b * gbg e r a * ig c e * ig d r)) := by
  have h1 : p3HalfB ig cg ga1 ga0 gbg f i j =
      (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 i b1 b4 * (f b4 b3 * (ga1 b0 b2 b5 * cg b5 j))))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 i b1 b4 * (f b4 b3 * (gbg b0 b2 b5 * cg b5 j))))) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga0 i b1 b4 * (f b4 b3 * (ga1 b0 b2 b5 * cg b5 j))))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga0 i b1 b4 * (f b4 b3 * (gbg b0 b2 b5 * cg b5 j)))))) := by
    simp only [p3HalfB]
    simp (config := { maxSteps := 10000000 }) only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    try ring
  have h2 : (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 i b1 b4 * (f b4 b3 * (ga1 b0 b2 b5 * cg b5 j))))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 i b1 b4 * (f b4 b3 * (gbg b0 b2 b5 * cg b5 j))))) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga0 i b1 b4 * (f b4 b3 * (ga1 b0 b2 b5 * cg b5 j))))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga0 i b1 b4 * (f b4 b3 * (gbg b0 b2 b5 * cg b5 j)))))) =
      (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga0 i d b * ga1 e r a * ig c e * ig d r))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga0 i d b * gbg e r a * ig c e * ig d r)
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d b * ga1 e r a * ig c e * ig d r)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d b * gbg e r a * ig c e * ig d r)) := by
    linear_combination nf_p3h_h1 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_p3h_h2 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_p3h_h3 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_p3h_h4 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
  exact h1.trans h2

private lemma nf_p4B_h1 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ig b2 b3 * ga1 b2 b3 b0 * (ga1 b0 i b1 * f b1 j)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga1 i b a * ga1 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga1s b i a, hfs a j]
  try ring

private lemma nf_p4B_h2 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ig b2 b3 * gbg b2 b3 b0 * (ga1 b0 i b1 * f b1 j)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga1 i b a * gbg c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga1s b i a, hfs a j]
  try ring

private lemma nf_p4B_h3 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ig b2 b3 * ga1 b2 b3 b0 * (ga0 b0 i b1 * f b1 j)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * ga1 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s b i a, hfs a j]
  try ring

private lemma nf_p4B_h4 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ig b2 b3 * gbg b2 b3 b0 * (ga0 b0 i b1 * f b1 j)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * gbg c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s b i a, hfs a j]
  try ring

private lemma nf_p4B_h5 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b4, ∑ b5, ∑ b6, ∑ b7, ig b6 b7 * ga1 b6 b7 b4 * (ga1 b4 j b5 * f i b5)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga1 j b a * ga1 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga1s b j a]
  try ring

private lemma nf_p4B_h6 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b4, ∑ b5, ∑ b6, ∑ b7, ig b6 b7 * gbg b6 b7 b4 * (ga1 b4 j b5 * f i b5)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga1 j b a * gbg c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga1s b j a]
  try ring

private lemma nf_p4B_h7 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b4, ∑ b5, ∑ b6, ∑ b7, ig b6 b7 * ga1 b6 b7 b4 * (ga0 b4 j b5 * f i b5)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * ga1 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s b j a]
  try ring

private lemma nf_p4B_h8 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b4, ∑ b5, ∑ b6, ∑ b7, ig b6 b7 * gbg b6 b7 b4 * (ga0 b4 j b5 * f i b5)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * gbg c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s b j a]
  try ring

lemma nf_p4B {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    p4B ig ga1 ga0 gbg f i j =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * ga1 c d b * ig c d)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * gbg c d b * ig c d))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f i a * ga1 j b a * ga1 c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga1 j b a * gbg c d b * ig c d)
      + (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * ga1 c d b * ig c d)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * gbg c d b * ig c d))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f j a * ga1 i b a * ga1 c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga1 i b a * gbg c d b * ig c d) := by
  have h1 : p4B ig ga1 ga0 gbg f i j =
      -((∑ b0, ∑ b1, ∑ b2, ∑ b3, ig b2 b3 * ga1 b2 b3 b0 * (ga1 b0 i b1 * f b1 j)) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ig b2 b3 * gbg b2 b3 b0 * (ga1 b0 i b1 * f b1 j)) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ig b2 b3 * ga1 b2 b3 b0 * (ga0 b0 i b1 * f b1 j)) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ig b2 b3 * gbg b2 b3 b0 * (ga0 b0 i b1 * f b1 j)))) + (-((∑ b4, ∑ b5, ∑ b6, ∑ b7, ig b6 b7 * ga1 b6 b7 b4 * (ga1 b4 j b5 * f i b5)) - (∑ b4, ∑ b5, ∑ b6, ∑ b7, ig b6 b7 * gbg b6 b7 b4 * (ga1 b4 j b5 * f i b5)) - ((∑ b4, ∑ b5, ∑ b6, ∑ b7, ig b6 b7 * ga1 b6 b7 b4 * (ga0 b4 j b5 * f i b5)) - (∑ b4, ∑ b5, ∑ b6, ∑ b7, ig b6 b7 * gbg b6 b7 b4 * (ga0 b4 j b5 * f i b5))))) := by
    simp only [p4B]
    simp (config := { maxSteps := 10000000 }) only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    try ring
  have h2 : -((∑ b0, ∑ b1, ∑ b2, ∑ b3, ig b2 b3 * ga1 b2 b3 b0 * (ga1 b0 i b1 * f b1 j)) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ig b2 b3 * gbg b2 b3 b0 * (ga1 b0 i b1 * f b1 j)) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ig b2 b3 * ga1 b2 b3 b0 * (ga0 b0 i b1 * f b1 j)) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ig b2 b3 * gbg b2 b3 b0 * (ga0 b0 i b1 * f b1 j)))) + (-((∑ b4, ∑ b5, ∑ b6, ∑ b7, ig b6 b7 * ga1 b6 b7 b4 * (ga1 b4 j b5 * f i b5)) - (∑ b4, ∑ b5, ∑ b6, ∑ b7, ig b6 b7 * gbg b6 b7 b4 * (ga1 b4 j b5 * f i b5)) - ((∑ b4, ∑ b5, ∑ b6, ∑ b7, ig b6 b7 * ga1 b6 b7 b4 * (ga0 b4 j b5 * f i b5)) - (∑ b4, ∑ b5, ∑ b6, ∑ b7, ig b6 b7 * gbg b6 b7 b4 * (ga0 b4 j b5 * f i b5))))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * ga1 c d b * ig c d)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * gbg c d b * ig c d))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f i a * ga1 j b a * ga1 c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga1 j b a * gbg c d b * ig c d)
      + (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * ga1 c d b * ig c d)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * gbg c d b * ig c d))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f j a * ga1 i b a * ga1 c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga1 i b a * gbg c d b * ig c d) := by
    linear_combination - nf_p4B_h1 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_p4B_h2 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_p4B_h3 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_p4B_h4 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_p4B_h5 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_p4B_h6 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_p4B_h7 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_p4B_h8 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
  exact h1.trans h2

private lemma nf_p3hswap_h1 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 j b1 b4 * (f b4 b3 * (ga1 b0 b2 b5 * cg b5 i))))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d b * ga1 e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r d, higs e c, hga1s r e a, hcgs a i]
  try ring

private lemma nf_p3hswap_h2 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 j b1 b4 * (f b4 b3 * (gbg b0 b2 b5 * cg b5 i))))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d b * gbg e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r d, higs e c, hgbgs r e a, hcgs a i]
  try ring

private lemma nf_p3hswap_h3 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga0 j b1 b4 * (f b4 b3 * (ga1 b0 b2 b5 * cg b5 i))))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga0 j d b * ga1 e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r d, higs e c, hga1s r e a, hcgs a i]
  try ring

private lemma nf_p3hswap_h4 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga0 j b1 b4 * (f b4 b3 * (gbg b0 b2 b5 * cg b5 i))))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga0 j d b * gbg e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r d, higs e c, hgbgs r e a, hcgs a i]
  try ring

lemma nf_p3hswap {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    p3HalfB ig cg ga1 ga0 gbg f j i =
      (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga0 j d b * ga1 e r a * ig c e * ig d r))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga0 j d b * gbg e r a * ig c e * ig d r)
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d b * ga1 e r a * ig c e * ig d r)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d b * gbg e r a * ig c e * ig d r)) := by
  have h1 : p3HalfB ig cg ga1 ga0 gbg f j i =
      (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 j b1 b4 * (f b4 b3 * (ga1 b0 b2 b5 * cg b5 i))))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 j b1 b4 * (f b4 b3 * (gbg b0 b2 b5 * cg b5 i))))) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga0 j b1 b4 * (f b4 b3 * (ga1 b0 b2 b5 * cg b5 i))))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga0 j b1 b4 * (f b4 b3 * (gbg b0 b2 b5 * cg b5 i)))))) := by
    simp only [p3HalfB]
    simp (config := { maxSteps := 10000000 }) only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    try ring
  have h2 : (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 j b1 b4 * (f b4 b3 * (ga1 b0 b2 b5 * cg b5 i))))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 j b1 b4 * (f b4 b3 * (gbg b0 b2 b5 * cg b5 i))))) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga0 j b1 b4 * (f b4 b3 * (ga1 b0 b2 b5 * cg b5 i))))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga0 j b1 b4 * (f b4 b3 * (gbg b0 b2 b5 * cg b5 i)))))) =
      (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga0 j d b * ga1 e r a * ig c e * ig d r))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga0 j d b * gbg e r a * ig c e * ig d r)
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d b * ga1 e r a * ig c e * ig d r)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d b * gbg e r a * ig c e * ig d r)) := by
    linear_combination nf_p3hswap_h1 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_p3hswap_h2 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_p3hswap_h3 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_p3hswap_h4 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
  exact h1.trans h2

private lemma nf_O0_h1 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b1 b4 * f b4 b3 * ig b3 b2 * ga1 b1 b2 b0 * dg b0 i j) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, dg a i j * f b c * ga1 d e a * ig b d * ig c e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [higs d b]
  try ring

private lemma nf_O0_h2 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b1 b4 * f b4 b3 * ig b3 b2 * gbg b1 b2 b0 * dg b0 i j) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, dg a i j * f b c * gbg d e a * ig b d * ig c e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [higs d b]
  try ring

private lemma nf_O0_h3 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b5, ∑ b6, ∑ b7, ig b1 b2 * ((1 / 2 : ℝ) * (ig b0 b7 * f b7 b6 * ig b6 b5 * gb b1 b2 b5)) * dg b0 i j) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, dg a i j * f b c * gb d e r * ig a b * ig c r * ig d e) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  ring

private lemma nf_O0_h4 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b8, ∑ b9, ∑ b10, f b8 j * (dig i b9 b10 * ga1 b9 b10 b8)) =
      (∑ a, ∑ b, ∑ c, dig i a b * f j c * ga1 a b c) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  rw [hfs c j]
  try ring

private lemma nf_O0_h5 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b8, ∑ b9, ∑ b10, f b8 j * (dig i b9 b10 * gbg b9 b10 b8)) =
      (∑ a, ∑ b, ∑ c, dig i a b * f j c * gbg a b c) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  rw [hfs c j]
  try ring

private lemma nf_O0_h6 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b8, ∑ b9, ∑ b10, f b8 j * (ig b9 b10 * dga1 i b9 b10 b8)) =
      (∑ a, ∑ b, ∑ c, dga1 i a b c * f j c * ig a b) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  rw [hfs c j]
  try ring

private lemma nf_O0_h7 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b8, ∑ b9, ∑ b10, f b8 j * (ig b9 b10 * dgbg i b9 b10 b8)) =
      (∑ a, ∑ b, ∑ c, dgbg i a b c * f j c * ig a b) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  rw [hfs c j]
  try ring

private lemma nf_O0_h8 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b11, ∑ b12, ∑ b13, f i b11 * (dig j b12 b13 * ga1 b12 b13 b11)) =
      (∑ a, ∑ b, ∑ c, dig j a b * f i c * ga1 a b c) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  ring

private lemma nf_O0_h9 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b11, ∑ b12, ∑ b13, f i b11 * (dig j b12 b13 * gbg b12 b13 b11)) =
      (∑ a, ∑ b, ∑ c, dig j a b * f i c * gbg a b c) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  ring

private lemma nf_O0_h10 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b11, ∑ b12, ∑ b13, f i b11 * (ig b12 b13 * dga1 j b12 b13 b11)) =
      (∑ a, ∑ b, ∑ c, dga1 j a b c * f i c * ig a b) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  ring

private lemma nf_O0_h11 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b11, ∑ b12, ∑ b13, f i b11 * (ig b12 b13 * dgbg j b12 b13 b11)) =
      (∑ a, ∑ b, ∑ c, dgbg j a b c * f i c * ig a b) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  ring

private lemma nf_O0_h12 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (dig i b15 b18 * f b18 b17 * ig b17 b16 * ga1 b15 b16 b14)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dig i b c * f b d * ga1 c e a * ig d e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hcgs a j, hdigs i c b]
  try ring

private lemma nf_O0_h13 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (ig b15 b18 * f b18 b17 * dig i b17 b16 * ga1 b15 b16 b14)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dig i b c * f b d * ga1 c e a * ig d e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hcgs a j, higs e d, hfs d b, hga1s e c a]
  try ring

private lemma nf_O0_h14 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (dig i b15 b18 * f b18 b17 * ig b17 b16 * gbg b15 b16 b14)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dig i b c * f b d * gbg c e a * ig d e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hcgs a j, hdigs i c b]
  try ring

private lemma nf_O0_h15 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (ig b15 b18 * f b18 b17 * dig i b17 b16 * gbg b15 b16 b14)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dig i b c * f b d * gbg c e a * ig d e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hcgs a j, higs e d, hfs d b, hgbgs e c a]
  try ring

private lemma nf_O0_h16 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b14, ∑ b15, ∑ b16, ∑ b19, ∑ b20, cg b14 j * (ig b15 b20 * f b20 b19 * ig b19 b16 * dga1 i b15 b16 b14)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dga1 i b c a * f d e * ig b d * ig c e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hcgs a j, higs e c]
  try ring

private lemma nf_O0_h17 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b14, ∑ b15, ∑ b16, ∑ b19, ∑ b20, cg b14 j * (ig b15 b20 * f b20 b19 * ig b19 b16 * dgbg i b15 b16 b14)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dgbg i b c a * f d e * ig b d * ig c e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hcgs a j, higs e c]
  try ring

private lemma nf_O0_h18' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b15, ∑ b16, ∑ b21, ∑ b22, (1 / 2 : ℝ) * dig i b15 b16 * f j b22 * ig b22 b21 * gb b15 b16 b21) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig i a b * f j c * gb a b d * ig c d) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

private lemma nf_O0_h18 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b14, ∑ b15, ∑ b16, ∑ b21, ∑ b22, ∑ b23, cg b14 j * (dig i b15 b16 * ((1 / 2 : ℝ) * (ig b14 b23 * f b23 b22 * ig b22 b21 * gb b15 b16 b21)))) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig i a b * f j c * gb a b d * ig c d) := by
  have hstep : (∑ b14, ∑ b15, ∑ b16, ∑ b21, ∑ b22, ∑ b23, cg b14 j * (dig i b15 b16 * ((1 / 2 : ℝ) * (ig b14 b23 * f b23 b22 * ig b22 b21 * gb b15 b16 b21)))) =
      (∑ b15, ∑ b16, ∑ b21, ∑ b22, (1 / 2 : ℝ) * dig i b15 b16 * f j b22 * ig b22 b21 * gb b15 b16 b21) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b15 _ => Finset.sum_congr rfl (fun b16 _ => Finset.sum_congr rfl (fun b21 _ => Finset.sum_congr rfl (fun b22 _ => ?_))))
    rw [show (∑ b23, ∑ b14, cg b14 j * (dig i b15 b16 * ((1 / 2 : ℝ) * (ig b14 b23 * f b23 b22 * ig b22 b21 * gb b15 b16 b21)))) = (∑ b23, ∑ b14, cg b14 j * ig b14 b23 * ((1 / 2 : ℝ) * dig i b15 b16 * f b23 b22 * ig b22 b21 * gb b15 b16 b21)) from Finset.sum_congr rfl (fun b23 _ => Finset.sum_congr rfl (fun b14 _ => by ring))]
    exact m0_collapse ig cg hcol (fun b23 => (1 / 2 : ℝ) * dig i b15 b16 * f b23 b22 * ig b22 b21 * gb b15 b16 b21) j
  rw [hstep]
  exact nf_O0_h18' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_O0_h19 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b14, ∑ b15, ∑ b16, ∑ b24, ∑ b25, ∑ b26, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (dig i b14 b26 * f b26 b25 * ig b25 b24 * gb b15 b16 b24)))) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * dig i a b * f b c * gb d e r * ig c r * ig d e) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [hcgs a j]
  try ring

private lemma nf_O0_h20' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b15, ∑ b16, ∑ b24, ∑ b25, (1 / 2 : ℝ) * ig b15 b16 * f j b25 * dig i b25 b24 * gb b15 b16 b24) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig i a b * f j a * gb c d b * ig c d) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

private lemma nf_O0_h20 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b14, ∑ b15, ∑ b16, ∑ b24, ∑ b25, ∑ b26, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (ig b14 b26 * f b26 b25 * dig i b25 b24 * gb b15 b16 b24)))) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig i a b * f j a * gb c d b * ig c d) := by
  have hstep : (∑ b14, ∑ b15, ∑ b16, ∑ b24, ∑ b25, ∑ b26, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (ig b14 b26 * f b26 b25 * dig i b25 b24 * gb b15 b16 b24)))) =
      (∑ b15, ∑ b16, ∑ b24, ∑ b25, (1 / 2 : ℝ) * ig b15 b16 * f j b25 * dig i b25 b24 * gb b15 b16 b24) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b15 _ => Finset.sum_congr rfl (fun b16 _ => Finset.sum_congr rfl (fun b24 _ => Finset.sum_congr rfl (fun b25 _ => ?_))))
    rw [show (∑ b26, ∑ b14, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (ig b14 b26 * f b26 b25 * dig i b25 b24 * gb b15 b16 b24)))) = (∑ b26, ∑ b14, cg b14 j * ig b14 b26 * ((1 / 2 : ℝ) * ig b15 b16 * f b26 b25 * dig i b25 b24 * gb b15 b16 b24)) from Finset.sum_congr rfl (fun b26 _ => Finset.sum_congr rfl (fun b14 _ => by ring))]
    exact m0_collapse ig cg hcol (fun b26 => (1 / 2 : ℝ) * ig b15 b16 * f b26 b25 * dig i b25 b24 * gb b15 b16 b24) j
  rw [hstep]
  exact nf_O0_h20' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_O0_h21' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b15, ∑ b16, ∑ b24, ∑ b27, (1 / 2 : ℝ) * ig b15 b16 * f j b27 * ig b27 b24 * dgb i b15 b16 b24) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dgb i a b c * f j d * ig a b * ig c d) := by
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c]
  try ring

private lemma nf_O0_h21 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b14, ∑ b15, ∑ b16, ∑ b24, ∑ b27, ∑ b28, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (ig b14 b28 * f b28 b27 * ig b27 b24 * dgb i b15 b16 b24)))) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dgb i a b c * f j d * ig a b * ig c d) := by
  have hstep : (∑ b14, ∑ b15, ∑ b16, ∑ b24, ∑ b27, ∑ b28, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (ig b14 b28 * f b28 b27 * ig b27 b24 * dgb i b15 b16 b24)))) =
      (∑ b15, ∑ b16, ∑ b24, ∑ b27, (1 / 2 : ℝ) * ig b15 b16 * f j b27 * ig b27 b24 * dgb i b15 b16 b24) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b15 _ => Finset.sum_congr rfl (fun b16 _ => Finset.sum_congr rfl (fun b24 _ => Finset.sum_congr rfl (fun b27 _ => ?_))))
    rw [show (∑ b28, ∑ b14, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (ig b14 b28 * f b28 b27 * ig b27 b24 * dgb i b15 b16 b24)))) = (∑ b28, ∑ b14, cg b14 j * ig b14 b28 * ((1 / 2 : ℝ) * ig b15 b16 * f b28 b27 * ig b27 b24 * dgb i b15 b16 b24)) from Finset.sum_congr rfl (fun b28 _ => Finset.sum_congr rfl (fun b14 _ => by ring))]
    exact m0_collapse ig cg hcol (fun b28 => (1 / 2 : ℝ) * ig b15 b16 * f b28 b27 * ig b27 b24 * dgb i b15 b16 b24) j
  rw [hstep]
  exact nf_O0_h21' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_O0_h22 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (dig j b30 b33 * f b33 b32 * ig b32 b31 * ga1 b30 b31 b29)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dig j b c * f b d * ga1 c e a * ig d e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hdigs j c b]
  try ring

private lemma nf_O0_h23 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (ig b30 b33 * f b33 b32 * dig j b32 b31 * ga1 b30 b31 b29)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dig j b c * f b d * ga1 c e a * ig d e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [higs e d, hfs d b, hga1s e c a]
  try ring

private lemma nf_O0_h24 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (dig j b30 b33 * f b33 b32 * ig b32 b31 * gbg b30 b31 b29)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dig j b c * f b d * gbg c e a * ig d e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hdigs j c b]
  try ring

private lemma nf_O0_h25 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (ig b30 b33 * f b33 b32 * dig j b32 b31 * gbg b30 b31 b29)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dig j b c * f b d * gbg c e a * ig d e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [higs e d, hfs d b, hgbgs e c a]
  try ring

private lemma nf_O0_h26 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b29, ∑ b30, ∑ b31, ∑ b34, ∑ b35, cg i b29 * (ig b30 b35 * f b35 b34 * ig b34 b31 * dga1 j b30 b31 b29)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dga1 j b c a * f d e * ig b d * ig c e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [higs e c]
  try ring

private lemma nf_O0_h27 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b29, ∑ b30, ∑ b31, ∑ b34, ∑ b35, cg i b29 * (ig b30 b35 * f b35 b34 * ig b34 b31 * dgbg j b30 b31 b29)) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dgbg j b c a * f d e * ig b d * ig c e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [higs e c]
  try ring

private lemma nf_O0_h28' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b30, ∑ b31, ∑ b36, ∑ b37, (1 / 2 : ℝ) * dig j b30 b31 * f i b37 * ig b37 b36 * gb b30 b31 b36) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig j a b * f i c * gb a b d * ig c d) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

private lemma nf_O0_h28 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b29, ∑ b30, ∑ b31, ∑ b36, ∑ b37, ∑ b38, cg i b29 * (dig j b30 b31 * ((1 / 2 : ℝ) * (ig b29 b38 * f b38 b37 * ig b37 b36 * gb b30 b31 b36)))) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig j a b * f i c * gb a b d * ig c d) := by
  have hstep : (∑ b29, ∑ b30, ∑ b31, ∑ b36, ∑ b37, ∑ b38, cg i b29 * (dig j b30 b31 * ((1 / 2 : ℝ) * (ig b29 b38 * f b38 b37 * ig b37 b36 * gb b30 b31 b36)))) =
      (∑ b30, ∑ b31, ∑ b36, ∑ b37, (1 / 2 : ℝ) * dig j b30 b31 * f i b37 * ig b37 b36 * gb b30 b31 b36) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b30 _ => Finset.sum_congr rfl (fun b31 _ => Finset.sum_congr rfl (fun b36 _ => Finset.sum_congr rfl (fun b37 _ => ?_))))
    rw [show (∑ b38, ∑ b29, cg i b29 * (dig j b30 b31 * ((1 / 2 : ℝ) * (ig b29 b38 * f b38 b37 * ig b37 b36 * gb b30 b31 b36)))) = (∑ b38, ∑ b29, cg b29 i * ig b29 b38 * ((1 / 2 : ℝ) * dig j b30 b31 * f b38 b37 * ig b37 b36 * gb b30 b31 b36)) from Finset.sum_congr rfl (fun b38 _ => Finset.sum_congr rfl (fun b29 _ => by rw [hcgs i b29]; try ring))]
    exact m0_collapse ig cg hcol (fun b38 => (1 / 2 : ℝ) * dig j b30 b31 * f b38 b37 * ig b37 b36 * gb b30 b31 b36) i
  rw [hstep]
  exact nf_O0_h28' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_O0_h29 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b29, ∑ b30, ∑ b31, ∑ b39, ∑ b40, ∑ b41, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (dig j b29 b41 * f b41 b40 * ig b40 b39 * gb b30 b31 b39)))) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * dig j a b * f b c * gb d e r * ig c r * ig d e) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  ring

private lemma nf_O0_h30' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b30, ∑ b31, ∑ b39, ∑ b40, (1 / 2 : ℝ) * ig b30 b31 * f i b40 * dig j b40 b39 * gb b30 b31 b39) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig j a b * f i a * gb c d b * ig c d) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

private lemma nf_O0_h30 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b29, ∑ b30, ∑ b31, ∑ b39, ∑ b40, ∑ b41, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (ig b29 b41 * f b41 b40 * dig j b40 b39 * gb b30 b31 b39)))) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig j a b * f i a * gb c d b * ig c d) := by
  have hstep : (∑ b29, ∑ b30, ∑ b31, ∑ b39, ∑ b40, ∑ b41, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (ig b29 b41 * f b41 b40 * dig j b40 b39 * gb b30 b31 b39)))) =
      (∑ b30, ∑ b31, ∑ b39, ∑ b40, (1 / 2 : ℝ) * ig b30 b31 * f i b40 * dig j b40 b39 * gb b30 b31 b39) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b30 _ => Finset.sum_congr rfl (fun b31 _ => Finset.sum_congr rfl (fun b39 _ => Finset.sum_congr rfl (fun b40 _ => ?_))))
    rw [show (∑ b41, ∑ b29, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (ig b29 b41 * f b41 b40 * dig j b40 b39 * gb b30 b31 b39)))) = (∑ b41, ∑ b29, cg b29 i * ig b29 b41 * ((1 / 2 : ℝ) * ig b30 b31 * f b41 b40 * dig j b40 b39 * gb b30 b31 b39)) from Finset.sum_congr rfl (fun b41 _ => Finset.sum_congr rfl (fun b29 _ => by rw [hcgs i b29]; try ring))]
    exact m0_collapse ig cg hcol (fun b41 => (1 / 2 : ℝ) * ig b30 b31 * f b41 b40 * dig j b40 b39 * gb b30 b31 b39) i
  rw [hstep]
  exact nf_O0_h30' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_O0_h31' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b30, ∑ b31, ∑ b39, ∑ b42, (1 / 2 : ℝ) * ig b30 b31 * f i b42 * ig b42 b39 * dgb j b30 b31 b39) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dgb j a b c * f i d * ig a b * ig c d) := by
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c]
  try ring

private lemma nf_O0_h31 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b29, ∑ b30, ∑ b31, ∑ b39, ∑ b42, ∑ b43, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (ig b29 b43 * f b43 b42 * ig b42 b39 * dgb j b30 b31 b39)))) =
      (1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dgb j a b c * f i d * ig a b * ig c d) := by
  have hstep : (∑ b29, ∑ b30, ∑ b31, ∑ b39, ∑ b42, ∑ b43, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (ig b29 b43 * f b43 b42 * ig b42 b39 * dgb j b30 b31 b39)))) =
      (∑ b30, ∑ b31, ∑ b39, ∑ b42, (1 / 2 : ℝ) * ig b30 b31 * f i b42 * ig b42 b39 * dgb j b30 b31 b39) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b30 _ => Finset.sum_congr rfl (fun b31 _ => Finset.sum_congr rfl (fun b39 _ => Finset.sum_congr rfl (fun b42 _ => ?_))))
    rw [show (∑ b43, ∑ b29, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (ig b29 b43 * f b43 b42 * ig b42 b39 * dgb j b30 b31 b39)))) = (∑ b43, ∑ b29, cg b29 i * ig b29 b43 * ((1 / 2 : ℝ) * ig b30 b31 * f b43 b42 * ig b42 b39 * dgb j b30 b31 b39)) from Finset.sum_congr rfl (fun b43 _ => Finset.sum_congr rfl (fun b29 _ => by rw [hcgs i b29]; try ring))]
    exact m0_collapse ig cg hcol (fun b43 => (1 / 2 : ℝ) * ig b30 b31 * f b43 b42 * ig b42 b39 * dgb j b30 b31 b39) i
  rw [hstep]
  exact nf_O0_h31' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

lemma nf_O0 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    O0F ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i j =
      (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dga1 j b c a * f d e * ig b d * ig c e))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dgbg j b c a * f d e * ig b d * ig c e)
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * dig j a b * f b c * gb d e r * ig c r * ig d e))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dig j b c * f b d * ga1 c e a * ig d e))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dig j b c * f b d * gbg c e a * ig d e))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dga1 i b c a * f d e * ig b d * ig c e))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dgbg i b c a * f d e * ig b d * ig c e)
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * dig i a b * f b c * gb d e r * ig c r * ig d e))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dig i b c * f b d * ga1 c e a * ig d e))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dig i b c * f b d * gbg c e a * ig d e))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, dg a i j * f b c * ga1 d e a * ig b d * ig c e))
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, dg a i j * f b c * gb d e r * ig a b * ig c r * ig d e))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, dg a i j * f b c * gbg d e a * ig b d * ig c e)
      + (∑ a, ∑ b, ∑ c, dga1 i a b c * f j c * ig a b)
      + (∑ a, ∑ b, ∑ c, dga1 j a b c * f i c * ig a b)
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dgb i a b c * f j d * ig a b * ig c d))
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dgb j a b c * f i d * ig a b * ig c d))
      + (-(∑ a, ∑ b, ∑ c, dgbg i a b c * f j c * ig a b))
      + (-(∑ a, ∑ b, ∑ c, dgbg j a b c * f i c * ig a b))
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig i a b * f j a * gb c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, dig i a b * f j c * ga1 a b c)
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig i a b * f j c * gb a b d * ig c d))
      + (-(∑ a, ∑ b, ∑ c, dig i a b * f j c * gbg a b c))
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig j a b * f i a * gb c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, dig j a b * f i c * ga1 a b c)
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig j a b * f i c * gb a b d * ig c d))
      + (-(∑ a, ∑ b, ∑ c, dig j a b * f i c * gbg a b c)) := by
  have h1 : O0F ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i j =
      -(∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b1 b4 * f b4 b3 * ig b3 b2 * ga1 b1 b2 b0 * dg b0 i j) - (-(∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b1 b4 * f b4 b3 * ig b3 b2 * gbg b1 b2 b0 * dg b0 i j)) + (-(∑ b0, ∑ b1, ∑ b2, ∑ b5, ∑ b6, ∑ b7, ig b1 b2 * ((1 / 2 : ℝ) * (ig b0 b7 * f b7 b6 * ig b6 b5 * gb b1 b2 b5)) * dg b0 i j)) + ((∑ b8, ∑ b9, ∑ b10, f b8 j * (dig i b9 b10 * ga1 b9 b10 b8)) - (∑ b8, ∑ b9, ∑ b10, f b8 j * (dig i b9 b10 * gbg b9 b10 b8)) + ((∑ b8, ∑ b9, ∑ b10, f b8 j * (ig b9 b10 * dga1 i b9 b10 b8)) - (∑ b8, ∑ b9, ∑ b10, f b8 j * (ig b9 b10 * dgbg i b9 b10 b8)))) + ((∑ b11, ∑ b12, ∑ b13, f i b11 * (dig j b12 b13 * ga1 b12 b13 b11)) - (∑ b11, ∑ b12, ∑ b13, f i b11 * (dig j b12 b13 * gbg b12 b13 b11)) + ((∑ b11, ∑ b12, ∑ b13, f i b11 * (ig b12 b13 * dga1 j b12 b13 b11)) - (∑ b11, ∑ b12, ∑ b13, f i b11 * (ig b12 b13 * dgbg j b12 b13 b11)))) + (-((∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (dig i b15 b18 * f b18 b17 * ig b17 b16 * ga1 b15 b16 b14)) + (∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (ig b15 b18 * f b18 b17 * dig i b17 b16 * ga1 b15 b16 b14))) - (-((∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (dig i b15 b18 * f b18 b17 * ig b17 b16 * gbg b15 b16 b14)) + (∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (ig b15 b18 * f b18 b17 * dig i b17 b16 * gbg b15 b16 b14)))) + (-(∑ b14, ∑ b15, ∑ b16, ∑ b19, ∑ b20, cg b14 j * (ig b15 b20 * f b20 b19 * ig b19 b16 * dga1 i b15 b16 b14)) - (-(∑ b14, ∑ b15, ∑ b16, ∑ b19, ∑ b20, cg b14 j * (ig b15 b20 * f b20 b19 * ig b19 b16 * dgbg i b15 b16 b14)))) + (-(∑ b14, ∑ b15, ∑ b16, ∑ b21, ∑ b22, ∑ b23, cg b14 j * (dig i b15 b16 * ((1 / 2 : ℝ) * (ig b14 b23 * f b23 b22 * ig b22 b21 * gb b15 b16 b21))))) + (-((∑ b14, ∑ b15, ∑ b16, ∑ b24, ∑ b25, ∑ b26, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (dig i b14 b26 * f b26 b25 * ig b25 b24 * gb b15 b16 b24)))) + (∑ b14, ∑ b15, ∑ b16, ∑ b24, ∑ b25, ∑ b26, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (ig b14 b26 * f b26 b25 * dig i b25 b24 * gb b15 b16 b24))))) + (-(∑ b14, ∑ b15, ∑ b16, ∑ b24, ∑ b27, ∑ b28, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (ig b14 b28 * f b28 b27 * ig b27 b24 * dgb i b15 b16 b24))))))) + (-((∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (dig j b30 b33 * f b33 b32 * ig b32 b31 * ga1 b30 b31 b29)) + (∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (ig b30 b33 * f b33 b32 * dig j b32 b31 * ga1 b30 b31 b29))) - (-((∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (dig j b30 b33 * f b33 b32 * ig b32 b31 * gbg b30 b31 b29)) + (∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (ig b30 b33 * f b33 b32 * dig j b32 b31 * gbg b30 b31 b29)))) + (-(∑ b29, ∑ b30, ∑ b31, ∑ b34, ∑ b35, cg i b29 * (ig b30 b35 * f b35 b34 * ig b34 b31 * dga1 j b30 b31 b29)) - (-(∑ b29, ∑ b30, ∑ b31, ∑ b34, ∑ b35, cg i b29 * (ig b30 b35 * f b35 b34 * ig b34 b31 * dgbg j b30 b31 b29)))) + (-(∑ b29, ∑ b30, ∑ b31, ∑ b36, ∑ b37, ∑ b38, cg i b29 * (dig j b30 b31 * ((1 / 2 : ℝ) * (ig b29 b38 * f b38 b37 * ig b37 b36 * gb b30 b31 b36))))) + (-((∑ b29, ∑ b30, ∑ b31, ∑ b39, ∑ b40, ∑ b41, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (dig j b29 b41 * f b41 b40 * ig b40 b39 * gb b30 b31 b39)))) + (∑ b29, ∑ b30, ∑ b31, ∑ b39, ∑ b40, ∑ b41, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (ig b29 b41 * f b41 b40 * dig j b40 b39 * gb b30 b31 b39))))) + (-(∑ b29, ∑ b30, ∑ b31, ∑ b39, ∑ b42, ∑ b43, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (ig b29 b43 * f b43 b42 * ig b42 b39 * dgb j b30 b31 b39))))))) := by
    simp only [O0F, wcF, d0F, dvfbF, chrCorrF]
    simp (config := { maxSteps := 10000000 }) only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    try ring
  have h2 : -(∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b1 b4 * f b4 b3 * ig b3 b2 * ga1 b1 b2 b0 * dg b0 i j) - (-(∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b1 b4 * f b4 b3 * ig b3 b2 * gbg b1 b2 b0 * dg b0 i j)) + (-(∑ b0, ∑ b1, ∑ b2, ∑ b5, ∑ b6, ∑ b7, ig b1 b2 * ((1 / 2 : ℝ) * (ig b0 b7 * f b7 b6 * ig b6 b5 * gb b1 b2 b5)) * dg b0 i j)) + ((∑ b8, ∑ b9, ∑ b10, f b8 j * (dig i b9 b10 * ga1 b9 b10 b8)) - (∑ b8, ∑ b9, ∑ b10, f b8 j * (dig i b9 b10 * gbg b9 b10 b8)) + ((∑ b8, ∑ b9, ∑ b10, f b8 j * (ig b9 b10 * dga1 i b9 b10 b8)) - (∑ b8, ∑ b9, ∑ b10, f b8 j * (ig b9 b10 * dgbg i b9 b10 b8)))) + ((∑ b11, ∑ b12, ∑ b13, f i b11 * (dig j b12 b13 * ga1 b12 b13 b11)) - (∑ b11, ∑ b12, ∑ b13, f i b11 * (dig j b12 b13 * gbg b12 b13 b11)) + ((∑ b11, ∑ b12, ∑ b13, f i b11 * (ig b12 b13 * dga1 j b12 b13 b11)) - (∑ b11, ∑ b12, ∑ b13, f i b11 * (ig b12 b13 * dgbg j b12 b13 b11)))) + (-((∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (dig i b15 b18 * f b18 b17 * ig b17 b16 * ga1 b15 b16 b14)) + (∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (ig b15 b18 * f b18 b17 * dig i b17 b16 * ga1 b15 b16 b14))) - (-((∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (dig i b15 b18 * f b18 b17 * ig b17 b16 * gbg b15 b16 b14)) + (∑ b14, ∑ b15, ∑ b16, ∑ b17, ∑ b18, cg b14 j * (ig b15 b18 * f b18 b17 * dig i b17 b16 * gbg b15 b16 b14)))) + (-(∑ b14, ∑ b15, ∑ b16, ∑ b19, ∑ b20, cg b14 j * (ig b15 b20 * f b20 b19 * ig b19 b16 * dga1 i b15 b16 b14)) - (-(∑ b14, ∑ b15, ∑ b16, ∑ b19, ∑ b20, cg b14 j * (ig b15 b20 * f b20 b19 * ig b19 b16 * dgbg i b15 b16 b14)))) + (-(∑ b14, ∑ b15, ∑ b16, ∑ b21, ∑ b22, ∑ b23, cg b14 j * (dig i b15 b16 * ((1 / 2 : ℝ) * (ig b14 b23 * f b23 b22 * ig b22 b21 * gb b15 b16 b21))))) + (-((∑ b14, ∑ b15, ∑ b16, ∑ b24, ∑ b25, ∑ b26, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (dig i b14 b26 * f b26 b25 * ig b25 b24 * gb b15 b16 b24)))) + (∑ b14, ∑ b15, ∑ b16, ∑ b24, ∑ b25, ∑ b26, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (ig b14 b26 * f b26 b25 * dig i b25 b24 * gb b15 b16 b24))))) + (-(∑ b14, ∑ b15, ∑ b16, ∑ b24, ∑ b27, ∑ b28, cg b14 j * (ig b15 b16 * ((1 / 2 : ℝ) * (ig b14 b28 * f b28 b27 * ig b27 b24 * dgb i b15 b16 b24))))))) + (-((∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (dig j b30 b33 * f b33 b32 * ig b32 b31 * ga1 b30 b31 b29)) + (∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (ig b30 b33 * f b33 b32 * dig j b32 b31 * ga1 b30 b31 b29))) - (-((∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (dig j b30 b33 * f b33 b32 * ig b32 b31 * gbg b30 b31 b29)) + (∑ b29, ∑ b30, ∑ b31, ∑ b32, ∑ b33, cg i b29 * (ig b30 b33 * f b33 b32 * dig j b32 b31 * gbg b30 b31 b29)))) + (-(∑ b29, ∑ b30, ∑ b31, ∑ b34, ∑ b35, cg i b29 * (ig b30 b35 * f b35 b34 * ig b34 b31 * dga1 j b30 b31 b29)) - (-(∑ b29, ∑ b30, ∑ b31, ∑ b34, ∑ b35, cg i b29 * (ig b30 b35 * f b35 b34 * ig b34 b31 * dgbg j b30 b31 b29)))) + (-(∑ b29, ∑ b30, ∑ b31, ∑ b36, ∑ b37, ∑ b38, cg i b29 * (dig j b30 b31 * ((1 / 2 : ℝ) * (ig b29 b38 * f b38 b37 * ig b37 b36 * gb b30 b31 b36))))) + (-((∑ b29, ∑ b30, ∑ b31, ∑ b39, ∑ b40, ∑ b41, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (dig j b29 b41 * f b41 b40 * ig b40 b39 * gb b30 b31 b39)))) + (∑ b29, ∑ b30, ∑ b31, ∑ b39, ∑ b40, ∑ b41, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (ig b29 b41 * f b41 b40 * dig j b40 b39 * gb b30 b31 b39))))) + (-(∑ b29, ∑ b30, ∑ b31, ∑ b39, ∑ b42, ∑ b43, cg i b29 * (ig b30 b31 * ((1 / 2 : ℝ) * (ig b29 b43 * f b43 b42 * ig b42 b39 * dgb j b30 b31 b39))))))) =
      (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dga1 j b c a * f d e * ig b d * ig c e))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dgbg j b c a * f d e * ig b d * ig c e)
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * dig j a b * f b c * gb d e r * ig c r * ig d e))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dig j b c * f b d * ga1 c e a * ig d e))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dig j b c * f b d * gbg c e a * ig d e))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dga1 i b c a * f d e * ig b d * ig c e))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dgbg i b c a * f d e * ig b d * ig c e)
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * dig i a b * f b c * gb d e r * ig c r * ig d e))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dig i b c * f b d * ga1 c e a * ig d e))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dig i b c * f b d * gbg c e a * ig d e))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, dg a i j * f b c * ga1 d e a * ig b d * ig c e))
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, dg a i j * f b c * gb d e r * ig a b * ig c r * ig d e))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, dg a i j * f b c * gbg d e a * ig b d * ig c e)
      + (∑ a, ∑ b, ∑ c, dga1 i a b c * f j c * ig a b)
      + (∑ a, ∑ b, ∑ c, dga1 j a b c * f i c * ig a b)
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dgb i a b c * f j d * ig a b * ig c d))
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dgb j a b c * f i d * ig a b * ig c d))
      + (-(∑ a, ∑ b, ∑ c, dgbg i a b c * f j c * ig a b))
      + (-(∑ a, ∑ b, ∑ c, dgbg j a b c * f i c * ig a b))
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig i a b * f j a * gb c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, dig i a b * f j c * ga1 a b c)
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig i a b * f j c * gb a b d * ig c d))
      + (-(∑ a, ∑ b, ∑ c, dig i a b * f j c * gbg a b c))
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig j a b * f i a * gb c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, dig j a b * f i c * ga1 a b c)
      + ((-1 / 2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, dig j a b * f i c * gb a b d * ig c d))
      + (-(∑ a, ∑ b, ∑ c, dig j a b * f i c * gbg a b c)) := by
    linear_combination - nf_O0_h1 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_O0_h2 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h3 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_O0_h4 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h5 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_O0_h6 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h7 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_O0_h8 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h9 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_O0_h10 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h11 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h12 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h13 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_O0_h14 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_O0_h15 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h16 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_O0_h17 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h18 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h19 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h20 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h21 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h22 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h23 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_O0_h24 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_O0_h25 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h26 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_O0_h27 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h28 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h29 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h30 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_O0_h31 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
  exact h1.trans h2

private lemma nf_V0_h1 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b0 b1 * (ig b2 b3 * (dga1 i b2 b0 b4 * cg b4 j * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dga1 i b c a * f d e * ig b d * ig c e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hdga1s i c b a, hcgs a j]
  try ring

private lemma nf_V0_h2 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b0 b1 * (ig b2 b3 * (dgbg i b2 b0 b4 * cg b4 j * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dgbg i b c a * f d e * ig b d * ig c e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hdgbgs i c b a, hcgs a j]
  try ring

private lemma nf_V0_h3 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 i b5 b4 * ga1 b2 b0 b5 * cg b4 j * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d a * ga1 e r d * ig b e * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs e b, higs r c, hga1s r e d, hcgs a j]
  try ring

private lemma nf_V0_h4 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 i b5 b4 * gbg b2 b0 b5 * cg b4 j * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d a * gbg e r d * ig b e * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs e b, higs r c, hgbgs r e d, hcgs a j]
  try ring

private lemma nf_V0_h5 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b6, ig b0 b1 * (ig b2 b3 * (ga1 i b0 b6 * ga1 b2 b6 b4 * cg b4 j * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d e * ga1 e r a * ig b d * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs d b, higs r c, hga1s r e a, hcgs a j]
  try ring

private lemma nf_V0_h6 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b6, ig b0 b1 * (ig b2 b3 * (ga1 i b0 b6 * gbg b2 b6 b4 * cg b4 j * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d e * gbg e r a * ig b d * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs d b, higs r c, hgbgs r e a, hcgs a j]
  try ring

private lemma nf_V0_h7 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b7, ig b0 b1 * (ig b2 b3 * (ga1 i b2 b7 * ga1 b7 b0 b4 * cg b4 j * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d e * ga1 e r a * ig b d * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r c, higs d b, hcgs a j, hfs c b]
  try ring

private lemma nf_V0_h8 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b7, ig b0 b1 * (ig b2 b3 * (ga1 i b2 b7 * gbg b7 b0 b4 * cg b4 j * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d e * gbg e r a * ig b d * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r c, higs d b, hcgs a j, hfs c b]
  try ring

private lemma nf_V0_h9 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ig b0 b1 * (ig b2 b3 * (dga1 j b2 b0 b8 * cg b8 i * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dga1 j b c a * f d e * ig b d * ig c e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hdga1s j c b a, hcgs a i]
  try ring

private lemma nf_V0_h10 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ig b0 b1 * (ig b2 b3 * (dgbg j b2 b0 b8 * cg b8 i * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dgbg j b c a * f d e * ig b d * ig c e) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_)))))
  rw [hdgbgs j c b a, hcgs a i]
  try ring

private lemma nf_V0_h11 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b9, ig b0 b1 * (ig b2 b3 * (ga1 j b9 b8 * ga1 b2 b0 b9 * cg b8 i * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d a * ga1 e r d * ig b e * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs e b, higs r c, hga1s r e d, hcgs a i]
  try ring

private lemma nf_V0_h12 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b9, ig b0 b1 * (ig b2 b3 * (ga1 j b9 b8 * gbg b2 b0 b9 * cg b8 i * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d a * gbg e r d * ig b e * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs e b, higs r c, hgbgs r e d, hcgs a i]
  try ring

private lemma nf_V0_h13 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b10, ig b0 b1 * (ig b2 b3 * (ga1 j b0 b10 * ga1 b2 b10 b8 * cg b8 i * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d e * ga1 e r a * ig b d * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs d b, higs r c, hga1s r e a, hcgs a i]
  try ring

private lemma nf_V0_h14 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b10, ig b0 b1 * (ig b2 b3 * (ga1 j b0 b10 * gbg b2 b10 b8 * cg b8 i * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d e * gbg e r a * ig b d * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs d b, higs r c, hgbgs r e a, hcgs a i]
  try ring

private lemma nf_V0_h15 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b11, ig b0 b1 * (ig b2 b3 * (ga1 j b2 b11 * ga1 b11 b0 b8 * cg b8 i * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d e * ga1 e r a * ig b d * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r c, higs d b, hcgs a i, hfs c b]
  try ring

private lemma nf_V0_h16 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b11, ig b0 b1 * (ig b2 b3 * (ga1 j b2 b11 * gbg b11 b0 b8 * cg b8 i * f b1 b3))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d e * gbg e r a * ig b d * ig c r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r c, higs d b, hcgs a i, hfs c b]
  try ring

private lemma nf_V0_h17 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b12, ∑ b13, ∑ b14, dig i b13 b14 * ga1 b13 b14 b12 * f b12 j) =
      (∑ a, ∑ b, ∑ c, dig i a b * f j c * ga1 a b c) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  rw [hfs c j]
  try ring

private lemma nf_V0_h18 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b12, ∑ b13, ∑ b14, dig i b13 b14 * gbg b13 b14 b12 * f b12 j) =
      (∑ a, ∑ b, ∑ c, dig i a b * f j c * gbg a b c) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  rw [hfs c j]
  try ring

private lemma nf_V0_h19 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b12, ∑ b13, ∑ b14, ig b13 b14 * dga1 i b13 b14 b12 * f b12 j) =
      (∑ a, ∑ b, ∑ c, dga1 i a b c * f j c * ig a b) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  rw [hfs c j]
  try ring

private lemma nf_V0_h20 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b12, ∑ b13, ∑ b14, ig b13 b14 * dgbg i b13 b14 b12 * f b12 j) =
      (∑ a, ∑ b, ∑ c, dgbg i a b c * f j c * ig a b) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  rw [hfs c j]
  try ring

private lemma nf_V0_h21 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b12, ∑ b15, ∑ b16, ∑ b17, ga1 i b15 b12 * (ig b16 b17 * ga1 b16 b17 b15) * f b12 j) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga1 i b a * ga1 c d b * ig c d) := by
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hfs a j]
  try ring

private lemma nf_V0_h22 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b12, ∑ b15, ∑ b16, ∑ b17, ga1 i b15 b12 * (ig b16 b17 * gbg b16 b17 b15) * f b12 j) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga1 i b a * gbg c d b * ig c d) := by
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hfs a j]
  try ring

private lemma nf_V0_h23 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b18, ∑ b19, ∑ b20, dig j b19 b20 * ga1 b19 b20 b18 * f i b18) =
      (∑ a, ∑ b, ∑ c, dig j a b * f i c * ga1 a b c) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  ring

private lemma nf_V0_h24 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b18, ∑ b19, ∑ b20, dig j b19 b20 * gbg b19 b20 b18 * f i b18) =
      (∑ a, ∑ b, ∑ c, dig j a b * f i c * gbg a b c) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  ring

private lemma nf_V0_h25 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b18, ∑ b19, ∑ b20, ig b19 b20 * dga1 j b19 b20 b18 * f i b18) =
      (∑ a, ∑ b, ∑ c, dga1 j a b c * f i c * ig a b) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  ring

private lemma nf_V0_h26 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b18, ∑ b19, ∑ b20, ig b19 b20 * dgbg j b19 b20 b18 * f i b18) =
      (∑ a, ∑ b, ∑ c, dgbg j a b c * f i c * ig a b) := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
  ring

private lemma nf_V0_h27 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b18, ∑ b21, ∑ b22, ∑ b23, ga1 j b21 b18 * (ig b22 b23 * ga1 b22 b23 b21) * f i b18) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga1 j b a * ga1 c d b * ig c d) := by
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

private lemma nf_V0_h28 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b18, ∑ b21, ∑ b22, ∑ b23, ga1 j b21 b18 * (ig b22 b23 * gbg b22 b23 b21) * f i b18) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga1 j b a * gbg c d b * ig c d) := by
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

lemma nf_V0 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    V0F ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i j =
      (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dga1 j b c a * f d e * ig b d * ig c e))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dgbg j b c a * f d e * ig b d * ig c e)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d a * ga1 e r d * ig b e * ig c r))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d a * gbg e r d * ig b e * ig c r)
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d e * ga1 e r a * ig b d * ig c r))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d e * gbg e r a * ig b d * ig c r))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dga1 i b c a * f d e * ig b d * ig c e))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dgbg i b c a * f d e * ig b d * ig c e)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d a * ga1 e r d * ig b e * ig c r))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d a * gbg e r d * ig b e * ig c r)
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d e * ga1 e r a * ig b d * ig c r))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d e * gbg e r a * ig b d * ig c r))
      + (∑ a, ∑ b, ∑ c, dga1 i a b c * f j c * ig a b)
      + (∑ a, ∑ b, ∑ c, dga1 j a b c * f i c * ig a b)
      + (-(∑ a, ∑ b, ∑ c, dgbg i a b c * f j c * ig a b))
      + (-(∑ a, ∑ b, ∑ c, dgbg j a b c * f i c * ig a b))
      + (∑ a, ∑ b, ∑ c, dig i a b * f j c * ga1 a b c)
      + (-(∑ a, ∑ b, ∑ c, dig i a b * f j c * gbg a b c))
      + (∑ a, ∑ b, ∑ c, dig j a b * f i c * ga1 a b c)
      + (-(∑ a, ∑ b, ∑ c, dig j a b * f i c * gbg a b c))
      + (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga1 j b a * ga1 c d b * ig c d)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f i a * ga1 j b a * gbg c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga1 i b a * ga1 c d b * ig c d)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f j a * ga1 i b a * gbg c d b * ig c d)) := by
  have h1 : V0F ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i j =
      -((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b0 b1 * (ig b2 b3 * (dga1 i b2 b0 b4 * cg b4 j * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b0 b1 * (ig b2 b3 * (dgbg i b2 b0 b4 * cg b4 j * f b1 b3))) + ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 i b5 b4 * ga1 b2 b0 b5 * cg b4 j * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 i b5 b4 * gbg b2 b0 b5 * cg b4 j * f b1 b3)))) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b6, ig b0 b1 * (ig b2 b3 * (ga1 i b0 b6 * ga1 b2 b6 b4 * cg b4 j * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b6, ig b0 b1 * (ig b2 b3 * (ga1 i b0 b6 * gbg b2 b6 b4 * cg b4 j * f b1 b3)))) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b7, ig b0 b1 * (ig b2 b3 * (ga1 i b2 b7 * ga1 b7 b0 b4 * cg b4 j * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b7, ig b0 b1 * (ig b2 b3 * (ga1 i b2 b7 * gbg b7 b0 b4 * cg b4 j * f b1 b3)))) + ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ig b0 b1 * (ig b2 b3 * (dga1 j b2 b0 b8 * cg b8 i * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ig b0 b1 * (ig b2 b3 * (dgbg j b2 b0 b8 * cg b8 i * f b1 b3))) + ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b9, ig b0 b1 * (ig b2 b3 * (ga1 j b9 b8 * ga1 b2 b0 b9 * cg b8 i * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b9, ig b0 b1 * (ig b2 b3 * (ga1 j b9 b8 * gbg b2 b0 b9 * cg b8 i * f b1 b3)))) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b10, ig b0 b1 * (ig b2 b3 * (ga1 j b0 b10 * ga1 b2 b10 b8 * cg b8 i * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b10, ig b0 b1 * (ig b2 b3 * (ga1 j b0 b10 * gbg b2 b10 b8 * cg b8 i * f b1 b3)))) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b11, ig b0 b1 * (ig b2 b3 * (ga1 j b2 b11 * ga1 b11 b0 b8 * cg b8 i * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b11, ig b0 b1 * (ig b2 b3 * (ga1 j b2 b11 * gbg b11 b0 b8 * cg b8 i * f b1 b3)))))) + ((∑ b12, ∑ b13, ∑ b14, dig i b13 b14 * ga1 b13 b14 b12 * f b12 j) - (∑ b12, ∑ b13, ∑ b14, dig i b13 b14 * gbg b13 b14 b12 * f b12 j) + ((∑ b12, ∑ b13, ∑ b14, ig b13 b14 * dga1 i b13 b14 b12 * f b12 j) - (∑ b12, ∑ b13, ∑ b14, ig b13 b14 * dgbg i b13 b14 b12 * f b12 j)) + ((∑ b12, ∑ b15, ∑ b16, ∑ b17, ga1 i b15 b12 * (ig b16 b17 * ga1 b16 b17 b15) * f b12 j) - (∑ b12, ∑ b15, ∑ b16, ∑ b17, ga1 i b15 b12 * (ig b16 b17 * gbg b16 b17 b15) * f b12 j)) + ((∑ b18, ∑ b19, ∑ b20, dig j b19 b20 * ga1 b19 b20 b18 * f i b18) - (∑ b18, ∑ b19, ∑ b20, dig j b19 b20 * gbg b19 b20 b18 * f i b18) + ((∑ b18, ∑ b19, ∑ b20, ig b19 b20 * dga1 j b19 b20 b18 * f i b18) - (∑ b18, ∑ b19, ∑ b20, ig b19 b20 * dgbg j b19 b20 b18 * f i b18)) + ((∑ b18, ∑ b21, ∑ b22, ∑ b23, ga1 j b21 b18 * (ig b22 b23 * ga1 b22 b23 b21) * f i b18) - (∑ b18, ∑ b21, ∑ b22, ∑ b23, ga1 j b21 b18 * (ig b22 b23 * gbg b22 b23 b21) * f i b18)))) := by
    simp only [V0F, covAF, covWF, dvfbF, vfbF]
    simp (config := { maxSteps := 10000000 }) only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    try ring
  have h2 : -((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b0 b1 * (ig b2 b3 * (dga1 i b2 b0 b4 * cg b4 j * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ig b0 b1 * (ig b2 b3 * (dgbg i b2 b0 b4 * cg b4 j * f b1 b3))) + ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 i b5 b4 * ga1 b2 b0 b5 * cg b4 j * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b5, ig b0 b1 * (ig b2 b3 * (ga1 i b5 b4 * gbg b2 b0 b5 * cg b4 j * f b1 b3)))) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b6, ig b0 b1 * (ig b2 b3 * (ga1 i b0 b6 * ga1 b2 b6 b4 * cg b4 j * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b6, ig b0 b1 * (ig b2 b3 * (ga1 i b0 b6 * gbg b2 b6 b4 * cg b4 j * f b1 b3)))) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b7, ig b0 b1 * (ig b2 b3 * (ga1 i b2 b7 * ga1 b7 b0 b4 * cg b4 j * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b4, ∑ b7, ig b0 b1 * (ig b2 b3 * (ga1 i b2 b7 * gbg b7 b0 b4 * cg b4 j * f b1 b3)))) + ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ig b0 b1 * (ig b2 b3 * (dga1 j b2 b0 b8 * cg b8 i * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ig b0 b1 * (ig b2 b3 * (dgbg j b2 b0 b8 * cg b8 i * f b1 b3))) + ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b9, ig b0 b1 * (ig b2 b3 * (ga1 j b9 b8 * ga1 b2 b0 b9 * cg b8 i * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b9, ig b0 b1 * (ig b2 b3 * (ga1 j b9 b8 * gbg b2 b0 b9 * cg b8 i * f b1 b3)))) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b10, ig b0 b1 * (ig b2 b3 * (ga1 j b0 b10 * ga1 b2 b10 b8 * cg b8 i * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b10, ig b0 b1 * (ig b2 b3 * (ga1 j b0 b10 * gbg b2 b10 b8 * cg b8 i * f b1 b3)))) - ((∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b11, ig b0 b1 * (ig b2 b3 * (ga1 j b2 b11 * ga1 b11 b0 b8 * cg b8 i * f b1 b3))) - (∑ b0, ∑ b1, ∑ b2, ∑ b3, ∑ b8, ∑ b11, ig b0 b1 * (ig b2 b3 * (ga1 j b2 b11 * gbg b11 b0 b8 * cg b8 i * f b1 b3)))))) + ((∑ b12, ∑ b13, ∑ b14, dig i b13 b14 * ga1 b13 b14 b12 * f b12 j) - (∑ b12, ∑ b13, ∑ b14, dig i b13 b14 * gbg b13 b14 b12 * f b12 j) + ((∑ b12, ∑ b13, ∑ b14, ig b13 b14 * dga1 i b13 b14 b12 * f b12 j) - (∑ b12, ∑ b13, ∑ b14, ig b13 b14 * dgbg i b13 b14 b12 * f b12 j)) + ((∑ b12, ∑ b15, ∑ b16, ∑ b17, ga1 i b15 b12 * (ig b16 b17 * ga1 b16 b17 b15) * f b12 j) - (∑ b12, ∑ b15, ∑ b16, ∑ b17, ga1 i b15 b12 * (ig b16 b17 * gbg b16 b17 b15) * f b12 j)) + ((∑ b18, ∑ b19, ∑ b20, dig j b19 b20 * ga1 b19 b20 b18 * f i b18) - (∑ b18, ∑ b19, ∑ b20, dig j b19 b20 * gbg b19 b20 b18 * f i b18) + ((∑ b18, ∑ b19, ∑ b20, ig b19 b20 * dga1 j b19 b20 b18 * f i b18) - (∑ b18, ∑ b19, ∑ b20, ig b19 b20 * dgbg j b19 b20 b18 * f i b18)) + ((∑ b18, ∑ b21, ∑ b22, ∑ b23, ga1 j b21 b18 * (ig b22 b23 * ga1 b22 b23 b21) * f i b18) - (∑ b18, ∑ b21, ∑ b22, ∑ b23, ga1 j b21 b18 * (ig b22 b23 * gbg b22 b23 b21) * f i b18)))) =
      (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dga1 j b c a * f d e * ig b d * ig c e))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg i a * dgbg j b c a * f d e * ig b d * ig c e)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d a * ga1 e r d * ig b e * ig c r))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d a * gbg e r d * ig b e * ig c r)
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d e * ga1 e r a * ig b d * ig c r))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga1 j d e * gbg e r a * ig b d * ig c r))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dga1 i b c a * f d e * ig b d * ig c e))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, cg j a * dgbg i b c a * f d e * ig b d * ig c e)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d a * ga1 e r d * ig b e * ig c r))
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d a * gbg e r d * ig b e * ig c r)
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d e * ga1 e r a * ig b d * ig c r))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga1 i d e * gbg e r a * ig b d * ig c r))
      + (∑ a, ∑ b, ∑ c, dga1 i a b c * f j c * ig a b)
      + (∑ a, ∑ b, ∑ c, dga1 j a b c * f i c * ig a b)
      + (-(∑ a, ∑ b, ∑ c, dgbg i a b c * f j c * ig a b))
      + (-(∑ a, ∑ b, ∑ c, dgbg j a b c * f i c * ig a b))
      + (∑ a, ∑ b, ∑ c, dig i a b * f j c * ga1 a b c)
      + (-(∑ a, ∑ b, ∑ c, dig i a b * f j c * gbg a b c))
      + (∑ a, ∑ b, ∑ c, dig j a b * f i c * ga1 a b c)
      + (-(∑ a, ∑ b, ∑ c, dig j a b * f i c * gbg a b c))
      + (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga1 j b a * ga1 c d b * ig c d)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f i a * ga1 j b a * gbg c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga1 i b a * ga1 c d b * ig c d)
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f j a * ga1 i b a * gbg c d b * ig c d)) := by
    linear_combination - nf_V0_h1 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h2 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h3 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h4 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h5 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h6 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h7 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h8 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h9 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h10 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h11 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h12 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h13 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h14 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h15 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h16 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h17 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h18 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h19 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h20 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h21 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h22 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h23 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h24 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h25 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h26 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_V0_h27 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_V0_h28 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
  exact h1.trans h2

private lemma nf_D1R_h1 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b3, ∑ b1, ∑ b2, ig b1 b2 * ga1 b1 b2 b0 * (ga0 b0 i b3 * f b3 j)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * ga1 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s b i a, hfs a j]
  try ring

private lemma nf_D1R_h2 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b3, ∑ b1, ∑ b2, ig b1 b2 * gbg b1 b2 b0 * (ga0 b0 i b3 * f b3 j)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * gbg c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s b i a, hfs a j]
  try ring

private lemma nf_D1R_h3 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b4, ∑ b1, ∑ b2, ig b1 b2 * ga1 b1 b2 b0 * (ga0 b0 j b4 * f i b4)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * ga1 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s b j a]
  try ring

private lemma nf_D1R_h4 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b0, ∑ b4, ∑ b1, ∑ b2, ig b1 b2 * gbg b1 b2 b0 * (ga0 b0 j b4 * f i b4)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * gbg c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s b j a]
  try ring

private lemma nf_D1R_h5' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b7 b8 * ga0 i b8 b9 * f b9 b11 * ga1 b7 j b11) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga1 j d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c, hga1s d j b]
  try ring

private lemma nf_D1R_h5 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b5 b6 * (ig b7 b8 * (ga0 i b8 b9 * f b9 b6 * (ga1 b7 j b11 * cg b11 b5)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga1 j d b * ig c d) := by
  have hstep : (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b5 b6 * (ig b7 b8 * (ga0 i b8 b9 * f b9 b6 * (ga1 b7 j b11 * cg b11 b5)))) =
      (∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b7 b8 * ga0 i b8 b9 * f b9 b11 * ga1 b7 j b11) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b7 _ => Finset.sum_congr rfl (fun b8 _ => Finset.sum_congr rfl (fun b11 _ => Finset.sum_congr rfl (fun b9 _ => ?_))))
    rw [show (∑ b6, ∑ b5, ig b5 b6 * (ig b7 b8 * (ga0 i b8 b9 * f b9 b6 * (ga1 b7 j b11 * cg b11 b5)))) = (∑ b6, ∑ b5, cg b5 b11 * ig b5 b6 * (ig b7 b8 * ga0 i b8 b9 * f b9 b6 * ga1 b7 j b11)) from Finset.sum_congr rfl (fun b6 _ => Finset.sum_congr rfl (fun b5 _ => by rw [hcgs b11 b5]; try ring))]
    exact m0_collapse ig cg hcol (fun b6 => ig b7 b8 * ga0 i b8 b9 * f b9 b6 * ga1 b7 j b11) b11
  rw [hstep]
  exact nf_D1R_h5' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h6' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b7 b8 * ga0 i b8 b9 * f b9 b11 * ga0 b7 j b11) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c, hga0s d j b]
  try ring

private lemma nf_D1R_h6 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b5 b6 * (ig b7 b8 * (ga0 i b8 b9 * f b9 b6 * (ga0 b7 j b11 * cg b11 b5)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
  have hstep : (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b5 b6 * (ig b7 b8 * (ga0 i b8 b9 * f b9 b6 * (ga0 b7 j b11 * cg b11 b5)))) =
      (∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b7 b8 * ga0 i b8 b9 * f b9 b11 * ga0 b7 j b11) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b7 _ => Finset.sum_congr rfl (fun b8 _ => Finset.sum_congr rfl (fun b11 _ => Finset.sum_congr rfl (fun b9 _ => ?_))))
    rw [show (∑ b6, ∑ b5, ig b5 b6 * (ig b7 b8 * (ga0 i b8 b9 * f b9 b6 * (ga0 b7 j b11 * cg b11 b5)))) = (∑ b6, ∑ b5, cg b5 b11 * ig b5 b6 * (ig b7 b8 * ga0 i b8 b9 * f b9 b6 * ga0 b7 j b11)) from Finset.sum_congr rfl (fun b6 _ => Finset.sum_congr rfl (fun b5 _ => by rw [hcgs b11 b5]; try ring))]
    exact m0_collapse ig cg hcol (fun b6 => ig b7 b8 * ga0 i b8 b9 * f b9 b6 * ga0 b7 j b11) b11
  rw [hstep]
  exact nf_D1R_h6' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h7' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b7 b8 * ga0 i b11 b10 * f b8 b10 * ga1 b7 j b11) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga1 j d c * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d b, hfs b a, hga1s d j c]
  try ring

private lemma nf_D1R_h7 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b5 b6 * (ig b7 b8 * (ga0 i b6 b10 * f b8 b10 * (ga1 b7 j b11 * cg b11 b5)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga1 j d c * ig b d) := by
  have hstep : (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b5 b6 * (ig b7 b8 * (ga0 i b6 b10 * f b8 b10 * (ga1 b7 j b11 * cg b11 b5)))) =
      (∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b7 b8 * ga0 i b11 b10 * f b8 b10 * ga1 b7 j b11) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b7 _ => Finset.sum_congr rfl (fun b8 _ => Finset.sum_congr rfl (fun b11 _ => Finset.sum_congr rfl (fun b10 _ => ?_))))
    rw [show (∑ b6, ∑ b5, ig b5 b6 * (ig b7 b8 * (ga0 i b6 b10 * f b8 b10 * (ga1 b7 j b11 * cg b11 b5)))) = (∑ b6, ∑ b5, cg b5 b11 * ig b5 b6 * (ig b7 b8 * ga0 i b6 b10 * f b8 b10 * ga1 b7 j b11)) from Finset.sum_congr rfl (fun b6 _ => Finset.sum_congr rfl (fun b5 _ => by rw [hcgs b11 b5]; try ring))]
    exact m0_collapse ig cg hcol (fun b6 => ig b7 b8 * ga0 i b6 b10 * f b8 b10 * ga1 b7 j b11) b11
  rw [hstep]
  exact nf_D1R_h7' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h8' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b7 b8 * ga0 i b11 b10 * f b8 b10 * ga0 b7 j b11) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d c * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d b, hfs b a, hga0s d j c]
  try ring

private lemma nf_D1R_h8 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b5 b6 * (ig b7 b8 * (ga0 i b6 b10 * f b8 b10 * (ga0 b7 j b11 * cg b11 b5)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d c * ig b d) := by
  have hstep : (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b5 b6 * (ig b7 b8 * (ga0 i b6 b10 * f b8 b10 * (ga0 b7 j b11 * cg b11 b5)))) =
      (∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b7 b8 * ga0 i b11 b10 * f b8 b10 * ga0 b7 j b11) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b7 _ => Finset.sum_congr rfl (fun b8 _ => Finset.sum_congr rfl (fun b11 _ => Finset.sum_congr rfl (fun b10 _ => ?_))))
    rw [show (∑ b6, ∑ b5, ig b5 b6 * (ig b7 b8 * (ga0 i b6 b10 * f b8 b10 * (ga0 b7 j b11 * cg b11 b5)))) = (∑ b6, ∑ b5, cg b5 b11 * ig b5 b6 * (ig b7 b8 * ga0 i b6 b10 * f b8 b10 * ga0 b7 j b11)) from Finset.sum_congr rfl (fun b6 _ => Finset.sum_congr rfl (fun b5 _ => by rw [hcgs b11 b5]; try ring))]
    exact m0_collapse ig cg hcol (fun b6 => ig b7 b8 * ga0 i b6 b10 * f b8 b10 * ga0 b7 j b11) b11
  rw [hstep]
  exact nf_D1R_h8' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h9 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b16, ig b12 b13 * (ig b14 b15 * (ga0 i b15 b16 * f b16 b13 * (ga1 b12 b14 b18 * cg b18 j)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga0 i d b * ga1 e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs e c, higs r d, hcgs a j]
  try ring

private lemma nf_D1R_h10 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b16, ig b12 b13 * (ig b14 b15 * (ga0 i b15 b16 * f b16 b13 * (gbg b12 b14 b18 * cg b18 j)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga0 i d b * gbg e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs e c, higs r d, hcgs a j]
  try ring

private lemma nf_D1R_h11 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b17, ig b12 b13 * (ig b14 b15 * (ga0 i b13 b17 * f b15 b17 * (ga1 b12 b14 b18 * cg b18 j)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga0 i d b * ga1 e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r d, higs e c, hfs c b, hga1s r e a, hcgs a j]
  try ring

private lemma nf_D1R_h12 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b17, ig b12 b13 * (ig b14 b15 * (ga0 i b13 b17 * f b15 b17 * (gbg b12 b14 b18 * cg b18 j)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga0 i d b * gbg e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r d, higs e c, hfs c b, hgbgs r e a, hcgs a j]
  try ring

private lemma nf_D1R_h13 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b19, ∑ b22, ∑ b20, ∑ b21, ig b20 b21 * ga1 b20 b21 b19 * (ga0 i j b22 * f b22 b19)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga1 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

private lemma nf_D1R_h14 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b19, ∑ b22, ∑ b20, ∑ b21, ig b20 b21 * ga0 b20 b21 b19 * (ga0 i j b22 * f b22 b19)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

private lemma nf_D1R_h15 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b19, ∑ b23, ∑ b20, ∑ b21, ig b20 b21 * ga1 b20 b21 b19 * (ga0 i b19 b23 * f j b23)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * ga1 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

private lemma nf_D1R_h16 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b19, ∑ b23, ∑ b20, ∑ b21, ig b20 b21 * ga0 b20 b21 b19 * (ga0 i b19 b23 * f j b23)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * ga0 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

private lemma nf_D1R_h17' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b24, ∑ b25, ∑ b30, ∑ b28, ig b24 b25 * ga0 b30 j b28 * f b28 b25 * ga1 b24 i b30) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 j c a * ga1 i d c * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d b, hga0s c j a, hga1s d i c]
  try ring

private lemma nf_D1R_h17 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b28, ig b24 b25 * (ig b26 b27 * (ga0 b27 j b28 * f b28 b25 * (ga1 b24 i b30 * cg b30 b26)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 j c a * ga1 i d c * ig b d) := by
  have hstep : (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b28, ig b24 b25 * (ig b26 b27 * (ga0 b27 j b28 * f b28 b25 * (ga1 b24 i b30 * cg b30 b26)))) =
      (∑ b24, ∑ b25, ∑ b30, ∑ b28, ig b24 b25 * ga0 b30 j b28 * f b28 b25 * ga1 b24 i b30) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b24 _ => Finset.sum_congr rfl (fun b25 _ => Finset.sum_congr rfl (fun b30 _ => Finset.sum_congr rfl (fun b28 _ => ?_))))
    rw [show (∑ b27, ∑ b26, ig b24 b25 * (ig b26 b27 * (ga0 b27 j b28 * f b28 b25 * (ga1 b24 i b30 * cg b30 b26)))) = (∑ b27, ∑ b26, cg b26 b30 * ig b26 b27 * (ig b24 b25 * ga0 b27 j b28 * f b28 b25 * ga1 b24 i b30)) from Finset.sum_congr rfl (fun b27 _ => Finset.sum_congr rfl (fun b26 _ => by rw [hcgs b30 b26]; try ring))]
    exact m0_collapse ig cg hcol (fun b27 => ig b24 b25 * ga0 b27 j b28 * f b28 b25 * ga1 b24 i b30) b30
  rw [hstep]
  exact nf_D1R_h17' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h18' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b24, ∑ b25, ∑ b30, ∑ b28, ig b24 b25 * ga0 b30 j b28 * f b28 b25 * ga0 b24 i b30) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c d * ga0 j d a * ig b c) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs c b, hga0s d j a, hga0s c i d]
  try ring

private lemma nf_D1R_h18 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b28, ig b24 b25 * (ig b26 b27 * (ga0 b27 j b28 * f b28 b25 * (ga0 b24 i b30 * cg b30 b26)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c d * ga0 j d a * ig b c) := by
  have hstep : (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b28, ig b24 b25 * (ig b26 b27 * (ga0 b27 j b28 * f b28 b25 * (ga0 b24 i b30 * cg b30 b26)))) =
      (∑ b24, ∑ b25, ∑ b30, ∑ b28, ig b24 b25 * ga0 b30 j b28 * f b28 b25 * ga0 b24 i b30) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b24 _ => Finset.sum_congr rfl (fun b25 _ => Finset.sum_congr rfl (fun b30 _ => Finset.sum_congr rfl (fun b28 _ => ?_))))
    rw [show (∑ b27, ∑ b26, ig b24 b25 * (ig b26 b27 * (ga0 b27 j b28 * f b28 b25 * (ga0 b24 i b30 * cg b30 b26)))) = (∑ b27, ∑ b26, cg b26 b30 * ig b26 b27 * (ig b24 b25 * ga0 b27 j b28 * f b28 b25 * ga0 b24 i b30)) from Finset.sum_congr rfl (fun b27 _ => Finset.sum_congr rfl (fun b26 _ => by rw [hcgs b30 b26]; try ring))]
    exact m0_collapse ig cg hcol (fun b27 => ig b24 b25 * ga0 b27 j b28 * f b28 b25 * ga0 b24 i b30) b30
  rw [hstep]
  exact nf_D1R_h18' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h19' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b24, ∑ b25, ∑ b30, ∑ b29, ig b24 b25 * ga0 b30 b25 b29 * f j b29 * ga1 b24 i b30) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 b c a * ga1 i d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c, hga1s d i b]
  try ring

private lemma nf_D1R_h19 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b29, ig b24 b25 * (ig b26 b27 * (ga0 b27 b25 b29 * f j b29 * (ga1 b24 i b30 * cg b30 b26)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 b c a * ga1 i d b * ig c d) := by
  have hstep : (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b29, ig b24 b25 * (ig b26 b27 * (ga0 b27 b25 b29 * f j b29 * (ga1 b24 i b30 * cg b30 b26)))) =
      (∑ b24, ∑ b25, ∑ b30, ∑ b29, ig b24 b25 * ga0 b30 b25 b29 * f j b29 * ga1 b24 i b30) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b24 _ => Finset.sum_congr rfl (fun b25 _ => Finset.sum_congr rfl (fun b30 _ => Finset.sum_congr rfl (fun b29 _ => ?_))))
    rw [show (∑ b27, ∑ b26, ig b24 b25 * (ig b26 b27 * (ga0 b27 b25 b29 * f j b29 * (ga1 b24 i b30 * cg b30 b26)))) = (∑ b27, ∑ b26, cg b26 b30 * ig b26 b27 * (ig b24 b25 * ga0 b27 b25 b29 * f j b29 * ga1 b24 i b30)) from Finset.sum_congr rfl (fun b27 _ => Finset.sum_congr rfl (fun b26 _ => by rw [hcgs b30 b26]; try ring))]
    exact m0_collapse ig cg hcol (fun b27 => ig b24 b25 * ga0 b27 b25 b29 * f j b29 * ga1 b24 i b30) b30
  rw [hstep]
  exact nf_D1R_h19' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h20' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b24, ∑ b25, ∑ b30, ∑ b29, ig b24 b25 * ga0 b30 b25 b29 * f j b29 * ga0 b24 i b30) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b c * ga0 c d a * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s b i c]
  try ring

private lemma nf_D1R_h20 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b29, ig b24 b25 * (ig b26 b27 * (ga0 b27 b25 b29 * f j b29 * (ga0 b24 i b30 * cg b30 b26)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b c * ga0 c d a * ig b d) := by
  have hstep : (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b29, ig b24 b25 * (ig b26 b27 * (ga0 b27 b25 b29 * f j b29 * (ga0 b24 i b30 * cg b30 b26)))) =
      (∑ b24, ∑ b25, ∑ b30, ∑ b29, ig b24 b25 * ga0 b30 b25 b29 * f j b29 * ga0 b24 i b30) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b24 _ => Finset.sum_congr rfl (fun b25 _ => Finset.sum_congr rfl (fun b30 _ => Finset.sum_congr rfl (fun b29 _ => ?_))))
    rw [show (∑ b27, ∑ b26, ig b24 b25 * (ig b26 b27 * (ga0 b27 b25 b29 * f j b29 * (ga0 b24 i b30 * cg b30 b26)))) = (∑ b27, ∑ b26, cg b26 b30 * ig b26 b27 * (ig b24 b25 * ga0 b27 b25 b29 * f j b29 * ga0 b24 i b30)) from Finset.sum_congr rfl (fun b27 _ => Finset.sum_congr rfl (fun b26 _ => by rw [hcgs b30 b26]; try ring))]
    exact m0_collapse ig cg hcol (fun b27 => ig b24 b25 * ga0 b27 b25 b29 * f j b29 * ga0 b24 i b30) b30
  rw [hstep]
  exact nf_D1R_h20' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h21 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b31, ∑ b32, ∑ b33, ∑ b34, ig b31 b32 * (ga1 j i b33 * (ga0 b32 b33 b34 * f b34 b31))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 c d a * ga1 i j c * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga1s j i c, hga0s d c a]
  try ring

private lemma nf_D1R_h22 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b31, ∑ b32, ∑ b33, ∑ b34, ig b31 b32 * (ga0 j i b33 * (ga0 b32 b33 b34 * f b34 b31))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j c * ga0 c d a * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s j i c, hga0s d c a]
  try ring

private lemma nf_D1R_h23 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b31, ∑ b32, ∑ b33, ∑ b35, ig b31 b32 * (ga1 j i b33 * (ga0 b32 b31 b35 * f b33 b35))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 c d a * ga1 i j b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga1s j i b, hga0s d c a, hfs b a]
  try ring

private lemma nf_D1R_h24 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b31, ∑ b32, ∑ b33, ∑ b35, ig b31 b32 * (ga0 j i b33 * (ga0 b32 b31 b35 * f b33 b35))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s j i a, hga0s d c b]
  try ring

private lemma nf_D1R_h25' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b38 b39 * ga0 b39 j b40 * f b40 b42 * ga1 b38 i b42) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 j c a * ga1 i d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c, hga0s c j a, hga1s d i b]
  try ring

private lemma nf_D1R_h25 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b36 b37 * (ig b38 b39 * (ga0 b39 j b40 * f b40 b37 * (ga1 b38 i b42 * cg b42 b36)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 j c a * ga1 i d b * ig c d) := by
  have hstep : (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b36 b37 * (ig b38 b39 * (ga0 b39 j b40 * f b40 b37 * (ga1 b38 i b42 * cg b42 b36)))) =
      (∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b38 b39 * ga0 b39 j b40 * f b40 b42 * ga1 b38 i b42) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b38 _ => Finset.sum_congr rfl (fun b39 _ => Finset.sum_congr rfl (fun b42 _ => Finset.sum_congr rfl (fun b40 _ => ?_))))
    rw [show (∑ b37, ∑ b36, ig b36 b37 * (ig b38 b39 * (ga0 b39 j b40 * f b40 b37 * (ga1 b38 i b42 * cg b42 b36)))) = (∑ b37, ∑ b36, cg b36 b42 * ig b36 b37 * (ig b38 b39 * ga0 b39 j b40 * f b40 b37 * ga1 b38 i b42)) from Finset.sum_congr rfl (fun b37 _ => Finset.sum_congr rfl (fun b36 _ => by rw [hcgs b42 b36]; try ring))]
    exact m0_collapse ig cg hcol (fun b37 => ig b38 b39 * ga0 b39 j b40 * f b40 b37 * ga1 b38 i b42) b42
  rw [hstep]
  exact nf_D1R_h25' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h26' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b38 b39 * ga0 b39 j b40 * f b40 b42 * ga0 b38 i b42) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s d j b, hfs b a, hga0s c i a]
  try ring

private lemma nf_D1R_h26 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b36 b37 * (ig b38 b39 * (ga0 b39 j b40 * f b40 b37 * (ga0 b38 i b42 * cg b42 b36)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
  have hstep : (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b36 b37 * (ig b38 b39 * (ga0 b39 j b40 * f b40 b37 * (ga0 b38 i b42 * cg b42 b36)))) =
      (∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b38 b39 * ga0 b39 j b40 * f b40 b42 * ga0 b38 i b42) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b38 _ => Finset.sum_congr rfl (fun b39 _ => Finset.sum_congr rfl (fun b42 _ => Finset.sum_congr rfl (fun b40 _ => ?_))))
    rw [show (∑ b37, ∑ b36, ig b36 b37 * (ig b38 b39 * (ga0 b39 j b40 * f b40 b37 * (ga0 b38 i b42 * cg b42 b36)))) = (∑ b37, ∑ b36, cg b36 b42 * ig b36 b37 * (ig b38 b39 * ga0 b39 j b40 * f b40 b37 * ga0 b38 i b42)) from Finset.sum_congr rfl (fun b37 _ => Finset.sum_congr rfl (fun b36 _ => by rw [hcgs b42 b36]; try ring))]
    exact m0_collapse ig cg hcol (fun b37 => ig b38 b39 * ga0 b39 j b40 * f b40 b37 * ga0 b38 i b42) b42
  rw [hstep]
  exact nf_D1R_h26' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h27' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b38 b39 * ga0 b39 b42 b41 * f j b41 * ga1 b38 i b42) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 b c a * ga1 i d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c, hga0s c b a, hga1s d i b]
  try ring

private lemma nf_D1R_h27 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b36 b37 * (ig b38 b39 * (ga0 b39 b37 b41 * f j b41 * (ga1 b38 i b42 * cg b42 b36)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 b c a * ga1 i d b * ig c d) := by
  have hstep : (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b36 b37 * (ig b38 b39 * (ga0 b39 b37 b41 * f j b41 * (ga1 b38 i b42 * cg b42 b36)))) =
      (∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b38 b39 * ga0 b39 b42 b41 * f j b41 * ga1 b38 i b42) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b38 _ => Finset.sum_congr rfl (fun b39 _ => Finset.sum_congr rfl (fun b42 _ => Finset.sum_congr rfl (fun b41 _ => ?_))))
    rw [show (∑ b37, ∑ b36, ig b36 b37 * (ig b38 b39 * (ga0 b39 b37 b41 * f j b41 * (ga1 b38 i b42 * cg b42 b36)))) = (∑ b37, ∑ b36, cg b36 b42 * ig b36 b37 * (ig b38 b39 * ga0 b39 b37 b41 * f j b41 * ga1 b38 i b42)) from Finset.sum_congr rfl (fun b37 _ => Finset.sum_congr rfl (fun b36 _ => by rw [hcgs b42 b36]; try ring))]
    exact m0_collapse ig cg hcol (fun b37 => ig b38 b39 * ga0 b39 b37 b41 * f j b41 * ga1 b38 i b42) b42
  rw [hstep]
  exact nf_D1R_h27' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h28' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b38 b39 * ga0 b39 b42 b41 * f j b41 * ga0 b38 i b42) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b c * ga0 c d a * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s d c a, hga0s b i c]
  try ring

private lemma nf_D1R_h28 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b36 b37 * (ig b38 b39 * (ga0 b39 b37 b41 * f j b41 * (ga0 b38 i b42 * cg b42 b36)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b c * ga0 c d a * ig b d) := by
  have hstep : (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b36 b37 * (ig b38 b39 * (ga0 b39 b37 b41 * f j b41 * (ga0 b38 i b42 * cg b42 b36)))) =
      (∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b38 b39 * ga0 b39 b42 b41 * f j b41 * ga0 b38 i b42) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b38 _ => Finset.sum_congr rfl (fun b39 _ => Finset.sum_congr rfl (fun b42 _ => Finset.sum_congr rfl (fun b41 _ => ?_))))
    rw [show (∑ b37, ∑ b36, ig b36 b37 * (ig b38 b39 * (ga0 b39 b37 b41 * f j b41 * (ga0 b38 i b42 * cg b42 b36)))) = (∑ b37, ∑ b36, cg b36 b42 * ig b36 b37 * (ig b38 b39 * ga0 b39 b37 b41 * f j b41 * ga0 b38 i b42)) from Finset.sum_congr rfl (fun b37 _ => Finset.sum_congr rfl (fun b36 _ => by rw [hcgs b42 b36]; try ring))]
    exact m0_collapse ig cg hcol (fun b37 => ig b38 b39 * ga0 b39 b37 b41 * f j b41 * ga0 b38 i b42) b42
  rw [hstep]
  exact nf_D1R_h28' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h29' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b45 b46 * ga0 j b46 b47 * f b47 b49 * ga1 b45 i b49) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 j c a * ga1 i d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c, hga1s d i b]
  try ring

private lemma nf_D1R_h29 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b43 b44 * (ig b45 b46 * (ga0 j b46 b47 * f b47 b44 * (ga1 b45 i b49 * cg b49 b43)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 j c a * ga1 i d b * ig c d) := by
  have hstep : (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b43 b44 * (ig b45 b46 * (ga0 j b46 b47 * f b47 b44 * (ga1 b45 i b49 * cg b49 b43)))) =
      (∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b45 b46 * ga0 j b46 b47 * f b47 b49 * ga1 b45 i b49) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b45 _ => Finset.sum_congr rfl (fun b46 _ => Finset.sum_congr rfl (fun b49 _ => Finset.sum_congr rfl (fun b47 _ => ?_))))
    rw [show (∑ b44, ∑ b43, ig b43 b44 * (ig b45 b46 * (ga0 j b46 b47 * f b47 b44 * (ga1 b45 i b49 * cg b49 b43)))) = (∑ b44, ∑ b43, cg b43 b49 * ig b43 b44 * (ig b45 b46 * ga0 j b46 b47 * f b47 b44 * ga1 b45 i b49)) from Finset.sum_congr rfl (fun b44 _ => Finset.sum_congr rfl (fun b43 _ => by rw [hcgs b49 b43]; try ring))]
    exact m0_collapse ig cg hcol (fun b44 => ig b45 b46 * ga0 j b46 b47 * f b47 b44 * ga1 b45 i b49) b49
  rw [hstep]
  exact nf_D1R_h29' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h30' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b45 b46 * ga0 j b46 b47 * f b47 b49 * ga0 b45 i b49) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hfs b a, hga0s c i a]
  try ring

private lemma nf_D1R_h30 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b43 b44 * (ig b45 b46 * (ga0 j b46 b47 * f b47 b44 * (ga0 b45 i b49 * cg b49 b43)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
  have hstep : (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b43 b44 * (ig b45 b46 * (ga0 j b46 b47 * f b47 b44 * (ga0 b45 i b49 * cg b49 b43)))) =
      (∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b45 b46 * ga0 j b46 b47 * f b47 b49 * ga0 b45 i b49) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b45 _ => Finset.sum_congr rfl (fun b46 _ => Finset.sum_congr rfl (fun b49 _ => Finset.sum_congr rfl (fun b47 _ => ?_))))
    rw [show (∑ b44, ∑ b43, ig b43 b44 * (ig b45 b46 * (ga0 j b46 b47 * f b47 b44 * (ga0 b45 i b49 * cg b49 b43)))) = (∑ b44, ∑ b43, cg b43 b49 * ig b43 b44 * (ig b45 b46 * ga0 j b46 b47 * f b47 b44 * ga0 b45 i b49)) from Finset.sum_congr rfl (fun b44 _ => Finset.sum_congr rfl (fun b43 _ => by rw [hcgs b49 b43]; try ring))]
    exact m0_collapse ig cg hcol (fun b44 => ig b45 b46 * ga0 j b46 b47 * f b47 b44 * ga0 b45 i b49) b49
  rw [hstep]
  exact nf_D1R_h30' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h31' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b45 b46 * ga0 j b49 b48 * f b46 b48 * ga1 b45 i b49) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 j c a * ga1 i d c * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d b, hfs b a, hga1s d i c]
  try ring

private lemma nf_D1R_h31 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b43 b44 * (ig b45 b46 * (ga0 j b44 b48 * f b46 b48 * (ga1 b45 i b49 * cg b49 b43)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 j c a * ga1 i d c * ig b d) := by
  have hstep : (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b43 b44 * (ig b45 b46 * (ga0 j b44 b48 * f b46 b48 * (ga1 b45 i b49 * cg b49 b43)))) =
      (∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b45 b46 * ga0 j b49 b48 * f b46 b48 * ga1 b45 i b49) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b45 _ => Finset.sum_congr rfl (fun b46 _ => Finset.sum_congr rfl (fun b49 _ => Finset.sum_congr rfl (fun b48 _ => ?_))))
    rw [show (∑ b44, ∑ b43, ig b43 b44 * (ig b45 b46 * (ga0 j b44 b48 * f b46 b48 * (ga1 b45 i b49 * cg b49 b43)))) = (∑ b44, ∑ b43, cg b43 b49 * ig b43 b44 * (ig b45 b46 * ga0 j b44 b48 * f b46 b48 * ga1 b45 i b49)) from Finset.sum_congr rfl (fun b44 _ => Finset.sum_congr rfl (fun b43 _ => by rw [hcgs b49 b43]; try ring))]
    exact m0_collapse ig cg hcol (fun b44 => ig b45 b46 * ga0 j b44 b48 * f b46 b48 * ga1 b45 i b49) b49
  rw [hstep]
  exact nf_D1R_h31' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h32' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b45 b46 * ga0 j b49 b48 * f b46 b48 * ga0 b45 i b49) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c d * ga0 j d a * ig b c) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs c b, hfs b a, hga0s c i d]
  try ring

private lemma nf_D1R_h32 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b43 b44 * (ig b45 b46 * (ga0 j b44 b48 * f b46 b48 * (ga0 b45 i b49 * cg b49 b43)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c d * ga0 j d a * ig b c) := by
  have hstep : (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b43 b44 * (ig b45 b46 * (ga0 j b44 b48 * f b46 b48 * (ga0 b45 i b49 * cg b49 b43)))) =
      (∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b45 b46 * ga0 j b49 b48 * f b46 b48 * ga0 b45 i b49) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b45 _ => Finset.sum_congr rfl (fun b46 _ => Finset.sum_congr rfl (fun b49 _ => Finset.sum_congr rfl (fun b48 _ => ?_))))
    rw [show (∑ b44, ∑ b43, ig b43 b44 * (ig b45 b46 * (ga0 j b44 b48 * f b46 b48 * (ga0 b45 i b49 * cg b49 b43)))) = (∑ b44, ∑ b43, cg b43 b49 * ig b43 b44 * (ig b45 b46 * ga0 j b44 b48 * f b46 b48 * ga0 b45 i b49)) from Finset.sum_congr rfl (fun b44 _ => Finset.sum_congr rfl (fun b43 _ => by rw [hcgs b49 b43]; try ring))]
    exact m0_collapse ig cg hcol (fun b44 => ig b45 b46 * ga0 j b44 b48 * f b46 b48 * ga0 b45 i b49) b49
  rw [hstep]
  exact nf_D1R_h32' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h33 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b54, ig b50 b51 * (ig b52 b53 * (ga0 j b53 b54 * f b54 b51 * (ga1 b50 b52 b56 * cg b56 i)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga0 j d b * ga1 e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs e c, higs r d, hcgs a i]
  try ring

private lemma nf_D1R_h34 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b54, ig b50 b51 * (ig b52 b53 * (ga0 j b53 b54 * f b54 b51 * (gbg b50 b52 b56 * cg b56 i)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga0 j d b * gbg e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs e c, higs r d, hcgs a i]
  try ring

private lemma nf_D1R_h35 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b55, ig b50 b51 * (ig b52 b53 * (ga0 j b51 b55 * f b53 b55 * (ga1 b50 b52 b56 * cg b56 i)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga0 j d b * ga1 e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r d, higs e c, hfs c b, hga1s r e a, hcgs a i]
  try ring

private lemma nf_D1R_h36 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b55, ig b50 b51 * (ig b52 b53 * (ga0 j b51 b55 * f b53 b55 * (gbg b50 b52 b56 * cg b56 i)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga0 j d b * gbg e r a * ig c e * ig d r) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun r _ => ?_))))))
  rw [higs r d, higs e c, hfs c b, hgbgs r e a, hcgs a i]
  try ring

private lemma nf_D1R_h37 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b57, ∑ b60, ∑ b58, ∑ b59, ig b58 b59 * ga1 b58 b59 b57 * (ga0 j i b60 * f b60 b57)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga1 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s j i a]
  try ring

private lemma nf_D1R_h38 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b57, ∑ b60, ∑ b58, ∑ b59, ig b58 b59 * ga0 b58 b59 b57 * (ga0 j i b60 * f b60 b57)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s j i a]
  try ring

private lemma nf_D1R_h39 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b57, ∑ b61, ∑ b58, ∑ b59, ig b58 b59 * ga1 b58 b59 b57 * (ga0 j b57 b61 * f i b61)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * ga1 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

private lemma nf_D1R_h40 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b57, ∑ b61, ∑ b58, ∑ b59, ig b58 b59 * ga0 b58 b59 b57 * (ga0 j b57 b61 * f i b61)) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * ga0 c d b * ig c d) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

private lemma nf_D1R_h41' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b62, ∑ b63, ∑ b68, ∑ b66, ig b62 b63 * ga0 b68 i b66 * f b66 b63 * ga1 b62 j b68) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga1 j d c * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d b, hga0s c i a, hga1s d j c]
  try ring

private lemma nf_D1R_h41 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b66, ig b62 b63 * (ig b64 b65 * (ga0 b65 i b66 * f b66 b63 * (ga1 b62 j b68 * cg b68 b64)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga1 j d c * ig b d) := by
  have hstep : (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b66, ig b62 b63 * (ig b64 b65 * (ga0 b65 i b66 * f b66 b63 * (ga1 b62 j b68 * cg b68 b64)))) =
      (∑ b62, ∑ b63, ∑ b68, ∑ b66, ig b62 b63 * ga0 b68 i b66 * f b66 b63 * ga1 b62 j b68) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b62 _ => Finset.sum_congr rfl (fun b63 _ => Finset.sum_congr rfl (fun b68 _ => Finset.sum_congr rfl (fun b66 _ => ?_))))
    rw [show (∑ b65, ∑ b64, ig b62 b63 * (ig b64 b65 * (ga0 b65 i b66 * f b66 b63 * (ga1 b62 j b68 * cg b68 b64)))) = (∑ b65, ∑ b64, cg b64 b68 * ig b64 b65 * (ig b62 b63 * ga0 b65 i b66 * f b66 b63 * ga1 b62 j b68)) from Finset.sum_congr rfl (fun b65 _ => Finset.sum_congr rfl (fun b64 _ => by rw [hcgs b68 b64]; try ring))]
    exact m0_collapse ig cg hcol (fun b65 => ig b62 b63 * ga0 b65 i b66 * f b66 b63 * ga1 b62 j b68) b68
  rw [hstep]
  exact nf_D1R_h41' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h42' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b62, ∑ b63, ∑ b68, ∑ b66, ig b62 b63 * ga0 b68 i b66 * f b66 b63 * ga0 b62 j b68) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d c * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d b, hga0s c i a, hga0s d j c]
  try ring

private lemma nf_D1R_h42 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b66, ig b62 b63 * (ig b64 b65 * (ga0 b65 i b66 * f b66 b63 * (ga0 b62 j b68 * cg b68 b64)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d c * ig b d) := by
  have hstep : (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b66, ig b62 b63 * (ig b64 b65 * (ga0 b65 i b66 * f b66 b63 * (ga0 b62 j b68 * cg b68 b64)))) =
      (∑ b62, ∑ b63, ∑ b68, ∑ b66, ig b62 b63 * ga0 b68 i b66 * f b66 b63 * ga0 b62 j b68) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b62 _ => Finset.sum_congr rfl (fun b63 _ => Finset.sum_congr rfl (fun b68 _ => Finset.sum_congr rfl (fun b66 _ => ?_))))
    rw [show (∑ b65, ∑ b64, ig b62 b63 * (ig b64 b65 * (ga0 b65 i b66 * f b66 b63 * (ga0 b62 j b68 * cg b68 b64)))) = (∑ b65, ∑ b64, cg b64 b68 * ig b64 b65 * (ig b62 b63 * ga0 b65 i b66 * f b66 b63 * ga0 b62 j b68)) from Finset.sum_congr rfl (fun b65 _ => Finset.sum_congr rfl (fun b64 _ => by rw [hcgs b68 b64]; try ring))]
    exact m0_collapse ig cg hcol (fun b65 => ig b62 b63 * ga0 b65 i b66 * f b66 b63 * ga0 b62 j b68) b68
  rw [hstep]
  exact nf_D1R_h42' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h43' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b62, ∑ b63, ∑ b68, ∑ b67, ig b62 b63 * ga0 b68 b63 b67 * f i b67 * ga1 b62 j b68) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 b c a * ga1 j d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c, hga1s d j b]
  try ring

private lemma nf_D1R_h43 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b67, ig b62 b63 * (ig b64 b65 * (ga0 b65 b63 b67 * f i b67 * (ga1 b62 j b68 * cg b68 b64)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 b c a * ga1 j d b * ig c d) := by
  have hstep : (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b67, ig b62 b63 * (ig b64 b65 * (ga0 b65 b63 b67 * f i b67 * (ga1 b62 j b68 * cg b68 b64)))) =
      (∑ b62, ∑ b63, ∑ b68, ∑ b67, ig b62 b63 * ga0 b68 b63 b67 * f i b67 * ga1 b62 j b68) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b62 _ => Finset.sum_congr rfl (fun b63 _ => Finset.sum_congr rfl (fun b68 _ => Finset.sum_congr rfl (fun b67 _ => ?_))))
    rw [show (∑ b65, ∑ b64, ig b62 b63 * (ig b64 b65 * (ga0 b65 b63 b67 * f i b67 * (ga1 b62 j b68 * cg b68 b64)))) = (∑ b65, ∑ b64, cg b64 b68 * ig b64 b65 * (ig b62 b63 * ga0 b65 b63 b67 * f i b67 * ga1 b62 j b68)) from Finset.sum_congr rfl (fun b65 _ => Finset.sum_congr rfl (fun b64 _ => by rw [hcgs b68 b64]; try ring))]
    exact m0_collapse ig cg hcol (fun b65 => ig b62 b63 * ga0 b65 b63 b67 * f i b67 * ga1 b62 j b68) b68
  rw [hstep]
  exact nf_D1R_h43' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h44' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b62, ∑ b63, ∑ b68, ∑ b67, ig b62 b63 * ga0 b68 b63 b67 * f i b67 * ga0 b62 j b68) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b c * ga0 c d a * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s b j c]
  try ring

private lemma nf_D1R_h44 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b67, ig b62 b63 * (ig b64 b65 * (ga0 b65 b63 b67 * f i b67 * (ga0 b62 j b68 * cg b68 b64)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b c * ga0 c d a * ig b d) := by
  have hstep : (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b67, ig b62 b63 * (ig b64 b65 * (ga0 b65 b63 b67 * f i b67 * (ga0 b62 j b68 * cg b68 b64)))) =
      (∑ b62, ∑ b63, ∑ b68, ∑ b67, ig b62 b63 * ga0 b68 b63 b67 * f i b67 * ga0 b62 j b68) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b62 _ => Finset.sum_congr rfl (fun b63 _ => Finset.sum_congr rfl (fun b68 _ => Finset.sum_congr rfl (fun b67 _ => ?_))))
    rw [show (∑ b65, ∑ b64, ig b62 b63 * (ig b64 b65 * (ga0 b65 b63 b67 * f i b67 * (ga0 b62 j b68 * cg b68 b64)))) = (∑ b65, ∑ b64, cg b64 b68 * ig b64 b65 * (ig b62 b63 * ga0 b65 b63 b67 * f i b67 * ga0 b62 j b68)) from Finset.sum_congr rfl (fun b65 _ => Finset.sum_congr rfl (fun b64 _ => by rw [hcgs b68 b64]; try ring))]
    exact m0_collapse ig cg hcol (fun b65 => ig b62 b63 * ga0 b65 b63 b67 * f i b67 * ga0 b62 j b68) b68
  rw [hstep]
  exact nf_D1R_h44' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h45 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b69, ∑ b70, ∑ b71, ∑ b72, ig b69 b70 * (ga1 i j b71 * (ga0 b70 b71 b72 * f b72 b69))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 c d a * ga1 i j c * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s d c a]
  try ring

private lemma nf_D1R_h46 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b69, ∑ b70, ∑ b71, ∑ b72, ig b69 b70 * (ga0 i j b71 * (ga0 b70 b71 b72 * f b72 b69))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j c * ga0 c d a * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s d c a]
  try ring

private lemma nf_D1R_h47 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b69, ∑ b70, ∑ b71, ∑ b73, ig b69 b70 * (ga1 i j b71 * (ga0 b70 b69 b73 * f b71 b73))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 c d a * ga1 i j b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s d c a, hfs b a]
  try ring

private lemma nf_D1R_h48 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b69, ∑ b70, ∑ b71, ∑ b73, ig b69 b70 * (ga0 i j b71 * (ga0 b70 b69 b73 * f b71 b73))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s d c b]
  try ring

private lemma nf_D1R_h49' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b76 b77 * ga0 b77 i b78 * f b78 b80 * ga1 b76 j b80) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga1 j d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c, hga0s c i a, hga1s d j b]
  try ring

private lemma nf_D1R_h49 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b74 b75 * (ig b76 b77 * (ga0 b77 i b78 * f b78 b75 * (ga1 b76 j b80 * cg b80 b74)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga1 j d b * ig c d) := by
  have hstep : (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b74 b75 * (ig b76 b77 * (ga0 b77 i b78 * f b78 b75 * (ga1 b76 j b80 * cg b80 b74)))) =
      (∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b76 b77 * ga0 b77 i b78 * f b78 b80 * ga1 b76 j b80) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b76 _ => Finset.sum_congr rfl (fun b77 _ => Finset.sum_congr rfl (fun b80 _ => Finset.sum_congr rfl (fun b78 _ => ?_))))
    rw [show (∑ b75, ∑ b74, ig b74 b75 * (ig b76 b77 * (ga0 b77 i b78 * f b78 b75 * (ga1 b76 j b80 * cg b80 b74)))) = (∑ b75, ∑ b74, cg b74 b80 * ig b74 b75 * (ig b76 b77 * ga0 b77 i b78 * f b78 b75 * ga1 b76 j b80)) from Finset.sum_congr rfl (fun b75 _ => Finset.sum_congr rfl (fun b74 _ => by rw [hcgs b80 b74]; try ring))]
    exact m0_collapse ig cg hcol (fun b75 => ig b76 b77 * ga0 b77 i b78 * f b78 b75 * ga1 b76 j b80) b80
  rw [hstep]
  exact nf_D1R_h49' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h50' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b76 b77 * ga0 b77 i b78 * f b78 b80 * ga0 b76 j b80) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c, hga0s c i a, hga0s d j b]
  try ring

private lemma nf_D1R_h50 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b74 b75 * (ig b76 b77 * (ga0 b77 i b78 * f b78 b75 * (ga0 b76 j b80 * cg b80 b74)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i c a * ga0 j d b * ig c d) := by
  have hstep : (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b74 b75 * (ig b76 b77 * (ga0 b77 i b78 * f b78 b75 * (ga0 b76 j b80 * cg b80 b74)))) =
      (∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b76 b77 * ga0 b77 i b78 * f b78 b80 * ga0 b76 j b80) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b76 _ => Finset.sum_congr rfl (fun b77 _ => Finset.sum_congr rfl (fun b80 _ => Finset.sum_congr rfl (fun b78 _ => ?_))))
    rw [show (∑ b75, ∑ b74, ig b74 b75 * (ig b76 b77 * (ga0 b77 i b78 * f b78 b75 * (ga0 b76 j b80 * cg b80 b74)))) = (∑ b75, ∑ b74, cg b74 b80 * ig b74 b75 * (ig b76 b77 * ga0 b77 i b78 * f b78 b75 * ga0 b76 j b80)) from Finset.sum_congr rfl (fun b75 _ => Finset.sum_congr rfl (fun b74 _ => by rw [hcgs b80 b74]; try ring))]
    exact m0_collapse ig cg hcol (fun b75 => ig b76 b77 * ga0 b77 i b78 * f b78 b75 * ga0 b76 j b80) b80
  rw [hstep]
  exact nf_D1R_h50' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h51' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b76 b77 * ga0 b77 b80 b79 * f i b79 * ga1 b76 j b80) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 b c a * ga1 j d b * ig c d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d c, hga0s c b a, hga1s d j b]
  try ring

private lemma nf_D1R_h51 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b74 b75 * (ig b76 b77 * (ga0 b77 b75 b79 * f i b79 * (ga1 b76 j b80 * cg b80 b74)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 b c a * ga1 j d b * ig c d) := by
  have hstep : (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b74 b75 * (ig b76 b77 * (ga0 b77 b75 b79 * f i b79 * (ga1 b76 j b80 * cg b80 b74)))) =
      (∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b76 b77 * ga0 b77 b80 b79 * f i b79 * ga1 b76 j b80) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b76 _ => Finset.sum_congr rfl (fun b77 _ => Finset.sum_congr rfl (fun b80 _ => Finset.sum_congr rfl (fun b79 _ => ?_))))
    rw [show (∑ b75, ∑ b74, ig b74 b75 * (ig b76 b77 * (ga0 b77 b75 b79 * f i b79 * (ga1 b76 j b80 * cg b80 b74)))) = (∑ b75, ∑ b74, cg b74 b80 * ig b74 b75 * (ig b76 b77 * ga0 b77 b75 b79 * f i b79 * ga1 b76 j b80)) from Finset.sum_congr rfl (fun b75 _ => Finset.sum_congr rfl (fun b74 _ => by rw [hcgs b80 b74]; try ring))]
    exact m0_collapse ig cg hcol (fun b75 => ig b76 b77 * ga0 b77 b75 b79 * f i b79 * ga1 b76 j b80) b80
  rw [hstep]
  exact nf_D1R_h51' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h52' {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b76 b77 * ga0 b77 b80 b79 * f i b79 * ga0 b76 j b80) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b c * ga0 c d a * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s d c a, hga0s b j c]
  try ring

private lemma nf_D1R_h52 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b74 b75 * (ig b76 b77 * (ga0 b77 b75 b79 * f i b79 * (ga0 b76 j b80 * cg b80 b74)))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b c * ga0 c d a * ig b d) := by
  have hstep : (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b74 b75 * (ig b76 b77 * (ga0 b77 b75 b79 * f i b79 * (ga0 b76 j b80 * cg b80 b74)))) =
      (∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b76 b77 * ga0 b77 b80 b79 * f i b79 * ga0 b76 j b80) := by
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm)))]
    rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ => Finset.sum_congr rfl (fun x3 _ => Finset.sum_comm))))]
    refine Finset.sum_congr rfl (fun b76 _ => Finset.sum_congr rfl (fun b77 _ => Finset.sum_congr rfl (fun b80 _ => Finset.sum_congr rfl (fun b79 _ => ?_))))
    rw [show (∑ b75, ∑ b74, ig b74 b75 * (ig b76 b77 * (ga0 b77 b75 b79 * f i b79 * (ga0 b76 j b80 * cg b80 b74)))) = (∑ b75, ∑ b74, cg b74 b80 * ig b74 b75 * (ig b76 b77 * ga0 b77 b75 b79 * f i b79 * ga0 b76 j b80)) from Finset.sum_congr rfl (fun b75 _ => Finset.sum_congr rfl (fun b74 _ => by rw [hcgs b80 b74]; try ring))]
    exact m0_collapse ig cg hcol (fun b75 => ig b76 b77 * ga0 b77 b75 b79 * f i b79 * ga0 b76 j b80) b80
  rw [hstep]
  exact nf_D1R_h52' ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j

private lemma nf_D1R_h53 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b81, ∑ b82, ∑ b83, ∑ b84, ig b81 b82 * (ga1 j i b83 * (ga0 b83 b82 b84 * f b84 b81))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 c d a * ga1 i j c * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga1s j i c]
  try ring

private lemma nf_D1R_h54 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b81, ∑ b82, ∑ b83, ∑ b84, ig b81 b82 * (ga0 j i b83 * (ga0 b83 b82 b84 * f b84 b81))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j c * ga0 c d a * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [hga0s j i c]
  try ring

private lemma nf_D1R_h55 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b81, ∑ b82, ∑ b83, ∑ b85, ig b81 b82 * (ga1 j i b83 * (ga0 b83 b81 b85 * f b82 b85))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 c d a * ga1 i j c * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d b, hga1s j i c, hfs b a]
  try ring

private lemma nf_D1R_h56 {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    (∑ b81, ∑ b82, ∑ b83, ∑ b85, ig b81 b82 * (ga0 j i b83 * (ga0 b83 b81 b85 * f b82 b85))) =
      (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j c * ga0 c d a * ig b d) := by
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun x0 (_ : x0 ∈ Finset.univ) => Finset.sum_congr rfl (fun x1 _ => Finset.sum_comm))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  rw [higs d b, hga0s j i c, hfs b a]
  try ring

lemma nf_D1R {n : ℕ} (ig cg f : Fin n → Fin n → ℝ)
    (dg dig ga0 ga1 gbg gb f3 : Fin n → Fin n → Fin n → ℝ)
    (ddg dga0 dga1 dgbg dgb : Fin n → Fin n → Fin n → Fin n → ℝ)
    (higs : ∀ a b, ig a b = ig b a)
    (hcgs : ∀ a b, cg a b = cg b a)
    (hfs : ∀ a b, f a b = f b a)
    (hdgs2 : ∀ m a b, dg m a b = dg m b a)
    (hga0s : ∀ a b k, ga0 a b k = ga0 b a k)
    (hga1s : ∀ a b k, ga1 a b k = ga1 b a k)
    (hgbgs : ∀ a b k, gbg a b k = gbg b a k)
    (hdga0s : ∀ m a b k, dga0 m a b k = dga0 m b a k)
    (hdga1s : ∀ m a b k, dga1 m a b k = dga1 m b a k)
    (hdgbgs : ∀ m a b k, dgbg m a b k = dgbg m b a k)
    (hddgs : ∀ m k a b, ddg m k a b = ddg m k b a)
    (hf3s : ∀ m a b, f3 m a b = f3 m b a)
    (hgbs : ∀ a b l, gb a b l = gb b a l)
    (hdgbs : ∀ m a b l, dgb m a b l = dgb m b a l)
    (hdigs : ∀ m a b, dig m a b = dig m b a)
    (hcol : ∀ l e, (∑ k, cg k e * ig k l) = if l = e then (1 : ℝ) else 0)
    (hga1e : ∀ a b k, ga1 a b k = (1 / 2 : ℝ) * ∑ l, ig k l * gb a b l)
    (hdga1e : ∀ m a b k, dga1 m a b k = (1 / 2 : ℝ) * ∑ l, (dig m k l * gb a b l + ig k l * dgb m a b l))
    (hdige : ∀ m a b, dig m a b = -∑ p, ∑ q, ig a p * ig q b * dg m p q)
    (hgbe : ∀ a b l, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgbe : ∀ m a b l, dgb m a b l = ddg m a l b + ddg m b l a - ddg m l a b)
    (i j : Fin n) :
    D1RF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i j =
      ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga0 j d b * ga1 e r a * ig c e * ig d r))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga0 j d b * gbg e r a * ig c e * ig d r))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga0 i d b * ga1 e r a * ig c e * ig d r))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga0 i d b * gbg e r a * ig c e * ig d r))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * ga0 c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * gbg c d b * ig c d)
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b c * ga0 c d a * ig b d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 b c a * ga1 j d b * ig c d))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * ga0 c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * gbg c d b * ig c d)
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b c * ga0 c d a * ig b d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 b c a * ga1 i d b * ig c d))
      + ((-4 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga1 c d b * ig c d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 c d a * ga1 i j b * ig c d)) := by
  have h1 : D1RF ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb i j =
      -((∑ b0, ∑ b3, ∑ b1, ∑ b2, ig b1 b2 * ga1 b1 b2 b0 * (ga0 b0 i b3 * f b3 j)) - (∑ b0, ∑ b3, ∑ b1, ∑ b2, ig b1 b2 * gbg b1 b2 b0 * (ga0 b0 i b3 * f b3 j))) + (-((∑ b0, ∑ b4, ∑ b1, ∑ b2, ig b1 b2 * ga1 b1 b2 b0 * (ga0 b0 j b4 * f i b4)) - (∑ b0, ∑ b4, ∑ b1, ∑ b2, ig b1 b2 * gbg b1 b2 b0 * (ga0 b0 j b4 * f i b4)))) + (-((∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b5 b6 * (ig b7 b8 * (ga0 i b8 b9 * f b9 b6 * (ga1 b7 j b11 * cg b11 b5)))) - (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b5 b6 * (ig b7 b8 * (ga0 i b8 b9 * f b9 b6 * (ga0 b7 j b11 * cg b11 b5))))) + (-((∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b5 b6 * (ig b7 b8 * (ga0 i b6 b10 * f b8 b10 * (ga1 b7 j b11 * cg b11 b5)))) - (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b5 b6 * (ig b7 b8 * (ga0 i b6 b10 * f b8 b10 * (ga0 b7 j b11 * cg b11 b5)))))) - (-((∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b16, ig b12 b13 * (ig b14 b15 * (ga0 i b15 b16 * f b16 b13 * (ga1 b12 b14 b18 * cg b18 j)))) - (∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b16, ig b12 b13 * (ig b14 b15 * (ga0 i b15 b16 * f b16 b13 * (gbg b12 b14 b18 * cg b18 j))))) + (-((∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b17, ig b12 b13 * (ig b14 b15 * (ga0 i b13 b17 * f b15 b17 * (ga1 b12 b14 b18 * cg b18 j)))) - (∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b17, ig b12 b13 * (ig b14 b15 * (ga0 i b13 b17 * f b15 b17 * (gbg b12 b14 b18 * cg b18 j))))))) - (-((∑ b19, ∑ b22, ∑ b20, ∑ b21, ig b20 b21 * ga1 b20 b21 b19 * (ga0 i j b22 * f b22 b19)) - (∑ b19, ∑ b22, ∑ b20, ∑ b21, ig b20 b21 * ga0 b20 b21 b19 * (ga0 i j b22 * f b22 b19))) + (-((∑ b19, ∑ b23, ∑ b20, ∑ b21, ig b20 b21 * ga1 b20 b21 b19 * (ga0 i b19 b23 * f j b23)) - (∑ b19, ∑ b23, ∑ b20, ∑ b21, ig b20 b21 * ga0 b20 b21 b19 * (ga0 i b19 b23 * f j b23))))) - (-((∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b28, ig b24 b25 * (ig b26 b27 * (ga0 b27 j b28 * f b28 b25 * (ga1 b24 i b30 * cg b30 b26)))) - (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b28, ig b24 b25 * (ig b26 b27 * (ga0 b27 j b28 * f b28 b25 * (ga0 b24 i b30 * cg b30 b26))))) + (-((∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b29, ig b24 b25 * (ig b26 b27 * (ga0 b27 b25 b29 * f j b29 * (ga1 b24 i b30 * cg b30 b26)))) - (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b29, ig b24 b25 * (ig b26 b27 * (ga0 b27 b25 b29 * f j b29 * (ga0 b24 i b30 * cg b30 b26))))))) - (-((∑ b31, ∑ b32, ∑ b33, ∑ b34, ig b31 b32 * (ga1 j i b33 * (ga0 b32 b33 b34 * f b34 b31))) - (∑ b31, ∑ b32, ∑ b33, ∑ b34, ig b31 b32 * (ga0 j i b33 * (ga0 b32 b33 b34 * f b34 b31)))) + (-((∑ b31, ∑ b32, ∑ b33, ∑ b35, ig b31 b32 * (ga1 j i b33 * (ga0 b32 b31 b35 * f b33 b35))) - (∑ b31, ∑ b32, ∑ b33, ∑ b35, ig b31 b32 * (ga0 j i b33 * (ga0 b32 b31 b35 * f b33 b35)))))) - (-((∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b36 b37 * (ig b38 b39 * (ga0 b39 j b40 * f b40 b37 * (ga1 b38 i b42 * cg b42 b36)))) - (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b36 b37 * (ig b38 b39 * (ga0 b39 j b40 * f b40 b37 * (ga0 b38 i b42 * cg b42 b36))))) + (-((∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b36 b37 * (ig b38 b39 * (ga0 b39 b37 b41 * f j b41 * (ga1 b38 i b42 * cg b42 b36)))) - (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b36 b37 * (ig b38 b39 * (ga0 b39 b37 b41 * f j b41 * (ga0 b38 i b42 * cg b42 b36)))))))) + (-((∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b43 b44 * (ig b45 b46 * (ga0 j b46 b47 * f b47 b44 * (ga1 b45 i b49 * cg b49 b43)))) - (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b43 b44 * (ig b45 b46 * (ga0 j b46 b47 * f b47 b44 * (ga0 b45 i b49 * cg b49 b43))))) + (-((∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b43 b44 * (ig b45 b46 * (ga0 j b44 b48 * f b46 b48 * (ga1 b45 i b49 * cg b49 b43)))) - (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b43 b44 * (ig b45 b46 * (ga0 j b44 b48 * f b46 b48 * (ga0 b45 i b49 * cg b49 b43)))))) - (-((∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b54, ig b50 b51 * (ig b52 b53 * (ga0 j b53 b54 * f b54 b51 * (ga1 b50 b52 b56 * cg b56 i)))) - (∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b54, ig b50 b51 * (ig b52 b53 * (ga0 j b53 b54 * f b54 b51 * (gbg b50 b52 b56 * cg b56 i))))) + (-((∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b55, ig b50 b51 * (ig b52 b53 * (ga0 j b51 b55 * f b53 b55 * (ga1 b50 b52 b56 * cg b56 i)))) - (∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b55, ig b50 b51 * (ig b52 b53 * (ga0 j b51 b55 * f b53 b55 * (gbg b50 b52 b56 * cg b56 i))))))) - (-((∑ b57, ∑ b60, ∑ b58, ∑ b59, ig b58 b59 * ga1 b58 b59 b57 * (ga0 j i b60 * f b60 b57)) - (∑ b57, ∑ b60, ∑ b58, ∑ b59, ig b58 b59 * ga0 b58 b59 b57 * (ga0 j i b60 * f b60 b57))) + (-((∑ b57, ∑ b61, ∑ b58, ∑ b59, ig b58 b59 * ga1 b58 b59 b57 * (ga0 j b57 b61 * f i b61)) - (∑ b57, ∑ b61, ∑ b58, ∑ b59, ig b58 b59 * ga0 b58 b59 b57 * (ga0 j b57 b61 * f i b61))))) - (-((∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b66, ig b62 b63 * (ig b64 b65 * (ga0 b65 i b66 * f b66 b63 * (ga1 b62 j b68 * cg b68 b64)))) - (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b66, ig b62 b63 * (ig b64 b65 * (ga0 b65 i b66 * f b66 b63 * (ga0 b62 j b68 * cg b68 b64))))) + (-((∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b67, ig b62 b63 * (ig b64 b65 * (ga0 b65 b63 b67 * f i b67 * (ga1 b62 j b68 * cg b68 b64)))) - (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b67, ig b62 b63 * (ig b64 b65 * (ga0 b65 b63 b67 * f i b67 * (ga0 b62 j b68 * cg b68 b64))))))) - (-((∑ b69, ∑ b70, ∑ b71, ∑ b72, ig b69 b70 * (ga1 i j b71 * (ga0 b70 b71 b72 * f b72 b69))) - (∑ b69, ∑ b70, ∑ b71, ∑ b72, ig b69 b70 * (ga0 i j b71 * (ga0 b70 b71 b72 * f b72 b69)))) + (-((∑ b69, ∑ b70, ∑ b71, ∑ b73, ig b69 b70 * (ga1 i j b71 * (ga0 b70 b69 b73 * f b71 b73))) - (∑ b69, ∑ b70, ∑ b71, ∑ b73, ig b69 b70 * (ga0 i j b71 * (ga0 b70 b69 b73 * f b71 b73)))))) - (-((∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b74 b75 * (ig b76 b77 * (ga0 b77 i b78 * f b78 b75 * (ga1 b76 j b80 * cg b80 b74)))) - (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b74 b75 * (ig b76 b77 * (ga0 b77 i b78 * f b78 b75 * (ga0 b76 j b80 * cg b80 b74))))) + (-((∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b74 b75 * (ig b76 b77 * (ga0 b77 b75 b79 * f i b79 * (ga1 b76 j b80 * cg b80 b74)))) - (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b74 b75 * (ig b76 b77 * (ga0 b77 b75 b79 * f i b79 * (ga0 b76 j b80 * cg b80 b74)))))))) + (-((∑ b81, ∑ b82, ∑ b83, ∑ b84, ig b81 b82 * (ga1 j i b83 * (ga0 b83 b82 b84 * f b84 b81))) - (∑ b81, ∑ b82, ∑ b83, ∑ b84, ig b81 b82 * (ga0 j i b83 * (ga0 b83 b82 b84 * f b84 b81)))) + (-((∑ b81, ∑ b82, ∑ b83, ∑ b85, ig b81 b82 * (ga1 j i b83 * (ga0 b83 b81 b85 * f b82 b85))) - (∑ b81, ∑ b82, ∑ b83, ∑ b85, ig b81 b82 * (ga0 j i b83 * (ga0 b83 b81 b85 * f b82 b85)))))) := by
    simp only [D1RF, vfbF, r3B]
    simp (config := { maxSteps := 10000000 }) only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    try ring
  have h2 : -((∑ b0, ∑ b3, ∑ b1, ∑ b2, ig b1 b2 * ga1 b1 b2 b0 * (ga0 b0 i b3 * f b3 j)) - (∑ b0, ∑ b3, ∑ b1, ∑ b2, ig b1 b2 * gbg b1 b2 b0 * (ga0 b0 i b3 * f b3 j))) + (-((∑ b0, ∑ b4, ∑ b1, ∑ b2, ig b1 b2 * ga1 b1 b2 b0 * (ga0 b0 j b4 * f i b4)) - (∑ b0, ∑ b4, ∑ b1, ∑ b2, ig b1 b2 * gbg b1 b2 b0 * (ga0 b0 j b4 * f i b4)))) + (-((∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b5 b6 * (ig b7 b8 * (ga0 i b8 b9 * f b9 b6 * (ga1 b7 j b11 * cg b11 b5)))) - (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b9, ig b5 b6 * (ig b7 b8 * (ga0 i b8 b9 * f b9 b6 * (ga0 b7 j b11 * cg b11 b5))))) + (-((∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b5 b6 * (ig b7 b8 * (ga0 i b6 b10 * f b8 b10 * (ga1 b7 j b11 * cg b11 b5)))) - (∑ b5, ∑ b6, ∑ b7, ∑ b8, ∑ b11, ∑ b10, ig b5 b6 * (ig b7 b8 * (ga0 i b6 b10 * f b8 b10 * (ga0 b7 j b11 * cg b11 b5)))))) - (-((∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b16, ig b12 b13 * (ig b14 b15 * (ga0 i b15 b16 * f b16 b13 * (ga1 b12 b14 b18 * cg b18 j)))) - (∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b16, ig b12 b13 * (ig b14 b15 * (ga0 i b15 b16 * f b16 b13 * (gbg b12 b14 b18 * cg b18 j))))) + (-((∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b17, ig b12 b13 * (ig b14 b15 * (ga0 i b13 b17 * f b15 b17 * (ga1 b12 b14 b18 * cg b18 j)))) - (∑ b12, ∑ b13, ∑ b14, ∑ b15, ∑ b18, ∑ b17, ig b12 b13 * (ig b14 b15 * (ga0 i b13 b17 * f b15 b17 * (gbg b12 b14 b18 * cg b18 j))))))) - (-((∑ b19, ∑ b22, ∑ b20, ∑ b21, ig b20 b21 * ga1 b20 b21 b19 * (ga0 i j b22 * f b22 b19)) - (∑ b19, ∑ b22, ∑ b20, ∑ b21, ig b20 b21 * ga0 b20 b21 b19 * (ga0 i j b22 * f b22 b19))) + (-((∑ b19, ∑ b23, ∑ b20, ∑ b21, ig b20 b21 * ga1 b20 b21 b19 * (ga0 i b19 b23 * f j b23)) - (∑ b19, ∑ b23, ∑ b20, ∑ b21, ig b20 b21 * ga0 b20 b21 b19 * (ga0 i b19 b23 * f j b23))))) - (-((∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b28, ig b24 b25 * (ig b26 b27 * (ga0 b27 j b28 * f b28 b25 * (ga1 b24 i b30 * cg b30 b26)))) - (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b28, ig b24 b25 * (ig b26 b27 * (ga0 b27 j b28 * f b28 b25 * (ga0 b24 i b30 * cg b30 b26))))) + (-((∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b29, ig b24 b25 * (ig b26 b27 * (ga0 b27 b25 b29 * f j b29 * (ga1 b24 i b30 * cg b30 b26)))) - (∑ b24, ∑ b25, ∑ b26, ∑ b27, ∑ b30, ∑ b29, ig b24 b25 * (ig b26 b27 * (ga0 b27 b25 b29 * f j b29 * (ga0 b24 i b30 * cg b30 b26))))))) - (-((∑ b31, ∑ b32, ∑ b33, ∑ b34, ig b31 b32 * (ga1 j i b33 * (ga0 b32 b33 b34 * f b34 b31))) - (∑ b31, ∑ b32, ∑ b33, ∑ b34, ig b31 b32 * (ga0 j i b33 * (ga0 b32 b33 b34 * f b34 b31)))) + (-((∑ b31, ∑ b32, ∑ b33, ∑ b35, ig b31 b32 * (ga1 j i b33 * (ga0 b32 b31 b35 * f b33 b35))) - (∑ b31, ∑ b32, ∑ b33, ∑ b35, ig b31 b32 * (ga0 j i b33 * (ga0 b32 b31 b35 * f b33 b35)))))) - (-((∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b36 b37 * (ig b38 b39 * (ga0 b39 j b40 * f b40 b37 * (ga1 b38 i b42 * cg b42 b36)))) - (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b40, ig b36 b37 * (ig b38 b39 * (ga0 b39 j b40 * f b40 b37 * (ga0 b38 i b42 * cg b42 b36))))) + (-((∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b36 b37 * (ig b38 b39 * (ga0 b39 b37 b41 * f j b41 * (ga1 b38 i b42 * cg b42 b36)))) - (∑ b36, ∑ b37, ∑ b38, ∑ b39, ∑ b42, ∑ b41, ig b36 b37 * (ig b38 b39 * (ga0 b39 b37 b41 * f j b41 * (ga0 b38 i b42 * cg b42 b36)))))))) + (-((∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b43 b44 * (ig b45 b46 * (ga0 j b46 b47 * f b47 b44 * (ga1 b45 i b49 * cg b49 b43)))) - (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b47, ig b43 b44 * (ig b45 b46 * (ga0 j b46 b47 * f b47 b44 * (ga0 b45 i b49 * cg b49 b43))))) + (-((∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b43 b44 * (ig b45 b46 * (ga0 j b44 b48 * f b46 b48 * (ga1 b45 i b49 * cg b49 b43)))) - (∑ b43, ∑ b44, ∑ b45, ∑ b46, ∑ b49, ∑ b48, ig b43 b44 * (ig b45 b46 * (ga0 j b44 b48 * f b46 b48 * (ga0 b45 i b49 * cg b49 b43)))))) - (-((∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b54, ig b50 b51 * (ig b52 b53 * (ga0 j b53 b54 * f b54 b51 * (ga1 b50 b52 b56 * cg b56 i)))) - (∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b54, ig b50 b51 * (ig b52 b53 * (ga0 j b53 b54 * f b54 b51 * (gbg b50 b52 b56 * cg b56 i))))) + (-((∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b55, ig b50 b51 * (ig b52 b53 * (ga0 j b51 b55 * f b53 b55 * (ga1 b50 b52 b56 * cg b56 i)))) - (∑ b50, ∑ b51, ∑ b52, ∑ b53, ∑ b56, ∑ b55, ig b50 b51 * (ig b52 b53 * (ga0 j b51 b55 * f b53 b55 * (gbg b50 b52 b56 * cg b56 i))))))) - (-((∑ b57, ∑ b60, ∑ b58, ∑ b59, ig b58 b59 * ga1 b58 b59 b57 * (ga0 j i b60 * f b60 b57)) - (∑ b57, ∑ b60, ∑ b58, ∑ b59, ig b58 b59 * ga0 b58 b59 b57 * (ga0 j i b60 * f b60 b57))) + (-((∑ b57, ∑ b61, ∑ b58, ∑ b59, ig b58 b59 * ga1 b58 b59 b57 * (ga0 j b57 b61 * f i b61)) - (∑ b57, ∑ b61, ∑ b58, ∑ b59, ig b58 b59 * ga0 b58 b59 b57 * (ga0 j b57 b61 * f i b61))))) - (-((∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b66, ig b62 b63 * (ig b64 b65 * (ga0 b65 i b66 * f b66 b63 * (ga1 b62 j b68 * cg b68 b64)))) - (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b66, ig b62 b63 * (ig b64 b65 * (ga0 b65 i b66 * f b66 b63 * (ga0 b62 j b68 * cg b68 b64))))) + (-((∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b67, ig b62 b63 * (ig b64 b65 * (ga0 b65 b63 b67 * f i b67 * (ga1 b62 j b68 * cg b68 b64)))) - (∑ b62, ∑ b63, ∑ b64, ∑ b65, ∑ b68, ∑ b67, ig b62 b63 * (ig b64 b65 * (ga0 b65 b63 b67 * f i b67 * (ga0 b62 j b68 * cg b68 b64))))))) - (-((∑ b69, ∑ b70, ∑ b71, ∑ b72, ig b69 b70 * (ga1 i j b71 * (ga0 b70 b71 b72 * f b72 b69))) - (∑ b69, ∑ b70, ∑ b71, ∑ b72, ig b69 b70 * (ga0 i j b71 * (ga0 b70 b71 b72 * f b72 b69)))) + (-((∑ b69, ∑ b70, ∑ b71, ∑ b73, ig b69 b70 * (ga1 i j b71 * (ga0 b70 b69 b73 * f b71 b73))) - (∑ b69, ∑ b70, ∑ b71, ∑ b73, ig b69 b70 * (ga0 i j b71 * (ga0 b70 b69 b73 * f b71 b73)))))) - (-((∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b74 b75 * (ig b76 b77 * (ga0 b77 i b78 * f b78 b75 * (ga1 b76 j b80 * cg b80 b74)))) - (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b78, ig b74 b75 * (ig b76 b77 * (ga0 b77 i b78 * f b78 b75 * (ga0 b76 j b80 * cg b80 b74))))) + (-((∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b74 b75 * (ig b76 b77 * (ga0 b77 b75 b79 * f i b79 * (ga1 b76 j b80 * cg b80 b74)))) - (∑ b74, ∑ b75, ∑ b76, ∑ b77, ∑ b80, ∑ b79, ig b74 b75 * (ig b76 b77 * (ga0 b77 b75 b79 * f i b79 * (ga0 b76 j b80 * cg b80 b74)))))))) + (-((∑ b81, ∑ b82, ∑ b83, ∑ b84, ig b81 b82 * (ga1 j i b83 * (ga0 b83 b82 b84 * f b84 b81))) - (∑ b81, ∑ b82, ∑ b83, ∑ b84, ig b81 b82 * (ga0 j i b83 * (ga0 b83 b82 b84 * f b84 b81)))) + (-((∑ b81, ∑ b82, ∑ b83, ∑ b85, ig b81 b82 * (ga1 j i b83 * (ga0 b83 b81 b85 * f b82 b85))) - (∑ b81, ∑ b82, ∑ b83, ∑ b85, ig b81 b82 * (ga0 j i b83 * (ga0 b83 b81 b85 * f b82 b85)))))) =
      ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga0 j d b * ga1 e r a * ig c e * ig d r))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg i a * f b c * ga0 j d b * gbg e r a * ig c e * ig d r))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga0 i d b * ga1 e r a * ig c e * ig d r))
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ r, cg j a * f b c * ga0 i d b * gbg e r a * ig c e * ig d r))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * ga0 c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b a * gbg c d b * ig c d)
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 j b c * ga0 c d a * ig b d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f i a * ga0 b c a * ga1 j d b * ig c d))
      + (-(∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * ga0 c d b * ig c d))
      + (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b a * gbg c d b * ig c d)
      + ((-2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 i b c * ga0 c d a * ig b d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f j a * ga0 b c a * ga1 i d b * ig c d))
      + ((-4 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga0 c d b * ig c d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 i j a * ga1 c d b * ig c d))
      + ((2 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d, f a b * ga0 c d a * ga1 i j b * ig c d)) := by
    linear_combination - nf_D1R_h1 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h2 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h3 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h4 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h5 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h6 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h7 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h8 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h9 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h10 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h11 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h12 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h13 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h14 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h15 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h16 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h17 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h18 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h19 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h20 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h21 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h22 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h23 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h24 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h25 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h26 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h27 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h28 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h29 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h30 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h31 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h32 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h33 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h34 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h35 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h36 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h37 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h38 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h39 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h40 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h41 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h42 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h43 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h44 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h45 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h46 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h47 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h48 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h49 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h50 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h51 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h52 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h53 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h54 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j - nf_D1R_h55 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j + nf_D1R_h56 ig cg f dg dig ga0 ga1 gbg gb f3 ddg dga0 dga1 dgbg dgb higs hcgs hfs hdgs2 hga0s hga1s hgbgs hdga0s hdga1s hdgbgs hddgs hf3s hgbs hdgbs hdigs hcol hga1e hdga1e hdige hgbe hdgbe i j
  exact h1.trans h2

end Gen
end M0Abstract
end M0AbstractLayer
end

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
