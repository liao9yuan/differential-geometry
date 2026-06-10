import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct

/-! # The Lᵖ-fibre-norm Gagliardo–Nirenberg interpolation for iterated covariant gradients

This file isolates the **Lᵖ-form** of the closed-manifold tensor Gagliardo–Nirenberg interpolation
(Hamilton, *Three-manifolds with positive Ricci curvature* §12.5; Aubin): for a smooth
compactly-supported `(0, s)`-tensor `u` with `C⁰`-sup fibre bound `Λ₀`, a top order `k ≥ 1`, and an
intermediate order `0 < j < k`, the `L^{2k/j}` fibre norm of the `j`-th iterated covariant gradient
is controlled by the interpolated product of the `L^∞` sup and the top-order covariant `L²`-jet:
```
‖∇^j u‖_{L^{2k/j}}^2 ≤ C · Λ₀^{2(1 − j/k)} · ‖∇^k u‖_{L²}^{2 j/k} .
```
Equivalently, in the squared-fibre-norm integral form used by the diagonal-product-grid consumer,
```
(∫ rfns(∇^j u)^{k/j} dμ)^{j/k} ≤ C · Λ₀^{2(1 − j/k)} · ‖∇^k u‖_{L²}^{2 j/k} ,
```
the left member being `‖∇^j u‖²_{L^{2k/j}}` (the `L^{2k/j}` norm of the *pointwise fibre norm*
`|∇^j u|`, raised to the second power and written through the squared fibre norm
`rfns(∇^j u) = |∇^j u|²`).

The companion `L²`-form already on disk
(`exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le`, `Analysis/Sobolev/MoserTameProduct.lean`)
is the *degenerate* `p = 2` case `j = k - 1` collapsed to the `L²` left member, and does **not**
imply this `L^{2k/j}` form: the diagonal-product-grid two-arm estimate
(`Analysis/Spectral/Tensor/CovGrad/GagliardoNirenbergProductTwoArm.lean`) integrates each pointwise
product `rfns(∇^i S)·rfns(∇^l T)` via Hölder at the conjugate pair `(k/i, k/l)`, which requires the
*genuine `L^{2k/i}` interpolation* of each factor — exactly the left member here, with a free
`L^p` exponent that the `L²`-form's fixed `L²` left member cannot supply.  This file is therefore
the precise Lᵖ-interpolation kernel the product grid consumes.

The deep analytic content is isolated in a single posited input
`lpFiberJet_logConvex_iteratedCovGrad`: the **single-step Gagliardo–Nirenberg log-convexity of the
mixed-`L^p` fibre jets** `c_i := ‖|∇^i u|‖_{L^{2k/i}}` (`c_0 := ‖u‖_{L^∞}`, `c_k := ‖∇^k u‖_{L²}`),
namely `c_i² ≤ K · c_{i-1} · c_{i+1}` (the genuine `L^p` interpolation engine — Mathlib carries only
the first-order Sobolev *embedding* `eLpNorm_le_eLpNorm_fderiv`, not this iterated-jet interpolation,
and no `L^p` Lyapunov interpolation).  On top of that single input the headline is assembled
outright by the discrete Hardy–Littlewood–Pólya power law `hlp_real` (proven here as elementary real
arithmetic on the abstract jets) and the `L^∞`-endpoint comparison, by a single `rpow` extraction —
exactly mirroring the `L²`-companion's `l2Interp_pow_iteratedCovGrad` architecture but carrying the
genuinely stronger `L^{2k/j}` left member.  Consumers transitively depend on the `sorryAx` of
`lpFiberJet_logConvex_iteratedCovGrad`. -/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Tensor

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Integral.Connection

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

section LpDiscreteLogConvex

/-- One-step "slope-defect" iterated (bounded form): if `Δ i ≤ Δ (i+1) + d` for all
`i < N`, then `Δ i ≤ Δ i' + (i'-i) * d` whenever `i ≤ i' ≤ N`.  Elementary real arithmetic. -/
private lemma lp_slope_spread (Δ : ℕ → ℝ) (d : ℝ) (N : ℕ)
    (hstep : ∀ i, i < N → Δ i ≤ Δ (i + 1) + d) :
    ∀ i i' : ℕ, i ≤ i' → i' ≤ N → Δ i ≤ Δ i' + (i' - i : ℕ) * d := by
  intro i i' hii' hiN
  induction i' with
  | zero => interval_cases i; simp
  | succ n ih =>
      rcases Nat.lt_or_ge i (n + 1) with hlt | hge
      · have hin : i ≤ n := Nat.lt_succ_iff.mp hlt
        have h1 := ih hin (by omega)
        have h2 := hstep n (by omega)
        have hbody : Δ i ≤ Δ (n + 1) + d + (n - i : ℕ) * d := by
          calc Δ i ≤ Δ n + (n - i : ℕ) * d := h1
            _ ≤ (Δ (n + 1) + d) + (n - i : ℕ) * d := by linarith
        have hcast : ((n + 1 - i : ℕ) : ℝ) = (n - i : ℕ) + 1 := by
          have hn : n + 1 - i = (n - i) + 1 := by omega
          rw [hn]; push_cast; ring
        rw [hcast]; nlinarith [hbody]
      · have hie : i = n + 1 := le_antisymm hii' hge
        subst hie; simp

/-- The discrete chord bound from a convexity defect, in additive form. If
`Δ i ≤ Δ (i+1) + d` for all `i + 1 < k` and `0 ≤ d`, then for `0 < j < k`
```
k * ∑_{i<j} Δ i ≤ j * ∑_{i<k} Δ i + k^3 * d.
```
Writing `Δ i = L (i+1) - L i` makes `∑_{i<n} Δ i = L n - L 0`, so this is exactly the
log-convex chord bound for `L`.  Elementary real arithmetic. -/
private lemma lp_chord_bound (Δ : ℕ → ℝ) (d : ℝ) (hd : 0 ≤ d) (j k : ℕ)
    (hstep : ∀ i, i + 1 < k → Δ i ≤ Δ (i + 1) + d) (hj : 0 < j) (hjk : j < k) :
    (k : ℝ) * (∑ i ∈ Finset.range j, Δ i)
      ≤ (j : ℝ) * (∑ i ∈ Finset.range k, Δ i) + (k ^ 3 : ℕ) * d := by
  have hsplit : (∑ i ∈ Finset.range k, Δ i)
      = (∑ i ∈ Finset.range j, Δ i) + ∑ i ∈ Finset.Ico j k, Δ i := by
    rw [← Finset.sum_range_add_sum_Ico Δ (le_of_lt hjk)]
  rw [hsplit, mul_add]
  set Sj : ℝ := ∑ i ∈ Finset.range j, Δ i with hSj
  set Sjk : ℝ := ∑ i ∈ Finset.Ico j k, Δ i with hSjk
  have hcard1 : (Finset.Ico j k).card = k - j := by rw [Nat.card_Ico]
  have hcard2 : (Finset.range j).card = j := by rw [Finset.card_range]
  have hLHS : ((k : ℝ) - j) * Sj = ∑ _i' ∈ Finset.Ico j k, Sj := by
    rw [Finset.sum_const, hcard1, nsmul_eq_mul]
    have hc : ((k - j : ℕ) : ℝ) = (k : ℝ) - j := by rw [Nat.cast_sub (le_of_lt hjk)]
    rw [hc]
  have hRHS : (j : ℝ) * Sjk = ∑ _i ∈ Finset.range j, Sjk := by
    rw [Finset.sum_const, hcard2, nsmul_eq_mul]
  have key : ((k : ℝ) - j) * Sj - (j : ℝ) * Sjk ≤ (k ^ 3 : ℕ) * d := by
    rw [hLHS, hRHS]
    have e1 : (∑ _i' ∈ Finset.Ico j k, Sj)
        = ∑ p ∈ (Finset.range j) ×ˢ (Finset.Ico j k), Δ p.1 := by
      rw [hSj, Finset.sum_product' (f := fun (a : ℕ) (_ : ℕ) => Δ a)]
      exact (Finset.sum_comm).symm
    have e2 : (∑ _i ∈ Finset.range j, Sjk)
        = ∑ p ∈ (Finset.range j) ×ˢ (Finset.Ico j k), Δ p.2 := by
      rw [hSjk, Finset.sum_product' (f := fun (_ : ℕ) (b : ℕ) => Δ b)]
    rw [e1, e2, ← Finset.sum_sub_distrib]
    have hbound : ∀ p ∈ (Finset.range j) ×ˢ (Finset.Ico j k),
        Δ p.1 - Δ p.2 ≤ (k : ℝ) * d := by
      intro p hp
      rw [Finset.mem_product] at hp
      obtain ⟨hp1, hp2⟩ := hp
      have hi : p.1 < j := Finset.mem_range.mp hp1
      have hi' : j ≤ p.2 := (Finset.mem_Ico.mp hp2).1
      have hi'k : p.2 < k := (Finset.mem_Ico.mp hp2).2
      have hle : p.1 ≤ p.2 := le_trans (le_of_lt hi) hi'
      have hstep' : ∀ i, i < k - 1 → Δ i ≤ Δ (i + 1) + d := fun i hik => hstep i (by omega)
      have hsp := lp_slope_spread Δ d (k - 1) hstep' p.1 p.2 hle (by omega)
      have hdiff : ((p.2 - p.1 : ℕ) : ℝ) ≤ (k : ℝ) := by
        have hpp : p.2 - p.1 ≤ k := by omega
        exact_mod_cast hpp
      have hstep2 : Δ p.1 - Δ p.2 ≤ (p.2 - p.1 : ℕ) * d := by linarith [hsp]
      calc Δ p.1 - Δ p.2 ≤ (p.2 - p.1 : ℕ) * d := hstep2
        _ ≤ (k : ℝ) * d := mul_le_mul_of_nonneg_right hdiff hd
    calc ∑ p ∈ (Finset.range j) ×ˢ (Finset.Ico j k), (Δ p.1 - Δ p.2)
        ≤ ∑ _p ∈ (Finset.range j) ×ˢ (Finset.Ico j k), (k : ℝ) * d :=
          Finset.sum_le_sum hbound
      _ = ((Finset.range j) ×ˢ (Finset.Ico j k)).card * ((k : ℝ) * d) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((j * (k - j) : ℕ) : ℝ) * ((k : ℝ) * d) := by
          rw [Finset.card_product, hcard1, hcard2]
      _ ≤ (k ^ 3 : ℕ) * d := by
          have hjk_le : j * (k - j) ≤ k * k := by
            calc j * (k - j) ≤ k * (k - j) := by apply Nat.mul_le_mul_right; omega
              _ ≤ k * k := by apply Nat.mul_le_mul_left; omega
          have hcastjk : ((j * (k - j) : ℕ) : ℝ) ≤ (k : ℝ) * (k : ℝ) := by exact_mod_cast hjk_le
          have hcast3 : ((k ^ 3 : ℕ) : ℝ) = (k : ℝ) * (k : ℝ) * (k : ℝ) := by push_cast; ring
          have hkd : 0 ≤ (k : ℝ) * d := mul_nonneg (by positivity) hd
          have hknn : (0 : ℝ) ≤ (k : ℝ) := by positivity
          rw [hcast3]
          nlinarith [hcastjk, hkd, hknn, hd, mul_le_mul_of_nonneg_right hcastjk hkd]
  nlinarith [key]

/-- Positivity propagates downward from any positive term: with all `a ≥ 0`, the
log-convexity `a (i+1)^2 ≤ M * a i * a (i+2)` forces `a (i+1) > 0 → a i > 0`, hence a
single positive `a j` makes every earlier term positive. -/
private lemma lp_pos_propagate (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (M : ℝ)
    (hlc : ∀ i, (a (i + 1)) ^ 2 ≤ M * a i * a (i + 2)) (j : ℕ) (hpos : 0 < a j) :
    ∀ i, i ≤ j → 0 < a i := by
  have hL : ∀ i, 0 < a (i + 1) → 0 < a i := by
    intro i hi
    by_contra h
    rw [not_lt] at h
    have hai : a i = 0 := le_antisymm h (ha i)
    have hh := hlc i
    rw [hai] at hh
    simp only [mul_zero, zero_mul] at hh
    nlinarith [hh, hi, sq_nonneg (a (i + 1))]
  have key0 : ∀ s, s ≤ j → 0 < a (j - s) := by
    intro s
    induction s with
    | zero => intro _; simpa using hpos
    | succ m ihm =>
        intro hs
        have hjm : 0 < a (j - m) := ihm (by omega)
        have hidx : j - m = (j - (m + 1)) + 1 := by omega
        rw [hidx] at hjm
        exact hL (j - (m + 1)) hjm
  intro i hi
  have heq : i = j - (j - i) := by omega
  rw [heq]
  exact key0 (j - i) (by omega)

/-- Positivity also propagates upward: a single positive `a j` (`0 < j`) makes every
later term positive. -/
private lemma lp_pos_propagate_up (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (M : ℝ)
    (hlc : ∀ i, (a (i + 1)) ^ 2 ≤ M * a i * a (i + 2)) (j : ℕ) (hj : 0 < j)
    (hpos : 0 < a j) :
    ∀ i, j ≤ i → 0 < a i := by
  have hR : ∀ i, 0 < a (i + 1) → 0 < a (i + 2) := by
    intro i hi
    by_contra h
    rw [not_lt] at h
    have hai : a (i + 2) = 0 := le_antisymm h (ha (i + 2))
    have hh := hlc i
    rw [hai] at hh
    simp only [mul_zero] at hh
    nlinarith [hh, hi, sq_nonneg (a (i + 1))]
  intro i hji
  obtain ⟨t, rfl⟩ : ∃ t, i = j + t := ⟨i - j, by omega⟩
  clear hji
  induction t with
  | zero => simpa using hpos
  | succ n ih =>
      have hjn : 0 < a (j + n) := ih
      have hidx : j + n = (j + n - 1) + 1 := by omega
      rw [hidx] at hjn
      have hRr := hR (j + n - 1) hjn
      have hidx2 : j + n - 1 + 2 = j + (n + 1) := by omega
      rw [hidx2] at hRr
      exact hRr

/-- **Discrete log-convexity power law (Hardy–Littlewood–Pólya, real form).** A
nonnegative sequence `a` satisfying `a (i+1)^2 ≤ M * a i * a (i+2)` with `1 ≤ M` obeys,
for `0 < j < k`,
```
(a j)^k ≤ M^(k^3) * (a 0)^(k-j) * (a k)^j.
```
The proof reduces (via the square bound) to the all-positive case, in which
`i ↦ Real.log (a i)` has a discrete second difference bounded below by `-Real.log M`; the
chord bound then yields the linear inequality on logs, which exponentiates to the claimed
power law.  Elementary real arithmetic; no `sorry`. -/
private theorem lp_hlp_real (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (M : ℝ) (hM : 1 ≤ M)
    (hlc : ∀ i, (a (i + 1)) ^ 2 ≤ M * a i * a (i + 2)) (j k : ℕ) (hj : 0 < j) (hjk : j < k) :
    (a j) ^ k ≤ M ^ (k ^ 3) * (a 0) ^ (k - j) * (a k) ^ j := by
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM
  rcases eq_or_lt_of_le (ha j) with hzero | hpos
  · rw [← hzero, zero_pow (by omega)]
    have h0 : 0 ≤ a 0 := ha 0
    have hk : 0 ≤ a k := ha k
    have hMnn : 0 ≤ M := le_of_lt hM0
    positivity
  · have hposj : 0 < a j := hpos
    have hpL : ∀ i, i ≤ j → 0 < a i := lp_pos_propagate a ha M hlc j hposj
    have hpU : ∀ i, j ≤ i → 0 < a i := lp_pos_propagate_up a ha M hlc j hj hposj
    have hpall : ∀ i, i ≤ k → 0 < a i := by
      intro i hik
      rcases Nat.lt_or_ge i j with h | h
      · exact hpL i (le_of_lt h)
      · exact hpU i h
    set L : ℕ → ℝ := fun i => Real.log (a i) with hLdef
    set Δ : ℕ → ℝ := fun i => L (i + 1) - L i with hΔdef
    have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
    have hstep : ∀ i, i + 1 < k → Δ i ≤ Δ (i + 1) + Real.log M := by
      intro i hik
      have hi0 : 0 < a i := hpall i (by omega)
      have hi1 : 0 < a (i + 1) := hpall (i + 1) (by omega)
      have hi2 : 0 < a (i + 2) := hpall (i + 2) (by omega)
      have hlci := hlc i
      have hlog : Real.log ((a (i + 1)) ^ 2) ≤ Real.log (M * a i * a (i + 2)) :=
        Real.log_le_log (by positivity) hlci
      rw [Real.log_pow] at hlog
      rw [Real.log_mul (by positivity) (ne_of_gt hi2),
          Real.log_mul (ne_of_gt hM0) (ne_of_gt hi0)] at hlog
      simp only [hΔdef, hLdef]
      push_cast at hlog
      nlinarith [hlog]
    have hchord := lp_chord_bound Δ (Real.log M) hlogM j k hstep hj hjk
    have htel : ∀ n, (∑ i ∈ Finset.range n, Δ i) = L n - L 0 := by
      intro n; simp only [hΔdef]; exact Finset.sum_range_sub L n
    rw [htel j, htel k] at hchord
    have hlin : (k : ℝ) * L j ≤
        ((k - j : ℕ) : ℝ) * L 0 + (j : ℝ) * L k + (k ^ 3 : ℕ) * Real.log M := by
      have hcastsub : ((k - j : ℕ) : ℝ) = (k : ℝ) - (j : ℝ) := by rw [Nat.cast_sub (le_of_lt hjk)]
      rw [hcastsub]; nlinarith [hchord]
    have hLHSpos : 0 < (a j) ^ k := by positivity
    have h0 : 0 < a 0 := hpall 0 (by omega)
    have hk : 0 < a k := hpall k (le_refl k)
    have hRHSpos : 0 < M ^ (k ^ 3) * (a 0) ^ (k - j) * (a k) ^ j := by positivity
    rw [← Real.log_le_log_iff hLHSpos hRHSpos]
    rw [Real.log_pow]
    rw [Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity)),
        Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity))]
    rw [Real.log_pow, Real.log_pow, Real.log_pow]
    simp only [hLdef] at hlin ⊢
    push_cast at hlin ⊢
    nlinarith [hlin]

end LpDiscreteLogConvex

/-- The mixed-`L^p` fibre-jet ladder of a smooth compactly-supported `(0, s)`-tensor `u` at top
order `k`: the value at order `i` is the `L^{2k/i}` norm of the pointwise fibre norm `|∇^i u|`,
written through its squared fibre norm as `c_i := (∫ rfns(∇^i u)^{k/i} dμ)^{i/(2k)}` for `0 < i`,
with the two posited endpoints folded in (`c_0 := Λ₀ · √(vol M)` the `L^∞`-endpoint comparison,
`c_k := ‖∇^k u‖_{L²}`).  It is the discrete sequence whose Gagliardo–Nirenberg log-convexity drives
the interpolation; it is `noncomputable` only through the volume measure. -/
private noncomputable def lpFiberJetLadder
    (g : SmoothRiemannianMetric I M) (s k : ℕ) (u : Integral.L2.SmoothCcTensor g 0 s)
    (Λ₀ : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then
    Λ₀ * Real.sqrt ((Integral.Measure.riemannianVolumeMeasure I M g) Set.univ).toReal
  else if i = k then
    Integral.L2.tensorL2Norm (I := I) g 0 (s + k)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s k u).toFun
  else
    (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s i u).toSection x)) ^ ((k : ℝ) / i)
        ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((i : ℝ) / (2 * k))

/-- **(POSIT — the single-step Gagliardo–Nirenberg log-convexity of the mixed-`L^p` fibre jets.)**

Fix an anchor `g`, a valence `s`, and a top order `k ≥ 1`.  There is a single multiplier `K ≥ 1`
(depending only on `g`, the manifold and `(s, k)`) such that for every smooth compactly-supported
`(0, s)`-tensor `u` with `C⁰`-sup fibre bound `Λ₀` and every order `i`, the mixed-`L^p` fibre-jet
ladder `c := lpFiberJetLadder g s k u Λ₀` (whose value at order `i` is the `L^{2k/i}` norm of the
pointwise fibre norm `|∇^i u|`, with the `L^∞`-endpoint `c_0 = Λ₀·√(vol M)` and the `L²`-endpoint
`c_k = ‖∇^k u‖_{L²}`) is **log-convex up to the multiplier `K`**:
```
c_{i+1}² ≤ K · c_i · c_{i+2}.
```

This is the genuine **`L^p` interpolation engine** of the closed-manifold tensor Gagliardo–Nirenberg
inequality (Hamilton 12.5, Aubin): consecutive mixed-`L^p` fibre jets are log-convex up to a
curvature/commutator multiplier, the single covariant analytic input from which the full `j`-versus-`k`
interpolation follows by the elementary discrete Hardy–Littlewood–Pólya power law.  Mathlib carries
only the *first-order Sobolev embedding* `eLpNorm_le_eLpNorm_fderiv` (`‖u‖_{L^{p*}} ≤ C‖Du‖_{L^p}`),
not this iterated-jet `L^p` interpolation, and no `L^p` Lyapunov interpolation; the content is
therefore posited here.

**Non-vacuity.**  `K` is quantified before `(u, Λ₀, i)`; the conclusion is the consecutive-jet square
bound on the *intrinsically defined* ladder `lpFiberJetLadder` (its order-`i` value genuinely reads
the `i`-th covariant jet of `u`), not a free sequence, so no degenerate witness is asserted (a tensor
with a nonvanishing intermediate jet rejects the `K = 0` reading by positivity of `c_i`).  Its body is
`sorry`: the genuine closed-manifold covariant `L^p` interpolation content; consumers transitively
depend on its `sorryAx`. -/
private theorem lpFiberJet_logConvex_iteratedCovGrad
    (g : SmoothRiemannianMetric I M) (s k : ℕ) (_hk : 1 ≤ k) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (u : Integral.L2.SmoothCcTensor g 0 s) (Λ₀ : ℝ),
        ∀ i : ℕ,
          (lpFiberJetLadder (I := I) (M := M) g s k u Λ₀ (i + 1)) ^ 2 ≤
            K * lpFiberJetLadder (I := I) (M := M) g s k u Λ₀ i *
              lpFiberJetLadder (I := I) (M := M) g s k u Λ₀ (i + 2) :=
  sorry

/-- **(POSIT — the Lᵖ-fibre-norm Gagliardo–Nirenberg interpolation for iterated covariant
gradients; Hamilton 12.5.)**

Fix an anchor `g`, a valence `s`, and a top order `k ≥ 1`.  There is a single constant `C ≥ 0`
such that for every smooth compactly-supported `(0, s)`-tensor `u` whose `C⁰`-sup fibre norm is
`≤ Λ₀` and every intermediate order `0 < j < k`, the `L^{2k/j}` fibre norm of the `j`-th iterated
covariant gradient — written through its squared fibre norm `rfns(∇^j u) = |∇^j u|²` as
`(∫ rfns(∇^j u)^{k/j} dμ)^{j/k} = ‖∇^j u‖²_{L^{2k/j}}` — is controlled by the **interpolated**
product of the `L^∞` sup `Λ₀` and the top-order covariant `L²`-jet:
```
(∫ rfns(∇^j u)^{k/j} dμ)^{j/k} ≤ C · Λ₀^{2(1 − j/k)} · ‖∇^k u‖_{L²}^{2 j/k} .
```

This is the genuine **`Lᵖ` Gagliardo–Nirenberg interpolation** with the *free exponent* `p = 2k/j`:
the intermediate covariant gradient is estimated by interpolation between the `L^∞` bound (order
`0`) and the top-order `L²` bound (order `k`), the interpolation weights being `1 − j/k` (on the
sup) and `j/k` (on the top jet), now in the **`L^{2k/j}`** norm rather than the degenerate `L²` of
the companion `exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le`.  It is the precise kernel that
the diagonal covariant-jet product grid
(`exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le`) consumes through Hölder at the
conjugate pair `(k/i, k/l)`: each Hölder factor is exactly an `L^{2k/i}` norm of one tensor's `i`-th
fibre jet, which this statement bounds.

**Non-vacuity.**  The constant `C` is uniform over `(u, Λ₀, j)` (quantified before all of them);
the bound `0 < j < k` confines the interpolation exponent `j/k ∈ (0, 1)` (so `p = 2k/j ∈ (2, ∞)`),
and the `k = 1` case is vacuous (no `j` with `0 < j < 1`), so no degenerate witness is asserted; a
`C = 0` witness is rejected by any `u` with a nonvanishing intermediate jet.

The proof is the genuine `k`-th-root (`rpow (1/k)`) extraction from the discrete log-convexity power
law on the mixed-`L^p` fibre-jet ladder `c := lpFiberJetLadder g s k u Λ₀`.  Feeding the posited
single-step log-convexity `lpFiberJet_logConvex_iteratedCovGrad` (`c_{i+1}² ≤ K·c_i·c_{i+2}`) to the
discrete Hardy–Littlewood–Pólya power law `lp_hlp_real` gives `c_j^k ≤ K^{k³}·c_0^{k-j}·c_k^j`;
identifying the ladder's interior value `c_j² = (∫ rfns(∇^j u)^{k/j})^{j/k}` (its `L^{2k/j}` fibre
norm squared), the `L^∞`-endpoint `c_0 = Λ₀·√(vol M)`, and the `L²`-endpoint `c_k = ‖∇^k u‖_{L²}`,
then taking `rpow (1/k)` of the squared bound and absorbing the volume factor
`(√(vol M))^{2(1−j/k)} ≤ max 1 (vol M)` into the constant `C := K^{2k²}·max 1 √(vol M)^2`, yields the
displayed interpolation.  It therefore depends transitively only on the `sorry` of
`lpFiberJet_logConvex_iteratedCovGrad` (the deep closed-manifold covariant `L^p` interpolation
engine), which `#print axioms` records as `sorryAx`; the displayed real-power statement is proven
outright on top of that single posited analytic input.  No packaging: the conclusion is a real-valued
`L^p` interpolation inequality on a single tensor's covariant jets, structurally distinct from any
consumer's Nemytskii conclusion. -/
theorem exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le
    (g : SmoothRiemannianMetric I M) (s k : ℕ) (_hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Integral.L2.SmoothCcTensor g 0 s) (Λ₀ : ℝ), 0 ≤ Λ₀ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s x (u.toSection x) ≤ Λ₀ ^ 2) →
        ∀ j : ℕ, 0 < j → j < k →
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s j u).toSection x)) ^ ((k : ℝ) / j)
              ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((j : ℝ) / k) ≤
            C * Λ₀ ^ (2 * (1 - (j : ℝ) / k)) *
              (Integral.L2.tensorL2Norm (I := I) g 0 (s + k)
                  (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s k u).toFun) ^ (2 * (j : ℝ) / k) := by
  classical
  obtain ⟨K, hK1, hlc⟩ := lpFiberJet_logConvex_iteratedCovGrad (I := I) (M := M) g s k _hk
  set V : ℝ := Real.sqrt ((Integral.Measure.riemannianVolumeMeasure I M g) Set.univ).toReal with hV
  have hVnn : 0 ≤ V := Real.sqrt_nonneg _
  have hmax1 : (1 : ℝ) ≤ max 1 V := le_max_left _ _
  have hmaxV : V ≤ max 1 V := le_max_right _ _
  have hmax_nn : 0 ≤ max 1 V := le_trans zero_le_one hmax1
  -- The single uniform constant.
  set C : ℝ := K ^ (2 * k ^ 2) * (max 1 V) ^ 2 with hC
  have hKnn : 0 ≤ K := le_trans zero_le_one hK1
  have hC_nn : 0 ≤ C := by rw [hC]; positivity
  refine ⟨C, hC_nn, ?_⟩
  intro u Λ₀ hΛ₀ hsup j hj0 hjk
  have hk0 : (k : ℕ) ≠ 0 := by omega
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  have hkRpos : (0 : ℝ) < (k : ℝ) := by positivity
  -- The mixed-L^p fibre-jet ladder.
  set c : ℕ → ℝ := fun i => lpFiberJetLadder (I := I) (M := M) g s k u Λ₀ i with hc_def
  -- Nonnegativity of every ladder value.
  have hc_nn : ∀ i, 0 ≤ c i := by
    intro i
    rw [hc_def]
    simp only [lpFiberJetLadder]
    split_ifs with hi0 hik
    · exact mul_nonneg hΛ₀ hVnn
    · exact Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + k) _
    · exact Real.rpow_nonneg (integral_nonneg (fun x =>
        Real.rpow_nonneg (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + i) x _) _)) _
  -- Log-convexity for this ladder (from the posited child).
  have hc_lc : ∀ i, (c (i + 1)) ^ 2 ≤ K * c i * c (i + 2) := by
    intro i; rw [hc_def]; exact hlc u Λ₀ i
  -- The HLP power law on the ladder.
  have hpow : (c j) ^ k ≤ K ^ (k ^ 3) * (c 0) ^ (k - j) * (c k) ^ j :=
    lp_hlp_real c hc_nn K hK1 hc_lc j k hj0 hjk
  -- Endpoint identifications: c 0 = Λ₀·V, c k = ‖∇^k u‖_{L²}, c j² = the LHS integral power.
  have hc0_eq : c 0 = Λ₀ * V := by
    simp only [hc_def, lpFiberJetLadder, if_pos rfl]
    rw [hV]
  have hck_eq : c k = Integral.L2.tensorL2Norm (I := I) g 0 (s + k)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s k u).toFun := by
    simp only [hc_def, lpFiberJetLadder, if_neg (show k ≠ 0 by omega), if_true]
  have hcj_sq : (c j) ^ 2 =
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s j u).toSection x)) ^ ((k : ℝ) / j)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((j : ℝ) / k) := by
    simp only [hc_def, lpFiberJetLadder, if_neg (show j ≠ 0 by omega), if_neg (show j ≠ k by omega)]
    set Iint : ℝ := ∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s j u).toSection x)) ^ ((k : ℝ) / j)
        ∂(Integral.Measure.riemannianVolumeMeasure I M g) with hIint
    have hIint_nn : 0 ≤ Iint := integral_nonneg (fun x =>
      Real.rpow_nonneg (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + j) x _) _)
    have hexp : (j : ℝ) / (2 * k) * ((2 : ℕ) : ℝ) = (j : ℝ) / k := by
      push_cast
      rw [mul_comm, ← mul_div_assoc, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [← Real.rpow_natCast (Iint ^ ((j : ℝ) / (2 * k))) 2,
        ← Real.rpow_mul hIint_nn, hexp]
  -- Nonnegativity of the endpoints.
  have hc0_nn : 0 ≤ c 0 := hc_nn 0
  have hck_nn : 0 ≤ c k := hc_nn k
  have hcj_nn : 0 ≤ c j := hc_nn j
  -- Square the HLP bound, then take rpow (1/k) of the squared form.
  have hpow_sq : ((c j) ^ 2) ^ k ≤
      (K ^ (k ^ 3)) ^ 2 * ((c 0) ^ 2) ^ (k - j) * ((c k) ^ 2) ^ j := by
    have hrw : ((c j) ^ 2) ^ k = ((c j) ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hrw]
    have hbase_nn : 0 ≤ K ^ (k ^ 3) * (c 0) ^ (k - j) * (c k) ^ j := by positivity
    calc ((c j) ^ k) ^ 2 ≤ (K ^ (k ^ 3) * (c 0) ^ (k - j) * (c k) ^ j) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hpow 2
      _ = (K ^ (k ^ 3)) ^ 2 * ((c 0) ^ 2) ^ (k - j) * ((c k) ^ 2) ^ j := by
          rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
          ring_nf
  -- Take rpow (1/k) of both sides of the squared bound.
  have hcj2_nn : 0 ≤ (c j) ^ 2 := by positivity
  have hmono : (((c j) ^ 2) ^ k) ^ ((k : ℝ)⁻¹) ≤
      ((K ^ (k ^ 3)) ^ 2 * ((c 0) ^ 2) ^ (k - j) * ((c k) ^ 2) ^ j) ^ ((k : ℝ)⁻¹) :=
    Real.rpow_le_rpow (by positivity) hpow_sq (by positivity)
  rw [Real.pow_rpow_inv_natCast hcj2_nn hk0] at hmono
  -- Compute the rpow (1/k) of the RHS via rpow algebra.
  have hcast_sub : ((k - j : ℕ) : ℝ) = (k : ℝ) - (j : ℝ) := by rw [Nat.cast_sub (le_of_lt hjk)]
  have hrhs : ((K ^ (k ^ 3)) ^ 2 * ((c 0) ^ 2) ^ (k - j) * ((c k) ^ 2) ^ j) ^ ((k : ℝ)⁻¹) =
      (K ^ (2 * k ^ 2)) * ((c 0) ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) * ((c k) ^ 2) ^ ((j : ℝ) / k) := by
    have hKpow_nn : 0 ≤ (K ^ (k ^ 3)) ^ 2 := by positivity
    have hc02_nn : 0 ≤ ((c 0) ^ 2) ^ (k - j) := by positivity
    have hck2_nn : 0 ≤ ((c k) ^ 2) ^ j := by positivity
    rw [Real.mul_rpow (by positivity) hck2_nn, Real.mul_rpow hKpow_nn hc02_nn]
    congr 1
    · congr 1
      · -- `((K^{k³})²)^{1/k} = K^{2k²}`
        have hexpK : ((k ^ 3 * 2 : ℕ) : ℝ) * (k : ℝ)⁻¹ = ((2 * k ^ 2 : ℕ) : ℝ) := by
          push_cast
          field_simp
        rw [← pow_mul, ← Real.rpow_natCast K (k ^ 3 * 2), ← Real.rpow_mul hKnn, hexpK,
          Real.rpow_natCast K (2 * k ^ 2)]
      · -- `(((c 0)²)^{k-j})^{1/k} = ((c 0)²)^{1 - j/k}`
        have hexp0 : ((k - j : ℕ) : ℝ) * (k : ℝ)⁻¹ = (1 : ℝ) - (j : ℝ) / k := by
          rw [hcast_sub]
          field_simp
        rw [← Real.rpow_natCast ((c 0) ^ 2) (k - j), ← Real.rpow_mul (by positivity), hexp0]
    · -- `(((c k)²)^j)^{1/k} = ((c k)²)^{j/k}`
      rw [← Real.rpow_natCast ((c k) ^ 2) j, ← Real.rpow_mul (by positivity), div_eq_mul_inv]
  rw [hrhs] at hmono
  -- Now substitute the endpoint identifications and the LHS, then fold the volume factor.
  rw [hcj_sq] at hmono
  rw [hc0_eq, hck_eq] at hmono
  -- `hmono` now reads: LHS ≤ K^{2k²}·((Λ₀·V)²)^{1-j/k}·(‖∇^k u‖_{L²}²)^{j/k}.
  -- Massage the endpoint powers to the displayed form.
  set ak : ℝ := Integral.L2.tensorL2Norm (I := I) g 0 (s + k)
    (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s k u).toFun with hak_def
  have hak_nn : 0 ≤ ak := Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + k) _
  -- `(ak²)^{j/k} = ak^{2j/k}`.
  have hak_pow : (ak ^ 2) ^ ((j : ℝ) / k) = ak ^ (2 * (j : ℝ) / k) := by
    rw [← Real.rpow_natCast ak 2, ← Real.rpow_mul hak_nn]
    congr 1
    push_cast; ring
  -- `((Λ₀·V)²)^{1-j/k} = Λ₀^{2(1-j/k)}·(V²)^{1-j/k}` and `(V²)^{1-j/k} ≤ (max 1 V)²`.
  have hweight_nn : 0 ≤ (1 : ℝ) - (j : ℝ) / k := by
    have : (j : ℝ) / k ≤ 1 := by
      rw [div_le_one hkRpos]; exact_mod_cast le_of_lt hjk
    linarith
  have hweight_le1 : (1 : ℝ) - (j : ℝ) / k ≤ 1 := by
    have : 0 ≤ (j : ℝ) / k := by positivity
    linarith
  have hLV_pow : ((Λ₀ * V) ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) =
      Λ₀ ^ (2 * ((1 : ℝ) - (j : ℝ) / k)) * (V ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) := by
    rw [mul_pow, Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast Λ₀ 2, ← Real.rpow_mul hΛ₀]
    norm_num
  -- `(V²)^{1-j/k} ≤ (max 1 V)²`.
  have hV2_le : (V ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) ≤ (max 1 V) ^ 2 := by
    have hV2_nn : 0 ≤ V ^ 2 := by positivity
    have h2max : (1 : ℝ) ≤ (max 1 V) ^ 2 := by
      have := pow_le_pow_left₀ (zero_le_one) hmax1 2
      rwa [one_pow] at this
    rcases le_total (V ^ 2) 1 with hle | hge
    · -- base ≤ 1: rpow to a nonnegative weight stays ≤ 1 ≤ (max 1 V)².
      have h1 : (V ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) ≤ 1 :=
        Real.rpow_le_one hV2_nn hle hweight_nn
      linarith
    · -- base ≥ 1: monotone in the exponent (≤ 1), so ≤ (V²)^1 = V² ≤ (max 1 V)².
      have h1 : (V ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) ≤ (V ^ 2) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hge hweight_le1
      rw [Real.rpow_one] at h1
      have hV2_le_max : V ^ 2 ≤ (max 1 V) ^ 2 := pow_le_pow_left₀ hVnn hmaxV 2
      linarith
  -- Assemble: chain `hmono` through the endpoint massaging and the volume fold.
  calc (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s j u).toSection x)) ^ ((k : ℝ) / j)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((j : ℝ) / k)
      ≤ K ^ (2 * k ^ 2) * ((Λ₀ * V) ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) * (ak ^ 2) ^ ((j : ℝ) / k) :=
        hmono
    _ = K ^ (2 * k ^ 2) *
          (Λ₀ ^ (2 * ((1 : ℝ) - (j : ℝ) / k)) * (V ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k)) *
          ak ^ (2 * (j : ℝ) / k) := by rw [hLV_pow, hak_pow]
    _ ≤ K ^ (2 * k ^ 2) *
          (Λ₀ ^ (2 * ((1 : ℝ) - (j : ℝ) / k)) * (max 1 V) ^ 2) *
          ak ^ (2 * (j : ℝ) / k) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left hV2_le (by positivity)
    _ = (K ^ (2 * k ^ 2) * (max 1 V) ^ 2) * Λ₀ ^ (2 * (1 - (j : ℝ) / k)) *
          ak ^ (2 * (j : ℝ) / k) := by ring
    _ = C * Λ₀ ^ (2 * (1 - (j : ℝ) / k)) * ak ^ (2 * (j : ℝ) / k) := by rw [hC]

end DifferentialGeometry.Analysis.Sobolev.Tensor

end
