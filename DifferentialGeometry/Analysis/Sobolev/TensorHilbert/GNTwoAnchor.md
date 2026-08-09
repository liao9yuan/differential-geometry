# `GNTwoAnchor.lean` — the per-factor two-anchor Gagliardo–Nirenberg bound (GN2)

Status: **GREEN, sorry-free, axiom-clean** (`[propext, Classical.choice, Quot.sound]`).
611 lines.  Built as the `GN2` brick dispatched by `UNIF_EXISTENCE_PLAN5.md`
No. 144; the free-weight product assembly `gnProdJet` (No. 145) landed here too
— see the session-7 section at the end.  Both `gnTwoAnchor` and `gnProdJet` are
axiom-clean, and `gnProdJet` is what closes `gridIntHigh`.

## What it provides

`gnTwoAnchor (g₀) (r s : ℕ)` — constants first, state after:

```
∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
  ∀ (Ψ : SmoothCcTensor g₀ r s) {Λ₀ Λ₁}, 0 ≤ Λ₀ → Λ₀ ≤ 1 → 0 ≤ Λ₁ →
    (∀ x, rfns g₀ r s x (Ψ.toSection x) ≤ Λ₀ ^ 2) →
    (∀ x, rfns g₀ r (s+1) x ((∇Ψ).toSection x) ≤ Λ₁ ^ 2) →
    ∀ m c, 2 ≤ c → c < m → ∀ θ,
      ((c:ℝ) - 1)/((m:ℝ) - 1) ≤ θ → θ ≤ (c:ℝ)/(m:ℝ) →
      (∫ x, rfns g₀ r (s+c) x ((∇^c Ψ).toSection x) ^ (1/θ) ∂μ_g) ^ θ ≤
        C m * Λ₁ ^ (2 * ((c:ℝ) - θ * m)) * ‖∇^m Ψ‖ ^ (2 * θ)
```

`C` is state-free (`C m = max 1 (A m) * max 1 (B (m-1)) ^ (2:ℝ)`, `A`/`B` the two
GN constant families).  Valence-generic `(r, s)`; the `gridIntHigh` consumer
instantiates `r = 0, s = 2`, where the integrand IS `gridBase g₀ P x c` on the
nose and `‖∇^m Ψ‖` IS `gridIntHigh`'s RHS jet.

## Why the range is exactly right for the assembly

Class-3 monomials of `gridIntHigh` are `∏_{j≤q} |∇^{c_j}P|²` with `q ≥ 3`, every
`c_j ≥ 2`, `∑ c_j = m+1`.  Then `c_j ≤ m+1-2(q-1) ≤ m-3 < m`, so `2 ≤ c_j < m`
always holds; and the assembly's weights
`θ_j = (1-t)(c_j-1)/(m-1) + t·c_j/m` with `t ∈ [0,1]` are by construction inside
`[(c_j-1)/(m-1), c_j/m]`.  So GN2's hypothesis set covers every pair the class
generates — no narrowing, no balance hypothesis.

## Route (the arithmetic that made it work)

Write `pA = m/c` (the `Ψ`-anchored exponent, `θ_A = c/m`), `pB = (m-1)/(c-1)`
(the `∇Ψ`-anchored one, `θ_B = (c-1)/(m-1)`).  `θ_B < θ_A` ⟺ `c < m`, so
`1/θ ∈ [pA, pB]`, and `lam := (pB - 1/θ)/(pB - pA) ∈ [0,1]` gives
`1/θ = lam·pA + (1-lam)·pB`.

* endpoint A = `exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs` at
  base `Ψ`, `k := m`, `j := c`.  Its `Λ₀` weight `2(1 - c/m) ≥ 0` dies against
  `Λ₀ ≤ 1` (`Real.rpow_le_one`).
* endpoint B = the same at base `∇Ψ` (valence `(r, s+1)`), `k := m-1`,
  `j := c-1`.  `∇^{c-1}(∇Ψ) = ∇^cΨ` and `∇^{m-1}(∇Ψ) = ∇^mΨ` via
  `rfns_iteratedCovGrad_comp` (pointwise) and `icgNormComp` (`L²`).
* flip both to `∫F^p ≤ K^p·R²` (`rpowFlip`, using `θ_A·pA = θ_B·pB = 1`), then
  `lyapunov_pow_le` between them, then raise to `θ`.

**Key exponent identity, verified twice and then in Lean:**
`θ·(1-lam)·(pB - 1) = c - θ·m`.  Proof in Lean via three factored quotients
(`pB - pA = (n-d)/(d(1+d))`, `pB - 1 = (n-d)/d`,
`1/θ - pA = ((1+d) - θ(1+n))/(θ(1+d))` with `c = 1+d`, `m = 1+n`) and one
`field_simp`.  Trying `field_simp` on the unfactored form fails — the compound
denominator `pB - pA` is not recognized as nonzero.

**Constant absorption.**  After raising to `θ` the constants appear as
`KA^{pA·lam·θ}` and `KB^{pB·(1-lam)·θ}`.  `θ·pA ≤ θ_A·pA = 1` and
`θ·pB ≤ θ_A·pB = c(m-1)/(m(c-1)) ≤ 2` (uses `c ≥ 2`), so with `KA, KB ≥ 1` these
are `≤ KA` and `≤ KB²`.  That is the ONLY place `c ≥ 2` (as opposed to `c ≥ 1`)
is used.

## Structure

* `rpowFlip` (private, pure real) — `X ≥ 0`, `a·b = 1`, `b ≥ 0`, `X^a ≤ Y` ⟹
  `X ≤ Y^b`.
* `gnMixCore` (private, pure real + measure) — the whole interpolation with the
  two endpoint bounds as hypotheses.  Keeps every rpow/cast step out of the
  geometric proof; this split is what kept the file short.
* `gnFam` (private) — the `Lᵖ` GN scale repackaged with its constant as a
  `ℕ → ℝ` family indexed by top order (`choose` over `k`, with the `k = 0` case
  discharged vacuously by `0 < j → j < k`).  Needed because `gridIntHigh` wants
  `∃ K : ℕ → ℝ` quantified before `∀ m`.
* `gnTwoAnchor` — the geometric statement.

## Lean lessons worth keeping

* **`MeasurableSpace M` is not ambient in the `TensorHilbert` layer.**  Stating
  `Integrable f (riemannianVolumeMeasure I M g₀)` needs the four
  `private local instance`s (`borel E`, `BorelSpace E`, `borel M`,
  `BorelSpace M`) — the instance is an argument of `Integrable`, synthesized
  BEFORE unification with the measure's carrier, so it cannot be recovered from
  the measure.  Additionally `Continuous.integrable_of_hasCompactSupport` needs
  `haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure …) :=
  riemannianVolumeMeasure_isFiniteMeasureOnCompacts …` — there is no global
  instance.
* **Truncated ℕ-subtraction is best avoided by substitution, not by casts.**
  `obtain ⟨d, rfl⟩ : ∃ d, c = 1 + d` and `⟨n, rfl⟩ : ∃ n, m = 1 + n` makes
  `∇^{c-1}(∇Ψ)` line up with `rfns_iteratedCovGrad_comp g₀ r s 1 d Ψ`
  syntactically (`(s+1)+d` vs `s+(1+d)`), so a bare `simp only [that lemma]`
  rewrites under the integral binder.  With `c - 1` left truncated, nothing
  matches.
* **Naming the integrand by `obtain ⟨F, hFapp⟩ : ∃ F, ∀ x, <long> = F x := ⟨_, fun _ => rfl⟩`**
  is better than `set`: `set` on a lambda does not fold occurrences that appear
  applied under a binder, while `simp only [hFapp]` does — and `Continuous F`
  transfers by `Continuous.congr hFapp`.
* `set p := …` DOES fold the exponents inside already-obtained hypotheses, but
  only if the term is syntactically present: `2 * ↑j / ↑k` must be turned into
  `2 * (↑j / ↑k)` by `rw [mul_div_assoc]` FIRST, otherwise the `2 * …` numerator
  hides the quotient.
* `Real.rpow_add'` (not `rpow_add`) is the one to use for
  `(R²)^lam · (R²)^{1-lam} = R²` — it needs only `0 ≤ R²` plus
  `lam + (1-lam) ≠ 0`, so no `R > 0` case split.
* Deprecated-name drift: this Mathlib rev wants `div_le_iff₀`,
  `le_div_iff₀`, `div_lt_div_iff₀`.
* `field_simp` sometimes closes the goal outright; a trailing `ring` then errors
  with "No goals". Three of the six `field_simp` sites here needed `ring`, three
  did not — check individually rather than pasting the pair.

## Reuse audit (project rule)

Searched `DifferentialGeometry/` before writing anything.  Reused, not
reproved: `exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs`
(`Analysis/Sobolev/GagliardoNirenbergLpFiberNorm.lean:5462`),
`Integral.lyapunov_pow_le`
(`Analysis/Integration/L2/FiniteProductHolderFiberNorm.lean:79`),
`icgNormComp` and `rfns_iteratedCovGrad_comp`, `SmoothCcTensor.norm_def`,
`SmoothCcTensor.continuous_inner_self`,
`riemannianVolumeMeasure_isFiniteMeasureOnCompacts`.  Nothing duplicated.

**Home note.**  The dispatch suggested "beside `lyapunov_pow_le` or the GN
primitives".  Neither works: `GagliardoNirenbergLpFiberNorm.lean` is already
5642 lines (over the 3000-line limit — must not grow), and
`FiniteProductHolderFiberNorm.lean` is below the `iteratedCovGrad` layer
entirely.  Decisive fact: the composition bridges GN2 needs
(`icgNormComp`, the public
`tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs`) live in
`Analysis/Sobolev/TensorHilbert/`, so that IS the canonical home; placing GN2
lower would have forced a duplicate of `icgNormComp`.

## What the assembly brick needs

* `import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.GNTwoAnchor` in
  `TameMarkWin.lean` (GN2 is a leaf; no cycle — it imports only `GradCapAtgw`,
  `GagliardoNirenbergLpFiberNorm`, `FiniteProductHolderFiberNorm`).
* `holder_integral_prod_riemannianFiberNormSq_le` (`:89`) at free weights
  `θ_j`, or `..._le_of_sup_bound` (`:153`) to discard the weight-0 entries
  against `Λ₀ ≤ 1` first.
* `t := (1-L)/(U-L)`, `L := (m+1-q)/(m-1)`, `U := (m+1)/m`; `q ≥ 2` gives
  `t ∈ [0,1]`, `∑θ_j = 1`.  Then `∏_j C m · Λ₁^{2(c_j - θ_j m)} · R^{2θ_j}
  = C m^q · Λ₁^{2(∑c_j - m)} · R^2 = C m^q · Λ₁² · R²`, which is
  `gridIntHigh`'s `K m · (1 + Λ₁²) · ‖∇^mP‖²` after `Λ₁² ≤ 1 + Λ₁²`.
  NOTE: GN2 needs no `max Λ₁ 1` — the `Λ₁` exponent is exact and nonnegative,
  so `Λ₁` itself (with only `0 ≤ Λ₁`) is the right anchor.
* `C m ^ q` is `q`-dependent, and `q ≤ 2 + k ≤ m + 1`, so the assembly's
  state-free `K m` will be `max 1 (C m) ^ (m+1)` or similar — bound `q` by `m+1`
  before choosing `K`.

## Session 7 (2026-08-04): the assembly landed here — `gnProdJet`

The assembly brick was built in THIS file (the handoff list above is now
history).  Home reasoning: it consumes `gnTwoAnchor` per factor and
`holder_integral_prod_riemannianFiberNormSq_le_of_sup_bound` — both already in
this file's import closure — and its statement is still pure jet analysis, not
`gridBase`/marked-grid bookkeeping.  Splitting it into a new file would have
bought nothing but an import hop; the file is ~610 lines, well under the cap.

### What it provides

```
gnProdJet (g₀) (r s : ℕ) :
  ∃ K : ℕ → ℝ, (∀ m, 0 ≤ K m) ∧
    ∀ Ψ {Λ₀ Λ₁}, 0 ≤ Λ₀ → Λ₀ ≤ 1 → 0 ≤ Λ₁ → (sup bounds on Ψ and ∇Ψ) →
      ∀ (m N : ℕ) (c : Fin N → ℕ) (t : Finset (Fin N)),
        (∀ j ∈ t, 2 ≤ c j) → (∀ j, j ∉ t → c j = 0) → 2 ≤ t.card →
        (∑ j ∈ t, c j) = m + 1 →
        ∫ ∏ j : Fin N, |∇^{c j}Ψ|² ≤ K m · Λ₁² · ‖∇^mΨ‖²
```

`K m = max 1 (C m) ^ (m + 1)` with `C` from `gnTwoAnchor` — state-free.

**Design note on the support hypothesis.**  The active set is taken as an
explicit `t : Finset (Fin N)` with "orders off `t` are `0`", not as
`univ.filter (c · ≠ 0)`.  This keeps `DecidablePred` out of the statement
entirely, so a caller working under `classical` can supply its own filter
without an instance mismatch when folding.  (Trying it the other way first is
what produced the only design churn of the session.)

**`2 ≤ t.card` suffices — `3` is not needed.**  At `q = 2` the ratio is `t = 0`
and the weights collapse to the pure `∇Ψ`-anchored family, which already sums to
`1`.  The dispatch spoke of class-3 monomials (`q ≥ 3`); the lemma is stated at
the weaker hypothesis per the weakest-assumptions rule, and `gridIntHigh` (which
always has `q ≥ 3`) simply meets it.

### The two named arithmetic lemmas

* `gnExpSum` — **the quadratic-budget identity**, the core of the design:
  `∑ cf j = mR + 1` and `∑ θ j = 1` ⟹ `∑ 2(cf j − θ j · mR) = 2`.  Four lines;
  the whole point is that it holds for ANY weight family summing to `1`, so the
  `Λ₁` exponent is pinned to `2` before the weights are even chosen.  Confirmed
  once more: the identity is TRUE with the recorded weights, no slack.
* `gnFreeWt` — the weight family itself.  `L = (mR+1−card)/(mR−1)`,
  `U = (mR+1)/mR`, `tt = (1−L)/(U−L)`,
  `θ j = (1−tt)·(cf j −1)/(mR−1) + tt·(cf j)/mR`.  Hypotheses actually used:
  `1 < mR`, `cf j ≤ mR` on `s`, `2 ≤ card`, `∑ cf = mR + 1`.  `2 ≤ cf j` is NOT
  needed here (only at the call site, for `0 < θ j`), and was dropped from the
  signature after the linter flagged it.

### Lean lessons (session 7)

* `obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = <body> := ⟨_, rfl⟩` instead of `set`: gives
  an opaque local constant plus a one-directional equation, with none of `set`'s
  fold-everywhere behaviour.  This is what made the `L`/`U`/`tt` algebra
  painless; the same idiom already appears in this file for the integrand `F`.
* `linear_combination httUL` closes `(1−tt)·L + tt·U = 1` from
  `tt·(U−L) = 1−L` in one step — cleaner than `nlinarith` for a pure identity.
* Passing `fun j => (c j : ℝ)` to a lemma whose hypotheses read
  `∀ j ∈ s, … cf j …` leaves the goal as `(fun j => ↑(c j)) j`, and
  `exact_mod_cast` refuses to see through the beta-redex.  Fix: a `change` to the
  beta-reduced form first.  (Use `change`, not `show` — the style linter rejects
  a `show` that changes the goal.)
* `Real.rpow_sum_of_nonneg (ha : 0 ≤ a) (h : ∀ x ∈ s, 0 ≤ f x)` is the exact
  tool for `∏_j Λ₁^{α_j} = Λ₁^{∑ α_j}` with `Λ₁ ≥ 0` — no positivity case split
  needed, and it is what turns the two exponent sums into the final `Λ₁²·R²`.
* `Real.rpow_natCast` needs no nonnegativity, so `y ^ (2:ℝ) = y ^ (2:ℕ)` is
  unconditional; state it as a local `∀ y` helper and `rw` twice.
* This Mathlib rev spells it `Finset.card_insert_of_notMem` (camel `notMem`).
