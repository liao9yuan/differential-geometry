# RicBoundClaims.lean — ric_bound Step 3: geometric Claims 1 & 2 (Phase R)

## ✅ R1 + R2 GREEN (2026-06-10, first check pass, sorry-free)

MSM135 Ch. 3, Lemma 3.11, Step 3 — both bookkeeping claims, in frame-component
tower form, consuming `AkMFold.lean` (parallel track, unmodified) and
`Lemma45Engine.lean`.

**Orientation convention (load-bearing):** `chrG` = the MOVING metric's LC frame
Christoffels (`∇_k`; Shi bounds live on its pure towers), `chrH` = the FIXED
reference connection (`∇`; the outer towers).  With this assignment
`claim1_LC`'s output bounds exactly the `chrDiffField chrG chrH`-towers that
`mixed_oneStep_rev`/`claim2_component` consume — NO sign-flip glue anywhere.
(`hkoszul_of_leviCivita (g := moving, gRef := fixed)` is already in this
orientation.)

## Contents

1. **`claim1_LC`** — geometric Claim 1: for LC connections of `(g, gRef)` in any
   `IsLocalFrameOn` frame on `u`, with bounded `g`-inverse (`hGinv`) and bounded
   `|∇_H^j g|`, `1 ≤ j ≤ m` (`hK`):
   `|∇_{H,U}^m (Γ_G − Γ_H)| ≤ C·(1 + |∇_H^{m+1} g|)` on `u`.
   Proof = ONE application: `claim1` (AkMFold) + `hkoszul_of_leviCivita` with
   `(c₁,c₂,c₃) = (½,½,−½)`, `(P₁,P₂,P₃) = (refl, swap 0 1, (finRotate 3).symm)`
   — the same instantiation pattern as `lemma45_F3`'s `hDb` step.
2. **`mixed_oneStep_rev`** — the reversed one-step:
   `|∇_H^{k+1} X| ≤ |∇_H^k (∇_G X)| + ε·oneStepConst B k r·Σ_{j≤k}|∇_H^j X|`
   from `hDbound : |∇_{H,U}^c(Γ_G−Γ_H)| ≤ B c·ε` (`c ≤ k`).  Same array identity
   as `mixed_oneStep_le` (`iterCov_one_chr_change` + `iterCovComp_sub` +
   `iterCovComp_finsetSum`), triangle read in the other direction; the
   `hcorrBound` block is verbatim.  This is the book's `∇ = ∇_k + A_k` expansion
   direction.
3. **`claim2Double`** (+ private `claim2DoubleAux`) — abstract Claim-2 induction:
   `W i 0 ≤ K` (Shi row) + `W i (k+1) ≤ W (i+1) k + A k·Σ_{j≤k} W i j` ⟹
   `W i k ≤ C` on `{i+k ≤ L}`.  KEY SHAPE: `∃ C` BEFORE `∀ W` (the family is
   quantified inside), so the geometric consumer gets one constant uniform over
   `x ∈ u`.  Strong induction on the second index; per-row constants totalized
   by `by_cases` + `choose`, summed over `range (L+1)`.
4. **`claim2_component`** — geometric Claim 2: `hDbound` (`c < L`, Claim 1's
   output as constants) + `hShi` (`|∇_G^s T| ≤ K`, `s ≤ L`) ⟹ all mixed towers
   `|∇_H^a (∇_G^b T)| ≤ C` for `a + b ≤ L`, uniformly on `u`.
   `claim2Double` at `A k := oneStepConst B k (r₀ + L)` (rank-monotonicity of
   `oneStepConst` absorbs the `i`-dependent rank), one-step from
   `mixed_oneStep_rev` at `ε = 1`; `W i 0 = |∇_G^i T|` is defeq to the Shi input.

Private copies (engine has them `private`): `contMDiffOn_finsetSum'`,
`compL2_finsetSum_le`.  Consolidate into `Lemma45Engine` on its next touch.

## Lean lessons (this file)

- `Σ` is a reserved token — `hΣ0` is a PARSE ERROR (3rd instance of the
  unicode-in-identifier trap: `r∞`, `hframe∞`, now `hΣ0`).  Renamed `hSig0`.
- An abstract lemma applied via `refine f (fun i k => …) ?_ ?_` leaves
  beta-redexes `(fun i k => …) i (k+1)` in the subgoals — linarith atoms break.
  Fix: build the hypotheses as standalone `have`s with explicit beta-REDUCED
  types, then ONE `exact f W h0 h1 h2 …` at the end (beta-defeq absorbed by
  `exact`, never seen by linarith).
- `funext n` on a goal `A = fun n => rhs n` leaves the RHS beta-redex; a `show`
  with the reduced form before `linarith` fixes the atom mismatch.
- The defeq identifications `iterCovComp chr X 0 ≡ X` and
  `(fun y => iterCovComp chrG (iterCovComp chrG T i) 1 y) ≡ iterCovComp chrG T (i+1)`
  are absorbed by `exact`/explicit-`have`-type (same as `lemma45_component_bdd`).
- `oneStepConst B k m = (m:ℝ)·Σ binom(k,·)B` unfolds by `rfl` in a calc step;
  rank-monotonicity is `mul_le_mul_of_nonneg_right` + `exact_mod_cast`.

## R3a + R3b GREEN (2026-06-10, focused check passed — whole file sorry-free)

One repair after the first check: `mixed_oneStep_top`'s `htopEq` needed an
explicit `rfl` after `rw [Nat.choose_self, Nat.sub_self, Nat.cast_one, one_mul]`
— `rw`'s trailing rfl is REDUCIBLE-only and cannot see through `chrDiffField`
delta or the 0-tower iota (4th unicode/transparency-class lesson).  Everything
else (including all of `mixed_descent` and its closing `nlinarith` with the
four product hints) elaborated on the first pass.

- **`mixed_oneStep_top`** (R3a): the top-split one-step, `hDbound` only `c < k`,
  conclusion carries `(r:ℝ)·|∇_{H,U}^k D|·|X|` verbatim (no hypothesis for the top
  order).  `Finset.sum_range_succ` peel; `k − k → 0` and `k.choose k → 1` are
  REWRITES (not defeq for variable `k`); the `D`-lambda ↔ `chrDiffField` bridge is
  an `rfl`-`have`.
- **`chain_le`** (private) + **`mixed_descent`** (R3b): the (A_N) analytic core —
  `|∇_H^N T| ≤ C·(1 + |∇_{H,U}^{N-1}D|)` pointwise from `hDlow` (`c+1 < N`,
  uniform), `hmix` (Claim 2 at `L = N−1`), `hShiN` (order-`N` Shi).  KEY DESIGN:
  `mixed_oneStep_top` is applied at EVERY descent step `i` (top factor needs no
  hypothesis); the D-factor is bounded by `|∇^{N-1}D| + ΣB` in both the `i=0`
  (defeq `N−0−1 ≡ N−1`, `rfl`-have) and `i≥1` (hDlow + `single_le_sum`) cases, so
  the per-step cost is CONSTANT in `i` and the chain sum collapses by
  `sum_const`+`card_range`+`nsmul_eq_mul` — no if-then-else, no `sum_range_succ'`
  index surgery.  All `N − i` index changes via two omega-`rw`s (`e1`, `e2`)
  before the one-step; head/terminal identifications by defeq-absorbing
  explicit-`have` types (`N−0 ≡ N`, `∇_G^0 T ≡ T`) + one `Nat.sub_self` rw.

## R4 recon (component ↔ intrinsic bridge, for the `ric_bound` Grönwall field)

`MetricCovOrderEvolutionInput.ric_bound` (AllTimesBounds.lean:4365) wants the
INTRINSIC form `√(normSq0S gRef (∇^p Rc)) ≤ Cpp·metricCovDerivNorm p g gRef + Cppp`.
Existing: `iterCovComp_eq_iterCov` (MetricCovDerivTower:134, tower = intrinsic at
`frameTuple`); `Tensor0SBundle.abs_component0S_le_sqrt_normSq0S` (single component
≤ intrinsic norm; cited from ApproximateIsometry's `metricCovComp_le` — NOTE
ApproximateIsometry.lean itself never built green, but the `Tensor0SBundle` lemma
lives upstream and is compiled).  MISSING/TO-FIND: the ON-frame Parseval identity
`normSq0S gRef x = Σ (component0S basis)²` at a `gRef`-orthonormal basis
(`MetricInverseInBasis … identityInvMetric` form) — that converts `compL2` of the
frame-component tower to the intrinsic norm EXACTLY, both directions.

## What consumes this next (R3 = Step 4, the (A_N)/(B_N) induction)

Design settled (2026-06-10): at stage `N` with IH `(B_r), r < N` (so uniform
`|∇^c A|`-bounds for `c ≤ N−2` via Claim 1, and Claim 2 available at
`L := N−1`):

- **R3a `mixed_oneStep_top`** (next brick, small delta on `mixed_oneStep_rev`):
  split the `c = k` term out of the correction block —
  `|∇_H^{k+1}X| ≤ |∇_H^k(∇_G X)| + (r:ℝ)·|∇_{H,U}^k D|·|X| + oneStepConst·Σ` with
  `hDbound` only for `c < k`.  In `hcorrBound`, split `Finset.sum_range_succ`;
  `binom(k,k) = 1`, X-factor `|∇_H^0 X| = |X|`.
- **R3b (A_N)**: `|∇_F^N Rc| ≤ C'·|∇_F^N g| + C''` pointwise — ONE
  `mixed_oneStep_top` at `k := N−1` (top factor `|∇_{F,U}^{N-1}D|` bounded
  pointwise by `claim1_LC` at `m = N−1`, which carries the `(1+|∇_F^N g|)`), then
  a finite descent of the leading mixed term `W(1, N−1) → … → W(N, 0) = Shi` via
  `mixed_oneStep_rev` (uniform D-orders `≤ N−2` ✓) with correction X-factors
  bounded by `claim2_component (L := N−1)`.  NOTE: the descent terms have TOTAL
  order `N`, NOT covered by Claim 2 — they are consumed by the next descent step;
  only the correction factors (total ≤ N−1) go to Claim 2.
- **R3c (B_N)**: `∂_t ∇^N g = −2 ∇^N Rc` (∇ fixed in t) + Grönwall
  (`metricCovOrderWindow_of_evolution`, exists per RicBoundProof.md item 5).
- Then R4 (Step 5 time derivatives), R5 (discharge `MetricCovOrderEvolutionInput`).

Verification: focused check PASSED (this file), first structural pass.
