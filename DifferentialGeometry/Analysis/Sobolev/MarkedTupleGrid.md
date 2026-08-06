# `MarkedTupleGrid.lean` — the marked antidiagonal grid window

Companion note.  Status, route, what was verified, what failed.

## Why this file exists

`antidiagonalTupleGridWindow b w` remembers only the total weight of a monomial,
not how many of its factors carry a *positive* weight.  For the quadratic C0
summands that distinction is the whole game: at top weight `i + 2` a monomial
with ONE factor is `|∇^{i+2}P|²`, one derivative over the `range (i+2)` budget and
untameable; the SAME weight split over two positive factors is inside the budget
once one of them is measured in `L^∞` (`TameGridProd.gridIntGrad`).

`markGrid b u w` is the window that keeps the count:

```
markGrid b 0       w = antidiagonalTupleGridWindow b (w + 1)
markGrid b (u + 1) w = ∑_{c ≤ w} b (c + 1) · markGrid b u (w - c)
```

A monomial of `markGrid b u w` is `b c₁ ⋯ b c_u · ∏ b (e m)` with every `c_j ≥ 1`
and total weight `≤ w + u`.

## Contents (all sorry-free)

| name | content |
| --- | --- |
| `markGrid` | the definition (structural recursion on the mark count) |
| `markGrid_zero`, `markGrid_succ` | the two equation lemmas, both `rfl` |
| `markGrid_nn` | nonnegativity |
| `one_le_markGrid0` | the unmarked window is `≥ 1` (entry for state-free arms) |
| `markGrid_mono` | monotone in the level |
| `mulConst_mono` | `antidiagonalTupleGridWindowMulConst` is monotone in both levels |
| `markGrid_shift` | shifting the inner level upward stays inside the shifted window |
| `markGrid_mul` | **the marks ADD under multiplication**, at the SAME combinatorial constant the unmarked window already pays |
| `markOne_of_term` | entry bridge: `b (c+1) · grid b k ≤ markGrid b 1 j` when `c + 1 + k ≤ j + 1` |

`markGrid_mul` is the only property a Leibniz fold needs, and its constant is
literally `antidiagonalTupleGridWindowMulConst w₁ w₂` — the marked currency costs
NOTHING extra over the unmarked one.  Proof: induction on `u₁`, with the base case
an inner induction on `u₂`; the two inductive steps are the same reindexing
(`markGrid_shift`) plus `mulConst_mono`.

`markOne_of_term` is the shape every `topSeparated` producer of the tree already
delivers (a bare jet of the state times an ordinary grid of the complementary
weight), which is why no arm has to be re-derived geometrically.

## Design decisions

* The recursion is on `Finset.range (w + 1)` with truncated subtraction `w - c`,
  NOT on `Finset.antidiagonal w`.  Truncated subtraction inside `range` is
  harmless (`c ≤ w` on the nose) and every proof reduces to
  `Finset.sum_le_sum` + `Finset.sum_le_sum_of_subset_of_nonneg`, with no
  `antidiagonal` API risk.
* Only ONE constant family is used throughout, so the fold constant of the marked
  currency is definitionally `foldConst 0 0` — the unmarked fold constant.

## Verification

Focused check: **passed, no errors, no warnings.**  Targeted module build:
passed.  Axiom census of `markGrid_mul`, `markGrid_mono`, `markOne_of_term`:
**clean** (`[propext, Classical.choice, Quot.sound]`).

## Lean lessons

* `Finset.range_subset.mpr (by omega)` inside a `Finset.sum_le_sum_of_subset_of_nonneg`
  application FAILS here: the `by omega` is elaborated before the range endpoints
  are fixed and reports a counterexample over unrelated variables.  The robust
  idiom, already used elsewhere in this tree, is the pointwise subset proof
  `fun z hz => Finset.mem_range.mpr (by rw [Finset.mem_range] at hz; omega)`.
* `le_trans (Finset.sum_le_sum …) ?_` postpones the middle term and poisons any
  `by omega` inside the first argument.  Split into two typed `have`s and combine
  with `le_trans` afterwards.
* In an outer `induction u₁ generalizing …`, the `zero` branch's goal carries
  `0 + u₂`, which blocks reuse of the inner induction hypothesis.  `simp only
  [Nat.zero_add]` FIRST, then start the inner induction.

## Session 5 (2026-08-04): the exact-weight entry

`prodLeGrid` / `prodLeMark1` / `atgLeMark1` close the last missing entry of the
marked currency: an *exact-weight* grid `atg b (i+1)` is a once-marked window of
level `i`, up to the monomial count, **provided `b 0 ≤ 1`**.

* The `b 0 ≤ 1` anchor is not decoration.  The monomial `b(i+1)·b(0)^i` IS a
  term of `atg b (i+1)` (the tuple `(i+1,0,…,0)` of length `i+1`), and
  `markGrid b 1 i` contains `b(i+1)` only with an empty grid, so without a bound
  on `b 0` the inequality is false for every `i ≥ 1`.  It is the same δ-anchor
  `mkOfP` spends.
* The induction that works: recurse on the tuple LENGTH with `Fin.prod_univ_succ`
  / `Fin.sum_univ_succ` and split on `e 0 = 0` vs `e 0 = c+1`.  In the zero case
  drop the factor by `mul_le_of_le_one_left`; in the positive case apply
  `single_factor_mul_antidiagonalTupleGrid_le` (`prodLeGrid`) or
  `markOne_of_term` (`prodLeMark1`).  No `Fin.succAbove` surgery, no
  "restrict to the support" step — that route was considered and is much worse.
* Lean note: `match hq : e 0 with` already substitutes `e 0` in the GOAL but not
  in earlier hypotheses; a following `rw [hq]` then fails with "did not find the
  pattern".  Rewrite `at he`, not in the goal.
* Lean note: `omega` cannot see through `∑ m, (fun m => e m.succ) m` vs
  `∑ i, e i.succ` (different atoms); `simpa using he` beta-reduces first.

Verification: focused check green, targeted build green, all three lemmas
axiom-clean.
