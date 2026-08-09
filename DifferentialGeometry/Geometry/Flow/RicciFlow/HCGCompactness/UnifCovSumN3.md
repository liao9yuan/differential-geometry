# UnifCovSumN3 — the `hAcc` m=2 glue and the unconditional N=3 telescoping endpoint

Companion to `UnifCovSumN3.lean`.  Sibling of `UnifCovSumCross.md` (the T-B `D_N` recursion) and
`ConnDiffDeriv2Bound.md` (the a=2 atom).  This leaf is the consumer glue: it feeds the a=2 atom
`covStepDiff2_exists_const` into the `D_N` telescoping recursion `iterCovG1_le`, closing UNIF
item 6's `N = 3` case.

## STATUS (2026-07-26) — N=3 GREEN

- **`covStepAcc2_le`** (the `hAcc` m=2 accumulator bound) and **`iterCovG1_three`** (the
  unconditional N=3 endpoint) are PROVED sorry-free.  Focused check + targeted module build
  passed; `#print axioms` on both = `[propext, Classical.choice, Quot.sound]` (literal).
- **`hAcc_of_jets`** (general-m accumulator bound, the a≥3 frontier) is STATED with a flagged
  `sorry` — the file's only sorry.  `iterCovG1_three` does NOT depend on it (axiom check above).
  Do not consume `hAcc_of_jets` downstream while the sorry stands.

## Why this file exists (import-graph justification)

The glue needs `iterCovG1_le` (`UnifCovSumCross.lean`, namespace `DifferentialGeometry.PDE.RicciFlow`)
AND `covStepDiff2_exists_const` (`ConnDiffDeriv2Bound.lean`, namespace
`DifferentialGeometry.HCGCompactness`).  `ConnDiffDeriv2Bound` imports `UnifCovSumCross`, so the
glue cannot live in `UnifCovSumCross.lean` (cycle); `ConnDiffDeriv2Bound.lean` is at ~3050 lines
(over the 3000 cap, split-flagged in its own §0).  Hence this leaf importing `ConnDiffDeriv2Bound`.
The endpoints live in `DifferentialGeometry.PDE.RicciFlow` beside their `iterCovG1_*` family.

Three tiny `UnifCovSumCross.lean` privates are re-derived privately here (`covStep_zero'`,
`sqrt_normSq0S_zero` — through the public `exists_gOrthonormalBasis` instead of the private
`exists_g_onbasis` — and `telescAccum_one`).  Hoist candidates: `covStep_zero'`/`telescAccum_one`
→ `MetricCovDerivLinear.lean`, `sqrt_normSq0S_zero` → `ProductMFoldNorm.lean`; pending planner
hoist (same status as the `UnifCovSumCross.md` "hoist candidate" list).

## The m=2 reconciliation (telescAccum-2 vs the atom's ∇₂²(A⋆S))

`telescAccum 2 = ∇₁(A⋆T) + A⋆∇₂T` is NOT literally the atom's shape.  The reshaping is two
rewrites (`telescAccum_one` + `∇₁ = ∇₂ + A` on the middle derivative, i.e.
`eq_add_of_sub_eq`-style unfolding realized as `simp only [diffStep]; abel`) followed by
`covStep_add` twice:

```
∇₂(telescAccum 2) = ∇₂²(A ⋆ T)          -- the atom, s = r          ⟹ C₂·(P₀+P₁+P₂)
                  + ∇₂(A ⋆ (A ⋆ T))     -- covStepDiff_of_jets s=r+1 ⟹ CA₁·(|A⋆T| + |∇₂(A⋆T)|)
                  + ∇₂(A ⋆ ∇₂T)         -- covStepDiff_of_jets s=r+1 ⟹ CA₁·(P₁+P₂)
```

with `|A⋆T| ≤ cs₀·P₀` (`diffStep_jet_one_le`, s=r) and `|∇₂(A⋆T)| ≤ CA₀·(P₀+P₁)`
(`covStepDiff_of_jets`, s=r — the m=1 bound reused).  Fold:
`Racc 2 = C₂ + CA₁·(cs₀ + CA₀ + 1)` (existential since `C₂` is), and the level-2 bound is SHARP
in the jets `P₀,P₁,P₂` (range `m+1 = 3`), one below the `range (m+2)` that `hAcc` allows — the
`P₃` pad is free by nonnegativity.

`iterCovG1_three` then instantiates `iterCovG1_le` at `N = 3` with
`Racc = fun m => if m = 1 then CA₀ else if m = 2 then C₂acc else 0`; m=0/m=1 discharge verbatim as
in `iterCovG1_two`; the endpoint constant is `max 0 (Dtower … Racc 3)` (the `max 0` gives
`0 ≤ C` without needing a point of `K`, the `covStepDiff2_exists_const` idiom).

## The a≥3 frontier (`hAcc_of_jets`)

Stated shape: jets of `g₁` against `g₂` through order `m+1` as a function family
`hJets : ∀ j, 1 ≤ j → j ≤ m+1 → MetricCovDerivOrderBoundOn K j g₁ g₂ (Λs j)`, plus `hEq`/`hjet`
(role asymmetry), conclusion = `hAcc` at level `m` with a `T,x`-uniform existential constant and
the consumer-exact `range (m+2)` jet sum.  Proof route (multi-session): the expansion of
`∇₂(telescAccum m)` produces all `{∇₂, A}`-words of weight `m+1` with ≥1 `A`; the needed atoms are
the a-fold base-Leibniz jets `∇₂ᵃ(A⋆·)` for `a ≤ m` (a=3+ siblings of `covStepDiff2_exists_const`)
composed over lower-order accumulators — likely by strong induction on `m` once the atom family
exists.  The m ≤ 2 instances suggest the sharp sum is `range (m+1)`.

## Lean lessons (this session)

- **The fibre-triangle whnf wall, and its cure.**  Passing raw `covStep`/`diffStep` trees through
  `sqrt_normSq0S_add_le` with `_ _` holes (a nested two-triangle) hit a deterministic whnf
  timeout at 1.6M heartbeats; `backward.isDefEq.respectTransparency false` did NOT help.  The
  cure is the `iterCovG1_le` taming idiom, verbatim: `set av/bv/cv := (the three fibre values)`
  + `clear_value av bv cv`, then the triangle with EXPLICIT arguments
  (`sqrt_normSq0S_add_le g₂ (av + bv) cv basis hinv`).  State the per-piece norm bounds BEFORE
  opacifying so `set` folds them.
- **Defeq-coercion for rank arithmetic works and is cheap.**  All `r+1+2 ↦ r+3`, `r+1+1 ↦ r+2`,
  `iterCov g₂ r T k ↦ covStep`-chain conversions were done by stating the bound in the target
  currency and proving it `:= (the emitted lemma)` — every such `have` elaborated instantly.
  The wall above is specifically about unifying fibre SUMS (instance-carrying `+` on
  `Tensor0SSpace`) against holes, not about Nat-rank defeq.
- **`reduceIte` does not fire on false Nat-literal conditions here** (m=0 branch); the working
  precedent is explicit `simp only [if_neg (by norm_num : (0:ℕ) ≠ 1), …]` (`iterCovG1_two`'s
  m=0 branch).  True conditions (`if 1 = 1`, m=1 branch) reduce fine with `reduceIte`, and
  term-mode `le_trans`/`mul_le_mul` steps see through unreduced ifs by whnf-defeq (m=2 branch
  needed no ite-reduction at all).

## What UNIF item 6 still needs after this (honest)

This closes the pointwise `j = 3` derivative-level bound.  The S0 endpoint still needs: the S0
`j ≥ 2` L² assembly (fibre+volume+derivative composition at each order), the remaining 2a-hi/pkg
and S2–S4/S1b items per `ShortTime/UNIF_ITEM6_RECON.md` / the UNIF plan, and for general `N` the
`hAcc_of_jets` frontier above.  See `UnifCovSumCross.md` §Status for the running T-B ledger.
