# `LowRegRungThree.lean` — notes

Status: **rung 3 is stated and proved, sorry-free.** The endpoint is
`lowregRung3`. Verification passed (focused check, targeted build, census;
`[propext, Classical.choice, Quot.sound]`, zero `sorryAx`).

Executor sessions for ledger №161 (Brick C-1, jet layer) and №163 (Brick C-2,
the closure + the endpoint).

## What is in this file

Jet layer (C-1):

* `symmS_jet_le` (public) — symmetrization does not increase a covariant jet.
  Rebuilt from `iteratedCovGrad_symmS_eq` and
  `riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection`, with the
  permutation-invariance step as the private helper `permJetNorm`.
* `galRepJet_le` — the **retraction-shrink** bound. `∑_{j ≤ n} ‖∇ʲ(symmS(rep))‖
  ≤ C·√(∑_{i∈F} (1+λᵢ)ⁿ (c i)²)`, i.e. `≤ C·√Eₙ`, for every `0 ≤ R`,
  unconditionally — no ball, first-exit or smallness hypothesis. This is the
  JOINT-RETR dissolution of №161 realized in Lean.
* `galRepJet_rad` — the same jet at order 2 read off the state ball instead:
  `∑_{j ≤ 2} ‖∇ʲ(symmS(rep))‖ ≤ C·R`.

Closure layer (C-2):

* `jetSqrtLe` — the micro-bridge `√(∑ aⱼ²) ≤ ∑ aⱼ` on a jet window.
  **Not written from scratch**: it is `sqrtFinSum` (public, from
  `LowRegA2PerIndex`) composed with `Real.sqrt_sq`. The exhibit sweep found the
  producer already in the a₂ file, as №163 predicted.
* `jetWinMono` (public), `mul3Le` (private) — window monotonicity and
  triple-product monotonicity.
* `armLadder3` — **the slot map, as a theorem.** From abstract jet
  handles `jet₅ ≤ X`, `jet₄ ≤ Y`, `jet₃ ≤ Z` it proves
  `∑_{q≤2}(‖∇^q a₂T‖ + ‖∇^q a₁T‖) ≤ (Ctop·Cδ + Kr2·Z + Kr1·Z)·X +
  Kmid·(1+Cδ)·(1+Y)²(1+Z)²`. The statement IS the whitelist: only three
  constants multiply `X`.
* `galArmVec` (public `def`) — the seed-subtracted forcing arm of a retracted
  Galerkin state, i.e. the `H¹` embedding of `A.a₂ T + A.a₁ T` at
  `T = symmS g₀ (galCoreRep g₀ R F c)`. It is definitionally the arm term
  `galForceArm` produces, so the split closes by `rfl`/`exact`.
* `galArmMass` (public) — the ladder input along the trajectory:
  `√(∑_{i∈F} w_i²·(arm coeff)²) ≤ (Ctop·Cδ + Kr2·R + Kr1·R)·√E₄ +
  Kmid·(1+√E₃)²`, five constants all fixed before `(F, c)` hence before `N`.
* `lowregRung3` (public) — **the endpoint.**

## The endpoint

```
lowregRung3 (hDim : finrank ℝ E = 3) (g₀) {δ Ctop B1 ρ P T B}
  (hδ hδ0 hδ3 hCtop hB1 hρ hP hreal hcore)          -- IsLowSolve-grade
  {U} (hUcont hUderiv hUinit)                       -- the Galerkin trajectory
  {Pr} (hPr0 hPrnn hPrcont hPrderiv hPrbd) :        -- the registered honest input
  ∃ Ctop₂ Kr2 Kr1 Cδ, 0 ≤ … ∧
    ∀ {ε}, 0 < ε →
      Ctop₂·Cδ + Kr2·lowregStateRad Ctop B1 ρ P + Kr1·lowregStateRad Ctop B1 ρ P
        + ε < 1 →
      ∃ Φ, ∀ N, ∀ t ∈ Icc 0 T, galerkinEnergy (eigenIdxFinset g₀ N) (U N) 3 t ≤ Φ
```

Adapter H is the single displayed inequality, and it names the constants the
theorem itself produces — the four whitelist contributions, with `2ε` from the
two Youngs appearing as `ε` after the `Cδ_engine < 2` normalization
(`Cδ_engine = 2α + 2ε`). No free-floating numerals.

`Pr` is `hL2H3` in `galRiderBound`'s primitive form (`Pr N 0 = 0`,
`0 ≤ Pr N ≤ B`, `Pr N' = E₃`). It is **carried, not discharged** — its producer
(PSTOP §6.1(ii) projected-MR replay plus the Galerkin identification) is a
registered campaign obligation.

## The slot map — CONFIRMED IN LEAN

The module docstring's table is now `armLadder3`'s conclusion. Reading the six
per-index instantiations (`a2PerIdxLin` and `a1PerIdxLin` at `q = 0, 1, 2`)
after the substitution `jet₅ ≤ X`, `jet₄ ≤ Y`, `jet_{≤3} ≤ Z`:

| ladder slot | destination | in Lean |
| --- | --- | --- |
| `a₂` `q=2` top, `Cδ·jet₅` | `E₄` coeff `Ctop·Cδ` | `b22`, first `X` term |
| `a₂` `q=2`, `i=q`, `K₂·(1+jet₅)·jet₃` | `E₄` coeff `Kr2·Z` | `b22` via `e10` |
| `a₁` `q=2`, `C₁` group `i=q−1`, `K₁(1)·(1+jet₅)·jet₃` | `E₄` coeff `Kr1·Z` | `b12` via `e10` |
| two Youngs of `two_sum_ladder_add_le` | `E₄` coeff `2ε` | engine |
| all remaining `a₂`/`a₁` slots | `Kmid·(1+Y)²(1+Z)²` | `b20 b21 b10 b11` + rest of `b12` |
| static seed `𝒩(0)` (`lowRegSeedMass`, `n := 3`) | `seed·√E₃` | `hstat` |
| radius-priced remainders | `c₀ = Kmid²/ε` | `γ` of the ladder |

**No foreign constant reaches `E₄`.** The JOINT-A1TOP failure class did not
trigger: the discipline that makes this work is that `jet₃` (window
`Finset.range 3`, i.e. jets through order 2) is *always* priced by the class
radius `Z`, never by `Y`. If it were priced by `Y`, the `a₁` `C₀` slots
`K₀ i·(1+jet₄)·(1+jet₄)·jet₃` would become cubic in `√E₃`, giving a middle
coefficient `β² ⊇ E₃²` outside the `∫E₃ ≤ B` budget. Every slot is at most
**quadratic** in `Y`, which is exactly what `galRiderBound`'s
`Crid·(1 + E₃)` rider absorbs (`β = Kmid(2+√E₃)`, `β²/ε ≤ 6Kmid²/ε·(1+E₃)`).

## Lean lessons from this session

* **`set` bodies poison `linarith`.** The jet windows and the middle bucket were
  introduced with `set`; `linarith`/`nlinarith` then spent their whole heartbeat
  budget in `isDefEq`/`whnf` unfolding the let-values back into the
  `iteratedCovGrad` sums. `clear_value` on all of them (plus `clear` of the
  defining equations, which are ℝ-equalities and therefore *used* by `linarith`)
  removed two hard timeouts instantly. Rule: after the last use of a `set`
  body, `clear_value` before any linear-arithmetic tactic.
* **`nlinarith` where `linarith` suffices is a timeout.** Every one of the
  fifteen arithmetic steps in `armLadder3` is linear in the monomial basis;
  supplying the monomial-nonnegativity facts (`0 ≤ Y*Z`, `0 ≤ Y*Y*Z`, …) as
  hypotheses and calling `linarith` is instant, while `nlinarith` on the same
  goal with the same hints times out (it forms all pairwise products first).
* **Do not `norm_num` a per-index bound.** `norm_num` on the `a₂`/`a₁`
  hypotheses unfolds `iteratedCovGrad` into explicit `covGrad` chains and
  destroys the window shape. Reduce the *outer* Leibniz sums only, with
  targeted `Finset.Icc 1 q = …` / `Finset.range q = …` rewrites (`from rfl`
  works for all of `Icc 1 0`, `Icc 1 1`, `Icc 1 2`, `range 0/1/2`) plus
  `Finset.sum_empty`/`sum_singleton`/`sum_pair`, applied to **each hypothesis
  separately** — `range 2` is an outer index set at `q = 2` but a *window* at
  `q = 0, 1`, so one shared simp set would corrupt the latter.
* `jetMono` was already taken (about `lowJetSq`, `LowRegOpJetWindows.lean:225`);
  the new window lemma is `jetWinMono`.
* The two benign defeq seams of №161 behaved as predicted: `galArmCap`'s cap
  feeds `a2PerIdxLin`'s `hfib` by `exact` (the `δ < 1` proof slot differs but is
  a Prop), and the seed lane closes with `simpa only [Nat.cast_ofNat] using …`
  (delta-unfolding `lowregNfun` to `lowRegN` inside the final `exact`).

## What is NOT done

* `Pr` (`hL2H3`) is an input, not a theorem.
* Rungs 4 and 5 are untouched. `armLadder3` is rung-3-specific (`range 3`,
  `q ≤ 2`); the general-`k` version needs the same regrouping with `q ≤ k−1`,
  and the engine will additionally need a dissipation export (`∫E_{k+1}`), which
  `galerkin_l1_single` does not provide.
* The Fatou glue (JOINT-IDENT, `galTameForce_eq`) is untouched; `lowreg_loMass`
  is still **0%**.

## 2026-08-05 GAP-ORDER follow-up

GAP-ORDER is now closed in this file.  `galArmMassOrd` fixes
`Ctop₂, Kr2, Kr1, Kcap` from `hDim,g₀` before introducing `R`, `δ`, or the
realization proof, and exposes the fibre coefficient as
`Kcap * (δ / (1 - δ)^2)`.  Its `Kmid` remains after those parameters because
it genuinely contains radius- and fibre-dependent factors, but it affects only
the Grönwall bound and not absorption.  `lowregRung3Ord` propagates exactly this
ordering through the rung endpoint.  The former declarations `galArmMass` and
`lowregRung3` are compatibility wrappers, so existing Fatou consumers did not
change.

Focused verification and the widened ShortTime axiom census passed.  Both new
ordered declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` was introduced.

The next gap is not a local consequence of this theorem.  An arbitrary
`IsLowSolve` does not retain a calibrated `δ` or radius cap and therefore cannot
imply the absorption inequality.  The smallest honest repair is a separate
explicit-witness solve package and adapted producer, projecting to the existing
`IsLowSolve` API while carrying the chosen `δ`, `Rcap`, and budget.  The
still-unproved `lowreg_loMass` input must then consume that adapted package (and
the low-mass Fatou consumer needs the corresponding explicit-witness sibling).
This is a statement/interface redesign, not a missing algebra lemma.

Honest progress after this brick: `lowreg_loMass` theorem **0%**; its dedicated
machinery ≈**86%**; (N) `ricci_flow_unif_existence` **0%**; whole HCG ≈**3%**.

## 2026-08-05 — ordered witness package

`IsRung3Ord g Ctop₂ Kr2 Kr1 Kcap` records one explicit ordered rung-three
certificate, including the exact universal continuation of `lowregRung3Ord`.
`lowregRung3Pack` selects the tuple once.  Adapted consumers must retain this
predicate and invoke its stored continuation; calling `lowregRung3Ord` again
would select an incomparable existential tuple and recreate GAP-ADAPTH's
coherence bug.

Focused verification and the targeted module refresh passed.  The package
proves no new rung and does not move `lowreg_loMass` above 0%; it only prevents
witness erasure in the calibrated route.

## 2026-08-05 — reusable rung-four boundary

`jetSqrtLe`, `jetWinMono`, and the raw ladder `armLadder3` are now public; their
statements are unchanged.  This is the narrow ShortTime reuse boundary needed
by `LowRegRungFour.lean`: the next rung can share the checked square-root/window
bookkeeping and the complete `q ≤ 2` arm estimate rather than copy either proof.

Focused verification passed after the promotion.  The downstream rung-four
module now uses this boundary and is checked independently.
