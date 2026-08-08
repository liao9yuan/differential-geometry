# CrossScaleCauchySchwarz

Spectral-coordinate Cauchy–Schwarz across neighbouring Sobolev scales, and the
pairing inequalities the parabolic energy hierarchy consumes.

## Contents

* `tensorSobolevWeight_eq_sqrt_succ_mul_sqrt_pred` — the weight split
  `w^σ = √(w^{σ+1}) · √(w^{σ-1})` that moves one derivative from the forcing
  onto the state.
* `sq_sum_crossScale_le` / `abs_sum_crossScale_le` — Cauchy–Schwarz in that
  split; `two_mul_sum_crossScale_le_eps` — its `ε`-Young form;
  `two_abs_cross_le_eps` — the corresponding absolute-value estimate used by
  signed Galerkin pairings.
* `sq_sum_sameScale_le` / `two_mul_sum_sameScale_le_sqrt` — the same-scale
  pairing that produces the `√`-seed term.
* `two_mul_sum_ladder_le` (2026-08-04, E1′ lane) — the composition: the
  parabolic **energy closure** produced from a ladder bound on the forcing.

## `two_mul_sum_ladder_le` — what it is and why

This is `PSTOP_PROPOSITION.md` §3 ("the pairing and absorption arithmetic") in
Lean, at the level of the spectral coordinates.  Input: a split
`f = fd + fs` on the retained mode set, a ladder bound
`‖fd‖_{σ-1} ≤ α‖u‖_{σ+1} + β‖u‖_σ` (the shape `n_diff_hm_rung` delivers), and a
static bound `‖fs‖_σ ≤ D`.  Output:

    2 ∑ w^σ · u · f  ≤  (2α + ε)·E_{σ+1} + (β²/ε)·E_σ + 2D·√(E_σ)

which is *exactly* the `hclosure` hypothesis of
`galerkin_energy_uniform_bound_perScale` / `galerkin_energy_l1_bound`
(`…/HeatSemigroup/GalerkinParabolicEnergy.lean`), with `Cδ = 2α + ε`,
`Cmid = β²/ε`, `seed = 2D`.

Consequence worth recording: the engines' absorption condition `Cδ < 2` becomes
`2α + ε < 2`, i.e. **`α < 1` with `ε` free in the remaining room** — which is
precisely P-STOP's absorption condition `Cδ* = κ·δ*/(1−δ*)² < 1`.  The
paper-side arithmetic and the Lean engine's interface therefore match with no
adapter and no constant loss (the spectral frame has `c_par = 1` exactly).

Proof route: `abs_sum_crossScale_le` for the difference half,
`two_mul_sum_sameScale_le_sqrt` for the static half, and one Young inequality
on the mixed term `√E_{σ+1}·√E_σ`, written as an explicit square expansion
(`field_simp; ring` on `(√ε·√A − (β/√ε)·√E)²`) rather than left to `nlinarith`.
Green first try.

`α` and `β` need **no sign hypotheses** — the Young step is a square expansion
valid for either sign, and dropping the two `0 ≤ ·` hypotheses cleared the
`unusedVariables` warnings.  Only `0 ≤ D` (consumed by
`two_mul_sum_sameScale_le_sqrt`) and `0 < ε` are required.

Verified: focused check clean, targeted module build green (8692 jobs), axiom
census `propext, Classical.choice, Quot.sound`.

## 2026-08-05 — `two_sum_ladder_add_le`: the additive-`γ` ladder variant

Brick C part 1b of ledger №161. `two_mul_sum_ladder_le` with the ladder
hypothesis widened to `‖fd‖_{σ−1} ≤ α‖u‖_{σ+1} + β‖u‖_σ + γ`. A low-regularity
ladder produces such a `γ` whenever a Leibniz slot is priced by a fixed radius
(`jet₂(T) ≤ C·R`) rather than by the state, so the closure has to carry it, and
`two_mul_sum_ladder_le` as landed could not express §6.4's own display.

The proof is the existing one with one extra Young step
`2γ√E_{σ+1} ≤ ε·E_{σ+1} + γ²/ε`, taken at the **same** `ε` as the mixed term —
deliberately, per №161 seam (d): a third `ε` would have to be tracked through
adapter H for no gain. Consequences for the consumer: the dissipation constant
becomes `2α + 2ε` (absorption available as soon as `α + ε < 1`, since the
engine needs `Cδ < 2`), and the closure gains the additive slot `γ²/ε`, which
`energy_l1_single` / `galerkin_l1_single` now accept.

The extra Young is proved from `ε·(ε·A + γ²/ε − 2γ√A) = (ε√A − γ)²` plus
`nlinarith`, rather than by the `√ε` change of variables used for the mixed
term — shorter, and it avoids a second `field_simp` on `Real.sqrt ε`.
Verification: focused check + targeted build green; census clean.

## 2026-08-07 — absolute-value cross-scale estimate

`two_abs_cross_le_eps` applies the existing signed Young estimate to both `h`
and `-h`, then combines the two inequalities with `abs_le`.  It is now
focused-check green.  No new analytic input or scale loss is introduced.
