# DeTurckRemainderPrincipalArmOpNorm.lean — note

This 9.4k-line module has no full note; this file records only the one change
made to it from the A1c lane (2026-08-04), because that change altered a public
derivative budget.

## The `16 ≤ a` gate on the first-order jet-window engine was an artefact

`exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le` and its two
halves `…_of_lowOrder` / `…_of_highOrder` advertised
`ha_super : 2 * finrank ℝ E + 10 ≤ a` (= `16 ≤ a` in dimension three).  This is
the order-generic engine for the **first-order** low-base arms — the one
`a1_ladder` has to consume — so that gate would have propagated into
`a1_ladder`, `n_diff_hm_rung`, and every hierarchy rung above them, putting the
a-priori ball at `H^18`.  `A1CUR_PLAN.md:283` had already flagged inheriting
`16 ≤ a` as a thing to avoid.

`ha_super` was **dead in `…_of_lowOrder`** (no textual use, and none of its
`omega`s needs it) and used in `…_of_highOrder` **only through two `omega`s**,
both of which are really about the hard-wired band split, not about `a`:

* `hSW_le_S` (`:4522`) needs `finrank ℝ E / 2 + m ≤ q` — the data's own
  sup-window `∇^{j+m} T₀`, `j ≤ finrank ℝ E / 2 + 1`, has to sit inside the
  output window `range (q+2)`;
* `hSW_le_B` (`:4530`) needs `finrank ℝ E / 2 + m ≤ a + 1` — the same window has
  to sit inside the a-priori ball `range (a+3)`.

and in `…_of_lowOrder` the only real requirement is `q + finrank ℝ E / 2 ≤ a`:
the coefficient's Sobolev jet window `∇^{i+j} C`, `i ≤ q`,
`j ≤ finrank ℝ E / 2 + 1`, has to sit inside the ball (`:4276`).

## What changed

* `…_of_lowOrder`: `ha_super` deleted; band hypothesis relaxed from
  `q + (finrank ℝ E / 2 + 3) ≤ a` to `q + finrank ℝ E / 2 ≤ a`.
* `…_of_highOrder`: `ha_super` replaced by `ha : finrank ℝ E / 2 ≤ a`; band
  hypothesis replaced by `finrank ℝ E / 2 + m ≤ q` (was `a ≤ q + (finrank/2+3)`).
* The combined engine: gate `ha : 2 * (finrank ℝ E / 2) ≤ a`, and the dispatch
  splits on `q < finrank ℝ E / 2 + m` instead of on `q + (finrank/2+3) ≤ a`.
  Exhaustiveness: if `q ≥ finrank/2 + m` take the high half; otherwise `m ≤ 1`
  forces `q ≤ finrank/2`, so `q + finrank/2 ≤ 2 * (finrank/2) ≤ a` and the low
  half applies.  Both side conditions are `by omega`.
* The single internal consumer (`:4768`,
  `…_threeArmAppCc_coeffJetEnvelope_…`) keeps its own `ha_super` and now passes
  the weaker gate by `omega`.

Nothing else in the tree calls the three declarations; the module has only three
direct importers (`DeTurckRemainderRealizeBallUniformSplit`, `LowRegLadderRung`,
`ShortTime/LowRegRemainderH0`), none of which name them.  Cost measure taken
before committing to the edit.

Net effect: the first-order arm's budget is `2 ≤ a` in dimension three, i.e. one
*below* `a2_ladder`'s `3 ≤ a`, so it never binds in the assembled ladder.

## Sharpness

`2 * (finrank ℝ E / 2) ≤ a` is sharp for this route, not conservative.  The
binding case is `q = 1, m = 1` in dimension three: neither half covers it below
`a = 2`, because the high half would need `q ≥ finrank/2 + m = 2` and the low
half needs the coefficient's third jet `∇³ C₁`, whose tower window reaches
`‖T‖_{H⁴}`, to stay inside the `H^{a+2}` ball.  The towers' own gate `1 ≤ a`
(`c0_jet_tower`) is therefore genuinely one lower than the ladder's: the ladder
additionally pays for the coefficient's Sobolev window.

## Verification

Targeted module build green (267s), no new warnings; the pre-existing
`unused variable ha_super` warnings at `:1204` and `:4887` belong to other
declarations and are untouched.  A first attempt was killed by the memory guard
at 232 s (physical free memory dipped below the 0.4 GB floor) — that was a kill,
not a proof failure; the retry with no competing jobs passed.
