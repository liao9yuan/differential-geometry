# HigherDerivative

## 2026-08-28: point-local top reaction estimate

- Added the canonical `BernsteinTower.reactionSum_top_at`.  It proves the
  existing top reaction-sum estimate from the explicit pointwise input
  `hw0 : B.w 0 t x <= B.K ^ 2`; the proof is the former
  `reactionSum_top_le` proof with only its use of `B.hw0_bound` replaced by
  `hw0`.
- Preserved `BernsteinTower.reactionSum_top_le` with its public statement and
  behavior as the global compatibility specialization using
  `B.hw0_bound t hmem x`.
- Focused verification passed without errors or warnings.  No named module
  refresh was run because no downstream source consumes the new export yet.

The exact next consumer is `Complete.GfunSupport_parabolic_le`: its localized
top reaction-sum step should supply the pointwise zeroth-order estimate directly
to `reactionSum_top_at`, without requiring `B.hw0_bound` at every point of the
manifold.

Progress accounting: this bounded generic API refactor is **100%**; that local
Bernstein consumer is not yet implemented (**0%**); `shiRm1_ball` and
`smooth_nlc` remain **0% theorem endpoints**.  The current L-geometry plan
records dedicated L8--L9 machinery at about **78--80%**, reused generic
infrastructure at **100%**, and whole P0--P9 infrastructure at **15--25%**.

## 2026-08-28: level-one top coefficient

- Added the canonical closed form `towerBarTop_one`, recording that the
  top reaction coefficient has no cross term at level one:
  `towerBarTop c C 1 = 2 * c`.
- This avoids repeatedly unfolding the recursive Bernstein constant family in
  the finite `m = 1` consumer.  `FiniteCutoff.estimate_cutoff_one` is the real
  downstream source that consumes the export.
- Focused verification and the required named refresh are warning-free GREEN.

This constant lemma is complete (**100%**).  It does not itself complete
`estimate_cutoff_one`, `shiRm1_ball`, or `smooth_nlc`; those theorem endpoints
retain their independently reported status.
