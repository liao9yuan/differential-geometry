# Complete

## 2026-08-28: point-local zeroth-order input

- `GfunSupport_parabolic_le` now takes the exact current-point bound
  `B.w 0 t x ≤ B.K ^ 2` and uses it both for the top reaction estimate and the
  zeroth cutoff-error term.
- The top reaction step consumes `BernsteinTower.reactionSum_top_at`; the two
  existing callers preserve the public API by supplying `B.hw0_bound` at their
  current point. No public theorem statement changed.
- Source refactor: 100%. Verification: focused check passed after the
  warning-free named refresh of `HigherDerivative`. The existing
  `estimate_complete` `sorry` warning remains and is unrelated to this refactor.
- This brick is dedicated local-Shi infrastructure, not the endpoint:
  `shiRm1_ball` remains 0% as a theorem, and `smooth_nlc` remains 0% as a
  theorem. The running phase estimates remain dedicated L8--L9 machinery about
  78--80%, reused generic infrastructure 100%, and whole P0--P9 infrastructure
  15--25%.
