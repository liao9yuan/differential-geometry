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

## 2026-08-29: `estimate_complete` interface audit

- The intended native exhaustion route is already present:
  `estimate_barrier_at` combines the all-order Bernstein induction with a
  centered `ShiBarrierCutoffData` exhaustion.  The sibling
  `estimate_cutoff_at` consumes a global `ShiCutoffData` exhaustion.  Both
  routes require `TowerNormGradUpTo B m` to control the cutoff-gradient cross
  terms.
- The public `estimate_complete` statement supplies neither that Kato input nor
  a cutoff producer.  `BernsteinTower` itself has regularity and heat-inequality
  fields but no norm-gradient field, so `TowerNormGradUpTo` is not a projection
  of the current structure.  The actual curvature-tower consumer constructs it
  separately from `towerNorm_grad_le` before calling `estimate_barrier_at`.
- No existing generic producer builds
  `forall O, Nonempty (ShiBarrierCutoffData G B.T O)` from the hypotheses of
  `estimate_complete`.  The available `shiBarrierCutoff_of_sol` is specialized
  to an actual `SolutionOn`; it uses the Ricci-flow equation, completeness of
  the initial Riemannian metric, and a zeroth curvature bound.  It does not
  apply to an arbitrary `MetricConnectionFamily` with only uniform quadratic
  equivalence and a Ricci lower bound.
- Three distinct routes therefore stop honestly: the cutoff/exhaustion route
  lacks `TowerNormGradUpTo` and cutoff data; the compact theorem
  `BernsteinTower.estimate` lacks `[CompactSpace M]` (not implied by complete
  and sigma-compact); and the additive complete-manifold/Calabi route has no
  generic maximum-principle producer in the current tree and the existing
  distance supports require actual Ricci-flow solution data.
- Smallest repair: specialize the complete endpoint to the actual solution
  curvature tower and construct the existing cutoff plus Kato producers there,
  or consume those two producers explicitly through the already checked
  `estimate_barrier_at`.  Adding them as fresh assumptions to
  `estimate_complete` would only move the frontier and was deliberately not
  done.
- `estimate_complete` theorem: still 0%.  Its dedicated finite-cutoff and
  exhaustion machinery remains about 90--95%.  Static audit completed; no Lean
  verification was run because the shared elaboration guard was occupied by
  the P1 campaign.
