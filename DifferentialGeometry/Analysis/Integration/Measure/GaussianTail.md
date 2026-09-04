# Gaussian tail from polynomial ball growth

## Scope

This file supplies the metric-measure shell estimate needed before the
moving-center reduced-density no-mass-loss argument.  It is deliberately
independent of comparison geometry, Ricci flow, κ-solutions, and surgery.

## Mathematical route

The exterior of the radius-`N` ball is covered by the shifted unit annuli
`N + k ≤ dist < N + k + 1`.  On each annulus the Gaussian is bounded at the
inner radius, while the annulus measure is bounded by the polynomial estimate
for the outer ball.  Summing gives `gauss_tail_of_ball` with the common tail
`gaussTail d decay N`.

The quadratic shell weights are summable by comparison with a polynomial times
a linearly decaying exponential.  `gaussTail_zero` then gives convergence of
the shifted common tail to zero.

## Assumptions and boundary

Only a pseudo-metric space, an arbitrary measurable space and measure, positive
Gaussian decay, and the stated polynomial upper bound for balls of radius at
least one are used.  There is no Borel, completeness, curvature, finite-measure,
or manifold hypothesis in this analytic layer.

## Verification

Focused verification is warning-free GREEN.  The first check's one
ball-membership orientation mismatch and two deprecated monotonicity calls were
repaired mechanically.  No refresh or build was needed.

## Project position

`gauss_tail_of_ball` and its dedicated generic analytic machinery are verified
complete.  The book12 moving-center Gaussian-tail theorem remains unstated in Lean (0% as a
theorem); this brick is roughly 25% of its dedicated machinery.  That theorem
is one small part of P2b no-mass-loss.  Across P0--P9, the whole Poincaré
formalization infrastructure is approximately 15--25% complete.
