# Lipschitz W1

## Role

`memW1p_ball_of_lip` is the reusable local Sobolev bridge for real-valued
Lipschitz functions on finite Euclidean balls.  It uses Rademacher weak partial
derivatives from `hasWeakPart_of_lip`; finite ball measure supplies the local
`L²` bounds for the function and its bounded line derivatives.

## Reuse

The proof was previously private to the Busemann-line energy consumer.  It now
lives in the canonical Euclidean Sobolev layer so individual Busemann functions
and later local elliptic arguments can reuse it without duplicating the weak
derivative construction.  A manifold chart caller must still supply a globally
Lipschitz Euclidean representative; the existing smooth-cutoff construction in
`BusemannLineEnergy` should next be parameterized in the manifold Lipschitz
layer rather than copied by each Busemann consumer.

## Status

The extracted theorem passed warning-free focused verification and its named
module refresh is green.  It has the same mathematical proof as the earlier
focused-green private helper and introduces no new assumption.

This is supporting machinery only.  The Cheeger--Gromoll splitting theorem is
still unstated (0%); whole-P1c dedicated machinery remains about 60--65%, and
the whole Poincare program infrastructure remains about 15--25%.
