# RegSpeedBall

## Role

`lRegSpeed_unif` combines the ball-local scalar-gradient estimate with the
existing Ricci quadratic estimate.  The resulting short-time threshold is
chosen before the flow, terminal time, center, and actual ball radius.  Its
prefix hypothesis is exactly the moving radius-`1/16` containment needed by
`lGrad_ball`.

The point being estimated is required to lie in the maximal regularized-ray
domain.  This is the honest noncompact interface: the existing automatic slab
continuation theorem assumes a compact manifold, while the later complete-flow
first-exit argument is responsible for closing the maximal domain.

The theorem deliberately bounds speed relative to its initial value.  Source
cutoffs belong to the later first-exit/range theorem, where the required
spatial margin is known.

## Status

`lRegSpeed_unif` is warning-free focused green.  It has no compact-manifold
assumption and introduces no new analytic hypothesis.  The local domain
membership is explicit because automatic noncompact continuation belongs to
the later complete-flow range layer.
