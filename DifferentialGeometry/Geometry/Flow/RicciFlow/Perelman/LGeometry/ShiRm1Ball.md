# `ShiRm1Ball.lean`

## Role

This module assembles the fixed compact ball cutoff and the finite-cutoff
first Bernstein estimate into the scale-invariant local first-derivative Shi
bound required by the Perelman L-geometry noncollapsing endgame.

## Current state

`shiRm1_ball` is stated and warning-free focused GREEN. It chooses one
dimension-only short time and constant before the flow, terminal time, ball,
or point. On the later half of the normalized time window and the radius
`r / 8` subball it proves the scale-invariant estimate

```text
sqrt |nabla Rm|^2 <= C / r^3.
```

The proof first builds the fixed compact cutoff and applies the finite `m = 1`
Bernstein estimate at radius one. It then transports completeness and regularity
through parabolic rescaling, uses the scalar `paraNablaRmNormSq` identity, and
scales back. It never compares whole tensor bundles or metric-valued maps.

The regularity input is the honest open-left curvature window. Completeness is
required only on the shorter normalized slab actually used by the maximum
principle. No whole-manifold curvature bound or stronger consumer hypothesis
was added.

## Progress

- `shiRm1_ball`: 100% (stated and warning-free focused GREEN).
- Dedicated finite-cutoff and fixed-ball-cutoff machinery: 100% and consumed by
  the endpoint.
- `smooth_nlc`: 0% (not yet stated or proved).

The next exact theorem is the scalar-gradient adapter `lGrad_ball`, using the
contracted Bianchi identity and native tensor-norm comparison.
