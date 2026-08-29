# NLCBallUpper

## Role

This module proves the controlled-ball upper bound for reduced volume used in
the good/bad L-exponential-source split.  It combines genuine endpoint
localization, a curvature-produced scalar lower bound, the pulled-back
Jacobian formula, moving-volume comparison, and the exactly normalized source
Gaussian tail.

## Producers

The real action, pointwise density, parametrized good-set, and final
good/bad-partition arguments now live in `NLCBallCore.lean`. The public
fixed-terminal statements in this file are unchanged:

- `lRedLen_scale` obtains the lower bound
  `-finrank^2 * eps <= redLength` for minimizing small-source endpoints.  Its
  proof uses `lRegRange_scale`, `scalar_ge_of_rm`, the nonnegative kinetic term,
  and the action/cost identity; no reduced-length bound is assumed.
- `lRedDen_scale` converts that length bound into the explicit pointwise
  reduced-density upper bound.
- `lRedJac_ball_le` changes variables through `lExpPartial` and bounds the
  small-source integral by the explicit density constant times the moving
  volume of the controlled terminal ball.
- `ballVol_move_le` applies the second quadratic-form comparison from
  `lMetric_scale` to `volumeMeasure_le`, giving the fixed determinant factor
  `sqrt((4/3)^finrank)`.
- `redVolume_ball_eta` partitions the full strict minimizing domain into the
  closed small-source part and its open complement.  The first part uses the
  preceding two estimates; the second uses `lRedJac_tail_le` and the
  dimension-uniform exact Gaussian threshold `lSrcGauss_unif`, contributing at
  most an arbitrary prescribed positive `eta`.
- `redVolume_ball_le` is the compatibility specialization `eta = 1/4`.

The pre-refactor implementation was warning-free focused green and its named
module artifact was refreshed. The extracted core is now warning-free focused
green, named-refreshed, and contains no `sorry` or `admit`; this downstream
wrapper is also warning-free focused green after the refactor.

## Quantifier boundary

Both public ball estimates are deliberately fixed-terminal-time
compact-backward-slab theorems: `time` and its regular slab are inputs before
the theorem produces
`eps0`.  This is the strongest statement justified by the checked
`lExp_scale_ball`, whose `eps0` is likewise produced after fixing terminal
time.  The proof does not commute `exists eps0` through `forall time` and does
not assume endpoint containment or noncollapse.

The arbitrary-tail obstruction is removed. The ball-local Shi, scalar-gradient,
regularized-speed, metric, maximal-range, and L-exponential producers are now
checked. `NLCBallUnif` reuses `NLCBallCore` to choose one `eps0` before the
flow, terminal time, center, and actual radius, and `SmoothNLC` consumes that
uniform endpoint.

## Progress accounting

- `redVolume_ball_le`: 100% for its stated fixed-terminal compact-slab
  interface.
- `redVolume_ball_eta`: 100% for arbitrary positive Gaussian-tail error.
- Dedicated good/bad source localization machinery at that interface: 100%.
- `redVolume_ball_unif`: 100% as a warning-free focused-green, named-refreshed
  theorem.
- `smooth_nlc`: 100% as a warning-free focused-green, named-refreshed theorem.
  Its ball-upper and compact reduced-volume-floor branches remain separately
  counted infrastructure.
- Under the full P0--P9 denominator, the final `poincare_of_inputs` theorem
  remains 0%; full-program infrastructure remains approximately 15--25%.
