# IndexFormPositive status

## Verified declarations

- `left_poincare_lt` is focused- and exact-green.  It proves the sharp one-sided
  Dirichlet/free Poincare inequality for every `a < pi / 2` by a regularized
  Riccati-weight square completion.
- `IsJacobiSolOn.end_pair_pos` is focused- and exact-green.  It combines the sharp
  inequality with `indexForm_eq_sub` and a pointwise curvature-form upper bound
  to obtain strict positivity of the endpoint pairing.
- The file is sorry-free, exact-current, and the focused check has no
  diagnostics.

## Role in the CGT producer

This closes the analytic sharp-constant brick needed by the general
`intrLoop_ge_cgt` statement.  It does not by itself prove the geometric Rauch
endpoint theorem: the next brick is the invariant curvature adapter and the
intrinsic Jacobi/endpoint-Hessian readout.

Connectedness is not part of this analytic API.  If a later geometric consumer
still inherits `[ConnectedSpace M]` from an older theorem, the CGT route will
restrict to the connected component containing the basepoint and finite orbit;
it will not add a global connectedness field to the producer.

## Honest accounting

- `left_poincare_lt`: theorem 100%; dedicated machinery 100%.
- `IsJacobiSolOn.end_pair_pos`: theorem 100%; dedicated machinery 100%.
- intrinsic geometric endpoint positivity: theorem 0%; dedicated machinery
  about 70%.
- `intrLoop_ge_cgt`: theorem 0%.
- `InjRadiusDecayInput` producer: theorem 0%.
- unconditional Theorem 3.9: theorem 0%.
- whole HCG supporting machinery: about 61%.

## Next target

Prove the lowest invariant curvature quadratic-form adapter and use it to turn
`end_pair_pos` into the intrinsic endpoint-pairing positivity theorem consumed
by the branch Hessian/strict-convexity layer.
