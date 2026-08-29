# WeightedInterval

## Mathematical route

`neg_mul_deriv_le` is the one-dimensional weighted integration-by-parts
inequality needed along minimizing radial segments.  Absolutely continuous
weights and tests give the exact product boundary identity; a nonnegative test
transports the a.e. derivative upper bound through the integral, while the
oriented boundary hypothesis discards the favorable endpoint term.

`neg_mul_deriv_le_on_initial` upgrades this finite-interval result to the
initial open segment `(0,b)`.  Its test has topological support strictly inside
one compact interval `[a,c]`: this kills both boundary values and makes the test
and its derivative vanish off `[a,c]`.  The proof therefore restricts all a.e.
hypotheses to `[a,c]`, applies `neg_mul_deriv_le`, and extends both integrals
back to `(0,b)` without any limiting or geometric assumptions.

`neg_mul_deriv_le_Ioo` is the finite-cut-endpoint variant needed when the test
need not vanish at `b`.  Its only support-shaped input is
`EqOn ψ 0 (Ioc 0 a)`: it constrains neither negative radii nor any radius after
`a`, and the radial consumer can establish it by choosing `a` strictly below
the positive lower distance bound of the test support.  On `(0,a)` the open-set
derivative congruence gives `deriv ψ = 0`, while the value at `a` kills the
initial boundary term.  At `b`, the test may be nonzero; the separate condition
`0 ≤ J b * ψ b` discards exactly the favorable terminal boundary term.

The proof restricts the open-domain hypotheses to `(a,b)`, applies
`neg_mul_deriv_le` on `[a,b]`, and identifies the resulting interval integrals
with the original `(0,b)` set integrals through `[a,b)`.  No upper-support or
terminal endpoint-vanishing hypothesis is used.

`neg_mul_deriv_le_lim` removes the remaining requirement that `J` and `ψ` be
absolutely continuous all the way to the true ray endpoint `b`.  It assumes
absolute continuity only on every compact `[a,c]` with `a < c < b`, together
with the genuinely needed local boundary sign `0 ≤ J c * ψ c`.  The proof uses

```text
c n = b - (b - a) / (n + 2),
```

so that `c n ∈ (a,b)`, `c` is monotone, and `c n → b`.  The measurable sets
`[a,c n)` increase to `[a,b)`.  The finite-interval inequality holds at every
`c n`; `tendsto_setIntegral_of_monotone` passes both sides to the limit, and
`le_of_tendsto_of_tendsto'` preserves the inequality.  Integrability of both
full-open-interval integrands is exactly what justifies these two limits.
The same lower-gap argument as in `neg_mul_deriv_le_Ioo` then identifies the
`[a,b)` limits with the desired `(0,b)` integrals.

The local boundary-sign hypothesis is not an assumption wrapper: without a
sign condition on the exhausting endpoints, local absolute continuity and
integrability alone do not control the integration-by-parts boundary term.
In the radial consumer it is supplied by nonnegativity of the radial density
and test function.

This is a general real-analysis producer.  It neither assumes nor supplies the
geometric radial-Jacobian derivative bound.

## Remaining interface gap

The signed evaluator `integral_ioiPow_set` now lives in the separate
`PolarEvaluation` layer.  What remains outside this file is consumer assembly:
the radial proof must instantiate the local absolute-continuity, boundary-sign,
derivative, and integrability hypotheses for its geometric density and test,
then reassemble the resulting ambient radial set integrals through the polar
formula.  This interval module introduces no geometric assumption to hide that
frontier.

## Project position

- `neg_mul_deriv_le_on_initial`: complete (100%).
- `neg_mul_deriv_le_Ioo`: complete (100%).
- `neg_mul_deriv_le_lim`: complete (100%).
- Compact-support, finite-cut-endpoint, and local-exhaustion Lebesgue
  initial-segment variants: complete (100%).
- The dedicated one-dimensional exhaustion producer and separate signed
  `volumeIoiPow` evaluator are complete (100%); their downstream radial consumer
  assembly is not implemented in this file (0%).
- The final distance distributional-Laplacian theorem is still unstated and
  unproved (0%); its separately tracked dedicated machinery is substantially
  built.  This producer is only a small part of P1c and of the whole Poincare
  program.

## Verification

Focused verification of the extended Lean file passes without warnings.  No
named module refresh was run.
