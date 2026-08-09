# H3BoundedGrid status

## Goal

Prove the dimension-three `H3` integral bound for the fixed
`boundedFactorGridWindow` with factor cap three and total-order window five.
This is the low analytic input needed to control the bounded-factor remainder
of a refolded Ricci--DeTurck order-zero coefficient in `H2`.

## Result

`h3_bfg5_int` is proved without `sorry`.  It gives a nonnegative bound
function for the integral of `boundedFactorGridWindow b 3 5` from the four
intrinsic `L2` jets making up the metric `H3` norm.

`h2_of_bfg5` is the consumer-shaped integration bridge.  If the first three
covariant derivatives of a coefficient field are pointwise bounded by the
refold residual windows `(i + 1, i + 3)`, it widens those windows to `(3, 5)`
and returns a uniform intrinsic `H2` jet bound from the metric `H3` jet alone.
No `H4` metric hypothesis is introduced.

`h2_of_bfg5_top` is the tame companion.  It accepts one explicitly separated
head term at order `i + 2`, integrates the same low windows using only the
metric `H3` jet, and retains the head as

`sum_(i < 3) Ctop i * ||nabla^(i+2) P||^2`.

Thus the only jet above `H3` is the linear `nabla^4 P` head at `i = 2`; it is
not hidden in a pointwise `H4` radius.

The proof reuses `h3_grid_int` for total orders zero through three.  At total
order four, the cap-three filter removes the fourth-derivative singleton.
The remaining positive-order cells, including the `2+2` cell, are controlled
by the existing two-arm estimate applied to the first covariant derivative of
the metric deviation.  Order-zero and order-one factors are absorbed by the
dimension-three pointwise jet estimate.

Focused verification passed with no local diagnostics after all three public
theorems were added.

## Frontier

This closes only the analytic window integral and its two generic
coefficient-jet consumers.  A raw coefficient-by-coefficient `H3`-only bound
is not the correct order-two route: differentiating the variable principal
coefficient leaves a genuine metric `H4` head.  The next producer must give
the complete refolded order-zero coefficient a public pointwise
head-plus-window estimate and apply `h2_of_bfg5_top`.  The resulting head is
then paired with the lower metric factor and packaged using
`L-infinity_t H3` and `L2_t H4`.

The endpoint `ricci_flow_unif_existence` remains unstated/proved at this
frontier (0%).  Its dedicated low-regularity machinery is approximately
85--88%; this theorem is one analytic producer inside that machinery, not the
common-horizon existence theorem itself.
