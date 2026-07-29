# RHSRefoldTameH2

## Goal

Build the dimension-three low-regularity coefficient bounds needed for the
same-horizon order-two Ricci--DeTurck bootstrap.  The correct tame shape keeps
one metric `H4` head explicit and controls every lower product window from the
metric `H3` jet.  It does not assert a pointwise `H4` ball.

## Verified bricks

- `ricciConn_h2_tame` converts the public pointwise top-amplitude estimate for
  the Ricci connection-difference coefficient into an intrinsic `H2` bound.
- `ricciBase_h2_tame` specializes the existing radius-free Ricci base-curvature
  producer to coefficient order two.  The `symmS` jets are contracted back to
  the raw metric deviation, the fourth jet remains explicit, and the first
  four jets feed only the lower tame function.
- `dLa_h2_tame` sums the radius-free DLa per-order producer through order two.
  Its zeroth-order grid radius comes from fibre smallness, its fourth metric
  jet remains one explicit head, and every lower jet is controlled by the
  metric `H3` radius.  It has no supercritical Sobolev-index hypothesis.
- `dLb_h2_tame` fixes the all-order producer's supercritical ceiling inside
  the proof and consumes only orders zero through two.  The public interface
  has no high-`a` or high-Sobolev-ball assumption.
- `lieCorr_h2_tame` applies the same internal-ceiling projection to
  `lieCorr0Field`.  Its lower window stops at the metric `H3` radius, while
  only the top term carries the explicit fourth metric jet.

The source-focused verification is green without local diagnostics.  Neither
theorem uses `sorry`, `admit`, an axiom declaration, or `whnf`.  The lower
DLb export is also exact-current (`9488/9488`).

## Route correction

The complete coefficient cannot be bounded from an instantaneous metric `H3`
radius alone.  Its genuine variable-principal part contains one fourth metric
jet.  The same-horizon route is therefore the time-tame estimate
`L-infinity_t H3` times `L2_t H4`; the endpoint `H4` quantity must remain
linear and explicit.

The all-order radius-free coefficient theorems are not exposed directly in
the low-regularity API: their statements impose the order-ceiling condition
`2 * dim + 10 <= a`.  At coefficient order two this ceiling is fixed inside
the proof.  It is not a metric regularity assumption and does not enter the
consumer statement.

The attempted identity
`dLaGridWin b 5 = b 4 + boundedFactorGridWindow b 3 5` is false: the
order-four antidiagonal grid also contains the fourth jet multiplied by
zeroth-order factors.  The correct route is the public radius-free
antidiagonal integrator at the fixed fibre-small radius.  It keeps the fourth
jet linear after integration without any pointwise `H4` assumption.

## Next frontier

The DLa, DLb, and `lieCorr0` tame constituents are now checked.  The next
frontier is the exact finite-sum assembly for `rhsRefold0`: first identify the
public Ricci-refold and Lie pair-trace identities that connect these
constituents to the literal `rhsRefold0` definition, then bound only the
remaining refold fields.  Do not estimate a pre-cancellation complete
coefficient or reintroduce a nonsmall `H3` top coefficient.

The theorem `ricci_flow_unif_existence` remains unproved.  These are dedicated
coefficient estimates for its order-two bootstrap, not the endpoint theorem.
