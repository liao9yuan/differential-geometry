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

## 2026-07-28 complete assembly

The exact finite-sum route has now been written:

- `liePair_h2_tame` expands the three signed pair terms into six arbitrary
  Palatini monomials and applies the low-order corner/residual window estimate.
- `rhs0_h2_tame` combines the Ricci connection and Palatini kernel, DLa, DLb,
  `lieCorr0`, and the negative Lie pair.  Its conclusion has one explicit
  fourth-jet head and a lower envelope depending only on the `H3` radius.
- The total proof uses the exact `rhsRefold_eq` identity from
  `RHSRefoldField.lean`; it does not estimate the cancelled `AA` or
  background-curvature fields.

The curvature-coefficient tower recovery is now exact green.  Both
`RHSRefoldField.lean` and this file subsequently passed focused and exact
verification; `liePair_h2_tame` and `rhs0_h2_tame` are therefore 100%
complete as stated.  There are no local diagnostics and no `sorry`, `admit`,
axiom declaration, `whnf`, or trace option in this file.

The next frontier is not another static coefficient estimate.  The current
order-one maximal-regularity solution supplies a uniform same-horizon
`L2_t H3` field and an `H2` trace, whereas `rhs0_h2_tame` honestly retains an
`H4` head.  Therefore it cannot simply be relabelled as an `A1(t)` family
without first proving the relevant time-regularity/linearization theorem.
The next implementation must either refold that head into the order-two
principal operator or prove the low-base same-horizon regularity step that
makes the head time-integrable.  It may not assume a uniform `H4` bound from
the C3 input class.

The theorem `ricci_flow_unif_existence` remains unproved (0%).  Its dedicated
machinery is conservatively about 88--90%; the fixed-background order-one
solve and complete static `H2` refold estimate are proved, while the
low-base regularity step, smoothing/realization, and uniform common-horizon
assembly remain separate theorem frontiers.
