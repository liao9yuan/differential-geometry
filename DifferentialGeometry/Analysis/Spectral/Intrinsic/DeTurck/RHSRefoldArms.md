# RHSRefoldArms

## Mathematical role

`rhsRefoldTop` adds the Ricci and DeTurck second-order coefficients returned by
`rhsLow0_refold` to the already combined top coefficient
`deTurckPhiMetTotal`.

`rhsSlope_refold` substitutes the exact order-zero refold into the complete
Ricci--DeTurck three-arm slope.  The result has one genuinely lower
order-zero coefficient, the existing order-one coefficient, and one explicit
refolded top coefficient.  It introduces no Sobolev, high-jet, or auxiliary
regularity assumption.

`lieRefold2_joint` and `rhsRefoldTop_joint` expose joint smoothness of the
returned second-order coefficient and of the complete refolded top family.
Their public statements have no high-order radius.  The DeTurck proof chooses
a finite smooth-input jet envelope internally only to project joint smoothness
from the existing quantitative theorem; none of its high-order constants are
used in a low-regularity estimate.

The attempted lower generic facade over
`deTurckLieCovDerivRefoldC2Family` was rejected: elaborating that full family in
the theorem type timed out even at the upstream file's heartbeat budget.  The
consumer-layer `lieRefold2` alias is the stable, cheaper interface.

## Verification

The complete source, including both new joint-smoothness declarations, passes
a focused Lean check without local diagnostics. There is no `sorry`, `admit`,
axiom declaration, or explicit `whnf`. An exact target refresh is deferred
until a downstream module needs the new public artifact.

## Honest status

This is algebraic machinery for the same-horizon order-two bootstrap.  It does
not prove an `H2` bound for `rhsRefold0`, construct the time-dependent `A1`
family, or discharge `ricci_flow_unif_existence`; that endpoint remains 0%.
