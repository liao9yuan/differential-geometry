# RHSRefoldPathIntegral

## Mathematical conclusion

The complete Ricci--DeTurck slope from the carrier metric to a symmetric
deviation now has a public refolded path-integral form.  The theorem
`rhs_sub_zero_refold` writes the realized right-hand-side difference as:

- the integrated complete order-zero refold applied to the deviation;
- the existing integrated order-one arm applied to its first covariant
  derivative; and
- the integrated complete top refold applied to its second covariant
  derivative.

The Ricci and DeTurck principal terms are combined before integration.  The
statement has no high-jet metric hypothesis and no nonsmall `H3` coefficient.

## Proof route

`rhsRefold0_joint` assembles joint smoothness of every explicit component of
the order-zero refold from the public moving-metric trace, Ricci coefficient,
DeTurck coefficient, and `lieCorr0` APIs.  `rhsRefold0Int` and
`rhsRefoldTopInt` then use the existing coefficient-field path integral.
Finally, `rhs_sub_zero_refold` integrates the exact public
`rhsSlope_refold` identity along the realized segment.

The old large remainder file was not extended and no new facade was added
there.  The temporary elaboration failures were local syntax, model-wrapper,
and private-helper visibility issues; they did not expose a different
mathematical route failure.

## Verification

The source passes focused verification without a local warning.  It contains
no `sorry`, `admit`, axiom declaration, or `whnf`.  The direct upstream
`RHSRefoldArms` artifact was refreshed and passed its named target build; this
new module itself has not been target-refreshed.

## Remaining frontier

The next producer is quantitative rather than algebraic: prove the
bounded-factor-grid pointwise jet windows for `rhsRefold0Int` and
`rhsRefoldTopInt`, then apply `H3BoundedGrid.h2_of_bfg5`.  Those `H2`
coefficient bounds will supply the same-horizon nonautonomous `A1/A2`
families.  Time measurability/uniform boundedness, the order-two bootstrap,
all-order smoothing and geometric realization, and the final common-horizon
assembly remain separate frontiers.

## Progress accounting

- `rhs_sub_zero_refold`: **100% as a source-checked theorem**.
- Its path-integral algebra and joint-smoothness machinery: **100%**.
- The same-horizon order-two bootstrap theorem: **0%** until stated and proved.
- `(N) ricci_flow_unif_existence`: **0% as a theorem**.
- Dedicated `(N)` machinery: conservatively **85--88%**.

