# DifferentiatedPalatini

## Role

This curvature-layer module owns the exact differentiated `(1,3)` Palatini
expansion used by the uniform order-one curvature envelope.  It keeps the
algebra separate from the class-uniform pointwise estimates and does not depend
on the HCG leaf.

## Current state

`covDerivPal_eq` proves the exact skew difference of `covDerivConnDiff2` plus
the four quadratic terms with one `covDerivConnDiff` and one `connDiff`.
`mixedCurvDeriv` and `mixed_sub_eq_pal` identify the derivative of the
`g₀` curvature operator taken with the `gBase` connection, minus the fixed
`gBase` curvature derivative, with that canonical Palatini term.
Focused verification and the exact module build pass, with no placeholders.

The earlier HCG-leaf extraction was not used as an import: refreshing that
historical source exposed a bundle-model inference failure in its private
subtraction helper.  Moving the identity to the canonical curvature layer
removes that stale-artifact dependency and leaves class-uniform estimates to a
separate HCG consumer.

## Project accounting

`ricci_flow_unif_existence` itself remains unstated here and is still 0%.
This module closes the exact-algebra part of the E3 Palatini wall; the
fixed-order `a = 1` envelope is now closed in the HCG consumer
`UnifCurvatureJetOne`; its class-uniform `Ksup` consumer remains.
