# UnifPalatiniJet1

## Role

This HCG sibling consumes the canonical differentiated Palatini identity and
the already banked class-uniform bounds for `A`, `∇A`, and `∇²A`.

## Current state

`unifPalatini1` is proved.  It gives a class-uniform fixed-order quadrilinear
bound for the canonical pointwise differentiated Palatini vector using metric
jets only through order three.  Both focused verification and the exact
targeted module refresh passed, and the declarations are axiom-clean.

The proof uses the canonical `covDerivPal_eq` split together with the banked
uniform bounds for `A`, `∇A`, and `∇²A`.  The older HCG-local
`covDerivConnDiff2` is definitionally identical to the canonical curvature
layer definition; a private equality bridge keeps the public API canonical.

## Remaining frontier

The complete fixed-order `a = 1` curvature envelope is now closed by
`UnifCurvatureJetOne.unifRmSecOne`. The next frontier is its class-uniform
`Ksup` consumer at `j = 1`.

## Project accounting

`ricci_flow_unif_existence` itself remains 0%. This closes the field-level
Palatini wall inside the dedicated machinery; the `a = 1` envelope is also
closed, while class-uniform `Ksup` at `j = 1` and E6 remain.
