# Standard-solution definitions

## Scope

`Defs.lean` separates candidate initial data from proved geometric properties.
`StdInit` contains only a tip and a smooth metric. `IsStdCore` records the
intrinsic properties that can already be stated with native APIs: completeness,
nonnegative sectional curvature, and curvature `1/4` near the tip.

The exact round-cylinder end is not represented yet. The smallest missing lower
layer is a canonical smooth product/cylindrical metric API, or an equivalent
intrinsic cylindrical-end predicate with a proved realization on a punctured
sphere. Rotational invariance is exposed independently through `IsMetricInv`.

## Verification

Focused verification passed.

## Progress

P5 main theorem remains 0%. P5-A data/API infrastructure is approximately 50%:
the candidate/core split is present, while the exact cylindrical-end predicate
and concrete standard initial metric are still missing.
