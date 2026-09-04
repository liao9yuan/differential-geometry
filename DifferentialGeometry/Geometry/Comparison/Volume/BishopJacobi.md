# BishopJacobi

## Scalar density comparison

`curveDensity_le_on` packages the scalar endpoint of the local Bishop--Jacobi
argument.  Its inputs are exactly the hypotheses used by `curveRatio_anti`
together with unit normalization of the density ratio at the pole.  Antitonicity
then compares every positive time with the right-hand germ at zero, and positivity
of the model density converts the ratio bound into the density bound.

The theorem is deliberately independent of completeness, exponential-map
domains, and raw/intrinsic distance agreement.  Those belong to downstream
specializations that construct the Jacobi family and prove its pole limit.

Focused verification passed without warnings.  This scalar producer is complete
(100%).  It is one reusable analytic step in the local Bishop volume machinery;
the downstream raw exponential-map specialization remains unstated (0%), so this
does not itself complete that endpoint or the wider Bishop comparison program.
