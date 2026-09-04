# Local cross-model curvature pullback

## Status

`rm04_localPull` no longer requires sigma compactness of its target manifold.
The source still requires the instances needed to construct `localPullMetric`.
Focused verification passes without warnings.

## Route

The local partial diffeomorphism supplies a diffeomorphism from the source
open subtype `U` to the target open subtype `V`.  The proof transports the
locally constructed sigma-compactness of `U` to `V` through that homeomorphism,
then applies the existing restriction and pullback-curvature identities.
