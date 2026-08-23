# `JointRegularity.lean`

## Result

The existing joint scalar-curvature theorem remains canonical.  The added
`chartScalarDeriv` result exposes joint `C^infinity` regularity of the spatial
scalar differential in a fixed chart on regular spacetime chart domains.
`chartScalarHess` differentiates each checked first coordinate component once
more in the spatial variable and adds the smooth Christoffel correction.
`scalarHess_cont` reconstructs these components as a continuous rank-two
covariant tensor family of scalar Hessians on regular time.  All three results
stay in fixed-chart scalar coordinates rather than creating a moving
gradient-bundle API.

An earlier route first converted `scalar_joint` after chart composition to a
model-space `ContDiffOn` theorem and then differentiated twice.  That conversion
hit a deterministic `whnf` performance wall even after being isolated.  The
checked route instead reuses `chartScalarDeriv`, identifies it with the native
`partialDeriv` component, and differentiates only once.

## Verification and use

Focused verification and the targeted export refresh passed without warnings.
The scalar Hessian family supplies a coefficient-continuity producer for the
fixed-chart Jacobi ODE.  This is generic regularity infrastructure; it does not
itself prove L-geodesic uniqueness or reduced-volume monotonicity.
