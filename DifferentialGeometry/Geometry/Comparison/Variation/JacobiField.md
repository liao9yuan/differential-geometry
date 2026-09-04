# JacobiField

## `wronskian_zero_Ioo`

The new endpoint-weakening theorem keeps the curve and both fields, including
their first covariant derivatives, regular on `Icc 0 b`, but requires the
Jacobi equation only on `Ioo 0 b`.  At an interior point the existing
`wronskian_deriv_at` gives zero derivative.  At the left endpoint, the two
`inner_deriv_at` product rules and `J 0 = K 0 = 0` make the right derivative of
the Wronskian vanish without any endpoint Jacobi equation.  Continuity on the
closed interval comes from the same product rules, so
`constant_of_has_deriv_right_zero` makes the Wronskian constant and its value at
zero is zero.

The older `wronskian_zero_on` signature is preserved as a compatibility
corollary by restricting its closed-interval Jacobi hypotheses to the
interior.

Focused verification passed without warnings.  The public theorem and its
compatibility corollary are therefore implemented and verified (100%).  This is
one small endpoint-regularity producer for the raw radial Jacobi/index-form
lane; the local compact-closure Bishop endpoint itself remains unstated (0%),
while its dedicated raw exponential/Jacobi infrastructure is still only a
partial portion of the P1a comparison phase.

## `jacobiAt_congr`

The pointwise Jacobi equation is local in both its base curve and its vector
field.  The bridge takes equality of the curve germ and equality of the
underlying model-space values of the field germ.  The latter two germs first
give equality of the first covariant derivatives on a smaller neighborhood;
applying the same local covariant-derivative calculation once more identifies
the second derivatives at the point.  Curve-germ equality also identifies the
velocity, while point equality transports the curvature operator.  Thus no
extra germ for the first covariant derivative and no smoothness, completeness,
or curvature assumption is exposed by the public theorem.

The cross-curve chart and covariant-derivative calculations are private to this
low-level module.  This avoids importing the higher `JacobiVariation` module,
which already depends on `JacobiField`, and does not create a second public
congruence hierarchy.

The stale file claim was verified against its dead owner PID and released
exactly.  The first focused rerun failed before the intended proof because ten
neighborhood filters had been mistyped as the unknown identifier `𝓑`; they
have been restored to the project-native `𝓝`.  The next focused pass reduced
the proof to an `EventuallyEq` field-notation mismatch and a reflexive
`mfderiv` goal; the former now has an explicit function equality view and the
latter an explicit reflexivity close.  Focused verification after these local
repairs passed without warnings.  A separate earlier coordinated exact named
module refresh also passed; the resumed verification used only the focused
file check and did not refresh any artifact.  `jacobiAt_congr` is implemented
and verified (100%).

## `jacobi_perp_of_init`

The new interval producer propagates the two scalar orthogonality equations
for a Jacobi field along a geodesic.  It assumes pointwise `C²` regularity of
the curve and chart regularity of the field and its first covariant derivative
on the closed interval, while the Jacobi equation is required only in the open
interval.  The initial data are exactly `J 0 = 0` and orthogonality of the
initial covariant derivative to the initial velocity.

The proof first shows that the velocity pairing with the first covariant
derivative has zero derivative in the open interval.  Continuity extends its
constant value to the left endpoint, where the supplied initial condition
makes it zero.  The same argument then makes the velocity pairing with the
field constant and uses `J 0 = 0`.  The only curvature algebra needed is the
standard skew-symmetry consequence that the curvature operator vanishes when
its first two inputs agree.

Focused verification passed without warnings.  The producer is implemented
and verified (100%).  The downstream raw radial-density theorem remains a
separate consumer and is not counted as completed here (0% from this file);
its dedicated Jacobi orthogonality infrastructure is now complete.
