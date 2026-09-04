# WeakLaplacian

## Scope

This module provides the intrinsic distributional meaning of an upper bound
for the scalar Riemannian Laplacian on an open set. The predicate records local
integrability of both functions and tests only against nonnegative, compactly
supported smooth functions whose topological support lies in the open set. It
does not require a global Sobolev hypothesis and does not define a
Busemann-specific weak-solution layer.

## Native route

Restriction to a smaller open set uses local-integrability restriction and the
same test inequality. For a smooth function, Green's second identity with the
compactly supported test function identifies the distributional pairing with
the integral of the pointwise Laplacian against the test. Pointwise order and
nonnegativity of the test then give the distributional inequality. The source
term is required only to be locally integrable.

Conversely, when the source term is continuous on the open set,
`lap_le_of_distrib` recovers the pointwise inequality from the distributional
one. The proof argues by contradiction at a point where `Δu - b` is positive,
shrinks to an open neighborhood where that difference stays positive, and
chooses a smooth nonnegative compactly supported bump equal to one at the
point. Green's second identity turns the distributional test inequality into a
nonpositive integral of `(Δu - b) * χ`, while continuity, nonnegativity, and
positivity at the chosen point make the same integral strictly positive. The
continuity assumption on `b` is essential for this pointwise conclusion; local
integrability alone determines only an almost-everywhere representative.

Distributional upper bounds are also closed under addition. The left and right
local-integrability fields add directly. For the compact-test inequality, the
Laplacian of the test has topological support inside the support of the test;
this supplies integrability of each summand, after which additivity of the
integral and the two input inequalities give the result. No zero-bound helper
was needed by this proof.

The support helpers used by the addition rule and smooth bridge are private.
They prove that the Riemannian Laplacian has support inside that of its input,
and hence that the Laplacian of a compactly supported smooth function remains
compactly supported, by locality of the native Laplacian and the
constant-function formula.

## Verification and project status

The previously present declarations passed their focused source check and
explicitly named module refresh. A separate axiom audit found only the standard
`propext`, `Classical.choice`, and `Quot.sound` dependencies for the predicate,
its restriction theorem, and the smooth producer. The first focused check of
the new pointwise converse failed only at two local expression shapes: extracting
the center value from an eventual equality on a singleton and commuting the
two scalar factors in an integrability congruence. Both were repaired without
changing the statement or mathematical route. The second focused check and
the explicit named module refresh then passed without warnings.
The file contains no `sorry`, new axioms, classes, instances, or notation.

The distributional predicate, open-set restriction, addition rule, smooth
pointwise producer, and pointwise converse in this module are complete and
focused-verified (100%). This is dedicated analytic
infrastructure: viscosity-to-distributional conversion is not stated here
(0%), and this module alone does not prove the P1c
Laplacian-comparison, Busemann, or splitting endpoint theorems (0% of each
endpoint theorem). The addition rule is one routine weak-algebra brick for the
splitting chain; the supplied-line splitting theorem itself remains unstated
and therefore 0% complete.
