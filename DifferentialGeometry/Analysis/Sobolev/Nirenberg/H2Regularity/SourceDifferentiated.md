# Differentiated scalar-source weak equation

## Result

`srcDiff_weak_eq` states the actual `H01` weak equation for the canonical first
weak partial `chosenWeakPartial' 2 l u Omega`.  Its scalar source is exactly

`chosenWeakPartial' 2 l f Omega + rho * homDiffSource B u Omega l`.

Thus the derivative of the original scalar source and the coefficient-
derivative source both occur with a positive sign.

## Native route

1. `srcSol_diff_id` supplies the differentiated identity on smooth compactly
   supported tests without duplicating the long weak integration-by-parts
   proof.
2. The coordinate field whose only nonzero component is `f` in direction `l`
   has weak divergence `chosenWeakPartial' 2 l f Omega`.
3. This field is added to `rho * homDiffField B u Omega l`; a private linearity
   lemma assembles the sum of the two verified weak divergences.
4. `diff_bilin_scaled` handles the arbitrary-witness/canonical-second-partial
   projection and coefficient scaling.
5. The existing `weak_eq_of_smooth` and `weakRHS_eq_integral` extend the smooth
   identity to every `H01` test and identify the resulting divergence
   functional with the displayed scalar pairing.

No Poincare estimate is needed: the differentiated scalar source is treated as
a divergence of an `L2` coordinate field.  No new solution predicate, final-
identity hypothesis, coefficient-bound assumption, or reference-tree import is
introduced.

## Verification

Focused verification is warning-free GREEN, and the explicit named module
refresh is GREEN for the real `SourceThird` downstream import.  The checked
file contains no `sorry`, `admit`, or axiom declaration.

The initial passes exposed only local elaboration shapes: a section instance
was incorrectly omitted from the divergence-linearity helper, pointwise `Pi`
multiplication needed explicit normalization, and several restricted
integrals needed parentheses to keep their scopes unambiguous.  The weak RHS
linearity proof also needed the existing divergence RHS equality in the
correct direction.  These repairs did not change the statement, hypotheses,
source sign, or mathematical route.

## Project position

The final splitting theorem remains unstated and therefore 0% complete.  This
producer is one local analytic bridge in the all-order Busemann regularity
bootstrap; it does not by itself complete the splitting endpoint.
