# Homogeneous differentiated identity

## Role

`homSol_diff_id` is the first differentiated-equation producer after local
`W^{2,2}` membership.  It turns a local homogeneous De Giorgi solution whose
coefficient is a positive constant multiple of a global smooth coefficient
into the weak equation for a canonical first weak partial.

The public left side uses
`chosenWeakPartial' 2 j (chosenWeakPartial' 2 l u Omega) Omega`, i.e. the
`j`-th weak derivative of the `l`-th canonical weak partial.  This is the
index order required by a later elliptic bootstrap consumer.

## Proof route

1. Test `hsol.to_homogeneous` with the smooth compactly supported partial
   derivative `partial_l psi` and expand the De Giorgi bilinear form.
2. Replace `A.a` by `rho * B.a` on the open domain and cancel `rho > 0`.
3. For each coefficient pair, apply `integral_smul_weak_partial_eq` in the
   `l` direction.  This gives the coefficient-derivative term and initially
   the canonical derivative in the order `D_l(D_j u)`.
4. Use two weak integrations by parts and symmetry of the classical mixed
   partials of the smooth test to exchange `D_l(D_j u)` with `D_j(D_l u)`
   under the required compactly supported pairing.
5. Commute the finite sums with the integrals and assemble the signed
   identity.

No source term, differentiated-equation predicate, compactness assumption on
the domain, or classical derivative of `u` is introduced.

## Verification

Focused verification is warning-free GREEN.  The checked proof contains no
`sorry`, `admit`, or new axiom.  The explicit named module refresh is also
GREEN, so the exported declaration is current for downstream imports.

The first focused pass exposed only local expression-shape issues: a split
field-notation chain, finite-sum coefficient scaling, explicit restricted-
measure presentation for `integral_const_mul`, and a redundant terminal
tactic.  The second pass proved the theorem and left one no-op `change`
warning; removing it gave the final warning-free pass.  None of these changed
the mathematical route or the theorem assumptions.

## Project position

- The final splitting endpoint is still unstated: 0%.
- Dedicated splitting/P1c machinery is approximately 45--50% complete.
- Whole P1c is approximately 65--70% complete.
- Whole Poincare infrastructure is approximately 20--30% complete.

## Scalar-source refactor

The weak two-integration-by-parts argument is now factored through the private
`diff_id_of_base` core.  Its input is only the actual value of the scaled
coefficient pairing against `partial_l psi`; it does not assume the desired
differentiated identity.  The original `homSol_diff_id` obtains the zero value
from the genuine homogeneous weak equation and keeps its public statement.

`srcSol_diff_id` is the corresponding genuine scalar-source producer.  It
consumes the actual `H01` weak equation and `MemWkp 1 2 f Omega`, uses the
canonical weak partial of `f`, and produces the positive
`rho⁻¹ * D_l f` term.  `diff_bilin_scaled` records the separate
witness-independent scaling projection used by downstream weak-equation
assembly.

The first focused pass on this refactor failed because both private helpers
were wrapped in an invalid `omit [NeZero d]`: their declarations still
reference that section instance.  The later unresolved goals and invalid named
arguments were cascading from those helpers not being generated.  The two
invalid `omit` wrappers were removed.  The corrected refactor is now
warning-free focused GREEN, and its explicit named module refresh is GREEN for
the downstream scalar-source module.  No large proof body was copied, and no
new predicate, assumption interface, `sorry`, or axiom was introduced.
