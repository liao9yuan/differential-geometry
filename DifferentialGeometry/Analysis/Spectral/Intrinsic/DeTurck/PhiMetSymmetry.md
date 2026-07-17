# Ricci--DeTurck top-coefficient symmetry

## 2026-07-15 arbitrary realized metric

`phiMet_symm_zero` proves that, at an arbitrary realized metric, the
Ricci--DeTurck top coefficient agrees with its pure-cometric part on tensors
which are symmetric in the two derivative slots.

`gradSwapCurvCoeff` fixes the background-curvature coefficient supplied by the
covariant-derivative commutator.  `phiMetCurvCoeff` composes it with the
non-pure top coefficient, and `phiMet_curv_fold` proves the exact identity
turning that coefficient applied to `nabla^2 S` into a zeroth-order coefficient
applied to `S`.  The fold holds for every covariant two-tensor `S`; no symmetry
hypothesis on `S` is used.

Focused verification passed.  A first local section-extensionality proof of
application associativity exposed a tensor-bundle instance inference problem.
The correct repair was to reuse the already public
`appCcRS_zero_eq_appCc`/`appCc_assoc` API rather than duplicate the old private
DeTurck helper.

The fold theorem is complete (100%).  The mixed `H^3 -> H^1` remainder theorem
is still unstated and therefore 0%; its dedicated low-regularity machinery is
approximately 65% complete.  The next missing producer is a uniform low-order
bound for the explicit path coefficients, followed by the `H^2`-coefficient
times `H^2`-tensor product estimate.

## 2026-07-16 public dependency migration

The module no longer imports the oversized remainder implementation. The Lie
principal readout now comes from `DeTurckLieCoeffAppCcValue`, and the gradient
slot commutator comes from the new public `gradSlot_sub_eq_curv` producer.

The source migration is complete. Its downstream focused verification is
temporarily blocked because the new curvature module cannot receive a named
`.olean` while the unrelated in-flight `Geometry/Operator/Operators.lean`
changes fail. The mixed `H3 -> H1` endpoint is still unstated (0%); dedicated
machinery is approximately 78% complete.
