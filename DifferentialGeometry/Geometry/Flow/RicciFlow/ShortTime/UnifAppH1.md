# Class-first application estimates into H1

`appCc_h1_unif` specializes the generic mixed class producer to the
rank-`(2,2)` order-zero lower-path arm.  The rank-two curvature-action package
converts spectral `H²` to its three-term jet radius, while `h1_jet_sq` and
`cc_h1_jet_sq` identify the intrinsic and spectral output norms exactly.
Focused verification passed with four Lean threads, and its temporary axiom
census contained only the standard `propext`, `Classical.choice`, and
`Quot.sound` dependencies.

`appCc_h2cov_unif` is the three-dimensional, class-first specialization used
by the low-regularity lower path.  It fixes one coefficient before the metric
varies and controls the actual rank-`(3,2)` coefficient acting on `∇U`, with
`U` a covariant rank-two field.

The proof combines the uniform rank-`(3,2)` mixed Morrey estimate,
`appCc_grad_unif`, the rank-two finite curvature-action `H²` jet comparison,
and the exact rank-two spectral `H¹` jet identity.  Consequently its public
hypotheses contain only the coefficient's three-term squared jet bound; no
redundant pointwise coefficient hypothesis is exposed.

Focused verification passed with four Lean threads and no warnings.  A
temporary axiom census for `appCc_h2cov_unif` reported only `propext`,
`Classical.choice`, and `Quot.sound`; the temporary print was removed.

`appCc_h23_unif` is the matching three-dimensional top-path cell.  It fixes
one class coefficient for a rank-`(4,2)` field acting on `∇²U` from spectral
`H³` to spectral `H¹`.  The proof uses the order-three curvature-action jet
comparison and `icg_comp_norm` to identify the three-jet radius of `∇U` with
orders one through three of `U`; no new tensor or Sobolev API was needed.
Focused verification again passed with four Lean threads and no warnings, and
its axiom census was the same standard trio.

These theorems close the differentiated application coefficients used by the
`(s,c)=(1,2)` lower-path cell and the `(s,c)=(2,2)` top-path cell.  They do not
yet cap every metricwise numerical witness returned by the RHS producer, so
the full class-first tame packet remains a separate assembly frontier.
