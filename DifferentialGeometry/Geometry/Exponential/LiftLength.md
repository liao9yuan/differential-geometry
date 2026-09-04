# LiftLength

## Map-generic lift fence

`lift_norm_le` extracts the integration and right-slope argument previously
embedded in the intrinsic exponential-map consumer.  It applies to an arbitrary
map `F : V → N` and assumes only pointwise first-order smoothness along the
lifted path, the differential norm identity at `0`, and the radial Cauchy
inequality supplied by the relevant geometry.  The radial inequality is now
required only at points of the lifted path, which is exactly where the proof
uses it and permits raw exponential specializations with merely path-local
radial-domain support.

The source inner-product space and the target manifold model are deliberately
independent.  No exponential-domain, curvature, compactness, local-diffeomorphism,
or ambient-completeness assumption belongs in this layer.  Raw and intrinsic
exponential maps should instantiate the two geometric hypotheses in their own
modules.

The target tangent `NormedAddCommGroup` and `NormedSpace` families are explicit
instance parameters of `lift_norm_le`.  This is not an extra geometric
assumption: `pathELength`, `hEnorm`, and the manifold derivative already use
these structures.  Binding them explicitly prevents the declaration from
baking in the canonical `Tensor0SBundle` norm and lets a caller consistently
select the `RiemannianBundle` norm across the norm hypothesis and path length.

## Verification

Focused verification of the instance-polymorphic signature passed without
warnings.  The earlier path-local hypothesis weakening also passed focused
verification.  The initial draft exposed two
routine abstraction cleanups: the target did not need ambient Riemannian-bundle
or pseudo-metric instances as theorem assumptions, and the zero-derivative case
needed the composed path value rewritten explicitly before applying the supplied
zero norm identity.  Both were removed locally; no broader or write-producing
build was run.
