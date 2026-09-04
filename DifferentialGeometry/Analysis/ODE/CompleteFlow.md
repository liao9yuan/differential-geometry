# Complete smooth flows

## Result

`curveAt_contMDiff` is the canonical joint-smoothness producer for the chosen
global flow of an arbitrary smooth vector field.  Its only global input is the
supplied existence statement giving a global integral curve through every
initial point.  It does not assume compact support, connectedness, metric
completeness, a Riemannian metric, or any parallel/unit-field property.

The theorem uses the time-first map
`(t, x) ↦ curveAt v hcomplete x t`, matching the product-model convention of
the time-dependent-flow API.

## Native route

For each fixed time, the proof applies the manifold
`flow_slice_smooth` theorem from `SmoothDependence/CompactTrajectory` to the
global `curveAt` family on a bounded interval containing both zero and the
target time.  Global integral-curve existence supplies the initial condition,
continuity, and derivative hypotheses.

At an arbitrary time-space point, the proof then uses
`local_flow_jointSmooth_and_integralCurve` around the state reached at that
time.  Local uniqueness identifies this local smooth flow with `curveAt`, and
`curveAt_add` converts that identification into a joint neighborhood formula.
The jointly smooth local formula and eventual equality finish the proof.

The proof reuses:

- `curveAt_zero` and `curveAt_integralCurve`;
- `curveAt_add`;
- `flow_slice_smooth`;
- `local_flow_jointSmooth_and_integralCurve`;
- `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless`.

No new structure, predicate, wrapper assumption, axiom, or reference-tree
dependency is introduced.  Completeness of the finite-dimensional model space
is installed locally in the proof rather than exposed as a theorem hypothesis.

## Source state and risks

The first focused verification failed because three neighborhood-filter
occurrences used the wrong Unicode glyph; the source now uses the native `𝓝`
notation.  Two subsequent passes found stuck product-chart metavariables at the
first and second projections; the final proof supplies all three manifold
models explicitly in both compositions, matching the repository's established
call shape.

Focused verification and the explicit named module refresh are now warning-free
green.  The proof contains no `sorry` or `admit`; the exported declaration is
fresh for the Busemann-flow consumer.

The joint-smoothness theorem and its artifact are verification-complete; the
Cheeger--Gromoll splitting endpoint remains a separate downstream theorem.

## Fixed-time diffeomorphisms

`curveAtDiffeo` is the canonical fixed-time producer attached to the same
arbitrary smooth vector field and supplied global integral-curve existence.  At
time `t` its forward map is `curveAt v hcomplete · t`, and its inverse is the
same flow at time `-t`.  It adds no assumptions beyond those of
`curveAt_contMDiff` and introduces no structure or predicate.

The implementation follows the existing `GradientLikeFlow.toDiffeomorph`
shape but constructs `Diffeomorph` directly, since no packaged flow structure
is needed here.  Smoothness of each map is the fixed-time slice obtained by
composing `curveAt_contMDiff` with `x ↦ (t, x)`.  The two inverse laws are the
`t + (-t)` and `(-t) + t` instances of `curveAt_add`, followed by
`curveAt_zero`.

Focused verification and the explicit named module refresh for
`curveAtDiffeo` are warning-free green.  The common P1 audit can now consume the
new export.
