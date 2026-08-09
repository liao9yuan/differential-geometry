# SlotFreeCurvatureOperatorDerivative

## Role

This module is the canonical first-jet companion to
`SlotFreeCurvatureOperatorField.lean`.  It packages the smooth raw
`(s, s + 2)` operator as `slotFreeOpCc` and states the general-rank
readout `slotFree_cov_eval` for its covariant derivative.

## Proof route

The source proof uses the Hom-bundle product rule to separate differentiation
of the operator from differentiation of its input.  It then peels the two
leading curvature slots with the tensor covariant Leibniz rule.  The resulting
four terms are identified with `nablaTensor0SCurv_def`; the existing
`nablaTensor0SCurv_apply_eval` theorem supplies the slot sum, and
`nablaRiemannOp_sec` converts each section-level differentiated-curvature value
to the pointwise operator.

The implementation deliberately remains at arbitrary covariant rank `s`; the
dimension-three restriction belongs to the later analytic bound, not to this
tensor-factory identity.

## Verification status

The first monolithic proof exceeded the local heartbeat budget.  Splitting it
at the mathematical interfaces `slotFree_riem_eval` and `slotFree_cov_sec`
reduced focused verification to a short check without raising the final budget
beyond the project-standard proof-heavy setting.

Focused verification now passes without warnings.  The public theorem's axiom
audit contains only `propext`, `Classical.choice`, and `Quot.sound`.

`slotFree_cov_eval`: 100% verified locally.
