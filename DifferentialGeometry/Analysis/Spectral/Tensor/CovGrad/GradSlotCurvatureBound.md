# GradSlotCurvatureBound

## Purpose

This file is the invariant-norm bridge for the explicit coefficient
`gradSlotCurvCoeff`.  It turns supplied tangent-operator caps for `Rm` and
`nabla Rm` into pointwise mixed-tensor fibre caps at coefficient jet orders
zero and one.

## Route

The proof uses the existing orthonormal-frame Parseval expansion for
`riemannianFiberNormSq`.  The public readouts `gradSlotCurv_eval` and
`gradSlot_cov_eval` reduce each mixed component to two slot-insertion terms.
Each term is bounded by the supplied tangent cap and the unit coframe factors;
summing the finite component family yields the general-dimensional factors
`d^6` and `d^7`; the class wrapper later specializes `d = 3`.

No compactness-selected coefficient, stronger metric jet, or replacement
producer is introduced.

## Verification

Focused verification passed without warnings after making the evaluation
terms explicit and normalizing the finite cardinalities.  Axiom audits for
both public bounds contain only `propext`, `Classical.choice`, and
`Quot.sound`.
