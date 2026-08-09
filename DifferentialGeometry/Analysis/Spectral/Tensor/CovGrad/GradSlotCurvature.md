# GradSlotCurvature

## Role

This module packages the Ricci commutator for the first two slots of a second
covariant gradient as a fixed smooth curvature coefficient.

## Verified state

`gradSlot_sub_eq_curv` is public, sorry-free, and passes focused verification.
It extracts the generic curvature producer previously available only inside
the oversized DeTurck remainder file.

The named module refresh is blocked before reaching this file by the unrelated
shared-tree failure in `Geometry/Operator/Operators.lean`. The local theorem
has no remaining proof goal; downstream import verification must be rerun once
that upstream file is green.

This producer is complete (100%). The consuming import migration is implemented
but not yet fully reverified.

## 2026-08-06 canonical coefficient carrier

The existential witness has been promoted to the explicit public coefficient
`gradSlotCurvCoeff`.  Its fibre is definitionally
`TensorRSSpace.ofCLM (slotFreeCurvOpFib g₀ 2 x)`; `gradSlotCurv_apply` and
`gradSlotCurv_eval` expose the fibre and tuple readouts.  The original long
commutator proof now proves the direct theorem `gradSlotCurv_spec`, while
`gradSlot_sub_eq_curv` remains as a compatibility existence wrapper with the
same public statement.

Focused verification passed with four Lean threads under the 6 GB cap.  The
five new or preserved public declarations use only the standard project axioms
`propext`, `Classical.choice`, and `Quot.sound`; the upstream module export was
refreshed successfully.

At that stage the first covariant-derivative readout was the exact missing API.
It required a naturality theorem identifying the covariant derivative of the
two-free-slot operator field with differentiated slotwise curvature.  That
historical gap is resolved by the geometry-layer and spectral adapters recorded
below.

## 2026-08-06 first derivative factory

`gradSlot_cov_eval` now exposes the first covariant derivative of the canonical
coefficient directly in the `covGrad` vocabulary consumed by spectral jet
bounds.  On the derivative slot `d`, curvature slots `u,w`, and tensor-input
tuple `m`, it is the sum obtained by inserting `nablaRiemannOp g₀ d u w`
into each of the two covariant input slots.  Its proof is a thin adapter around
the geometry-layer `slotFree_cov_eval`; it does not unfold tensor
representations or introduce a second curvature-coefficient hierarchy.

The new import is downward and non-circular: the geometry derivative module
depends only on the slot-free curvature field and pointwise curvature-derivative
API, while this spectral module supplies the compactly-supported coefficient
and `covGrad` wrapper.  Focused verification passes without warnings.  The
axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.
The derivative bridge is therefore 100% verified locally; the downstream
fixed-curvature jet bound remains a separate producer.
