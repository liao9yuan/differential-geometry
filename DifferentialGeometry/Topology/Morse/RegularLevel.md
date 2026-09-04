# Regular-level model transport

## Goal

Provide the smallest native bridge showing that critical-point status does not depend on replacing
a manifold's model vector space by a continuously linearly equivalent one.

## Route

The identity map between the original model and
`ModelWithCorners.transContinuousLinearEquiv` is Mathlib's
`ContinuousLinearEquiv.toTransContinuousLinearEquiv`. Applying the manifold chain rule once in each direction
expresses each version of the derivative as the other followed by the derivative of this identity
diffeomorphism. Hence either derivative being zero forces the other to be zero. If the function is
not differentiable in the original model, differentiability invariance under the same identity
diffeomorphism shows that it is not differentiable in the transported model either; Mathlib then
reduces both manifold derivatives to zero.

The public theorem therefore needs no differentiability or smoothness assumption. No manifold
regularity instance, global smoothness, or new predicate is introduced.

## Verification status

Focused verification and the explicit named module refresh are warning-free GREEN.

The first check exposed only a namespace mismatch: the identity diffeomorphism constructor belongs
to `ContinuousLinearEquiv`, not `Diffeomorph`. Correcting that qualification made the bidirectional
chain-rule proof elaborate without changing its statement or route.

The unconditional strengthening then required only a local nondifferentiable branch; its first check
left the already normalized reflexive proposition `0 = 0 ↔ 0 = 0`, closed by the terminal simplifier.
