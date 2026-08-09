# NonautonomousL2Lift

## Role

`nonautL2_lift` is the generic same-horizon adjacent-scale bootstrap for the
zero-initial non-autonomous maximal-regularity solver.

It consumes:

- high-scale `A2 : H^(a+2) -> H^a` and `A1 : H^(a+1) -> H^a` families;
- low-scale `A2 : H^((a-1)+2) -> H^(a-1)` and
  `A1 : H^((a-1)+1) -> H^(a-1)` families;
- the native measurability, uniform top-arm bounds, `MemLp` first-arm data,
  and contraction smallness at both scales;
- almost-everywhere commuting squares for both operator families;
- compatible affine forcing; and
- one existing low forcing fixed point.

It produces a high strong Duhamel solution on the original horizon, proves
that its included forcing is the supplied low fixed point, and proves that
its full Duhamel field includes to the low full Duhamel field.

## Proof route

The proof uses the project-native spectral and fixed-point APIs.
`duhamel_incl` supplies the canonical full-to-intermediate realization.
Mode-coordinate injectivity shifts the zero-initial Duhamel fields across the
adjacent base exponents.  Almost-everywhere evaluation of `timeOp` and
`timeOpL2` transfers the two commuting operator squares to the forcing maps.
Finally, the existing `nonautL2_contract` estimate and Banach fixed-point
uniqueness identify the included high force with the prescribed low force.

No hypothesis asserts solution equality, field equality, or forcing equality;
those are conclusions.

## Audited alternatives

Three routes were checked before fixing the implementation:

1. Directly compare all Duhamel fields mode by mode.  This works, but by itself
   bypasses the canonical `duhamel_incl` interface.
2. Compare only the `timeH1` carriers.  The current API has no adjacent-scale
   `timeH1` inclusion theorem strong enough to transfer the nonlinear forcing
   map.
3. Transfer the concrete forcing maps arm by arm, then use low-scale
   contraction uniqueness.  This is the implemented route and keeps the one
   genuine analytic input in the existing solver.

## Verification

Focused verification passes without local warnings.  The Lean source contains
no deferred proof or axiom facade.  A direct dependency audit of
`nonautL2_lift` reports only `propext`, `Classical.choice`, and `Quot.sound`.
The unchanged `NonautonomousL2` artifact was refreshed under a separate
exact-target handback solely to make the focused import available; this module
itself was not exact-built.

## Project position

- `nonautL2_lift`: theorem 100%; its dedicated generic analytic machinery
  100%.
- The concrete same-horizon order-two Ricci--DeTurck bootstrap theorem: 0%
  until the geometric high/low families are instantiated in a theorem; its
  dedicated machinery is approximately 98--99%.
- `ricci_flow_unif_existence`: endpoint theorem 0%; its dedicated
  low-regularity machinery remains approximately 98%.
- The HCG compactness project is a separate lane and is not advanced by this
  module.
