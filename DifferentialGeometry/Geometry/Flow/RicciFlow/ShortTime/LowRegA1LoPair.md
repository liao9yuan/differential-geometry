# LowRegA1LoPair

## Status (2026-07-30)

GREEN and placeholder-free.  The module is the ShortTime adapter from
`radialA1Lo_pair` to `LowA1CorePair`.

It now also exports `lowA1Lo_ball`: on every nonnegative ambient `H3` radius,
the completed `H2 -> H1` coefficient has a uniform operator bound.  The proof
uses the ball-local smooth-core pair estimate on a radius enlarged by one,
then passes through the dense completion by a closed-set argument.  No global
affine growth estimate is asserted.

## Route and rejected shortcut

The global `hHiPair` route remains mathematically invalid and is not used.
The valid input is the fourth-jet-free low pair estimate, whose constant may
depend on the chosen `H3` ball.  Comparing with the zero core value gives the
finite ball bound needed by the time-dependent M-witness.

Focused and exact verification passed.  No `sorry`, `admit`, `axiom`, `whnf`,
or trace declaration remains.

