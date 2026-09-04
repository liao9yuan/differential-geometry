# Tail map provenance

## Route

`tailSystem_apply` identifies every direct-system transition of
`tailBallSystem` with the corresponding ambient `chainComp`.  The proof unfolds
only the one-step `SmoothSeqSystem.ofSucc` transition, then inducts over the
number of steps.  Subtype extensionality removes the open-ball membership
proofs; the only remaining transport is the target-index cast from
`(j₀ + n) + k` to `j₀ + (n + k)`.

`tailInvIncl_apply` then composes this result with `invIncl_incl_le`: pulling a
point represented at stage `n` back through the stage `n + k` limit chart has
the same ambient value as the length-`k` `chainComp`, modulo the same explicit
associativity cast.

`tailBall_capture` packages the genuine generic reverse-capture argument.  For
a prescribed radius it chooses one `limitCore`, uses `ball_subset_image` on the
finite-stage `D₀` map restricted to `coreRadius`, and identifies the lifted
direct-limit member map with that finite chain through `tailInvIncl_apply`.
Only ambient properness is added, exactly to compact the chosen closed ball.

## Verification

`tailSystem_apply` is warning-free focused GREEN.  Its proof uses the existing
one-step `SmoothSeqSystem.ofSucc_F_succ` and `chainComp_apply_succ` equations;
the final dependent cast is discharged by equality elimination on the
associativity index equality.  No reference-tree code was used.

`tailInvIncl_apply` is also warning-free focused GREEN.  It reuses
`invIncl_incl_le` and `tailSystem_apply`; no additional direct-limit or
compactness assumptions were introduced.

The first focused check of `tailBall_capture` exposed only a local dependent
transport mismatch for membership in the ambient ball.  Equality elimination
for the stage-index equality repaired it, and the focused recheck is
warning-free GREEN.  Its exact named module refresh is also GREEN.

## Project progress

The `tailSystem_apply`, `tailInvIncl_apply`, and generic `tailBall_capture`
endpoints are each 100%, and their dedicated tail-map provenance machinery is
100%.  The checked canonical consumer `canon_ball_capture` is also 100%.  The
broader P2b no-mass-loss endpoint remains 0% because its moving-center
quadratic coercivity input belongs to P3.
