# RayContinue

## Goal

Prove that a regularized L-ray exists across a compact regular backward-time
slab whenever its existing prefixes have bounded speed and lie in one explicit
compact spatial set.  Compact manifolds are then a specialization.

## Route

The generic theorem receives uniform speed and compact-range bounds. At a
putative boundary point of the maximal domain it takes actual late phase seeds,
passes only the base points to a convergent subsequence, and places the eventual
chart positions and velocities in one compact phase cage.  Compact phase ODE
existence supplies a common restart interval, and the existing family restart
API glues a late seed across the boundary.  No limiting velocity or tangent-disk
compactness is used.

## Status

Both `lRegDomain_of_cpt` and the preserved compact specialization pass focused
verification without warnings. The generic theorem discards a finite prefix of
the boundary sequence before applying compactness, so its range hypothesis is
needed only on the requested square-root-time interval. The proof uses the
native compact phase-flow and family-restart APIs; no additional continuation
assumption remains.

## Progress

- `lRegDomain_of_slab`: verified and sorry-free (100%).
- `lRegDomain_of_cpt`: verified and sorry-free (100%).
- Dedicated continuation machinery: verified (100%).
- Complete noncompact P2 continuation input: 100%; its `lRegRange_unif`
  consumer remains to be proved.
- `smooth_nlc`: 0%; dedicated L8--L9 machinery is about 90--92%, generic
  continuation infrastructure is 100%, and whole P0--P9 is about 15--25%.
