# LieCorr0Core

## Role

This module owns the reusable zeroth-order DeTurck correction field extracted
from the legacy monolithic implementation.

## Verified state

`lieCorr0Field` is public, sorry-free, and has passed focused verification and
its named module build. The extraction keeps the coefficient construction below
the 3000-line source limit and introduces no Sobolev assumptions.

This producer is complete (100%). It is infrastructure for, not a proof of,
the mixed `H3 -> H1` endpoint, which remains theorem-level 0%.
