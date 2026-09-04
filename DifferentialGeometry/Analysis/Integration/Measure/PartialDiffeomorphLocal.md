# PartialDiffeomorphLocal

## Role

This module contains the generic measure-theoretic localization needed after
pulling a measure back through the inverse of a partial diffeomorphism.

## Route

`lint_map_fin_loc` first uses the inverse map formula on the restricted target,
then exchanges a finite nonnegative sum with the lower integral.  Each summand
is localized to the image of a set containing its support; the partial inverse
identities prove that the summand vanishes on the rest of the target.

The theorem does not depend on Riemannian volume, a preferred atlas, Ricci flow,
global measure finiteness, or disjointness of the local pieces.

`map_inv_tail_le` is the complementary tail-localization fact.  If a source
set lies in the partial map domain and its image captures a target set, then
the inverse-map transport assigns no more mass to the source complement than
the original measure assigns to the target complement.  The proof expands the
map on the measurable source complement and uses only the partial inverse
identity and monotonicity of measure.

## Verification

Focused verification and the final exact named refresh passed.  The first pass
exposed an unused inherited finite-dimensionality assumption, and the exact
refresh additionally exposed an unnecessary decidable-equality argument; both
were removed from the public assumptions before the final refresh.

## Progress

- Generic finite partial-map localization theorem: 100% stated, proved, and
  focused-check verified.
- Generic inverse-map tail transport: 100% stated, proved, and warning-free
  focused-check and exact-refresh verified.  It uses arbitrary smoothness
  grade and does not require finite-dimensionality, manifold regularity, or
  finite mass.
