# Convex shaving

## Scope

This module contains the generic metric and geodesic consumers used by one
step of convex shaving.  The boundary set is an explicit parameter `B`; the
module does not claim to construct the relative boundary of a convex subset.

## Implemented API

`innerParallel C B r` is the part of `C` at distance at least `r` from `B`.
Its namespace supplies membership, antitonicity in `r`, nonemptiness from a
witness, closedness, compactness inside a compact carrier, and total convexity
when distance to `B` is geodesically concave on `C`.

`deepestSet C B` is the set of points of `C` maximizing distance to `B`.  Its
namespace supplies containment in `C`, compact maximum attainment,
identification with an inner parallel set at the maximum value, compactness,
total convexity from relative geodesic concavity, and disjointness from `B`
when some point of `C` has positive boundary distance.

The total-convexity proof for `deepestSet` uses both endpoint maximum
properties and concavity directly, so it does not require compactness or a
chosen maximum witness.

For a relatively open stratum `N` in a compact carrier `C`, with
nonempty stratum and frontier, `exists_frontier_dist` produces a carrier point
at strictly positive distance from `frontierIn C N`.  This supplies the exact
nondegeneracy input used by `deepestSet.disjoint`.

## Correctness boundary

`Metric.infDist x empty = 0`, so an empty boundary makes every distance level
degenerate.  Taking `B = C` is also invalid because the distance vanishes on
the carrier.  A strict Soul shave still requires a nonempty relative boundary,
positive distance somewhere, its geodesic concavity, and a separate strict
dimension-drop theorem.

The classical relative boundary uses the dense smooth stratum `N` of `C`:
`B = C \ N = frontierIn C N`.  `RelativeFrontier.lean` records this identity
from relative openness and density.  Taking `frontierIn C C` instead gives an
empty frontier.  Producing the embedded totally geodesic dense stratum remains
a genuine missing theorem.

## Verification

Focused, targeted, and full-project verification passed without a new warning
or placeholder.  Direct axiom verification of compactness, maximum attainment,
the two total-convexity consumers, and the positive frontier-distance bridge
found only `propext`, `Classical.choice`, and `Quot.sound`.

## Progress

The Soul theorem remains unstated and therefore 0%.  Its dedicated machinery
is approximately 32--33%; this module supplies generic shaving consumers, not
the dense stratum, boundary-concavity, or dimension-drop producers.  The whole B1
lane remains approximately 22--25%, and the whole post-HCG Poincare program
remains approximately 15--20%.
