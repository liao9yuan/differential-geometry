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

`frontier_shave_data` packages the whole topology-and-metric part of one
nonterminal shave.  Relative openness and density identify the boundary with
`C \ N`; when this boundary is nonempty, it is compact, has positive distance
from some carrier point, and its deepest set is nonempty, compact, disjoint
from the boundary, and contained in `N`.

## Correctness boundary

`Metric.infDist x empty = 0`, so an empty boundary makes every distance level
degenerate.  Taking `B = C` is also invalid because the distance vanishes on
the carrier.  A strict Soul shave still requires a nonempty relative boundary,
positive distance somewhere, its geodesic concavity, and a separate strict
dimension-drop theorem.

The classical relative boundary uses the dense smooth stratum `N` of `C`:
`B = C \ N = frontierIn C N`.  `RelativeFrontier.lean` records this identity
from relative openness and density.  Taking `frontierIn C C` instead gives an
empty frontier.  `ConvexStratum.lean` now produces the embedded, totally
geodesic dense stratum; the missing geometric producer is concavity on `C` of
distance to this relative boundary.

The smallest hard leaf for that producer is Sakai's local affine upper support
for boundary distance.  Its proof still needs a boundary tangent-cone
supporting half-space theorem, a sharp moving-base parallel-exponential Rauch
estimate with `J(0) = v` and `J'(0) = 0`, and a local hinge comparison.  The
current Jacobi and Calabi APIs do not provide these statements, so this is a
comparison-geometry blocker rather than a set-theoretic or instance issue.

## Verification

Focused and targeted verification and the root aggregate check passed without
a new warning or placeholder.  Direct axiom verification of the frontier
shave package found only `propext`, `Classical.choice`, and `Quot.sound`.  The
current full-project build is pending.

## Progress

The Soul theorem remains unstated and therefore 0%.  Its dedicated machinery
is approximately 48--52%; this module now closes the generic topology-and-
metric shaving package, but not boundary concavity or dimension drop.  The
whole B1 lane is approximately 30--34%, and the whole post-HCG Poincare program
approximately 18--22%.
