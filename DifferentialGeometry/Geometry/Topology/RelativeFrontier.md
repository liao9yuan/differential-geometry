# Relative frontier

## Scope

This module defines the interior, frontier, and closure of a set `C` relative
to an explicit carrier set `A`, using the induced topology on the subtype `A`.
It is a topological API and does not assert that `A` is a manifold or a
totally geodesic submanifold.

## Implemented API

`Set.interiorIn A C`, `Set.frontierIn A C`, and `Set.closureIn A C` map the
corresponding subtype-topology sets back to the ambient type.  Carrier and
subset lemmas expose their elementary containment properties.  The self
lemmas prove that the relative interior and closure of a carrier in itself are
the carrier, while its relative frontier is empty.

`dense_iff_closureIn` identifies density in the subtype carrier with the
ambient equality `closureIn A C = A`.  If `C` is also relatively open,
`frontierIn_eq_sdiff` then identifies its relative frontier with `A \ C`.
Applied to the classical dense smooth stratum `N` inside a compact convex set
`C`, this gives the convex boundary as `frontierIn C N = C \ N`.
`frontierIn_isCompact` shows that every relative frontier in a compact carrier
is compact, without requiring openness or density.

The identity `frontierIn C C = empty` is an intentional guardrail: using the
set being shaved as its own carrier destroys the boundary.  For a
lower-dimensional closed subset, using the ambient frontier is also wrong,
because that frontier is the whole subset and its boundary distance vanishes.

## Verification

Focused, targeted, and full-project verification passed without a warning or
placeholder.  Direct axiom verification of `frontierIn_self`,
`dense_iff_closureIn`, `frontierIn_eq_sdiff`, and `frontierIn_isCompact` found
only `propext`, `Classical.choice`, and `Quot.sound`.

## Frontier

The next genuine Soul producer must construct, from a nonempty compact totally
convex set `C`, its connected embedded totally geodesic smooth stratum `N`,
prove that `N` is relatively open and dense in `C`, and identify its closure
with `C`.  Current Mathlib and project APIs do not provide a general
submanifold or convex-stratum producer.

The Soul theorem remains unstated and therefore 0%.  Its dedicated machinery
is approximately 32--33%; the whole B1 lane remains approximately 22--25%,
and the whole post-HCG Poincare program remains approximately 15--20%.
