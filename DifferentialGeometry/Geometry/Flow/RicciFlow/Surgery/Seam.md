# Seam

## Role

`Seam.lean` is the first S0 surgery-spacetime producer.  It models one event
between two genuinely different manifold types.  The retained region is a set
inside an open neighborhood, and the neighborhood is smoothly identified with
an open post-surgery neighborhood.

This is the event-presentation route suggested by Morgan--Tian's gluing lemma.
It avoids pretending that all surgery slices live on one fixed manifold, and
it does not pretend that the exotic total surgery spacetime is an ordinary
manifold with boundary.

## Boundary decisions

- `SurgerySeam` contains only smooth gluing data.
- `keep` is not identified with the open source: the kept region may have
  boundary while the diffeomorphism germ needs an open domain.
- Metric matching is a later predicate, not a structure field.
- The local Ricci-flow equation remains on the two `SolutionOn` slabs.
- Neck quality, cap geometry, pinching, noncollapse, and canonical
  neighborhoods do not belong in this module.
- The global exotic atlas is a later realization problem.  A dependent sum of
  slices is not accepted as a substitute.

## Exported layer

The module provides ambient pre/post retained sets, discarded and created
regions, an injective ambient identification, and the induced equivalence of
the retained regions.

## Verification

Focused verification passed with no warnings or placeholders.

## Honest progress

- `SurgerySeam` theorem/API layer: complete and focused-green.
- Global RFWS endpoint: unstated, therefore 0%.
- Dedicated S0 data-model machinery: approximately 10--15% after this module
  verifies.
- Whole surgery phase: approximately 1--2% infrastructure, theorem endpoints
  0%.
- Whole post-HCG Poincare program: approximately 15--20%.
