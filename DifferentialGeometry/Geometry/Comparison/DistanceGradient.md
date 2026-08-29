# DistanceGradient

## Mathematical route

`dist_grad_radial` proves differentiability of the distance from the pole at
every nonzero vector in `SegInt`, with gradient equal to the outgoing unit
radial velocity.  The proof uses a smooth upper `branchRadius` from the pole and
a smooth lower support obtained by reversing the remaining tail of a longer
minimizing segment.  Their sum has a local minimum at the evaluation point, so
the two supports have the same first derivative and squeeze the distance to
that derivative.

The proof reuses the exported `tailCurve_eq`, `tailVel_one`, `minTail_edist`, and
`tail_not_conj_of_min` producers.  The private model-space sandwich lemma records
only the final calculus step.  No cut-locus openness hierarchy, new assumption,
or differentiability hypothesis is introduced.

This is the first-order geometric producer required by the direct polar route;
it is dedicated P1c machinery, not yet the formal weak Laplacian-comparison
endpoint.

## Verification

Focused verification and the explicitly targeted module refresh both passed
without warnings.
