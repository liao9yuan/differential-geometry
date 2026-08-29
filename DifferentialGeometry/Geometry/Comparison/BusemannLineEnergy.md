# Busemann line energy

## Purpose

`buse_pair_memW1p` supplies the local Euclidean `W^{1,2}` membership needed by
the De Giorgi weak-supersolution interface.  It uses only the minimizing-line
and metric-norm data already present in the Busemann comparison lane.

The proof localizes the intrinsically two-Lipschitz Busemann pair by a smooth
manifold bump function, applies the chart Lipschitz bridge, constructs the
De Giorgi weak derivatives on a finite Euclidean ball, and then removes the
cutoff by almost-everywhere congruence where the bump equals one.

## Status

The theorem previously passed focused verification without warnings.  Its
private local Euclidean-ball helper has now been moved unchanged to the
canonical Euclidean Sobolev layer as `memW1p_ball_of_lip`, and this consumer
calls that public producer.  The extraction has not yet been rechecked because
the shared Lean guard is occupied.

The surrounding smooth-cutoff/chart argument has now also been extracted once
to the manifold Lipschitz layer as `raw_memW1p_of_lip`.  This theorem has been
shortened to its intrinsic two-Lipschitz estimate followed by that generic
producer.  The refactor passed warning-free focused verification.  Its public
theorem signature is unchanged, so no proof-body-only named refresh was needed.

This closes the local Lipschitz-to-`MemW1p 2` producer, but not the full
splitting theorem.  The next independent analytic frontier is conversion of
the distributional Laplacian inequality to the chart divergence-form energy
inequality against all `MemH01` test witnesses required by
`DeGiorgi.IsSupersolution`.

Whole-project estimate: the splitting theorem itself remains unstated (0%);
its dedicated machinery is about 35--40%, whole-P1c dedicated machinery is
about 60--65%, and whole P0--P9 infrastructure remains about 15--25%.
