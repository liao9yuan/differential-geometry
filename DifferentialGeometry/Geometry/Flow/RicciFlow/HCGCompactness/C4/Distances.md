# Distances

## Source

MSM135 Chapter 4, Proposition "Distances" proves that an
`(epsilon,0)` pre-approximate isometry sends a `g`-ball of radius `r` into the
`h`-ball of radius `sqrt (1 + epsilon) * r`.

## This pass

The implemented theorems now include the F2 route at the path-speed-bound
level. `pathComp_tangent` turns a target-path producer with pointwise
Riemannian speed bound into the smooth path-length comparison used in the book.
`edist_le_of_path_comp`, `dist_le_of_path_comp`, and
`image_ball_subset_of_path_comp` turn that path comparison into distance and
ball-inclusion statements. The direct consumers `dist_le_tangent` and
`image_ball_tangent` package Proposition "Distances" from the path-speed bound.
The older metric-space wrappers `lipschitz_sqrt_of_dist_le` and
`image_ball_subset_of_lipschitz_sqrt` remain as smaller consumers.

## Remaining frontier

F2 is complete once the construction supplies the target path and pointwise
speed bound.  The remaining optional bridge for later map-building phases is to
derive that speed bound from a concrete map by combining the chain rule,
`Diffeomorph.pullbackMetric_inner` or equivalent pullback-tensor evaluation,
the F1 `C^0` metric comparison, and a compatibility theorem identifying the
explicit metrics used by `PreApproxIsometryData` with the typeclass
Riemannian tangent norms/distances used by Mathlib's `riemannianEDist`.

## Verification

Verification passed for the targeted `Distances` file.
