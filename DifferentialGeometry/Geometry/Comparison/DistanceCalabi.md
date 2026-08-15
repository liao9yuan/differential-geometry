# DistanceCalabi

## Status

The Calabi-tail comparison additions are implemented without placeholders. Focused, targeted, and full-project verification passed.

`CalabiTailData.dist_le_radius` records the broken-path upper bound, while `tail_edist` extracts the exact minimizing tail distance from the full minimizing segment. The Hessian adapters now cover launch-perpendicular and arbitrary endpoint directions. `CalabiTailData.geo_upper` and `calabi_geo_upper` turn the selected branch radius into a smooth scalar upper support along a smooth geodesic with the standard second-derivative bound.

The exact full-distance hypothesis in `tail_edist` is essential: a local inverse branch and absence of conjugate points do not by themselves imply global minimizing behavior.

## Project position

- Exact Calabi-tail distance and branch-radius upper support: 100%.
- Arbitrary-direction Calabi Hessian bound: 100%.
- Finite-distance semiconcavity along smooth geodesics: 100%.
- Smooth-geodesic Busemann composition concavity: 100%.
- Public all-segment Busemann concavity: unstated, 0%; the current geodesic-concavity predicate omits curve continuity.
- Soul theorem: unstated, 0%; dedicated machinery approximately 24%.
