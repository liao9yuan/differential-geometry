# Pointed limit existence

## Result

`LimitExistence.lean` exposes the P5-facing conditional assembly
`std_limit_of_bounds`. It directly reuses the provider-native Hamilton
compactness theorem and returns smooth pointed convergence together with
completeness of every time slice of the limit.

This theorem does not claim that the required sequence exists. The missing
producer is the common-window compact-double sequence with uniform curvature
and basepoint injectivity bounds. Once that producer is supplied, no additional
compactness theorem is needed for P5-D.

## Verification

Focused verification passed. The missing transitive object file left by the
interrupted refresh was restored by refreshing only its explicitly named
module; no broad `CompactDouble` refresh was restarted.

## Progress

P5 main theorem remains 0%. The checked conditional P5-D assembly is complete,
while the upstream standard-approximation input producer remains 0%.
