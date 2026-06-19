# Pullback

2026-06-17: Relaxed `Diffeomorph.pullbackMetric` and its projection lemmas.

The construction did not use `BoundarylessManifold`, `InnerProductSpace` on the
model, or `NeZero (Module.finrank Real E)`.  The public assumptions now match
the actual proof: a normed finite-dimensional model, smooth source/target
manifolds, and `SigmaCompactSpace`/`T2Space` on the pullback source.  This lets
HCG open comparison domains use `Diffeomorph.pullbackMetric` after constructing
their open-subtype restricted target metrics.

Verification: passed for this file.
