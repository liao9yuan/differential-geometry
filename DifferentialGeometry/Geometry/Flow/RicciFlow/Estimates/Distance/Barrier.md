# Barrier

## Status

Focused verification is warning-free GREEN after extracting the explicit-tail
dynamic core.

`scaled_of_tail` turns an actual `CalabiTailData` into the existing
`ScaledDistSupport`. Its static Ricci lower input is required only along the
tail geodesic, while its absolute Ricci input is required only on an outer
metric ball containing the tail and the minimizing left segment. The original
global `scaled_of_quad` theorem remains a compatibility consumer of the same
core.

The two radial pieces are kept in the outer ball by
`CalabiTailData.mem_eball` and the intrinsic minimizing-geodesic distance
bound. No moving tangent bundle or Hom object is compared.

## Next theorem

Extract the existing cutoff-profile composition in `Shi/Cutoff.lean` as a
generic consumer of `ScaledDistSupport`, retaining the quadratic radial scale
in its error instead of weakening it through `a ^ 2 <= a`.
