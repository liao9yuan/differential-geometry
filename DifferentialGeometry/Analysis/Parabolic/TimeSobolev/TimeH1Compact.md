# TimeH1Compact

## Result

This file supplies the finite-dimensional compactness brick for time-`H¹`
maps. A norm-bounded sequence has one strict-mono subsequence and a limit in
`timeH1` such that:

- all Hilbert inner-product tests converge along the subsequence;
- the canonical continuous representatives converge uniformly on
  `Set.Icc 0 T`.

The proof uses the existing vector-valued Arzelà–Ascoli theorem for uniform
compactness and sequential Banach–Alaoglu plus Fréchet–Riesz for weak
compactness. The two limits are identified pointwise through the adjoint of the
bounded time-evaluation map.

## Supporting estimates

`integral_uIoc_le` bounds the `L¹` norm on an unoriented subinterval by the
square root of its length times the ambient time-`L²` norm.
`timeH1.toFun_sub_le` gives the resulting two-point Hölder-`1/2` estimate for
the canonical representative.

The Hilbert compactness section deliberately introduces a fresh target type
whose normed-space structure is inherited from its inner-product structure.
This avoids an instance diamond with the older explicit `NormedSpace` context
used by the norm-only estimates. Separability is derived locally from finite
dimensionality and the existing separable-measure and `WithLp` APIs; it is not
an extra public hypothesis.

## Verification and frontier

Focused verification passed without warnings, `sorry`, or `admit`.

This completes the generic time-`H¹` compactness stage requested for the
chart-local direct method. It does not by itself establish lower
semicontinuity of a variable quadratic action, nor does it turn a uniform
limit of manifold-valued curves into an admissible manifold `H¹` curve. The
remaining geometric frontier is still a chart-compatible weak-derivative /
velocity realization API.

Progress accounting for this brick: `compact_subseq` and its dedicated
two-point modulus machinery are complete (100%). The manifold-valued Perelman
minimizer theorem remains unstated and therefore 0%; `redVolume_anti` remains
0%. This file adds generic reused compactness infrastructure and does not by
itself advance the dedicated L-geometry theorem percentage.
