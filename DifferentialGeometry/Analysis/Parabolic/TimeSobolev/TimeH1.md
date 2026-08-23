# Time H1 paths

## Implemented adapter

`timeH1.ofContDiffOn` realizes a vector-valued `C¹` curve on `Icc 0 T` as the
continuous representative of a `timeH1` element for the weakest natural time
assumption `0 <= T`. It uses the ordinary derivative as the L2 representative;
the one-sided endpoint issue is removed almost everywhere rather than by
asserting differentiability outside the interval.

`timeH1.toFun_ofContDiffOn` proves equality with the original curve on the
whole closed interval, including the degenerate case `T = 0`.
`timeH1.deriv_ofContDiffOn` identifies the weak time derivative almost
everywhere with the ordinary derivative.

## Verification and boundary

Focused verification passes without warnings or placeholders. This adapter is
generic finite- or infinite-dimensional linear infrastructure; it does not
define a manifold-valued H1 path or identify a weak chart derivative with
`mfderiv`/`lVelocity`.

For the Perelman direct method, the next geometric producer is a single-chart
realization such as `chartTimeH1`, followed by finite chart localization,
overlap weak chain rules, moving-coefficient lower semicontinuity, and a
separate Tonelli regularity upgrade. `exists_lMinimizer` remains 0%.
