# BishopRadial notes

## 2026-07-18 assembled local radial producer

- Added `exists_radial_base` and `radialRatio_auto`, then assembled
  `exists_radial_cmp`. One common radius now supplies differentiability,
  Jacobi fields, linear independence, Wronskian symmetry, the mean comparison,
  and antitonicity of the local radial density ratio.
- The current honest producer retains completeness, connectedness, continuous
  Riemannian-bundle data, and the norm compatibility hypothesis because the
  available Wronskian/frame construction genuinely consumes them.
- Focused verification and the exported module refresh passed.
- This is local dedicated machinery only. The global Bishop--Gromov theorem
  and the `SeqBoundedGeometry` volume-input producer both remain 0% proved.

## 2026-07-19 normal-density ratio transfer

Added `normalRatio_anti`, the direct consumer of `normalDensity_curve`.  A
positive radius-independent basis factor multiplies the transverse
`curveDensity / hypDensity` ratio, so its antitonicity transfers to
`r ^ card ι * normalChartDensity (r • u) / hypDensity`.  The theorem carries
only the normal source/radius assumptions and the already-proved curve-ratio
input; it does not repeat the Riccati producer's geometric hypotheses.

Focused verification passed without warnings.  `normalRatio_anti` is complete
(100%).  The next substantial theorem `normalBall_ratio` remains unstated
(0%); before it can be stated honestly, the polar layer needs a center-metric-
ball adapter because the live formula uses the fixed ambient model norm.
Dedicated Route B machinery is about 52%, the full V1--V3 volume-comparison/CGT
program is about 39--43%, and unconditional HCG endpoint theorems remain 0%.
