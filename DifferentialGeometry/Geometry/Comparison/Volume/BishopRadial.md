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
