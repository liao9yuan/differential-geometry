# CompactVolumeEquiv

## Source state (2026-07-19)

This file implements the compact-ratio route for comparing the volume
measures of a jointly `C^0` family of smooth Riemannian metrics with one fixed
reference metric.

The source-written producer chain is:

- `density_cont_of_gram`: componentwise joint continuity of the chart Gram
  matrix implies joint continuity of the chart density, without requiring the
  stronger `MetricFamilyRegularAt` time-derivative interface;
- `density_ratio_bdd`: on
  `J x tsupport (chartAtlasPOU alpha)`, compactness and positivity bound both
  moving/reference chart-density ratios;
- `volume_density_bdd`: the finite canonical POU supplies one constant for all
  nonzero chart weights;
- `chart_lintegral_le`: `chartLocalMeasure_lintegral` transports a density
  bound directly to the corresponding POU-weighted chart lower integral;
- `volume_lintegral_le`: finite POU summation gives two-sided global lower
  integral comparison;
- `volume_uniform_equiv`: testing the lower-integral comparison on measurable
  indicators gives the two measure inequalities
  `dmu_(g t) <= C dmu_q` and `dmu_q <= C dmu_(g t)` on the same compact time
  set.

This route intentionally does not use Loewner-order determinant monotonicity
or an explicit dimension-dependent constant.  It needs only the joint `C^0`
chart-Gram regularity already present in the forward-uniqueness endpoint.

## Verification

All declarations are source-complete and contain no `sorry`, `admit`, or new
axiom.  Focused Lean verification is pending because the shared global build
was still active when the file was written; no competing Lean process was
started.  Until that check passes these declarations are 0% accepted Lean
theorems.

## Downstream effect

`Pullback/HarmonicPrincipal.lean` consumes `volume_uniform_equiv` in the
endpoint-shaped `hmfVolumeEquiv` theorem on each compact initial subslab.  The
next moving-form task is to combine this measure comparison with the existing
inverse-cometric pointwise bounds to extend `hmfMass` and `hmfWeakForm` to the
fixed `TensorH1Compl q 0 1` carrier and prove uniform boundedness/coercivity.

