# GlobalVectorField

## Role

This module is the acyclic foundation for the global geodesic vector field.
It keeps the existing public declarations and moves them below
`MaximalInterval`; it does not introduce a second geodesic domain or a
parallel vector-field API.

The moved declarations comprise:

- the generic tangent-chart first and second component formulas formerly in
  `ChartIdentification`;
- the low-level projection-coordinate lemmas formerly at the start of
  `ProjDerivative`;
- `geodesicVectorFieldChart_eq_geodesicVectorField`,
  `chart_vf_on_iff`, and `geodesicVF_smooth`, formerly in
  `CrossVFReduction`.

The import closure uses only `Equation`, chart-transition geometry, and
Mathlib differential/manifold support.  In particular, it has no dependency
path to `MaximalInterval).

## Mathematical route

The chart/global equality is still the original coordinate-change proof.  Its
positive-dimensional branch uses the existing coordinate transformation
calculation; the zero-dimensional branch is discharged by subsingleton
coordinates.  Consequently the equality, integral-curve equivalence, and
global smoothness no longer carry a gratuitous `NeZero` assumption.  The
integral-curve equivalence is the pointwise lifting over a supplied chart
source, and global smoothness is still obtained locally from the checked
fixed-chart vector field.

## Verification

Focused verification passed without warnings.  The explicit named refresh
also passed, and the moved exports are available to downstream modules.

The lower-module extraction is complete (100%).  It is support machinery only;
the compact-closure Bishop endpoint remains unstated and therefore 0%.
