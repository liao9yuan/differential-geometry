# MinimizingLine

## Role

This module supplies the canonical geometric input for the supplied-line
Cheeger--Gromoll splitting route.  A minimizing line is a global geodesic whose
ordered subsegments realize Riemannian distance with unit-speed
parametrization.

## API

- `IsMinimizingLine` records the global geodesic and ordered exact-distance
  properties.
- `IsMinimizingLine.isGeodesic` and `IsMinimizingLine.edist_eq` expose those
  fields.
- `IsMinimizingLine.pos_ray` and `IsMinimizingLine.neg_ray` produce the two
  supplied minimizing rays based at the line origin.

The definition carries no completeness, noncompactness, or curvature
assumptions.  The reverse-ray proof reuses the native geodesic-reversal theorem
and Riemannian-distance symmetry.

## Verification

Focused verification passed without warnings.  The targeted module refresh also
passed with all declarations checked.

## Project status

The supplied-line splitting theorem remains unstated and therefore 0% complete.
This file is the first small producer in its line/Busemann dependency chain;
the splitting-specific machinery remains about 15% complete overall.
