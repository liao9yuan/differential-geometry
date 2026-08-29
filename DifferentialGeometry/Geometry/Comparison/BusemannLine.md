# BusemannLine

## Role

This module supplies the metric Busemann pair attached to a supplied minimizing
line.  It is the last purely metric producer before the weak maximum-principle
and elliptic-regularity stages of Cheeger--Gromoll splitting.

## API

- `buse_pair_nonneg` proves that the positive and negative Busemann functions
  have nonnegative sum everywhere.
- `buse_pair_zero` records that their sum vanishes at the line origin.
- `buse_pair_line` strengthens this to every point of the supplied line.

The results use the two minimizing rays supplied by `IsMinimizingLine`, the
integer-pole Busemann convergence theorem, the distance triangle inequality,
and the exact line-distance identity.  They require no completeness or
curvature assumptions.

## Verification

Focused verification passed without warnings.  The targeted module refresh also
passed with all declarations checked.

## Project status

The supplied-line splitting theorem remains unstated and therefore 0% complete.
This metric pair closes one small input to its future weak maximum-principle
stage; splitting-specific machinery remains only about 15--20% complete.
