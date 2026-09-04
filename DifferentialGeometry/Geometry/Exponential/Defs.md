# Defs

## Global zero-velocity support

The exponential-map definitions and their public interfaces are unchanged:
`expMap`, `expMap_def`, `expDomain`, and `mem_expDomain_iff` retain the same
statements, and `expMap` keeps its existing junk value outside `expDomain`.

The stationary maximal witness now uses
`geodesicVectorField_zero_section` and the constant integral curve of the
global geodesic vector field.  This matches the global support carried by
`IsGeodesicOnWithInitial`.

The zero-velocity propagation theorem now also takes global-vector-field
support.  Its proof compares the supplied lift with the constant zero-section
lift using `gvf_eqOn` on the open preconnected time domain.  The former clopen
argument, fixed-chart source checks, and chart-local uniqueness calls were
removed.  The downstream zero-curve and `expMap_zero` assembly is otherwise
unchanged.

The lower global-vector-field foundation handles the zero-dimensional model
separately.  The propagation theorem and its two direct public consumers
therefore keep their previous weakest signatures and do not require
`NeZero (Module.finrank ℝ E)`.

## Verification and scope

Focused verification passed without warnings.  The explicit named refresh for
downstream exponential/chart-flow consumers also passed.

- Global zero-support migration in this file: 100% complete and checked.
- `expMap` / `expDomain` public definitions and junk semantics: preserved.
- Whole P1a compact-closure comparison theorem: not stated or proved here
  (0% theorem completion in this file); this migration is estimated below 1%
  of that larger assembly.
