# Chained flow continuity

## Global-support migration

`maximalGeodesic_eqOn_lift_of_footInSource` retains its chart-specific caller
interface.  The source hypothesis converts that integral curve to the global
geodesic vector field with `chart_vf_on_iff`.  The chosen maximal witness now
already carries global support, so uniqueness on the intersection follows
directly from `gvf_eqOn`; no chart-source condition is required for the chosen
witness.  The proof structure of `continuousOn_base` and the indirect
continuity theorem are unchanged.

The first verification attempt was blocked before elaboration because the
genuinely required `PreconnectedPropagation` object was not yet available.
After that upstream module was verified and refreshed, focused verification of
this file passed without warnings.

## Progress

- This file's global-support migration: 100%.
- The P1a compact-closure local Bishop endpoint: 0% proved by this file; this is
  supporting continuity infrastructure only, well under 1% of that endpoint.
