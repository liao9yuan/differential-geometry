# LocalDiffeoIFT

## Written derivative bridge

`written_fderiv_inv` exposes the canonical coordinate-layer conversion from an
invertible manifold derivative to the invertible Fréchet derivative of the
written extended-chart map.  Boundarylessness of the source model identifies
the model range with the whole space; no manifold regularity or target
boundarylessness is used.

The helper replaces the need to reproduce the private exponential-specific
adapter in `Exponential/ExpInvBranch.lean`.  Focused verification passed
without warnings.  No downstream refresh or broader build was run during the
parallel P1b window.
