# ChartBasisReadout

## 2026-07-27 extraction

This module contains the three chart-basis readouts formerly embedded in
`RicciThreeArmAppCc.lean`.  Its imports were narrowed to the actual tensor
component, cometric, chart-basis metric, inverse-Gram, and bundle-locality APIs.
In particular, it no longer imports the full Ricci linearization arm field or
Hessian/Laplacian trees.

The unit-evaluation dependency is now the small `UnitModel` module rather than
the complete slot-permutation naturality module.

The original extracted source checked successfully.  The narrowed import
version is pending a focused recheck: an unrelated concurrent targeted build
currently owns the shared artifact-writing window, and the interrupted prior
refresh left intermediate object files temporarily absent.
