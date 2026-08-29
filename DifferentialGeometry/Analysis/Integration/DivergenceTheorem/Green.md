# Green

## 2026-08-29: noncompact Green second identity

- Added `green_second_of_supp`, the Green second integral identity on a
  boundaryless, not necessarily compact manifold when either smooth scalar
  function has compact support.
- The proof uses the compactly supported current
  `f ∇h + (-h) ∇f`.  Each summand is compactly supported from either the
  compact scalar factor or the compact gradient factor.  The existing
  first-order product-divergence formula expands both summands, metric symmetry
  cancels the cross-gradient terms, and the compact-support divergence theorem
  makes the current's divergence integrate to zero.
- This strengthens only the support scope of the existing compact-manifold Green
  second identity; it does not add integrability assumptions or change the
  existing first Green identities.
- The focused check passed without warnings, and the explicit named module
  refresh passed completely.  The axiom audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`; there is no project-specific axiom.

## Project position

- `green_second_of_supp`: focused warning-free, explicitly refreshed, and
  axiom-audited; checked producer status is current.
- The theorem is integration infrastructure for a future
  viscosity-to-distributional layer; it does not itself prove weak Laplacian
  stability or any P1c endpoint.
