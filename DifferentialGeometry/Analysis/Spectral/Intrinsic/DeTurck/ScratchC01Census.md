# ScratchC01Census.lean — axiom census notes

This scratch module prints the axiom dependencies of the low-regularity
coefficient, per-index ladder, and Galerkin energy interfaces.  It contains no
proof frontier.

The 2026-08-05 dissipation-export update added `energy_l1_diss` and
`galRiderDiss` to the census.  The upstream module refresh and focused census
check passed.  Both declarations print only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`.

The same pass repaired the stale `jetAdd` census entry to `opJetAdd`, matching
the window-local rename that removed the combined-import collision with the H²
lane.

## 2026-08-05 - strict-cutoff census

The census now prints 129 declarations.  The two additions are
`radialA2_pairR` and `lowA2_small_one`, covering the radius-flexible A2 pair and
its strict-contraction specialization.  The full focused census passed; every
declaration reports only `propext`, `Classical.choice`, and `Quot.sound`, with
zero `sorryAx`.
