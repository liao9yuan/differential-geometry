# Local

## 2026-08-30: complete-Shi route cleanup

- Removed the unused private helper `complete_of_heat`, whose only purpose was
  to call the under-specified generic `estimate_complete` interface.
- The live public endpoint `movingShi_complete` is unchanged. It already
  assembles the actual Ricci-flow curvature tower, `towerNorm_grad_le`,
  `shiBarrierCutoff_of_sol`, and the checked private `complete_of_barrier`
  route. No hypothesis was added and no frontier was moved into an assumption.
- Source review found no remaining Lean reference to the removed declarations.
  Focused regression verification passed without warnings. A subsequent named
  refresh traversed a broad stale dependency cone and failed only in the dirty
  P1-owned `MaximalRescaling.lean`; it removed that module's old artifact, so
  the downstream direct axiom audit was temporarily blocked at import time.
  P1 later restored that artifact in an exclusive window. No P1 file was edited
  by this lane, and no further refresh is permitted while tasks run in parallel.
- The resulting 32-endpoint focused axiom audit is warning-free green;
  `movingShi_complete` depends only on `propext`, `Classical.choice`, and
  `Quot.sound`.
- `movingShi_complete` is the complete bounded-curvature solution endpoint;
  the broader P2b reduced-geometry package remains unstated and therefore 0%
  as a package theorem. Its dedicated machinery is about 42--45% after this
  source regression is counted.
