# GradientRegularity

## 2026-08-28: local Laplacian subtraction producer

- Added `laplacian_sub_at` in the local gradient-regularity layer.  It states
  pointwise Laplacian subtraction from `ContMDiffAt ... ∞` hypotheses on the
  two scalar functions, without requiring global differentiability.
- The proof downgrades local smoothness to a finite grade to obtain eventual
  `MDifferentiableAt`, uses local smoothness of both gradient sections, transports
  their eventual subtraction identity through the covariant derivative, and
  finishes with `divergence_sub`.
- This is the lowest missing producer for the subsequent barrier-to-viscosity
  comparison layer.  It does not itself assert a viscosity, weak, distributional,
  or limit-stability result.
- The first focused check failed at the theorem signature because the newly
  added block accidentally used the wrong Unicode model notation `𝒤` instead
  of the canonical `𝓘`.  All eight occurrences in that block were corrected
  without changing the API or proof route.
- The second focused check passed without warnings, and the explicit named
  module refresh also passed completely.  `laplacian_sub_at` is therefore a
  checked local operator producer.

## Project position

- `laplacian_sub_at`: focused warning-free and explicitly refreshed; checked
  producer status is current.
- Barrier-to-viscosity theorem: not yet proved here (0%); this file only supplies
  its local operator producer.
- P1c splitting, soul, volume rigidity, and fundamental-group endpoints remain
  unstated or unproved (0% each).  This producer is a small part of the
  Laplacian/barrier infrastructure and does not change endpoint completion.
