# Busemann line minimum

## Role

`buse_pair_eq_zero` is the strong-minimum endpoint for the Busemann pair of a
supplied minimizing line.  Under nonnegative Ricci curvature and dimension
greater than two, it combines the distributional Laplacian comparison with the
native De Giorgi strong minimum principle to prove that the pair vanishes on
the whole connected manifold.

## Proof route

The proof first derives continuity from the two intrinsic one-Lipschitz
estimates, and uses the existing nonnegativity, origin-zero, and distributional
Laplacian producers.  Around an arbitrary zero of the pair, it intersects the
radius supplied by `buse_pair_memW1p` with a coordinate radius whose closed ball
lies in the chart target.  Restricting the existing Sobolev witness to this
smaller ball introduces no new assumption.

`exists_metric_coeff` constructs the normalized weighted inverse-metric
coefficient, and `chart_super_of_lap` turns the global distributional inequality
into the local De Giorgi supersolution predicate.  `super_zero_on_ball` then
annihilates the chart pullback on the concentric quarter ball.  Pulling that
ball back through the extended chart proves that the zero set is open.  It is
closed by continuity and nonempty by `buse_pair_zero`, so connectedness makes it
the whole manifold.

The public dimension assumption is only
`2 < Module.finrank ℝ E`.  The proof derives both the positive transverse
dimension needed by `buse_pair_lap` and the real-valued dimension inequality
needed by the De Giorgi theorem.  It also derives the internal `NeZero` instance
instead of exposing it as another theorem hypothesis.

## Verification

The first focused check failed on four local elaboration/import-shape errors;
it did not reach a mathematical proof obligation.  All four have now been
statically repaired:

- line 44: unknown identifier `RicciBoundedBelow`.  The imported producer keeps
  this name in `Geometry.Riemannian.BonnetMyers`, so that namespace is now open,
  matching `BusemannLineLaplacian`;
- lines 157 and 161: `rw [uE, ...]` treated the applied local let as a rewrite
  argument.  Both sites now unfold `uE` first with `dsimp only [uE]`, then
  rewrite only by `chartPushedRaw_apply_of_mem`;
- line 175: unknown identifier `𝒩`.  `Topology` is now included in
  `open scoped`.

No retry or named refresh has been run.  The static repairs are pending the
next authorized focused check, so the restricted Sobolev witness and the
strong-minimum argument remain unverified.

The authorized focused retry cleared the `RicciBoundedBelow` namespace error
and both local-`uE` rewrite errors, but stopped at line 178 with unknown
identifier `𝒩`.  The source used that undefined calligraphic glyph at all three
neighborhood sites rather than Lean's topology notation.  All three sites now
use the unambiguous ASCII spelling `nhds`, without changing the proof route;
this static repair is pending the next authorized focused retry.

The failed elaboration also emitted an unused-section-variable warning for
`SigmaCompactSpace M` and `ConnectedSpace M`.  This is provisional: elaboration
stopped before the later connectedness assembly, and the intended proof uses
both the chart supersolution bridge and `IsClopen.eq_univ`.  No assumption has
been removed or omitted on the basis of this incomplete run.  No second retry,
Solution check, or named refresh was run.

After replacing the three malformed neighborhood glyphs by ASCII `nhds`, the
next authorized focused retry passed without warnings.  In particular, the
earlier unused-section warning disappeared once the whole proof elaborated, so
both `SigmaCompactSpace M` and `ConnectedSpace M` remain genuine dependencies.
The subsequently authorized explicit named refresh also completed
successfully.  No downstream Solution check has been run.

## Project status

The theorem `buse_pair_eq_zero` is warning-free focused and named-refresh GREEN,
and therefore 100% verified-complete.  The supplied-line splitting theorem is
still unstated and therefore 0% complete.  Its dedicated machinery is now
roughly 40--45%, since local
single-Busemann weak harmonicity, harmonic regularity,
parallel-gradient/Bochner, flow, and global product-isometry remain separate
stages.  The whole P1c machinery is roughly 60--65%, the whole Poincare P0--P9
infrastructure roughly 15--25%, and the final Poincare endpoint remains 0%.
