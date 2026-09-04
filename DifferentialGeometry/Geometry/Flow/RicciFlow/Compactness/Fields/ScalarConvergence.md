# ScalarConvergence

## Role

`ConvOut.scalar_convOn` is the P2b compact-by-time scalar-curvature convergence
producer.  It strengthens the existing fixed-point `ConvOut.scalar_conv_at`
endpoint without adding a convergence assumption: the source is the existing
`ConvOut.conv` two-jet convergence on compact sets.

`ConvOut.scalar_compOn` is the moving-point adapter needed by confined pointed
action limits.  It accepts an arbitrary compact-parameter clock `tau`, so it
covers both ordinary backward time and the regularized clock `T - s^2`.

## Native route

- `gSeqExt_lower` gives the common positive lower metric bound for the extended
  sequence, and `ConvOut.lower_of` passes that bound to `co.gInf`.
- The `hcovTail` hypothesis used by `ConvOut.scalar_conv_at`, together with the
  bump-family compact exhaustion, gives a common order-at-most-two covariant
  metric bound on the chosen compact set.  One fixed `ConvOut.conv` comparison
  transfers the same bound to the limit metric.
- `scalarSub_le_dNormOn` converts the common ellipticity/two-jet bounds and the
  compact-uniform metric two-jet difference into a compact-uniform scalar
  difference.
- `gSeqExt_scalar` identifies the resulting scalar curvature with the scalar
  curvature of the original pulled-back flow term.
- `ConvOut.scalar_compOn` first regards `scalar_convOn` as uniform convergence
  on the compact spacetime product.  Eventual continuity of the pulled-back
  source scalar fields then makes the limit scalar field continuous, hence
  uniformly continuous there.  Uniform curve convergence supplies the moving-
  point term, and a triangle estimate joins it to the same-point scalar limit.
- The supplied pseudometric is required only to express curve uniform
  convergence; its topology is explicitly required to agree with the pointed
  manifold topology.  This is compatibility data, not an action-comparison or
  scalar-convergence assumption.

No new class, predicate, notation, or frontier hypothesis is introduced.

## Verification

Focused verification is warning-free GREEN, and the explicit named module
refresh is GREEN.  The exported `ConvOut.scalar_convOn` declaration is fresh
for downstream consumers.

The unused local nonnegativity witness for the derivative supremum was removed
during static warning cleanup; the theorem statement and proof route are
unchanged.

After `scalarSub_le_dNormOn` dropped its unused public `0 <= B` hypothesis, the
corresponding local `B0` nonnegativity witness and call argument were removed.
The bound `B0` itself and every bound passed to the compact scalar estimate are
unchanged.

The first focused check stopped at a pure parser/layout failure in the
parenthesized source-scalar term: a `letI` chain there requires explicit
semicolons.  The chain now uses semicolons, with the higher-grade instance proof
parenthesized; this changes neither the statement meaning nor the proof body.

The second focused check exposed three local elaboration shapes, now repaired
statically: the compactness binder installs `P.topology` before elaborating
`IsCompact K`; `ConvOut.lower_of` uses its actual Unicode parameter name `Φ`;
and the local `delta` definition is unfolded with `dsimp only` before applying
`div_mul_cancel₀`.  None changes the mathematical hypotheses or conclusion.

The parser/layout, named-argument, local-definition unfolding, scalar-rewrite,
finite-sum, and completeness-instance risks are all discharged by the final
warning-free focused check.

The moving-point theorem was focused-checked warning-free GREEN.  No named
refresh was run while the parallel P2 lanes were active.  Its first draft used
the special clock `T - s`; the verified public statement instead takes an
arbitrary `tau`, matching the current regularized-action consumer.  Early local
failures were instance-shape issues only: the generic pointed manifold carries
topology but no uniformity, and product uniformity has a propositionally equal
product topology.  The final statement therefore takes a compatible
pseudometric and the proof transports compactness/continuity only at the
Heine--Cantor step.

## Progress

- `ConvOut.scalar_convOn` theorem endpoint: 100% implemented and verified;
  exported artifact fresh.
- `ConvOut.scalar_compOn` theorem endpoint: 100% source-implemented and
  warning-free focused verified; exported artifact awaits a coordinated refresh
  only when its downstream consumer imports it.
- Dedicated compact-by-time scalar-convergence machinery: 100% implemented and
  verified.
- Full confined action convergence remains open; this scalar producer is one
  input and does not by itself prove that endpoint.
- Gaussian tightness/no-mass-loss is unaffected and remains a separate P2b
  producer frontier.
- Compact ordinary-flow P2a: 100% (unchanged).
- Whole P0--P9 infrastructure: about 15--25% (unchanged).
