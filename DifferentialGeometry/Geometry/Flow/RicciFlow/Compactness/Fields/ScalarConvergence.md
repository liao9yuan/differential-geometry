# ScalarConvergence

## Role

`ConvOut.scalar_convOn` is the P2b compact-by-time scalar-curvature convergence
producer.  It strengthens the existing fixed-point `ConvOut.scalar_conv_at`
endpoint without adding a convergence assumption: the source is the existing
`ConvOut.conv` two-jet convergence on compact sets.

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

No new class, predicate, notation, or frontier hypothesis is introduced.

## Verification

Source-written and statically reviewed.  Focused verification is intentionally
pending: `RicciFromJetsCompact` must first pass its focused check and receive
the explicitly named artifact refresh, and the shared Lean guard must then be
granted by the P2 coordinator.

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

The most likely local elaboration risks are the final scalar-rewrite direction,
the finite constant sum over `Finset.range 3`, and inference of the local
finite-dimensional completeness instance.  These are expected to be routine
shape issues rather than missing mathematics.

## Progress

- `ConvOut.scalar_convOn` theorem endpoint: 0% verified (source implementation
  exists, but no Lean check has run).
- Dedicated compact-by-time scalar-convergence machinery: about 85% source-ready,
  0% verified until the upstream and this file check.
- Compact ordinary-flow P2a: 100% (unchanged).
- Whole P0--P9 infrastructure: about 15--25% (unchanged).
