# Restriction of scalar-source weak equations

## Result

`srcEq_restrict` lowers an actual scalar-source `H₀¹` weak equation from an
open domain `Omega` to any open subset `W ⊆ Omega`.  Its coefficient is the
existing native `EllipticCoeff.restrict`, and its solution witness is the
existing `MemW1pWitness.restrict`; the source remains the same function and the
conclusion integrates it on `W`.

## Native route

The missing bridge was not coefficient restriction: `EllipticCoeff.restrict`,
`MemW1pWitness.restrict`, and weak-partial restriction were already present.
The missing generic step was the reverse test-function movement.  A test in
`H₀¹(W)` is extended by zero to `Omega`; its original compactly supported
smooth approximation sequence is reused, so no compactness assumption on
`closure W` and no new solution predicate are needed.  Indicator identities
then identify both the restricted bilinear form and the restricted source
integral with their large-domain counterparts.

The prior localization API only supplied this route for metric balls.  That
ball-specific theorem was used as a proof-shape reference; the new theorem is
stated directly for arbitrary nested open sets and uses only project-native
APIs.

## Verification

The first two focused checks reached only the explicit zero-extension gradient
component lemma.  The first compared a whole-space cast against an already
restricted witness.  The initial repair reversed that order in the proof, but
the definition itself still constructed a whole-space cast and restricted it
afterward, so the second check exposed the remaining cast/restrict mismatch.

The definition and proof now both mechanically follow the already checked
ball-localization template in `External/DeGiorgi/Localization.lean`: the
real-exponent zero extension is restricted to `Omega` first, and only then is
the exponent simplified from `ENNReal.ofReal 2` to `2`.  No compatibility lemma
or public wrapper was added.

Final focused verification passed without warnings.  The explicit named module
refresh also passed, so downstream nested-domain induction may consume the new
export without a stale artifact.

## Project position

- `srcEq_restrict`: stated, proved, focused-verified, and refreshed.
- All-order nested-domain regularity: still a separate theorem endpoint; this
  file supplies only the exact equation-restriction producer needed by its
  induction.
