# EdgePathBound

## Role

This module is the pointwise bridge from the complete fixed-parameter raw
closed-edge partner bound to its path-integrated formal partner.  It uses the
unit-length path-integral fibre-norm transfer and performs no spatial
integration by parts.

## Current status

- `fiber_path_le` is the private generic transfer cell.
- `edgeTopInt_zero_unif` is the public class-first bound for the complete
  path-integrated raw top partner, uniform in the reference metric,
  permutations, admissible signs, and realized path.
- The theorem is dedicated infrastructure for the short-time raw-top cross
  estimate; it does not itself prove that ShortTime theorem.

## Verification

Focused verification passed without `sorry`.  The direct export refresh also
passed, so downstream ShortTime modules can consume the public bound.
