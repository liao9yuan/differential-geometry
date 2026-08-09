# UnifReverseJetTwo

## Purpose

`UnifReverseJetTwo.lean` is the narrow producer for reversing metric jets
through order two.  It keeps the class-Morrey lane below the much larger
order-three Ricci--DeTurck right-hand-side module.

## Public interface (2026-08-05)

- `metric_self_sum` evaluates the intrinsic metric-derivative sum and remains
  public because the order-three producer also consumes it.
- `revJetOneC` and `revJetTwoC` are the explicit reverse-jet coefficients.
- `reverseJetOne` and `reverseJetTwo` prove the individual reverse bounds.
- `reverseJetPack` exposes the common first-order coefficient, the reverse
  second-order coefficient, their nonnegativity, and the three bound predicates
  consumed by the rank-two class Morrey theorem.

The private metric-parallelism and zero-norm lemmas were moved with this API;
no downstream assumptions or new mathematical frontier were introduced.

## Verification

The first focused check reached `reverseJetOne` and failed because the broad
source had obtained `normSq0S_neg` from an undeclared transitive import.  Rather
than duplicate that tensor-algebra fact locally, the narrow module now imports
its canonical low-level home, `Tensor0SMetricIneq`, and uses the qualified
theorem directly.  Focused one-thread verification and the direct targeted
module refresh then passed under the campaign memory guard.

## Project position

This is dedicated infrastructure for the finite-`H²` realization lane.  The
downstream realization package and uniform-existence theorem remain unproved
(0%); this extraction only makes an already proved producer cheaply importable.
