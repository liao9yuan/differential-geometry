# `UnifInsertH1.lean`

## Purpose

This module packages the cancellation-preserving insertion background
difference into a dimension-three class-first `H1` estimate.  Its public
coefficient is chosen from `(gBase, Λ, δ₀)` before the class metric, moving
metric, and perturbation vary.

## Current state

- `connSec_h1_unif` is source-complete and combines the public uniform
  connection-difference pointwise grid with `h1_low_unif`.
- `insert_h1_unif` is source-complete and follows the checked local insertion
  factorization: moving trace times the fixed lowered connection difference,
  then the moving connection action, slot raising, and the final insertion
  reduction.
- The fixed connection term uses `connFix_h2_unif`; this is the only place the
  third class metric jet is consumed.
- A private self-connection cancellation lemma is used because no canonical
  public `connDiffLoweredCc g g = 0` theorem was found.  It is proved directly
  from the public unit-model evaluation API and introduces no assumption.
- There are no `sorry`s or added frontier assumptions in this module.
- Focused verification and direct export pass without warnings.  Axiom
  censuses for both public theorems contain only `propext`,
  `Classical.choice`, and `Quot.sound`.

## Progress accounting

- `connSec_h1_unif` and `insert_h1_unif`: verified, 100% locally.
- Dedicated class-first insertion machinery: 100% for this arm.
- `lowreg_bounds_unif`: 0%; this module is one producer for that future
  assembly and does not prove it.
- `ricci_flow_unif_existence`: 0%; it remains neither stated nor proved from
  this producer lane.
- Whole HCG compactness project: about 3% on the current honest denominator.

The generic trace call and fixed-connection norm bridge both elaborated in
their intended orientations; no further interface repair was needed.
