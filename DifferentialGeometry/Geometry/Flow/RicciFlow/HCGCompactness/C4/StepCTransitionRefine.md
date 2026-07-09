# StepCTransitionRefine.lean

## 2026-07-01, fixed-pair refinement bridge

Added the subsequence-stability bridge needed before the finite Step-C hat
fold can reuse the fixed-pair Step-B transition producer.

Implemented:

- `ExpInverseDerivBoundInput.subseq`: reindexes the `lbl418` exp-inverse
  derivative input along any subsequence.
- `existsTransRefine`: reruns `exists_transitionLimit_normalTransition` after
  an already chosen strict master subsequence and records that the composed
  subsequence remains strict.
- `existsTransFinite`: folds the fixed-pair refinement over a finite family of
  transition pairs, producing one shared strict subsequence and per-pair
  transition limits.
- `existsTransUniv`: specializes the finite extractor to a full finite index
  type and exposes actual endpoint families `Jinf i`, `Jbarinf i`, including
  continuity facts in the shape expected by the decoded-composition averaging
  bridge.

This does not choose finite-hat domains.  It does close the abstract finite
subsequence-alignment part: once the concrete hat layer supplies centers,
domains, overlap containment, and cocycle data for the finite hat index type,
the common transition-limit subsequence and family-valued transition limits are
now produced by `existsTransUniv`.

Verification status: focused Lean check and targeted module build passed.  The
axiom probe for `existsTransRefine`, `existsTransFinite`, and
`existsTransUniv` reports only the usual project axioms.  No new `sorry` or
`admit` occurs in this file.

## 2026-07-08 canonical subseq cleanup

Removed the local duplicate `ExpInverseDerivBoundInput.subseq`; its canonical
home is now `StepBInputs.lean`, where both Step B and later Step C/D consumers
can import it without declaration collisions.  The refinement theorems still
call `ExpInverseDerivBoundInput.subseq`, now resolved through the Step B input
API.
