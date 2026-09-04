# SourceWeakSolution

## Result

- `srcSol_substOn` is proved without `sorry`.
- It takes the actual scalar-source `H₀¹` weak equation with the supplied
  solution witness and substitutes the localized standard Nirenberg test.
- The conclusion exposes the original witness gradient through the same
  explicit difference-quotient integrand as `homSol_substOn`, with right-hand
  side `∫ x in Ω, f x * standardNirenbergTest k h eta u x`.

## Route

The proof reuses `stdTestWitnessOn`, `stdTest_memH01On`, and `stdTest_grad` from
`HomogeneousWeakSolution`.  It applies the supplied weak equation to that test,
then unfolds only `bilinFormOfCoeff` and rewrites the witness gradient.  No new
weak-solution predicate, assumption, or final-identity hypothesis was added.

## Verification

Focused verification and the explicit named export refresh both passed with no
reported warnings.  No broad build was run.

## Progress estimate

- `srcSol_substOn`: 100% as a proved theorem.
- The scalar-source standard-test substitution brick: 100%.
- A scalar-source local `W²` estimate: not stated or proved here, 0%; this file
  supplies only its substitution input.
- The all-order `MemWkp` bootstrap and resulting P1c smooth-representative
  theorem: not stated or proved, 0%; their dedicated local elliptic machinery
  remains roughly 65–70% complete.
- The final P1 splitting theorem remains unstated/unproved, 0%.
