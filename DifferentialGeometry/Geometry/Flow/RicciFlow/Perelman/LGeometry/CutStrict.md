# CutStrict

## Result

`lMinVec_unique_lt` proves strict pre-cut uniqueness: if `Z` minimizes through
`tau`, `0 < sigma < tau`, and a minimizing `W` reaches the same point at
`sigma`, then `W = Z`.

The proof is native to `DifferentialGeometry`.  It splices the two minimizing
regularized curves, transports the branchwise action while ignoring the single
node, applies finite chart-H1 minimizer regularity to obtain C1 matching at the
node, and propagates the matched phase state back to zero by regularized ODE
uniqueness.

## Verification

Focused verification passed without warnings.  The axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.  The source contains no
placeholder proof.

## Frontier

This closes the immediate strict pre-cut uniqueness theorem.  It does not prove
openness of `lMinDomain`: membership is intentionally inclusive at cut time.
The classical cut alternative at the first non-minimizing time remains a
separate frontier requiring a native limiting/compactness statement for
minimizing initial tangents and the conjugate-point alternative.

Project accounting: `lMinVec_unique_lt` is complete (100%); its dedicated
strict-splice machinery is complete (100%).  The broader cut-alternative
theorem is not yet stated or proved (0%); the existing dedicated minimizing,
splice, ODE-uniqueness, and conjugate infrastructure is substantial but is not
counted as completion of that theorem.
