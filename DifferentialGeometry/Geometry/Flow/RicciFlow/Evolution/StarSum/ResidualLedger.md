# ResidualLedger

## Purpose

This lower module owns the arbitrary-dimensional constructor-cost recurrence
shared by the time recursion and the final residual package.  Moving the ledger
below `TimeRecursion` avoids an import cycle while preserving the public names
`rmGammaCost`, `rmResidualCost`, and their nonnegativity lemmas.

## Status

The module passes focused verification.  Its generated artifact is newer than
the source; the original targeted wrapper timed out after spawning Lean, so the
downstream exact refresh remains the authoritative end-to-end check.

The ledger itself is 100% checked infrastructure.  It does not prove
`residualStarCosted`, which remains theorem-level 0% until the generic successor
and solution-only capstone are assembled.
