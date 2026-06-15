# MetricPreconvWindowSolutions.lean

## 2026-06-13

Stopped per user request before continuing into refactor work.

Current result: the producer-shape route is mathematically viable through the
main analytic seams, but the final endpoint currently exposes a Lean
elaboration/performance blocker.

Verified before adding the final endpoint: the new file focused-checked with
the following pieces in place:
- `SolCovData`, `SolLipData`, and `SolSwapData`;
- `covZeroBdd`;
- `covBddAllSol`;
- `hgLip0Sol`, using `hevComp_of_solutions (N := 0)`;
- `hgLipFinSol`, taking the finite maximum over orders `a <= p`.

Added after that verified point:
- `SolLip0Data`;
- `SolLowData`;
- `denseIccSeq`;
- `winGInfOfSol`, the intended `windowGInf` assembly theorem.

Current blocker: focused checking the file times out at the declaration of
`winGInfOfSol`, at `whnf`, even after bundling the heavy swap, zero-order
Lipschitz, and lower-bound inputs and increasing the local heartbeat ceiling.
The timeout is at theorem elaboration/normalization rather than a mathematical
counterexample or failed proof obligation.

Interpretation: this is likely a refactor/business issue around endpoint
statement shape.  The next clean step is to reduce the public endpoint surface
with a single theorem-facing solution-window data package and/or a named
window-convergence conclusion predicate, then re-export a readable wrapper only
if Lean can elaborate it cheaply.

Verification: final focused check failed on the `winGInfOfSol` timeout.  No
targeted build or axiom checks were run after this blocker.
