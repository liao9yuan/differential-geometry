# SourceCovLip

## Role

`SourceCovLip.lean` is the source-native, constants-first analytic interface for
the P4 open-window convergence producer.  It intentionally does not mention a
`BumpFamily`, `gSeqExt`, target collars, or target-side compact sets.

The structure `SrcCovLipData` records two uniform outputs.  For each requested
order, its constant is selected before the varying source index `k`:

- whole-source bounds for `metricCovDerivNorm` throughout the closed window;
- whole-source time-Lipschitz bounds for every lower `metricDerivNorm` order.

The theorem `srcCovLip_of_soln` states the honest producer from a uniform
source-metric equivalence, uniform moving Shi estimates, and one uniform
initial covariant envelope.

The module imports only the source-flow/extension foundation in
`ConvFieldAssembly`; it does not depend on the older consumer-side producer
collection in `ConvFieldInputs`.

## Checked assembly and exact frontier

The outer `srcCovLip_of_soln` assembly is now checked.  Its proof exposes one
local joint invariant-estimate frontier and then completes all downstream
steps:

- the covariant half of the joint estimate fills `SrcCovLipData.cov`;
- the Ricci-evolution half is combined with the checked pulled-back
  `sourceFlow` equation and `hevComp_of_solutions`;
- `timeLipschitz_of_hasDerivAt` gives the estimate at each fixed order;
- a finite sum over `Finset.range (p + 1)` gives one nonnegative constant for
  every order `q <= p`.

The sole remaining `sorry` is therefore exactly the constants-first invariant
induction which, for each `q`, chooses `Cq` and `Lq` before `k` and proves on
every whole source domain both

1. the `gRef`-covariant bound for `nabla^q g(t)`; and
2. the `gRef`-norm bound for the evolution tensor `-2 nabla^q Ric(g(t))`.

This cannot be obtained by invoking the existing per-source compact theorem
after fixing `k`, because that route chooses the constants in the wrong order.
The intended proof reuses the invariant algebra behind
`covOrderBound_of_soln`, but removes its finite spatial-subcover dependence and
runs the induction uniformly on the varying whole source domains.

No endpoint assumption or branch-specific field has been added.  Downstream,
`SrcCovLipData.cov` feeds the grow-local `covTail_of_bounds`, while
`SrcCovLipData.lip` feeds both the grow-local and compact-source time estimates.

## Verification and accounting

Focused verification passed with the one intentional analytic-frontier
warning.  The target theorem remains theorem-level 0% until that explicit
joint estimate is proved; its Lean-facing assembly after the estimate is 100%,
and the dedicated file machinery is about 45%.  The unconditional
`compactnessSol` endpoint remains theorem-level 0%.
