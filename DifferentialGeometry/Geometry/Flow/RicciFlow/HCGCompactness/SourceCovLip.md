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

## Frontier

The theorem proof is the one remaining analytic frontier in this file.  It
cannot be obtained by invoking the existing per-source compact theorem after
fixing `k`, because that route chooses the constants in the wrong order.
The intended proof reuses the constants-first `covOrderBound_of_soln` algebra
but must run it uniformly on the varying whole source domains.

No endpoint assumption or branch-specific field has been added.  Downstream,
`SrcCovLipData.cov` feeds the grow-local `covTail_of_bounds`, while
`SrcCovLipData.lip` feeds both the grow-local and compact-source time estimates.

## Verification and accounting

Focused verification passed.  The `SrcCovLipData` interface is dedicated
machinery; `srcCovLip_of_soln` remains theorem-level 0% until its analytic
proof replaces the single explicit `sorry`.
