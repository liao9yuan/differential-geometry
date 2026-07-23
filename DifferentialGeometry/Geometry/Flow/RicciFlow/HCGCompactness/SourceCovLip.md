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

The module imports the source-flow/extension foundation in
`ConvFieldAssembly` and reuses the existing explicit order-zero metric bound
`covNorm0_le` from `ConvFieldInputs`.  No duplicate tensor-norm proof is kept
locally.

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

The order-zero case is now checked separately.  `covRic0_le` combines
`covNorm0_le`, metric norm comparison, `nablaRicReal_normSq`, and the order-zero
moving Shi bound into explicit constants independent of the source index.  The
main proof consumes this helper in its `q = 0` branch.

The sole remaining `sorry` is therefore exactly the positive-order
constants-first invariant induction which, for each `q >= 1`, chooses `Cq` and
`Lq` before `k` and proves on every whole source domain both

1. the `gRef`-covariant bound for `nabla^q g(t)`; and
2. the `gRef`-norm bound for the evolution tensor `-2 nabla^q Ric(g(t))`.

This cannot be obtained by invoking the existing per-source compact theorem
after fixing `k`, because that route chooses the constants in the wrong order.
The existing `covOrderBound_of_soln` route cannot be reused directly: its
`ric_tower_const` chooses local Claim-1/Claim-2 witnesses after selecting a
good frame and then uses a finite spatial subcover.  The positive-order route
must instead expose those numeric witnesses before the frame/domain arguments
and apply the resulting per-point estimate with one common constant.

The feasibility choice and requested declaration-level review are recorded in
`SOURCE_COVLIP_CONSULT.md`.  The next implementation gate is a constants-first
Claim-1 declaration whose witness is independent not only of the local frame
but also of the manifold type; no positive-order consumer edit should precede
that gate.

No endpoint assumption or branch-specific field has been added.  Downstream,
`SrcCovLipData.cov` feeds the grow-local `covTail_of_bounds`, while
`SrcCovLipData.lip` feeds both the grow-local and compact-source time estimates.

## Verification and accounting

Focused verification passed with the one intentional analytic-frontier
warning.  The target theorem remains theorem-level 0% until that explicit
positive-order joint estimate is proved.  Its order-zero core and Lean-facing
assembly after the estimate are 100%; the dedicated file machinery is about
50%.  The unconditional
`compactnessSol` endpoint remains theorem-level 0%.
