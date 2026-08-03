# LowRegBgA1Pair

## Role

This sibling integrates the sharp coefficient pairs and packages both the
arbitrary-background low `H2 -> H1` action pair and the same-background high
`H3 -> H2` action pair needed for completion.

## Current state

The arbitrary-background low first-order pair and the same-background high
first-order pair are complete.

- `bg0_pair_h1` integrates the moving-metric background correction and gives
  its sharp one-jet pair estimate.
- `c0_bg_pair_h1` combines that correction with the intrinsic zero-order pair.
- `rhs1_bg_pair_h2` proves the full pointwise Ricci--DeTurck order-one pair for
  an independent background metric.
- `c1_bg_pair_h2` integrates the order-one pair along the realized path.
- `a1Lo_bg_pair` feeds the resulting one- and two-jet coefficient radii into
  the existing `a1Lo_diff` completion theorem.  Its state inputs stop at H3;
  no fourth jet or high-state smallness is used.
- `a1Hi_self_pair` combines the same-background `c0_pair_h3` estimate with
  `c1_bg_pair_h2` specialized to `gB = g`, then applies the common `a1_diff`
  completion theorem.  Both coefficient differences are controlled in H2,
  so the resulting operator is genuinely `H3 -> H2` and still has no H4
  state input.

Persistent-LSP diagnostics, the focused check, and the targeted module refresh
are GREEN.  The file contains no `sorry`, `admit`, axiom declaration, `whnf`,
or trace option.

2026-08-02: after the `LowRegBgC0Pair` capstone restoration (this module's
`bg0_pair_h1` consumes `lie0_bg_pair_h1`), the targeted module refresh is
GREEN again (27 s) with no source change.  During the window when the capstone
was lost, this file was the visible breakage point (`Unknown identifier
lie0_bg_pair_h1` at line 308); nothing here needed fixing.

The updated persistent-LSP loop exposed one stale direct import explicitly,
refreshed it through `Restart File`, and then re-elaborated each saved proof
step in about 0.45--0.9 seconds.  An identical goal query reused the info tree
in 0.23 seconds.  The final focused check took about 41 seconds with two Lean
threads after the wrapper closed the file worker while preserving the server.

## Next consumer

After refreshing this module, use `a1Hi_self_pair` in `LowRegBgTime.lean` to
construct the same-background radial H3-to-H2 action, its smooth-core identity,
continuity, and the adjacent-scale commuting square with the already completed
low action.  The A2 completion in that file is already closed.

`ricci_flow_unif_existence` remains unproved (0%). Its dedicated machinery is
approximately 73%; the whole HCG compactness project remains in the low single
digits.
