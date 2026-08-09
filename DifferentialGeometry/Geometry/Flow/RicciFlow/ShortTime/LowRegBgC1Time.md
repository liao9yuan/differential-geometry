# LowRegBgC1Time

## Role

This module isolates the path-integrated order-one coefficient `C1` from the
fixed-background low-base action.  This isolation is necessary because the
actual low-regularity state is only in time `L2 H3`: the older complete-A1 time
packet assumes an essentially bounded H3 trajectory and therefore is not the
endpoint input.

## Exports

- `c1_bg_aff` proves the fixed-H2-ball coefficient bound affine in the
  independent H3 state size.
- `c1_bg_time` constructs compatible completed `H3 -> H2` and `H2 -> H1`
  coefficient maps, identifies both on the smooth core, radializes the same
  passenger on both scales, and returns time-L2 certificates with the bound
  `L * ||u|| + sqrt T * Z` along every `u : L2_t H3`.

## Proof route

The local pair estimate uses `c1_bg_pair_h2`, the radial H3 Lipschitz estimate,
and `a1_diff`.  The independent static bound comes from `c1_bg_aff`.  These two
inputs feed the generic dense-extension theorem on each adjacent scale.  A
single smooth-core action formula proves their global commuting square by
density.  The time packet then combines continuity with radial-operator
measurability and `memLp_clm_affine`; no H3 or H4 smallness and no H3-in-time
essential bound is introduced.

## 2026-08-02 API preservation

`c1_bg_time` now retains the affine pointwise bounds for `FHi` and `FLo` that
its proof already obtained from `c1_ext_pair`.  Previously those fields were
discarded after deriving the time-`L²` packet.  This source-only API extension
is awaiting the user-controlled VS Code elaboration together with the combined
refold module.

## Verification

The focused check and named module refresh are GREEN.  Direct axiom inspection
of both public theorems reports only `propext`, `Classical.choice`, and
`Quot.sound`.  The source contains no `sorry`, `admit`, axiom declaration,
`whnf`, or trace.  No root or full-project build was run.

The persistent LSP was effective for proof search: after loading the file,
typical saved-file iterations took roughly 0.2--1.4 seconds.  Reopening after a
direct import-graph change cost about 61 seconds, and the focused verifier still
caught several underconstrained norm metavariables that the LSP diagnostics had
not reported.  Thus LSP materially accelerated the small-step loop but remains
a diagnostic aid rather than the acceptance check.

## Remaining frontier and accounting

The C1 time arm is closed.  The complete A2 packet is also already closed.  The
remaining first-order endpoint wall is the C0 path-integrated time arm: combine
the completed same-background C0 pair with the arbitrary-background
`lie0_bg_pair_h1` correction and obtain the corresponding radius-free
time-integrable completed action.

`ricci_flow_unif_existence` itself remains unproved (0%); its dedicated
low-regularity machinery is approximately 83% complete after this C1 packet.
The whole HCG compactness project remains in the low single digits.

## 2026-08-02 (later pass) — quantifier hoist: `c1_bg_time` → `c1_bg_pack`, GREEN

The public export of this lane is now the **trajectory-free** packet.

- `c1_bg_time` was replaced by `c1_bg_pack`: same statement with the `T` and
  `u : timeL2 H³ T` binders and the `MemLp` / `toLp` / time-square conjuncts
  removed, and the u-free square `∀ x, incl12 ∘ FHi x = FLo x ∘ incl32` added as
  the last conjunct.  Proof is 12 lines: obtain the private `c1_ext_pair` packet
  and re-shape the two core formulas by `simpa only [c1Part]`.
- `c1_ext_pair` stays **private** on purpose: its core formulas are phrased with
  the private `c1Part`, so it is not exportable as-is.  `c1_bg_pack` keeps the
  explicit `{ C0 := 0, C1 := …, C2 := 0 }` record shape that `c1_bg_time`
  already used for exactly this reason.
- The ~120 lines of time-certificate proof that `c1_bg_time` carried are gone;
  nothing consumed them (`refold_time`, the only caller, extracted only the
  commuting square and rebuilt the `MemLp` witnesses itself).

Module docstring updated accordingly.  Focused check + targeted `.olean` build
GREEN; `c1_bg_pack` axiom-clean.
