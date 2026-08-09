# UnifGagliardoNirenberg

## Class-first producer (2026-08-05)

This module is focused-green without warnings.  It provides:

- `volumeReal_cross` and `volRadius_cross`, the real-volume and volume-radius
  forms of the existing two-sided class measure comparison;
- `volClassC`, one explicit background-class constant controlling both
  `sqrt(vol_g M)` and its reciprocal, including the zero-volume/empty-manifold
  branch without a `Nonempty M` assumption;
- `gnClassC`, the resulting explicit class coefficient; and
- `gn_rs_unif`, the genuine class-first mixed-valence interpolation theorem.

The coefficient is chosen from `gBase`, `Lambda`, dimension, and top order
before the varying metric, valences, tensor, and interpolation rung.  The proof
uses `gn_rs_bound` plus the two-sided volume comparison; it does not introduce a
compactness choice, a metric-indexed package, or a new analytic hypothesis.

An in-source temporary axiom census was run and then removed.  `gn_rs_bound`,
the volume adapters, `gnClassC_spec`, and `gn_rs_unif` depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

The two-arm grid used directly by `appCc_grad_l2` has now been refactored at the
lower layer to expose `gridRsConst` and `grid_rs_bound`; its focused check is
green.  The class wrapper is routine finite-sum monotonicity after that module's
`.olean` can be refreshed.

Correction to the first routing note: `h2_grid_int` and `h3_top_grid_int` do
not consume the two-arm theorem.  They consume GN directly together with a
rank-two pointwise/Morrey bound.  Their common next producer is therefore a
separate positive-order single-tensor grid theorem using `morreyTwoC_spec` and
`gn_rs_unif`; the `k = 0` H2 case remains a volume-only branch.

## Class-first rank-two grid package (2026-08-05)

The distinct single-tensor branch is now explicit and focused-green:

- `rankTwoGridC` and `rank_two_grid_unif` combine `morreyTwoC_spec`,
  `gn_rs_unif`, and `grid_prod_int_le`. The coefficient is fixed from
  `gBase`, `Lambda`, the positive grid order, and the lower H2 radius before
  the class metric and tensor vary. Only varying-metric jets of orders one
  and two are consumed.
- `h2GridC` / `h2_grid_unif` package the orders through two. The order-zero
  case is proved separately from `volumeReal_cross`; it is not forced through
  the positive-order interpolation theorem.
- `h3TopGridC` / `h3_top_grid_unif` retain the tame separation between the
  lower H2 radius and the third-derivative bound.

Focused verification passes without warnings, and the new source contains no
`sorry`. A temporary in-source axiom census for all three grid theorems reports
only `propext`, `Classical.choice`, and `Quot.sound`; the print commands were
then removed. The exact artifact refresh is still blocked by the existing memory
wall: Lake replayed the large dependency graph and entered
`ConnectionDifferenceArmRfnsBound`; the physical-memory guard stopped it at
about 1.1 GB free. That interrupted dependency artifact was restored from the
aligned audit worktree after confirming identical source hashes and the same
Lean toolchain. Do not repeat this refresh without first changing the build or
dependency-memory situation.

The next analytic use is a class-first wrapper around the existing
`grid_h1_le` / `grid_h2_le` finite summations. The separate two-arm grid for
`appCc_grad_l2` still awaits a memory-safe export of its lower explicit
coefficient.
