# LowRegBgRungPack.lean

## Role

`IsLowGateOrdBg g g_bg A B` is the common per-metric envelope for the ordered
background rung-three, rung-four, rung-five, and all-higher witnesses.
`lowregGatePackBg` selects the four certificates coherently for one metric pair.

The scalar inequality `rungGate_le` is independent of both metrics and is
reused from `LowRegRungPack.lean`; no duplicate background theorem is added.

## Uniformity boundary

This package is deliberately metricwise.  Its `A`, `B`, bottom-rung witnesses,
and high-rung witness are selected after `(g, g_bg)`.  It does not establish the
class-first absorptive envelope required later by `lowreg_adapt_unif`, and it
must not be used to choose a common threshold, radius, or lifetime before `g`
varies.

## Verification

After `LowRegBgRungFive.olean` became fresh, the focused four-thread, 6144 MB
check passed without local warnings.  The exact targeted module refresh also
passed.  The source contains no `sorry`, `admit`, `axiom`, or heartbeat
override.

## Accounting

The metricwise gate-bookkeeping brick is complete and verified (100%).  This
closes plan brick 5, but it does not advance the later class-first absorptive
gate theorem, which remains unstated (0%).  `lowreg_loMassBg` and headline
`ricci_flow_unif_existence` also remain unstated/unproved (0%).
