# UnifRhsConvex

## Route

`rhs0_h1_of_unif` and `rhs1_h2_of_unif` feed one `IsConvexJetUnif` packet into
the extracted `rhs0_h1_of_conv` and `rhs1_h2_of_conv` cores.  This fixes the
quantifier order of the convex `H2`/`H3` path constants while preserving the
exact metricwise coefficient functions returned by each RHS assembly.

`rhs1_h2_unif` now closes the stronger order-one face.  It selects the convex
packet and the uniform Ricci/Lie coefficient functions before the class metric,
then reuses the public `rhs1_h2_of_aux` assembly.  Its coefficient functions are

```text
B0 R = 4 * Br0 (C2 * R) + 2 * Bl0 (C2 * R),
B1 R = 4 * (Br1 (C2 * R) * C3) + 2 * (Bl1 (C2 * R) * C3).
```

`rhs1_path_unif` is the class-first path-integral endpoint for the same
order-one coefficient.  It retains exactly these two functions before the
class metric varies, calls `rhs1_h2_unif` pointwise along the realized path,
and passes the resulting bound through `path_jetL2_le`.  No extra constant is
chosen, and its public class assumptions still consume metric jets only through
order three.

The two `_of_unif` compatibility adapters remain deliberately narrower and
retain metricwise witnesses.  The new order-one theorem no longer has that
leak.  The corresponding order-zero theorem is still blocked by class-first
DeTurck-Lie coefficient producers, beginning with the DLa pointwise grid.

## Verification and accounting

Focused verification and direct export passed without warnings or `sorry`
after both `rhs1_h2_unif` and `rhs1_path_unif` were added.  Temporary axiom
censuses for the compatibility adapters and both new class-first endpoints
reported only `propext`, `Classical.choice`, and `Quot.sound`.

The class-first order-one RHS coefficient and its path-integral wrapper are
both verified and 100% locally.  The class-first order-zero RHS theorem, the
joint tame producer, and
`lowreg_bounds_unif` remain unstated (0%); `ricci_flow_unif_existence` remains
unproved (0%).  Dedicated uniform-existence machinery is approximately 99%;
the whole HCG compactness project remains approximately 3% complete.

## 2026-08-06 class-first order-zero closure

`rhs0_h1_unif` now selects the convex packet and the uniform Ricci, `DLa`, and
five-piece tail coefficient functions before the class metric varies.  It uses
the public supplied-parts assembly `rhs0_h1_parts`; it does not call either
metricwise existential adapter.  Its affine functions have the form

```text
B0 R = 4 * (R0 R + D0 R + T0 R),
B1 R = 4 * (R1 R + D1 R + T1 R).
```

`rhs0_path_unif` transports the same functions through the canonical interval
integral.  Both declarations are focused-green, directly exported, and their
axiom censuses contain only `propext`, `Classical.choice`, and `Quot.sound`.
The obsolete global heartbeat option was removed after the file remained green
at the default setting.

The order-zero coefficient and path endpoints are each 100% complete.  The next
theorem is the class-first remainder assembly; it, the dense tame transport,
`lowreg_bounds_unif`, `lowreg_dt_unif`, and `ricci_flow_unif_existence` remain
separate 0% theorems.  Dedicated uniform-existence machinery is approximately
99%; whole HCG closure remains approximately 3%.
