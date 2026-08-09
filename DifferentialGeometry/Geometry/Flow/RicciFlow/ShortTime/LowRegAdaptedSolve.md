# LowRegAdaptedSolve

## 2026-08-05 — calibrated explicit package

This layer joins the exact solve package from `LowRegApplyTwo` with one stored
ordered rung-three certificate from `LowRegRungThree`.

`IsAdaptedLowSolve` carries:

- the exact `IsLowSolveAt` witness tuple and external state cap;
- the same `IsRung3Ord` tuple later consumed by the Fatou/rung proof;
- a positive `ε` and the absorption inequality at the solve's own threshold and
  state radius.

`lowreg_absorb` uses

```
δ = 1 / (16 * (Ctop₂*Kcap + 1))
Rabs = 1 / (8 * (Kr2 + Kr1 + 1))
ε = 1/4
```

to bound the fibre and radius contributions by `1/8` each.  The adapted
producer calls the exact solver at `min Rmax Rabs`, preserving both the endpoint
cap and the absorption cap.

Focused verification passed warning-free, and the targeted module build passed.
This closes only the
per-metric GAP-ADAPTH interface.  Uniform class bounds for the ordered rung
constants remain a separate load-bearing producer for `(N)`.

Honest denominator: `lowreg_loMass` theorem 0%; `(N)` theorem 0%; whole HCG
about 3%.  Supporting machinery remains reported separately.

## 2026-08-05 — common gate and fixed-witness recalibration

`IsAdaptedLowSolve` now stores the complete `IsLowGateOrd` package, its common
ordered envelopes, and the exact solve witnesses used downstream.  The
compatibility projection retains the previous tuple shape.  No rung theorem or
projected trajectory is reselected after calibration.

This package feeds the same-path fifth-rung and generic higher-rung closures, so
the downstream `lowreg_loMass` theorem is now proved (100%).  Focused
verification and the direct module refresh passed warning-free.  The package is
still selected per metric in the self-background theory; the class-uniform
hoist needed by `(N)` remains a separate theorem-level 0% producer.

## 2026-08-05 - non-vacuous adapted producer

`lowreg_adapt_open` preserves the strict operator-floor certificate from
`lowreg_solve_open` while joining the exact solve witnesses to the common gate
package.  The compatibility theorem `lowreg_solve_adapt` still has its previous
statement and simply discards `B2 < 1`.

Focused verification and the targeted module refresh passed warning-free.  The
result gives a genuine positive per-metric window, but the witness tuple is
still chosen after the metric and hence is not the class-uniform producer.
