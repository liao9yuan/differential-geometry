# Time H1 density

## Result

`exists_flat_smooth` proves fixed-endpoint strong density for vector-valued time
`H1` curves on a positive interval in a finite-dimensional real normed space.
It returns global smooth functions and their exact `timeH1` realizations.  The
functions agree with the original continuous representative at both endpoints,
are constant on neighborhoods of both endpoints, converge strongly in
`timeH1`, and their realized derivatives converge strongly in `timeL2`.

The existing `exists_flat_dense` statement is unchanged.  It is now the `C1`
compatibility endpoint obtained by lowering the smoothness furnished by
`exists_flat_smooth`.

## Construction

The proof uses `exists_flat_deriv` from `TimeH1Flat` for smooth derivative
approximation.  Its support inclusion in `Ioo 0 T` alone does not imply a zero
germ at either endpoint, so a shrinking interior bump is applied.  The added
boundary-layer error is controlled by `MemLp.eLpNorm_indicator_le`.

A fixed normalized interior bump corrects the total derivative integral.  The
correction tends to zero because the native `timeIntegral` is continuous.  The
corrected derivative is integrated globally, producing a global smooth primitive
with exact endpoint values and constant endpoint germs.  Native
`timeH1.ofContDiffOn` realizes each primitive and supplies exact representative
agreement on `Icc 0 T`.

Smoothness uses `contDiff_infty_iff_deriv`: the primitive is differentiable by
the interval-integral API, its global derivative is the already smooth corrected
derivative `d n`, and the fixed-order `timeH1` constructors use the resulting
`C1` downgrade.  Thus the long approximation proof is not duplicated.

All interval-integral and `timeMeasure` identifications are proved explicitly;
the endpoint correction uses `ContDiffBump.integral_normed`.

## Verification

Focused verification passed without placeholders or diagnostics.  The first
focused pass exposed only explicit-order mismatches at the three `timeH1`
constructors and an ambiguous `∞`; a single local `C1` downgrade and an explicit
`WithTop ℕ∞` annotation resolved them.

## Project status

- Smooth `exists_flat_smooth` producer: 100%.
- Compatibility `exists_flat_dense` endpoint: 100%, with its public statement
  and callers unchanged.
- Downstream `lAction_c1_dense`: 100%, now checked in `ActionDensity.lean`.
- `exists_lMinimizer`: 0% until the minimizer theorem is proved.

For the P2b changing-distance lane, this smooth endpoint-flat density producer is
complete, but the sharp long-distance theorem itself remains unstated and hence
0%.  Its dedicated endpoint-ramp analytic machinery is about 40%; the geometric
index-form/Ricci producer remains the larger frontier.  This module is less than
1% of the whole Poincare formalization project.

This module is analytic infrastructure for the L-geometry density lane.  It
supplies the terminal missing density input but does not itself prove minimizer
existence or reduced-volume monotonicity.
