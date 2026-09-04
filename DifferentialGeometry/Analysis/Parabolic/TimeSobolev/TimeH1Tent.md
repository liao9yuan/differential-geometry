# Tent variations in time H1

## Native API audit

`timeH1.ofContDiffOn` realizes globally `C¹` curves and therefore cannot
directly realize a genuine tent whose two one-sided slopes differ at the node.
`timeH1.slice` restricts and translates an existing `timeH1` curve but does not
construct a shared-node variation.  `ActionEuler` uses smooth fixed-endpoint
variations and contains no generic piecewise-affine test producer.

The lowest natural home is consequently the generic
`Analysis/Parabolic/TimeSobolev` layer.  The construction uses `timeH1.mk` and
Mathlib's native `MemLp.piecewise` for the two constant slopes; it does not add
a geometric wrapper or assume a momentum condition.

## Result

`timeH1.tent T c z` is the piecewise-affine path which is zero at times `0`
and `T` and takes the value `z` at the interior node `c`.  The API records its
piecewise formula, its two almost-everywhere constant slopes, and its initial,
node, and terminal values.

The scalar `timeH1.trapezoid L r` is the normalized sum of the tents with
nodes `r` and `L-r`.  Under the weakest geometric hypotheses `0 < r` and
`2*r ≤ L`, `trap_left`, `trap_mid`, and `trap_right` identify its two affine
ramps and constant middle plateau.  `trap_deriv_sq` gives the exact derivative
energy `2/r`, while `trap_defect_int` gives
`∫ (1 - trapezoid²) = 4*r/3`.

This normalization is exact: multiplying the sum of the two tents by
`(L-r)/L` produces slope `1/r` on the left, value `1` on the middle interval,
and slope `-1/r` on the right.  No additional strict inequality beyond
`2*r ≤ L` is needed, so the degenerate zero-length plateau at `L = 2*r` is
included.

## Strong-limit consumer audit

`timeQuad_strong` already supplies the fixed-coefficient continuity required
when smooth approximations converge strongly to this trapezoid.  Specializing
both coefficient families to the same essentially bounded operator makes the
uniform coefficient-convergence premise immediate; strong `timeH1`
convergence passes to strong `timeL2` convergence through `toTimeL2`.  A second
quadratic-continuity wrapper would therefore duplicate existing API.

## Verification and project position

The original tent API passed focused verification without warnings.  The new
trapezoid source has been written and statically reviewed.  Its first focused
check failed only on local coercion and rewrite shapes: the Lp scalar-multiple
lemma had been instantiated before exposing the derivative of a sum, a.e.
derivative equalities needed explicit pointwise transport through norm-square,
the polynomial integral theorem needed its root name, and the reflected
interval endpoints needed explicit normalization.  Those five local issues
were repaired statically.  The second focused check narrowed the remaining
failure to two mechanical issues: the Lp sum equality was still hidden under
pointwise scalar action, and one outer rewrite bracket was missing in the left
energy calculation.  The third focused check showed the final two layers of
the same issue: pointwise function addition still needed `Pi.add_apply`, and
the nested rewrite brackets had to be closed on separate lines.  Both are now
repaired statically.  The fourth focused check left only six unused-simp
warnings and the same separated-bracket repair in the analogous right-energy
calculation; those mechanical issues are now repaired statically.  The next
focused check then reached only the elementary right-interval length identity
`L - (L - r) = r`; terminal ring normalization closed it.  The final focused
check passed without warnings.  These were routine local proof-shape issues,
not a mathematical, statement, or missing-API obstruction.  No targeted module
refresh was run.  The source adds no `sorry`, `admit`, axiom declaration,
class, or notation, and all public names are within the twenty-character limit.

This requested generic tent producer is complete (100%).  It provides all of
the test-function infrastructure for a two-segment shared-node first-variation
argument, but it proves no corner condition itself.  The Perelman
momentum-matching theorem remains unstated and therefore 0% complete; dedicated
L-geometry machinery remains roughly 86% complete, while `exists_lMinimizer`
remains 0%.  The separate P2a endpoint `redVolume_anti` is now 100% complete.

For the P2b endpoint-ramp lane, the trapezoid theorem and its dedicated scalar
integral machinery are verified complete (100%).  The geometric
`ricci_int_end_le` theorem is still unstated and therefore 0%, and the full
changing-distance theorem also remains 0%.  This local scalar producer is
below 1% of P2b and of the whole Poincare formalization program.
