# RHSZeroRefold

## Mathematical conclusion

The source now states the exact no-high-regularity factorization of the actual
order-zero Ricci--DeTurck path coefficient:

`rhsLow0Coeff(T) = rhsRefold0(T) + rhsRefold2(nabla^2 T)`.

The Ricci part uses the Palatini identity for the difference of the Riemann
coefficient.  Its lower coefficient contains the background Riemann term,
the `AA` commutator, the background-curvature commutator, the sharp-gradient
Koszul residual, and the Ricci fold remainder.  The removed second derivatives
enter `2 * riemannPalatiniRefoldC2Family`.

The DeTurck covariant-derivative part is refolded through the public pair-trace
core, while its endomorphism arm and `lieCorr0` remain genuinely order zero.
The resulting C2 coefficient is the sum of the Ricci and DeTurck refold
families.  The statement assumes metric symmetry and the small fibre bound,
but no high Sobolev order or high-jet radius.

## Verification

The theorem has not yet reached Lean elaboration because several unrelated
shared `.olean` artifacts are missing.  Its moving pair-trace dependency has
been separated from the Sobolev residual grid, and the generic output-slot
permutation module is focused-green.  Verification still stops in the
transitive cache at missing `TensorRSChartFiberOpNorm.olean`.  Therefore this
is source-level progress only, not a verified theorem.  No `sorry` or `whnf`
is present.

Once the cache is restored, check `RefoldPairingCore.lean` first and then this
file.  The first real proof error, if any, should be treated as the next local
frontier.
