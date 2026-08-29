# DistribSupersolution

## Role

This file supplies the coordinate divergence-form producer needed to pass from
distributional Laplacian inequalities to Euclidean weak supersolution tests.
The coefficient is the weighted inverse Gram matrix `ρ g⁻¹`.

## Status

`laplacian_chart_div`, `chart_div_test_le`, and `chart_super_of_lap` passed
focused verification without warnings. The last theorem extends the chain to
the De Giorgi supersolution interface: first for nonnegative smooth compact
tests, then for arbitrary nonnegative `H01` tests by the native positive-test
density theorem and bilinear-form continuity. No weak-gradient compatibility
or variational identity is assumed.

Three earlier focused checks failed only on local elaboration details. The
first found the limit inequality direction, declaration exposure, stable
`simp` normalization, and scalar inner-product notation. The second left the
explicit scalar binder of `HasCompactSupport.fderiv_apply` and two finite-sum
algebra normalizations. The third left one multiplication commutation under a
finite sum. An explicit per-summand proof discharged that residual, and the
subsequent focused check was warning-free GREEN.

## Project accounting

The splitting theorem itself remains 0%; its dedicated machinery is about
35--40%. Whole P1c is about 60--65%, while the whole P0--P9 program is about
15--25%. The final Poincare endpoint remains 0%. These figures keep verified
infrastructure separate from theorem completion: `chart_super_of_lap` is now a
focused-verified producer, not the splitting theorem itself.

## Verification

The static proof uses a smooth global extension of each local coefficient on
the compact test support, weak-coordinate integration by parts with the given
`MemW1pWitness`, the positive scalar coefficient identity, and
`MemH01.nonneg_approx`. Focused verification and the named artifact refresh are
warning-free GREEN.
