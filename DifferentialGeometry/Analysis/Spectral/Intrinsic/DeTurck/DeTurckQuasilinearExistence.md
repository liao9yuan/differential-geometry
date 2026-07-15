# DeTurckQuasilinearExistence

## 2026-07-14: explicit constants-first lifetime

`nemytskii_sol_const` is proved and focused verification passes.  It takes the
mixed Lipschitz constants `C1`, `C2` and a nonnegative budget `D` for
`norm (Nfun 0)` explicitly.  Its positive fixed-point lifetime is therefore an
explicit function of those three inputs.  The previous theorem
`quasilinear_maxreg_solution_of_nemytskii` remains at the same public interface
and is now a compatibility specialization using the existentially chosen
constants and the exact zero-forcing norm.

This removes an `Exists.choose` obstruction from future uniform estimates, but
does not prove C3-uniform Ricci--DeTurck existence.  The current DeTurck
nonlinearity still works at the high Sobolev order
`a = 4 * finrank E + 10`; order-at-most-three metric bounds do not control its
zero-forcing norm or mixed constants uniformly.  In addition, the current
joint-smooth realization shrinks the maximal-regularity interval to a positive
subinterval with no uniform lower bound.

Honest accounting: the low-regularity Ricci--DeTurck existence theorem is not
stated or proved (0%).  Its dedicated quantitative-input machinery is about
15% across the E1 lane: the fixed-point lifetime now has the right
constants-first interface, and the chart-C3 and family-uniform ellipticity
producers are focused-verified, but
the low-regularity parabolic solver and uniform regularization horizon are the
dominant missing analysis.
