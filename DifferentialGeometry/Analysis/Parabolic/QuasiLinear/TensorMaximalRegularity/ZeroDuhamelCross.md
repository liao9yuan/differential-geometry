# ZeroDuhamelCross

## Result

This module packages the zero-initial maximal-regularity solution as a
cross-scale field.  Its intermediate representative:

- is zero at time zero;
- agrees almost everywhere with the `H^(a+1)` Duhamel companion;
- is strongly measurable for the restricted time measure;
- commutes almost everywhere with subtraction of forcing terms;
- satisfies `||repr t|| <= 2 sqrt(1+T) ||f||`.

## Role

These are precisely the path inputs required to apply an `L2_t` family of
first-order operators through `timeOpL2`.  The module is generic analytic
machinery and does not construct the metric-dependent Ricci--DeTurck
coefficient.

Focused verification passed without local warnings.
