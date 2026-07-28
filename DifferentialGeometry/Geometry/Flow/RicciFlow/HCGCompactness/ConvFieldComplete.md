# ConvFieldComplete

## 2026-07-27 fixed-window completeness

`ConvOut.complete_at` transfers completeness of the fixed reference pointed
manifold to every slice of a fixed-window limit.  It combines the uniform
sequence lower bound already retained by `ConvOut.lower_of` with
`MetricComplete.complete_of_lower`; no new compactness or convergence
assumption is introduced.

The focused source verification passed without warnings.  This theorem is a
completed infrastructure brick, not the Hamilton compactness endpoint:

- `ConvOut.complete_at`: 100%;
- conditional closed-window flow upgrade `ham3_closed_upg`: 100% and
  focused-green;
- conditional closed-window smooth-CGH package `ham3_closed_cgh`: 100% and
  focused-green;
- `ham3_cgh_limit`: 0%;
- whole-HCG supporting machinery: about 62%.

The former endpoint issue was resolved by deriving the source covariant
estimates from the untruncated buffered Hamilton rescalings, whose regular
time sets contain the closed common window.  `convOut_of_src` now consumes
that package without requiring the restricted flow to be regular at both
carrier endpoints.  The remaining unconditional frontier is the time-zero
`MetricCompactBase`, including its A0-prime arbitrary-center volume-overlap
producer; fixed-scale Perelman noncollapse is not a replacement for that
input.
