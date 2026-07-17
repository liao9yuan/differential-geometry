# Covariant tensor metric

## 2026-07-16 squared-norm sign

Added `normSq0S_nonneg`, the canonical nonnegativity projection from the
metric-induced fiber inner product.  This avoids reopening coordinate sums in
downstream square-sign arguments.  Focused verification passed without a new
`sorry`.

This is a reusable tensor-layer producer; its use in the `W` derivative sign
does not count as completion of the no-local-collapsing endpoint.
