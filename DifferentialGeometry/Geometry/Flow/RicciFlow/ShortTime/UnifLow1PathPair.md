# Class-first diagonal first-order path pairing

## Status (2026-08-08)

`low1_pair_h4_unif` proves the quantitative diagonal D1 estimate

```text
2 |<L^2 T, L(D1(T) nabla T)>|
  <= C0 H4 H3 + C1 R H4^2
```

with `C0`, `C1`, and the coefficient-radius cap order selected before the
class metric varies.  It combines `rhs1_path_unif` with the class-first
`appCc_h23_h2_unif`, then uses the exact spectral interpolation
`H3^2 <= H2 * H4`.  No high-state radius or fourth varying-metric jet enters.

`low1_pair_abs_unif` selects a positive class-first `H2` cap for every
`eta > 0` and absorbs the quantitative bound into

```text
eta * H4^2 + G * H3^2.
```

Focused verification passed.  The diagonal D1 pairing cell is 100% complete.
This does not separate D0 from its top cancellation: the combined D0/top
directed-Green residual remains the genuine unstated frontier (0%), and
`lowbase_full3_unif` itself remains unstated (0%).  The rounded dedicated Route
(c) machinery remains approximately 92%; theorem `(N)` remains 0%, and the
whole HCG compactness project remains approximately 3%.
