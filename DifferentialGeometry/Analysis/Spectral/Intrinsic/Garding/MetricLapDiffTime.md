# Vanishing moving scalar Laplacian operator

## State — 2026-07-10

Focused and targeted verification pass.

For a smooth realized metric family and a regular time `T`, `lapDiffA2 G T s`
is the actual operator

```text
H²(G(T)) ->L TensorL2 0 0 (G(T))
```

obtained from `Delta_(G(T-s)) - Delta_(G(T))` on the finite spectral core.

The public results are:

- `lapDiffA2_core`: eventual equality with the genuine finite-core action;
- `lapDiffA2_bound`: a support-independent modulus `omega(s) -> 0`;
- `lapDiffA2_zero`: the operator norm tends to zero.

The modulus is `sqrt C * |rho(s)|`, where `rho` is the cumulative order-one
fixed-background metric seminorm.  `metric_c1_tendsto` composed with
`s -> T-s` gives `rho(s) -> 0`.  Absolute value avoids a separate global
nonnegativity API for the supremum.

The final convergence theorem is deliberately norm-valued.  Rewriting it
through `tendsto_zero_iff_norm_tendsto_zero` caused expensive typeclass
synthesis for the full continuous-linear-map type; stating the operator-norm
limit directly is both cheaper and exactly the consumer-facing result.

## Honest progress

- Requested genuine `A2 : H²(gT) →L L²(gT)` with `omega -> 0`: complete
  (100%).
- Ready `H⁰`/strongly-measurable input for `nonaut_strong_exists`: complete
  (100%) via `lapDiffA20_short`.
- Moving conjugate-heat theorem: not proved (0%).
- Perelman no-local-collapsing theorem: not proved (0%).
