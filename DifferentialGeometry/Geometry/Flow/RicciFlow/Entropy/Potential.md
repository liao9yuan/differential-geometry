# Potential

## Verified producer

`Potential.lean` defines `perelmanPotential` directly from a positive scalar
density and proves:

- `density_potential`: for `tau > 0` and pointwise positive `u`, substituting
  the reconstructed potential into `perelmanDensity` returns `u` exactly;
- `weighted_potential`: the corresponding Perelman weighted measure is exactly
  `mu.withDensity (ENNReal.ofReal ∘ u)`.

The proof is entirely scalar.  Positivity of `tau` is used only to prove that
the density prefactor is positive, so the logarithm and cancellation are
legitimate.  No flow, regularity, chart, or nonemptiness assumption was added.

Focused verification passed without a local `sorry`.

## Honest frontier

These two bridge theorems are complete (100%).  They are dedicated W-entropy
machinery, not the W-monotonicity or no-local-collapsing theorem itself.

- W-monotonicity theorem: not yet stated/proved in Lean (0%).
- Perelman no-local-collapsing endpoint: not yet stated/proved in Lean (0%).

The remaining work separates into three genuine classes:

1. potential evolution and regularity: transfer the positive conjugate-heat
   solution through `-log` and prove the spatial/time derivative identities;
2. geometric variation: supply the real moving-metric derivative of
   `|grad f|^2` (and the compatible scalar/Hessian inputs) to the existing first
   variation framework;
3. entropy completion and application: prove the weighted integration-by-parts
   and square-dissipation identity, then the localized analytic estimates that
   turn W monotonicity into noncollapsing.
