# HeatEarlyFlux

## Verified producer

`HeatEarlyFlux.lean` proves the near-cylinder part of the early
`Y¹ -> L∞` heat-potential estimate for a divergence source.

- `lintegral_enorm_le_sqrt` is the finite-measure `L² -> L¹`
  Cauchy--Schwarz inequality in the ENNReal form used by rough cylinder
  masses.
- `earlyFluxCyl_volume_le` bounds an early half-cylinder by its exact
  parabolic volume scale `(sqrt t)^(n+2)`.
- `earlyFlux_l1` and `earlyFlux_l1_scale` turn `GradCarl` control into local
  `L¹` mass and prove that its scale is exactly `(sqrt t)^(n+1)`.
- `halfScale_cancel_succ` cancels that scale against the first spatial
  derivative of the heat kernel.
- `heatD1_early_near` is the concrete fixed-scale Gaussian bound on the
  near cylinder.
- `heatEarly1Near_norm` bounds the actual Bochner potential by
  `ofReal ||w|| * earlyFluxC(V) * C^(1/2)`, uniformly in the observation
  time.

The focused Lean check passes with no warnings. The source contains no
`sorry`, `admit`, axiom, opaque replacement, new class, instance, or notation.

## Honest frontier

This file is the near-cylinder atom, not yet the full early divergence
potential. The next producer must use the existing quantitative finite-ball
cover to bound every spatial shell by finitely many translated copies of this
atom, retain the first-derivative Gaussian factor, and sum the resulting
polynomial-times-exponential series. After that, `KLSource1.local_l2` converts
the squared radius to its stated `A₂` bound.

The exact theorem `ricci_flow_forward_unique` remains 0% until the complete
heat map, harmonic-map heat-flow gauge, Ricci--DeTurck uniqueness continuation,
and gauge removal are proved. `ricci_flow_unif_existence` also remains 0%.
