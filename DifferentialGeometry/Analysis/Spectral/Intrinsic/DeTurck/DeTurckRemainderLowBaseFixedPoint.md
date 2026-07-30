# DeTurckRemainderLowBaseFixedPoint

## Role

This module is the fixed-background, dimension-three consumer of the low-base
action split.  It assembles the compatible total coefficient maps and radial
states into the autonomous `H3 → H1` forcing used by `partial_sol_tame`.

## Current state

- `lowBaseForce` is the genuine zero-state Ricci--DeTurck remainder lowered
  from its canonical `H2` realization to `H1`.
- `lowBaseForce_core` identifies it with the direct `H1` spectral embedding
  of the smooth zero-state remainder.
- `lowBaseN` combines that affine term with the total low `A2` and `A1`
  actions.  Its two passengers are the compatible total radial states at
  `H3` and `H2`.
- `lowBaseNBall` restricts this total forcing to the `lowerState g 1 R`
  domain expected by maximal regularity while keeping the smaller state
  radius separate from the outer coefficient cutoff radius.
- `lowBaseN_zero` identifies the zero forcing exactly.
- The next proof brick is continuity and the consumer-shaped three-arm tame
  estimate.  Those are not hypotheses of this module: they must be derived
  from the canonical C2 and C0/C1 pair endpoints before applying
  `partial_sol_tame`.
- Radius selection must freeze all pair constants at a positive outer
  `H2` envelope first.  The actual cutoff/state radius is then chosen smaller,
  using `c2_h2_small` for the top arm and the first-order pair constant for the
  high-size-times-lower-difference arm.  This avoids a circular choice from an
  existential radius whose constant was selected simultaneously.
- `lowRadialH3_le` is now verified in the Time layer, so the radial H3
  passenger contributes at most the original top-state norm; no quadratic
  passenger loss is needed in the operator telescope.
- The private `clm_apply_sub_le` records the exact operator/passenger
  telescope used by both action arms.  This local algebra brick is focused
  GREEN and leaves only the geometric pair constants to instantiate.
- `lowBaseN_sub_eq` expands the full affine forcing difference into exactly
  four terms: A2 operator difference, A2 passenger difference, A1 operator
  difference, and A1 passenger difference.  The fixed zero-state force
  cancels algebraically.  This identity is focused GREEN.
- `lowBaseN_sub_le` is the corresponding completed-space norm telescope.  It
  reduces the final three-arm estimate to four operator/radial bounds without
  any additional analytic assumption.  This inequality is focused GREEN.
- `lowBaseN_radial_le` discharges every radial passenger factor using
  `lowRadialH3_le`, the mixed H3/H2 cutoff difference, the H2 radius bound,
  and H2 nonexpansiveness.  The remaining right side consists only of the A2
  and A1 operator norms/differences in the exact shape supplied by the two
  parallel pair endpoints.  This inequality is focused GREEN.
- The same first-order pair estimate is also the route to the later
  same-horizon bootstrap: setting one endpoint to zero and using the uniform
  `H2` radial bound makes the `H3 -> H2` operator norm grow at most linearly in
  the `H3` state.  The older one-state polynomial coefficient estimate alone
  is not sufficient to prove the required time-`L2` operator integrability.
- Before the mixed nonautonomous bootstrap can replace radial passengers by
  the original Duhamel field, the rough fixed-point solution must be shown
  spectrally symmetric and its H2 bound must make the cutoff inactive.  The
  needed honest bridge is an `eq_self` theorem for both total radial maps,
  followed by symmetry preservation/uniqueness for the rough solution; an H2
  ball bound alone does not make radialization the identity.

## Progress

- `ricci_flow_unif_existence`: unstated/unproved, 0%.
- Fixed-background low-base fixed-point assembly: about 15%.
- Dedicated low-base machinery feeding uniform existence: about 98%.

Focused verification passed, including the new smooth-core read-off for the
fixed affine forcing.

## 2026-07-29 frozen operator form

- `lowBaseA u : H3 ->L H1` combines the canonical A2 and A1 coefficient
  operators with frozen radial passengers. It is linear in its passenger;
  only the final dependence on the state `u` is nonlinear.
- `lowBaseN_frozen` proves the exact identity
  `lowBaseN u = lowBaseForce + lowBaseA u u`.
- `lowBaseA_le` bounds the full frozen operator by the sum of the A2 and A1
  coefficient norms, with no loss from radialization or Sobolev inclusion.
- `lowBaseA_aemeas` packages strong measurability of the assembled frozen
  operator family from the two coefficient paths and the radial state path.
  This is the exact measurability input required by the nonautonomous maximal
  regularity consumer.

These statements are focused GREEN and the module has passed a targeted exact
refresh including `lowBaseA_le` and `lowBaseA_aemeas`. The
fixed-background fixed-point assembly is about 35%: the exact operator form
is complete, but the final state-Lipschitz/`MemLp` packet and the
`partial_sol_tame` instantiation still depend on the two geometric pair
endpoints. `ricci_flow_unif_existence` itself remains unstated/unproved (0%);
its dedicated low-base machinery remains about 98%.
