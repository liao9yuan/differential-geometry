# DeTurckRemainderLowBaseTimeA2

## Role

This module is the static second-order operator brick in the time-realization
lane.  It shrinks any already realized spectral `H2` ball to the canonical
`c2_h2_small` radius and applies the existing `a2_pair` completion theorem.

## Current state

`radialA2_pair` is stated without a pairwise coefficient assumption.  Its
inputs are only the dimension-three hypothesis and the fibre realization of
one positive `H2` ball.  It returns uniform bounds for the same canonical
radial coefficient on `H4 → H2` and `H3 → H1`, together with their commuting
square.

`radialA2_lip` now shrinks the realized ball against the canonical
`a2_pair_lip` radius and promotes both radial coefficient maps to genuine
Lipschitz maps on the completed `H2` state space.  Its modulus depends only
on the `H2` state difference, with no `H3` or `H4` state factor.  One
returned threshold works simultaneously for every smaller cutoff, so the
eventual A1 and A2 constructions can select one common radius.  At each such
cutoff the endpoint records both smooth-core read-offs and proves the
completed adjacent-scale commuting square by density, using the radius-free
`a2_comm`.

Focused verification and the targeted exact refresh of this threshold form
are GREEN.  The source contains no
`sorry`/`admit`/`axiom`/`whnf`/`trace`.

## Project accounting

- `ricci_flow_unif_existence`: unstated and unproved (0%).
- Dedicated uniform low-base machinery: about 98%.
- Static radial A2 operator realization: 100%; uniform bounds,
  completed-state Lipschitz continuity, smooth-core identities,
  compatibility, and hence measurable composition with measurable state
  paths are available.
