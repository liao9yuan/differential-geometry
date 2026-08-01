# `LowRegBgTime.lean`

## Role

This module is the thin fixed-background adapter between the intrinsic
low-base action and the existing spectral radial state.  It keeps the frozen
spectral metric `g` and the DeTurck background `gB` as independent parameters.

## Verified brick

- `lowCoreDataBg` evaluates the canonical `lowBaseData g gB` bundle on the
  existing `lowRadial g` smooth core.
- `lowCoreBg_split` applies the public arbitrary-background `lowData_split` and
  gives the exact zero-based smooth Ricci--DeTurck remainder identity on that
  radial state.
- `lowA2HiBg` and `lowA2LoBg` extend the same arbitrary-background second-order
  coefficient to the completed `H2` state space at the adjacent `H4 -> H2` and
  `H3 -> H1` scales.
- `radialA2Bg_lip` supplies one radius and one Lipschitz modulus for both maps,
  their exact smooth-core values, and the commuting square.  Its only geometric
  pair input is the already arbitrary-background `a2_pair_lip`; no new
  background regularity or high-state smallness is introduced.

Persistent-LSP diagnostics are clean.  The focused check and targeted module
refresh are GREEN.  The module contains no `sorry`, `admit`, axiom declaration,
`whnf`, or trace option.

## Remaining frontier

The arbitrary-background A2 pair and completion are now closed.  The A1 pair
producers still specialize `lowBaseData g g`; static general-background C0/C1
bounds do not imply the pairwise modulus needed by `Dense.extend`.  The
smallest honest next producer is therefore the general-background C0/C1 pair
estimate, obtained by pairing the explicit background correction before
completing the two adjacent-scale A1 maps.

## Progress accounting

- `ricci_flow_unif_existence`: endpoint theorem remains unproved, **0%**.
- Fixed-background smooth radial split: **100%**.
- General-background completed A2 Lipschitz pair and compatibility: **100%**.
- General-background completed A1 continuity/measurability: **0%** as a stated
  theorem; its diagonal coefficient/action bounds are verified.
- Dedicated uniform-existence machinery: approximately **74--76%**.
