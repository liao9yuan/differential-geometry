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
- `BgA1CorePair` records the ball-local H3 smooth-core pair for the independent
  DeTurck background.
- `radialA1Bg_pair` derives that predicate from `a1Lo_bg_pair`; the square-root
  coefficient modulus factors exactly as a fixed nonnegative constant times
  the H3 difference.
- `lowA1LoBg` is the completed H2-to-H1 action on the H3 state space.
  `lowA1LoBg_core`, `lowA1LoBg_cont`, and `lowA1LoBg_aesm` provide its smooth
  value, continuity, and preservation of a.e. strong measurability.
- `BgA1HiCorePair` and `radialA1Hi_self` give the D4-free same-background
  H3 smooth-core pair for the high first-order action.  The radial proof uses
  only H3/H2 differences and factors its coefficient envelope exactly as a
  fixed ball-local constant times the H3 distance.
- `lowA1HiBg` extends that same smooth-core formula to an `H3 -> H2`
  operator-valued map.  `lowA1HiBg_core`, `lowA1HiBg_cont`, and
  `lowA1HiBg_aesm` provide its smooth value, continuity, and time
  measurability.
- `lowA1Bg_comm` proves that `lowA1HiBg g g` and `lowA1LoBg g g` are the two
  adjacent-scale completions of one action.  The completed square is obtained
  by density from the existing smooth `radialA1_pair` square.

Persistent-LSP diagnostics, the focused check, and the targeted module refresh
are GREEN.  The module contains no `sorry`, `admit`, axiom declaration, `whnf`,
or trace option.

With the updated memory-controlled workflow, the initial file load took about
78 seconds.  Saved proof steps then re-elaborated in roughly 0.2--2.6 seconds.
Adding the public `TimeA1` import correctly triggered the stale-import guard;
`Restart File` refreshed only that direct upstream and retained the same
server.  The wrapper closed the single file worker before the 41-second,
two-thread focused check, so LSP and focused elaboration never overlapped.

## Remaining frontier

The arbitrary-background A2/low-A1 packet and the same-background high-A1
completion packet are now closed.  The next frontier is to use the continuous
`lowA1HiBg g g` coefficient in the actual time-dependent high forcing packet;
this must avoid the already rejected demand for a global smooth representative
of an arbitrary completed H3 state.

## Progress accounting

- `ricci_flow_unif_existence`: endpoint theorem remains unproved, **0%**.
- Fixed-background smooth radial split: **100%**.
- General-background completed A2 Lipschitz pair and compatibility: **100%**.
- General-background completed low A1 continuity/measurability: **100%**.
- Same-background completed high A1 continuity and compatibility: **100%**.
- Dedicated uniform-existence machinery: approximately **75%**; the endpoint
  theorem itself remains unstated here and unproved.
