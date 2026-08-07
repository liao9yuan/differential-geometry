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
- `radialA1HiBg_pair` (2026-08-07, focused check GREEN first run, no
  warnings): the ARBITRARY-background analogue of `radialA1Hi_self`, from
  `a1Hi_bg_pair hDim g gB`.  The scalar envelope factors exactly as designed:
  with `R2 := C2·ρ`, `A3 := C3·r`, `L := 1 + (1/ρ)·r`, the self/bounded/first
  groups `Fs := Bs R2·(1+A3²)·(C3·L+C2+1)`,
  `Fb := B0 R2·C3·L + B1 R2·C2 + B1 R2·A3·C2 + B1 R2 + B1 R2·A3`,
  `F1 := O0·C3·L + O1 + O1·A3` combine into `E0 := 2·(Fs²+Fb²) + F1²`,
  `K := Ca·√E0`, and the full radicand factors as `E0·D²`
  (`D := ‖H3(T) − H3(U)‖`) before the existing `sqrt_scale`.  The core refold
  is `simpa only [lowCoreDataBg, T0, U0] using hout` with both core terms at
  `g gB`.  The metricwise high-A1 core pair is therewith complete.

Persistent-LSP diagnostics, the focused check, and the targeted module refresh
are GREEN.  The module contains no `sorry`, `admit`, axiom declaration, `whnf`,
or trace option.

With the updated memory-controlled workflow, the initial file load took about
78 seconds.  Saved proof steps then re-elaborated in roughly 0.2--2.6 seconds.
Adding the public `TimeA1` import correctly triggered the stale-import guard;
`Restart File` refreshed only that direct upstream and retained the same
server.  The wrapper closed the single file worker before the 41-second,
two-thread focused check, so LSP and focused elaboration never overlapped.

- `lowA1Bg_comm_bg` (2026-08-07, focused check GREEN first run): the
  ARBITRARY-background completed inclusion square, mirroring the diagonal
  `lowA1Bg_comm` density skeleton with the smooth-core square supplied by
  the new bundle-generic `a1_comm`
  (`DeTurck/DeTurckRemainderLowBaseA1Comm.lean` — see its note for why the
  Lip monolith was NOT edited: its re-elaboration exceeds the focused-check
  memory budget; the identity was re-assembled from the public
  `a1_pair`/`a1_h3_h2`/`a1_h2_h1`).  After the two `_core` rewrites the
  goal IS `a1_comm`'s statement — no refold needed.

## Remaining frontier

The arbitrary-background A2/low-A1 packet, the same-background high-A1
completion packet, the metricwise high-A1 core pair
(`a1Hi_bg_pair` + `radialA1HiBg_pair`), AND the arbitrary-background
inclusion square (`lowA1Bg_comm_bg`) are now closed.  Next in order:

1. The genuine A1 frontier is CLASS-FIRST: one common radius and affine
   constants chosen before `g` varies, for the ACTUAL `lowCoreDataBg` arms.
   `refold_aff_bg` is NOT a substitute — its core formula is
   `c0CoreData + oneCoreBg`, and no theorem identifies that with the required
   actual background core.
2. A2 stop condition (standing): do NOT claim a class-3 canonical high-A2
   producer in this architecture.  `lowA2HiBg : H2 → (H4 →L H2)` needs a
   uniform spectral-H4 ↔ covariant-jet4 comparison; squaring the rough
   Laplacian differentiates its zeroth-order coefficient twice (`∇²Rm` in the
   commutator) ⟹ metric jet 4.  Honest options: (i) move the lane to class 4
   (`covsum_hs_four`, then `appD2Hs_norm_unif`) or (ii) keep class 3 via a
   substantial differentiated parabolic bootstrap for `∇u`.  No structure /
   assumption wrapper / opaque certificate may hide this.

## Progress accounting

- `ricci_flow_unif_existence`: endpoint theorem remains unproved, **0%**.
- Fixed-background smooth radial split: **100%**.
- General-background completed A2 Lipschitz pair and compatibility: **100%**.
- General-background completed low A1 continuity/measurability: **100%**.
- Same-background completed high A1 continuity and compatibility: **100%**.
- Metricwise high-A1 core pair (`a1Hi_bg_pair` → `radialA1HiBg_pair`):
  **100%** (this session).
- Arbitrary-background completed inclusion square (`a1_comm` →
  `lowA1Bg_comm_bg`): **100%** (this session).
- `IsBgLiftAt` existence producer: **0%**.
- Dedicated uniform-existence machinery: approximately **80%**; the endpoint
  theorem itself remains unstated here and unproved.
