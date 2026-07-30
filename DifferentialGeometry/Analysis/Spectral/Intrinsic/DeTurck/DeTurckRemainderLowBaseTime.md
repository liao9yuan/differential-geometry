# DeTurckRemainderLowBaseTime

## Role

This module is the time-realization sibling for the uniform low-regularity
Ricci--DeTurck split.  It must extend the same canonical smooth-core A2 and A1
formulas; it must not reintroduce the principal-only decomposition as an
additional second-order action.

## Current state

- `lowRadial` symmetrizes a smooth representative and retracts its spectral
  H2 image to a fixed small ball.
- The embedding identity, ball bound, fibrewise symmetry, and H2
  nonexpansiveness are proved.
- `lowRadialHs` is the canonical total H2 extension.  Its core identity,
  one-Lipschitz estimate, continuity, radius bound, and
  almost-everywhere-strong-measurability composition transfer are proved.
- `lowRadial_h3_eq` identifies the same smooth radial representative with
  the project-native lower-scale cutoff for the spectral inclusion
  `H3 -> H2`.
- `lowRadial_h3_sub` proves the radius-free mixed H3/H2 difference bound:
  the H3 endpoint norms occur only as tame factors and no H3 ball or H3
  smallness is assumed.
- `lowRadialH3` is the total H3 state map obtained from that locally
  Lipschitz smooth core.  Its continuity, exact smooth-core value, and the
  same global mixed H3/H2 difference estimate are proved.
- `lowRadialH3_le` proves that the H2-measured cutoff does not increase the
  H3 norm.  This is the passenger bound used when a two-state A2 coefficient
  difference acts on one radial H3 endpoint.  No additional H2 norm lemma is
  needed: `lowRadialHs_norm` already gives the stronger cutoff-radius bound
  consumed by the A1 telescope, while `lowRadialHs_lip` controls differences.
- `lowRadialH3_incl` proves that total H3 radialization commutes with the
  spectral inclusion to H2, so both adjacent operator scales see one state.
  `lowRadialH3_aemeas` transfers almost-everywhere strong measurability for
  H3-valued time states, and `lowRadialH3_norm` proves that the radialized
  state lies in the selected H2 ball.
- The smooth, H2-total, and H3-total radial maps all fix zero, which gives the
  fixed-point nonlinearity its exact affine value at the origin.
- `dense_ext_lip` is a private bridge from an ambient pairwise distance
  estimate on a dense subtype to the canonical `dense_lipschitz` extension
  API.  It is shared infrastructure for the later A2 and A1 extensions; it
  does not assert either coefficient estimate.
- `exists_lowRadius` supplies one positive H2 radius and one common
  `δ ≤ 1 / 3` realizing fibre-smallness for every smooth state in that ball.
- `lowCoreData` evaluates the canonical same-background low-base coefficient
  bundle on the radial core, and `lowCore_split` proves its exact zero-based
  smooth remainder split.
- `lowA2Hi` and `lowA2Lo` are the canonical `Dense.extend` maps from the
  spectral `H2` state space to the completed `H4 → H2` and `H3 → H1`
  operators.  They use the two existing `A2` projections of the same
  `lowCoreData`; no second coefficient selector is introduced.
- `lowA1Hi` and `lowA1Lo` use the spectral `H3` state topology, with dense
  cores built from `highCore` and `highRep`, and take values in the completed
  `H3 → H2` and `H2 → H1` operator spaces.  Exact private core-value lemmas
  identify all four cores with the corresponding projections of
  `lowCoreData`.
- The total maps are now defined, but their dense-core read-off, continuity,
  adjacent-scale commuting squares on all completed states, and
  almost-everywhere-strong-measurability composition are intentionally not
  asserted yet.  `Dense.extend` needs actual state-variable continuity for
  those facts: the A2 proof waits on `c2_pair_lip`, and the A1 proof waits on
  the final C0/C1 pair theorem.  Static boundedness alone is not a substitute
  for either pairwise producer.

Focused and exact verification are GREEN for the current source, and the
static frontier audit is clean.  The radial core uses the project-native
spectral embedding, slot symmetrization, Hilbert-ball retraction, lower-scale
cutoff, dense Lipschitz extension, and continuous-composition measurability
APIs; it introduces no all-order Sobolev ball or high-state smallness.

## Project accounting

- `ricci_flow_unif_existence`: unstated and unproved (0%).
- Dedicated uniform low-base machinery: about 98%.
- Time realization in this module: about 60%; the total H2 and H3 radial
  state maps and the four correctly-topologized operator extensions are
  defined, while only the radial maps currently have verified
  continuity/core/measurability bridges.  The operator-map pair estimates,
  completed-state commuting squares, and measurable time families remain the
  next producer-dependent brick.

## 2026-07-29 frozen-passenger bridge

- `symmHs` is the canonical contraction extending smooth tensor
  symmetrization at every nonnegative Sobolev order, and `symmHs_incl` proves
  it commutes with Sobolev inclusion.
- `radialScale` freezes the lower `H2` cutoff scalar; `radialCLM` is the
  resulting linear passenger operator. It has pointwise and operator norm at
  most one and commutes with every Sobolev inclusion.
- `lowRadialH3_eq` and `lowRadialHs_eq` identify the two pre-existing total
  radial maps with low-scale cutoff and ordinary ball retraction after
  spectral symmetrization.
- `radialCLM_h3` and `radialCLM_h2` prove that self-application of the frozen
  passenger recovers those canonical nonlinear radial states.
- `radialCLM_aemeas` proves the operator family is a.e. strongly measurable
  along a measurable lower-state path. It deliberately does not claim the
  scalar selector is continuous at zero.

Focused verification and the targeted exact refresh, including the
measurability export, are GREEN. Time realization is about 75%: the remaining
producer-dependent work is continuity/compatibility of the total A2/A1
coefficient maps and their combined time family. The final uniform existence
theorem remains 0%.
