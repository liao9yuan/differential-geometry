# LowRegBgA1Time

## Role

This module is the time-dependent consumer of the completed same-background
first-order action.  It replaces the rejected global affine-growth input of
`liftA1Two_data` with the correct statement: on an a.e. bounded `H3` trajectory,
the high and low coefficient families are uniformly bounded and hence belong
to time `L2`.

## Exports

- `lowA1HiBg_ball` and `lowA1LoBg_ball` pass the two ball-local smooth-core pair
  estimates to uniform bounds for the completed coefficient maps.
- `lowA1HiBg_time` gives strong measurability and time-`L2` membership of the
  completed high coefficient along a measurable bounded trajectory.
- `hiAffA1Bg` and `loAffA1Bg` freeze the canonical radial passenger operators
  on the adjacent `H3 -> H2` and `H2 -> H1` scales.
- `hiAffA1Bg_data` and `loAffA1Bg_data` provide the measurable, time-`L2`, and
  pointwise-bounded packets for those radialized families.
- `affA1Bg_comm` proves their adjacent-scale commuting square at every time.

No smooth representative of a completed state is selected, and no global
state-independent Lipschitz or affine-growth estimate is asserted.

## Verification

Persistent-LSP elaboration, the two-thread focused check, and the targeted
module refresh are GREEN.  The file contains no `sorry`, `admit`, axiom
declaration, `whnf`, or trace option.  Warm LSP changes elaborated in about
0.2--2.8 seconds; reopening the worker after a focused check took about 35
seconds and retained the same persistent server.

## Remaining frontier

Combine this A1 packet with the already completed compatible A2 packet and the
low affine forcing identity, then feed the concrete families to
`lowreg_realize_two`.  The endpoint theorem `ricci_flow_unif_existence` remains
unproved (0%); its dedicated machinery is approximately 76%, while the whole
HCG compactness project remains in the low single digits.
