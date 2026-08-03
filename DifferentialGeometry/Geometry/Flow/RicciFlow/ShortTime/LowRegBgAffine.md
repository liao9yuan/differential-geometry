# LowRegBgAffine

## Role

This sibling assembles the arbitrary-background low affine forcing from the
completed A2 and low A1 actions in `LowRegBgTime`.  It is the low-side bridge
needed when the fixed DeTurck background is `gBase`, rather than the evolving
initial metric.

## Current state

The arbitrary-background low affine bridge is complete.  The public surface
contains `lowBaseForceBg`, its smooth-core realization, the completed forcing
`lowBaseNBg`, its continuity theorem, and the exact dense-extension identity
`lowreg_N_bg_affine` with `lowRegN g gB`.

The identity is proved only on the smooth core before passing to the completed
space by density.  It does not assert that an arbitrary completed H3 state has
an exact smooth representative.  Such a representative need not exist, so the
representative-producer route suggested after `force_hi_smooth` is not a valid
high-side endpoint route.

Focused and targeted verification are GREEN.  The file has no
`sorry`/`admit`/new axiom or diagnostic placeholder.

## Progress

`ricci_flow_unif_existence` remains unproved (0%).  Dedicated machinery is
approximately 72% complete, while the whole HCG compactness project remains in
the low single digits.  This module closes the arbitrary-background low side;
it does not instantiate the adjacent-scale lift.

The next genuine frontier is the high A1 completion.  Its missing input is a
D4-free H2 pair estimate for the C0/high-A1 coefficient, local on H3 balls.
That estimate should feed continuous dense extension, the H3-to-H2 high A1
map, and its time-integrable forcing packet.  The completed low A1 pair should
not be reopened.
