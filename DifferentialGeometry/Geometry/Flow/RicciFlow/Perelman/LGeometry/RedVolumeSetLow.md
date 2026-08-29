# RedVolumeSetLow

## Role

This is the canonical low-level home of `redVolume_set_low`.  A measurable
slice set on which reduced length has a uniform upper bound contributes the
corresponding constant normalized density times its Riemannian volume to
reduced volume.

The declaration was moved unchanged from `SmoothNLC.lean`.  Its lower placement
lets `SliceVolumeLow.lean` consume it without making the late-volume producer
depend on the final smooth-noncollapsing capstone.

## Verification

The new low-level module is warning-free focused green and its named artifact
was refreshed.  The public statement and proof of `redVolume_set_low` are
unchanged, with no `sorry`, `admit`, or new axiom.

## Progress

`redVolume_set_low` is a complete theorem endpoint for its set-level interface
(100%).  It is infrastructure for, rather than part of the completion count
of, higher reduced-volume and noncollapsing theorems.
