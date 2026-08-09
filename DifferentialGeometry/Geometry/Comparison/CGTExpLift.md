# CGTExpLift

## 2026-07-27 compact-continuation closure

This file is the proof owner for short lifts of the intrinsic framed
exponential in the Cheeger--Gromov--Taylor collision argument.

The verified layer now consists of:

- `IntrFrameLift`, the selected zero-start `C¹` lift data;
- `IntrFrameLift.norm_lt`, which combines `intrLift_norm_le`, lift equality,
  and monotonicity of path length to keep every partial lift strictly inside
  the controlling model ball;
- `IntrFrameLift.maps_ball`, the corresponding set-valued confinement result;
- `IntrFrameLift.norm_le_length`, the fixed full-length closed-ball fence;
- `exists_intr_lift`, which consumes the generic compact continuation theorem
  `IsLiftOn.exists_of_compact` and produces a full intrinsic framed lift;
- `IntrFrameLift.eqOn`, uniqueness of two such lifts in the same local-
  diffeomorphism ball.

The existence proof uses one compact closed ball strictly inside the controlling
open ball.  It does not assume a covering map, properness of the exponential,
or global injectivity.

The full short-lift theorem and its dedicated lift machinery are 100% at both
the focused-check and exact-artifact levels.  Homotopy lifting and right
cancellation are now closed in `CGTHomotopyLift.lean`; the immediate frontier
is the actual inverse-fiber injection of paper Lemma 4.5.  The later
collision/propeller theorem `intrLoop_ge_cgt` remains 0%; its dedicated
machinery is about 45--50%.  The sequence
`InjRadiusDecayInput` producer and unconditional compactness theorem remain 0%.
