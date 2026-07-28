# CGTHomotopyLift

## 2026-07-27 right-cancellation closure

This file proves the endpoint consequences of a uniformly short homotopy
through the intrinsic framed exponential.

`ShortHomotopy.exists_lift_family` selects the two-parameter lift using the
local-homeomorphism monodromy theorem.  `ShortHomotopy.lift_end_eq` gives equal
final lift values for short-homotopic paths.

`IntrFrameLift.append_mid_eq` identifies the midpoint of a concatenated lift
with the endpoint of the prefix lift.  `IntrFrameLift.cancel_right` runs local-
homeomorphism uniqueness backward from the common final value along the common
suffix.  `IntrFrameLift.end_eq_of_append` and
`ShortHomotopy.lift_end_cancel` are the paper Lemma 4.4 capstones.

No explicit reverse lift, spur homotopy, path quotient, or covering-space
assumption is used.  Focused verification and the targeted artifact refresh
are green.

Paper Lemma 4.4 is theorem 100% and dedicated machinery 100%.  Paper Lemma 4.5
is theorem 0%; its dedicated machinery is about 60%, with the actual
inverse-fiber injection as the next target.  `intrLoop_ge_cgt` and the
sequence-level injectivity-decay producer remain theorem 0%.
