# StepCHatReadout status

Status: 2026-07-13, focused verification passed without warnings or `sorry`.

## Checked result

`HasHatCmEqn` records the actual selected-live-slot output: a quantitative
normal branch, its fence, and the branch-native center equation for the filled
finite-hat configuration.

`exists_hat_cm_tail` is the non-transition join of the physical readout route.
It:

- chooses the minimizing coefficient `aMin` before `D`;
- retains the slotwise branch data from `exists_slot_min`;
- intersects that sequence tail with live/dead stabilization;
- exposes the canonical `seqCenterD` radius fact needed by
  `hatPtsCasesComp`;
- obtains the positive active radius from `exists_hat_radius`;
- uses `exists_rad_cage` for one common pair-index threshold;
- builds the actual filled `CenterInput` with `inputOfFillSelf`; and
- applies `exists_hat_cm_eqn` to produce the selected-branch equation.

The theorem adds no endpoint radius field.  `StrictDistInput` is deliberately
the final continuation parameter and remains the independent
Hessian/geodesic-convexity frontier.

## Remaining frontier

The next B/C consumer work is the concrete outer source-slot diagonal: use the
fixed ordered-net source slot `seqCenterD ... beta` and the active ordered-net
target slot `seqCenterD ... alpha`, then feed `hatPtsCasesComp` into this tail
theorem.  The current generic arbitrary-`y` `stepCJoin` interface has no radial
profile and must not be repaired with a new endpoint assumption.

The selected Gates 1--6 machinery is 100%.  Dedicated Step-B/B1 machinery is
about 83%, Chapter 4 machinery about 79%, and whole-HCG machinery remains about
53%.  `StepB1RawInput`, textbook B1, and the conditional Theorem 3.9 endpoint
remain theorem-level 0%.
