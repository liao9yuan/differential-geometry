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

## 2026-07-13 explicit support-local tail

Added `exists_hat_cm_tail_support`. For a prescribed source slot and arbitrary
`s` contained in its hat, it consumes `WeightDataOn s (fun _ => univ)` and
two-index point convergence only at nonzero weights. It uses
`exists_active_radius` to uniformize the finite target slots, `exists_rad_cage`
to uniformize the finite source branches, builds the filled `CenterInput`, and
calls `exists_hat_cm_eqn_at` for the prescribed source slot. Focused
verification passed without a local `sorry`.

The old POU entrypoint remains unchanged as compatibility API. The remaining
outer B/C frontier is producer-side: construct the finite source cover and fuse
the sparse `InterSlot` transition extraction with the stable-disjoint zero-atom
branch. `StrictDistInput` remains the independent Hessian/convexity frontier.
Endpoint theorem completion remains 0%; this change completes the dedicated
support-local readout machinery only.

## 2026-07-13 outer consumer closure

The producer-side frontier recorded above is now closed in
`StepCProducers.exists_supp_pts_fin` and
`StepCSupportCapstone.exists_supp_cm_fin`.  Each chart-local limit-weight
family is pulled back only to its own source patch, point families alone are
totalized at the ambient finite index, and one finite source maximum produces
the common pair tail. `exists_cm_on_source` then gives an existential source
patch at every point of the global source ball; it does not define a chart
selector.

The approved conditional source-local/global capstone is 100%. Dedicated
Step-B/B1 machinery is about 88%, Chapter 4 machinery about 82%, and whole-HCG
machinery about 54%. `StrictDistInput`/Hessian--Neumann remains independent;
`StepB1RawInput`, textbook B1, and all compactness endpoints remain 0%.
