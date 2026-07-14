# NormalBranchCage

## Role

This module is intended to combine the center/point cage ledger with one
selected quantitative branch for the whole finite configuration.

## Verified state

- `seqCenterD_rInf_lt` identifies the totalized center distance with the ordered
  net radius and places it eventually below `rInf gamma + 1`.
  `liveCenters_rInf` finite-intersects this slotwise statement.
- `exists_slot_min` calls `normalMinScale` once, before `D` is chosen.  The same
  positive `aMin` is then specialized to every `LiveSlot` at
  `Rgamma = rInf gamma + 1`, retaining the full minimizing branch, the metric
  radius bound, and the non-strict half-radius `expRadiusGp` floor.
- `lamInf_lt_halfMin` converts the one-shot physical budget
  `8 * exp C < aMin * D` into the strict slotwise half-margin
  `4 * lamInf gamma < (aMin * mu (rInf gamma + 1)) / 2`.
- `exists_rad_cage` takes a finite supremum of the positive slot margins.  One
  common pair-index threshold then places every active-point radius inside the
  physical cage for every stabilized live slot.
- `HasNormalBrFull.exists_cm_eqn` re-encodes the actual point family in the
  selected normal chart and applies the minimizing readout using the checked
  non-strict `expRadiusGp` floor; it returns the branch fence and the actual
  `chartCmEqnB = 0` equation.
- `aliveSlots_tail`, `hat_mem_live`, and `hat_dist_centerD` make the finite-hat
  routing dead-slot aware: a positive POU weight forces the chosen hat slot to
  be live and supplies its canonical four-`lamInf` distance bound.
- `exists_hat_cm_eqn_at` is the source-local readout: a prescribed
  `alpha : LiveSlot` together with membership in its hat and its slotwise cage
  inequality supplies the corresponding minimizing-branch fence and center
  equation.  It does not select a target weight and makes no assertion about
  compatibility between different source charts.
- `exists_hat_cm_eqn` keeps the previous API as a corollary.  It selects a
  positive-weight slot, proves it live, and delegates the geometric readout to
  `exists_hat_cm_eqn_at`.

Focused verification passes for both source-local and compatibility entrypoints,
without a local `sorry`.

## Frontier

The fixed-stage physical finite-hat readout is closed, but the higher assembly
is not.  It still has to intersect and thread the actual transition-map and POU
tails into this consumer and produce the concrete `CenterInput`; in particular,
the `StrictDistInput`/strict-convexity content carried by that input has not been
proved here.  Hessian/Neumann is therefore still a separate analytic frontier,
not a consequence of the cage inequalities.

No endpoint radius assumption was added.  The selected minimizing-branch
Gates 1--6 machinery and this fixed-stage physical cage/readout sub-brick are
100%.  The concrete `StepB1RawInput` producer, textbook B1 theorem, full
item-3 geodesic-convexity theorem, and compactness endpoints remain 0%.
Dedicated Step-B/B1 machinery is about 83%, Chapter 4 machinery about 79%, and
whole-HCG compactness machinery remains about 53% after conservative rounding.
