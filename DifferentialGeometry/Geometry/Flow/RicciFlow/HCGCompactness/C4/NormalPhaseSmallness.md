# NormalPhaseSmallness

## Role

This module closes the numerical small-parameter bridge between the normal
metric jet bounds and the strict error threshold required by a quantitative
inverse theorem.

## Current state

- `normalPhaseK_zero`, `normalPhaseK_cont`, and `normalPhaseK_lim` show that
  the explicit acceleration Lipschitz polynomial vanishes continuously with
  the velocity radius.
- `normalPhaseErr_lim` composes this with the generic phase error limit.
- `normalPhaseErr_lt_ev` gives the eventual strict bound below every positive
  threshold.
- `NormalRadiusProfile.phaseRadius` chooses one quarter of the checked relative
  radius floor; `phaseRadius_metric` and `phaseRadius_exp` place its ball inside
  both the normal-metric control region and the quarter exponential ball on a
  fixed distance sublevel.
- `exists_normal_q_lt` selects a positive `q` for any positive ordinary radius
  and any positive endpoint-error threshold.  Its conclusions are exactly the
  two numerical hypotheses of `NormalPhase.exists_normalFlow`, together with
  the requested error bound at velocity radius `2q`.
- `NormalRadiusProfile.exists_phase_q` specializes that selection to
  `phaseRadius`.  Combined with `phaseRadius_metric` and `phaseRadius_exp`, it
  supplies every radius and numerical input needed by `exists_normalFlow` on a
  fixed distance sublevel.

Focused verification and the targeted module build passed for the complete
API, including the new `q`-selection producer and its profile specialization,
without local proof or style warnings.

## Frontier

The small-radius numerical selection and profile containment are now complete.
The remaining frontier is geometric: identify the retained time-one endpoint
with the moving diagonal exponential, then consume the quantitative inverse
branch.  The moving inverse theorem itself remains unstated and therefore 0%;
this numerical-selection substage is 100%, but this module only advances the
theorem's dedicated machinery.
