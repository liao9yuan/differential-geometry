# ClosedEdgeGronwall

## Mathematical role

`gronwall_zero_on` is the low-level scalar closure for a nonnegative energy
which is continuous on a closed interval, differentiable only on its interior,
zero at the left edge, and satisfies `energy' <= K * energy`.

The theorem is independent of Ricci flow and belongs in `Analysis/ODE`.  It
replaces the high-level `EdgeStrongData` dependency of `MovingEdgeEnergy`.

## Verification

Focused verification passed without warnings.  Exact artifact verification is
pending the shared writer window.

## Honest status

The scalar theorem itself is fully stated and implemented.  It is one small
closure input to the uniform low-regularity Ricci--DeTurck existence program;
`ricci_flow_unif_existence` remains unproved (0%), with its dedicated machinery
at approximately 84--87%.
