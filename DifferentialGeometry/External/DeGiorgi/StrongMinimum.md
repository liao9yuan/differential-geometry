# StrongMinimum

## Role

This module is the local strong-minimum producer for the P1c splitting lane. It
turns the normalized Euclidean weak-Harnack estimate into pointwise vanishing on
the quarter ball for a continuous nonnegative supersolution with an interior
zero.  The unit-ball result is also transported to arbitrary positive-radius
balls by the canonical affine `BallScaling` API.

## Implementation route

- Shift the supersolution by a positive constant using the existing constant-
  subtraction API.
- Choose the weak-Harnack exponent so both real powers reduce to one.
- Identify the essential infimum of the shifted function with the shift. The
  upper bound is obtained by upgrading an almost-everywhere inequality to a
  pointwise inequality using continuity on the open ball.
- Let the shift tend to zero, then upgrade almost-everywhere vanishing to
  pointwise vanishing by continuity.
- For an arbitrary ball, pull the normalized coefficient and supersolution back
  along `z ↦ c + R • z`, apply `super_zero_ball`, and transport its pointwise
  conclusion back along `x ↦ R⁻¹ • (x - c)`.  This adds no new Harnack
  argument.

## Verification

Both `super_zero_ball` and `super_zero_on_ball` passed focused verification
without warnings.  The arbitrary-center/radius theorem reuses the normalized
coefficient and supersolution transports from `BallScaling`; it introduces no
new hypotheses and does not duplicate the weak-Harnack proof.

## Project status

- `super_zero_ball`: proved and focused-verified (100%).
- `super_zero_on_ball`: proved and warning-free focused-verified (100%).
- The final splitting endpoint remains unstated (0%); its dedicated endgame
  machinery is approximately 35--40% complete.
- The whole P1c program is approximately 60--65% complete at the infrastructure
  level.  This local transport theorem closes one consumer-support gate but is
  not itself the splitting endpoint.
- Whole-Poincare infrastructure is approximately 15--25% complete, while the
  final Poincare endpoint remains unstated (0%).
- The chartwise manifold supersolution producer remains unstated (0%); its
  infrastructure was not assessed by this narrow task.
- The final Busemann-pair vanishing theorem remains unstated (0%), and the final
  splitting theorem remains unstated (0%). This producer supplies only the
  local analytic propagation step, so it does not change either endpoint's
  theorem-completion percentage.
