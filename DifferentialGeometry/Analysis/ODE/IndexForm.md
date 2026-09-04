# Index-form ODE endpoint closure

## Mathematical route

`IsJacobiSolOn.of_Ioo` closes both first-order Jacobi equations from the open
interval to a nondegenerate closed interval.  A local generic derivative
closure is applied once to the field and once to its velocity.  At the left
and right endpoints it uses the one-sided derivative-limit theorems; interior
points retain their ordinary derivatives.

The acceleration itself is assumed continuous.  This is weaker than assuming
the whole operator family is continuous and adds no completeness or endpoint
value hypothesis.

## Verification

Focused verification passed without warnings.

## Project position

The endpoint-closure producer is implemented and verified (100%).  Integration
into a future raw no-conjugate theorem is outside this file and remains 0% in
this task.  This bridge is a small part of the radial-Jacobi/index-form
infrastructure and contributes less than one percentage point to the overall
comparison-geometry campaign; the compact-ball comparison endpoint remains a
separate theorem frontier.
