# Busemann eikonal identity

## Role

`busemann_grad_sq` is the post-regularity geometric bridge for the splitting
chain.  It proves the unit squared norm of the metric gradient at every point
where the Busemann function is manifold-differentiable.  Differentiability is
the exact local input; no Ricci bound or global smoothness is added to this
theorem.

## Proof route

Use `exists_asymp_ray` at the chosen point and retain its unit initial vector.
The global support inequality and the one-Lipschitz lower bound force the
Busemann function to equal its initial value minus the ray parameter on the
nonnegative half-line.  Comparing the right derivative at zero with the
manifold chain rule gives gradient pairing `-1` against the unit direction.
Cauchy--Schwarz gives the lower unit bound for the gradient norm, while
`grad_norm_le_lip` gives the upper unit bound.

## Verification

The first focused pass stopped at one malformed implicit binder.  The next
pass reached the final norm estimate and exposed only a namespace name split
across a line.  After those local syntax repairs, focused verification passed
without warnings.  The theorem statement and mathematical route were
unchanged throughout.  The explicit named refresh also passed, so downstream
consumers can read the new export.

## Project accounting

The Cheeger--Gromoll splitting theorem remains unstated and is therefore 0%
complete.  This file is dedicated machinery only; it does not close the local
weak-solution regularity, Hessian-parallelism, flow, or global product
frontiers.
