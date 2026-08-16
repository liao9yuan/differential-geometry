# Radial Rauch

## Scope

This module is the fixed-center nonnegative-sectional-curvature comparison
layer used by the Soul boundary-distance route.  It does not contain the
moving-base Rauch II theorem.

## Implemented chain

- `jacobi_ratio_anti` proves antitonicity of the squared transverse intrinsic
  Jacobi norm divided by the squared radial parameter on a minimizing segment.
- `jacobi_ratio_tendsto` identifies the exact pole limit with the squared norm
  of the initial derivative.
- `intrJacobi_sq_le` gives the sharp transverse endpoint estimate.
- `intrJacobi_le` adds the radial component and proves contraction for every
  launch variation.
- `intrFrame_deriv_le` transfers the estimate to the intrinsic framed
  exponential differential.
- `intrFrame_edist_le` integrates the pointwise bound along model segments
  whose launches stay in the minimizing segment domain and in the selected
  local framed-diffeomorphism source.

Focused, targeted-module, and root-aggregate verification pass without local
warnings.  Direct axiom inspection reports only `propext`,
`Classical.choice`, and `Quot.sound` for all six public theorems.
Full-project verification passes.

## Remaining frontier

This completes the fixed-center Rauch II(1) and local hinge input.  The
moving-base estimate requires a self-adjoint full Neumann Lagrange Jacobi
family together with a no-focal or full-rank condition; a nonvanishing single
Jacobi field is insufficient.  The other independent input to boundary-
distance concavity is the strict inward tangent-cone supporting half-space.

The Soul theorem remains unstated and therefore 0%.  Its dedicated machinery
is approximately 50--54%; the whole B1 lane is approximately 31--35%, and the
whole post-HCG program is approximately 19--23%.
