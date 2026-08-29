# SegmentRadialDensity

## Role

This module is the geometry specialization consumed by the signed radial
integration step.  It packages the derivative bound for the transverse Jacobi
density together with its identification as the exponential Jacobian density.

## Route

- Radial downward closure of `SegInt` supplies nonconjugacy throughout the open
  interval below the chosen endpoint.
- `intrDen_deriv_le` gives the derivative formula and Bishop upper bound for the
  transverse curve density.
- Nonnegativity of the normal-chart density transports that upper bound through
  the constant factor.
- `intrJacobi_li` supplies the linear independence required by `expJac_radial`,
  which identifies the weighted exponential Jacobian with the same density.
- `segRadial_deriv_on` uses an internal midpoint above each requested radial
  parameter.  Consequently an open initial segment may end at the actual cut
  radius without falsely requiring that endpoint itself to lie in `SegInt`.
- `segRadial_ac` treats each intrinsic Jacobi field as the variation field of
  the globally smooth intrinsic variation.  Smooth bundle inner products make
  every Gram entry smooth, and the finite determinant polynomial is therefore
  smooth.  Segment-interior nonconjugacy and `intrJacobi_li` make that
  determinant positive throughout the compact positive interval.  Its square
  root is `C¹`, hence Lipschitz on the interval and absolutely continuous.
  This route uses no Ricci bound, radial-perpendicular assumption, or
  downstream consumer hypothesis.

## Status

`segRadial_deriv_le` is implemented; focused verification and the explicit
named module refresh pass without warnings.
The weaker open-endpoint specialization `segRadial_deriv_on` is implemented;
its focused verification passes without warnings.  It has not received a
named module refresh yet because no downstream checked module has consumed the
new declaration.

The compact-interval absolute-continuity producer `segRadial_ac` is implemented
and passes focused verification without warnings.  Its only geometric inputs
are positive radial speed, an orthonormal transverse source frame, and segment-
interior coverage on the interval.  No named module refresh was run for this
declaration.

Its first focused check reached only the midpoint arithmetic; the two strict
inequalities needed the upper component of the interval-membership hypothesis
passed explicitly to arithmetic normalization.  That local repair is now
verified; no geometric step failed.

Progress accounting: all three producers in this module, including the new
absolute-continuity theorem, are 100% complete. The final signed polar
integration theorem remains a separate, unstated and unproved downstream
endpoint (0% as a theorem); this module is only one producer in that broader
P1c assembly and does not change the whole-project completion estimate by
itself.
