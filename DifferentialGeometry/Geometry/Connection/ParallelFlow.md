# ParallelFlow

## Scope

This module supplies the generic connection-level producer needed after a
complete smooth vector field has been constructed.  It does not assume metric
completeness, connectedness, Ricci curvature, an inner-product model, or any
Busemann-specific structure.

## Native route

`curveAt_mfderiv_par` embeds an arbitrary initial tangent vector in a smooth
curve and applies the commuting-covariant-derivatives identity to the resulting
two-parameter family of complete flow lines.  The time derivative of this
variation is the generating field by `curveAt_integralCurve`.  Restriction of
the Levi-Civita derivative to the transverse curve therefore vanishes by the
pointwise parallel-field hypothesis.  Commutation transfers that vanishing to
the spatial differential along the central flow line.  The final identification
of the variation field is the manifold chain rule `mfderiv_comp_apply`.

The implementation reuses `curveAt_contMDiff`, `curveAt_integralCurve`,
`exists_smooth_curve`, `commute_ds_dt_intrinsic`,
`covDerivAlong_restrict_eq_leviCivita`, and `mfderiv_comp_apply`.

## Verification state and risks

`curveAt_mfderiv_par` passed a warning-free focused check.  The only repairs
needed after the source pass were the repo-native real model notation, explicit
real tangent-vector application for one-dimensional `mfderiv`, and dependent
base-point alignment in the manifold chain rule.  No mathematical route or
public assumptions changed.

The theorem passed both its warning-free focused check and explicit named
module refresh, so downstream metric-preservation modules may consume the new
export.  The broader Cheeger--Gromoll splitting assembly remains a separate
multi-stage frontier.
