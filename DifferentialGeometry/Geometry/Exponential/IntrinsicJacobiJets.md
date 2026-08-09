# IntrinsicJacobiJets

## Role

This module starts the intrinsic launch-parameter jet layer needed by the H6
normal-coordinate metric producer.  It works below the HCG consumer API and
adds no metric-jet or chart-radius assumption.

## Current result

- `intrLaunch3` is the complete intrinsic geodesic with two affine launch
  parameters and one time parameter.
- `intrLaunch3_smooth` proves joint all-order smoothness of that family.
- `intrLaunchJ` packages the second-launch derivative as the total derivative in
  the canonical launch direction. `intrLaunchJ_smooth` proves that this tangent
  field is jointly smooth in the remaining launch parameter and geodesic time,
  and `intrLaunchJ_eq` identifies it with the one-variable derivative consumed
  by the Jacobi API.
- `intrLaunchMix_smooth` and `intrMixDeriv_smooth` prove joint smoothness of the
  mixed launch-Jacobi field and its time covariant derivative. They are the
  regularity inputs for the inhomogeneous covariant Gronwall step.
- `intrLaunchDir_smooth` proves joint smoothness after applying the total
  derivative to any fixed launch/time direction. `intrLaunchA_eq` and
  `intrLaunchT_eq` identify the first-launch and time directions with the
  existing `Variation.varFst` and `Variation.varSnd` partial velocities.
- `intrLaunchA_zero` and `intrLaunchJ_zero` identify the two central launch
  slices with the existing intrinsic Jacobi fields. They are the canonical
  rewrite bridge used by the H6 pair estimates.
- `intrLaunchDA_zero` and `intrLaunchDJ_zero` identify their time covariant
  derivatives without unfolding the connection in H6 consumers.
- `intrLaunch_jacobi` identifies every fixed first-launch slice of the second
  launch derivative with the existing complete intrinsic Jacobi field.
- `intrLaunch_mix_zero` proves that the covariant mixed launch derivative has
  zero value at geodesic time zero.
- `intrLaunch_dmix0` proves that its time covariant derivative also vanishes
  there. The proof differentiates the constant initial Jacobi velocity and
  uses the smooth covariant commutator; the curvature remainder vanishes
  because the Jacobi value at launch is zero.
- `intrLaunch_commute` proves that the two covariant launch derivatives commute
  at every geodesic time.
- `intrLaunch_var_eq` instantiates the general two-parameter
  `Variation.jacobi_var_eq` theorem for the intrinsic affine launch family. It
  gives the first launch derivative of the launch-Jacobi field an explicit
  inhomogeneous Jacobi equation whose forcing contains one covariant curvature
  derivative and lower velocity/Jacobi slots.
- `intrJetResidual` and `intrJetCorr` specialize the general finite-order
  Jacobi residual API to the intrinsic launch family.
- `intrJetResidual_zero` closes the order-zero Jacobi residual directly from
  `intrLaunch_jacobi` and `intrLaunchJ_eq`.
- `intrJetCurv_smooth` supplies the honest joint smoothness of the curvature
  term for every launch jet. `intrJetResidual_succ` then proves the exact
  arbitrary finite-order residual recurrence without a supplied forcing or
  regularity hypothesis.

Focused verification is green with no local diagnostics. The exact artifact is
current and green `3819/3819`. The fixed-direction API remains consumed by
`H6JacobiForce.intrJacForce_le`; it avoids restating seven separate smoothness
assumptions at the intrinsic H6 layer.

## Frontier

The exact finite-order residual recurrence is complete. Its correction is
still expressed as `Variation.jacStepCorr`, so the next target is to normalize
the `n`th correction into a finite sum of curvature-tower evaluations and
lower launch jets using `CurvOpTower.curvOpN_cov_sum`. That normalization is
the remaining mathematical input before constants-first force and pair bounds.

## Progress

- `exists_h6NormalData`: theorem remains unstated, so theorem completion is 0%.
- All-order intrinsic metric-jet machinery: about 66%.
- Native H6 producer machinery including radius, branch, and provider work:
  about 73%.
- Whole HCG compactness project: about 62% machinery; unconditional textbook
  compactness endpoint remains 0%.
