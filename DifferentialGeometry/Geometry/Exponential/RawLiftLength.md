# RawLiftLength

## Mathematical route

`rawFrame_radial_le` combines the full raw Gauss pullback identity with metric
Cauchy--Schwarz.  It needs only radial-segment membership in `expDomain`; it
does not impose a small normal radius, curvature, or completeness of the
ambient manifold.  `rawLift_norm_le` then specializes the map-generic
`lift_norm_le` fence to `framedExpMap` along a path whose pointwise radial
segments stay in the raw domain.

The target tangent `NormedAddCommGroup` and `NormedSpace` families are explicit
instance parameters of `rawLift_norm_le`, matching the generic fence.  These
structures were already required by `hEnorm`, the manifold derivative, and
`pathELength`; exposing them prevents the declaration from baking in the
canonical `Tensor0SBundle` norm and permits a consistent Riemannian-bundle norm
selection downstream.

The public statements require neither positive model dimension nor an explicit
model completeness assumption.  Finite-dimensional completeness is installed
only inside the zero-derivative proof where the existing exponential API needs
it.

The reusable derivative chain rule lives one layer lower as
`mfderiv_framedMap` in `RawFramedLocalDiffeo.lean`.  The generic lift fence was
also weakened so its radial Cauchy hypothesis is required only along the input
path, matching its proof and avoiding an impossible global raw-domain
assumption.

## Verification

The explicit norm-family signature passed focused verification without
warnings.  The original source had also passed after the exact upstream
artifact refreshes.  The earlier local repairs were purely shape-level: split the
zero-dimensional case so the public statement does not inherit `NeZero`, make
the derivative-at-zero composition congruence explicit, and expose one
continuous-linear-map application before applying `raw_gauss_pullback`.
