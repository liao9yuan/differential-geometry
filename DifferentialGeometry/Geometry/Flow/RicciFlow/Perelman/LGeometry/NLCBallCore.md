# NLCBallCore

## Role

This module is the reusable assembly layer shared by the fixed-terminal and
terminal-time-uniform controlled-ball reduced-volume estimates. It separates
the real action argument from short-scale selection and keeps the
change-of-variables proof independent of a particular source cutoff.

## Source-ready producers

- `lRedLen_of_range` takes an exact moving-ball range witness for a minimizing
  regularized ray on the ordinary compact flow, together with
  `0 < eps <= 1`, and proves
  `-finrank^2 * eps <= redLength`. Its proof is the former real action proof
  from `lRedLen_scale`; it uses the controlled-ball scalar lower bound and does
  not assume a reduced-length estimate.
- `lRedDen_of_len` is the pointwise algebraic conversion from any lower bound
  `-C <= redLength` to the corresponding reduced-density upper bound.
- `lRedJac_set_le` performs the L-exponential change of variables on an
  arbitrary measurable good-source set and bounds its integral by a constant
  density times the moving volume of any target set containing the image.
- `redVolume_split` combines estimates on a measurable good/bad partition of
  the strict source domain.

The fixed-terminal theorems in `NLCBallUpper.lean` now call all four core
producers and retain their public statements unchanged. Focused verification
of this core module is warning-free green. Its named artifact and the
downstream fixed-terminal consumer have now also passed the coordinated
dependency sequence.

## Assumption boundary

The action producer retains `CompactSpace`, exactly because the existing
`lMinDomain_down` producer used to pass from the strict injectivity domain to
the endpoint minimizing domain requires it; compactness also supplies the
`SigmaCompactSpace` needed by the action-integrability API. The pointwise
density conversion has no compactness assumption. The current native
L-exponential partial-diffeomorphism and Jacobian producers also require
`CompactSpace`, in addition to the nonzero-dimension assumption. This is the
ordinary compact smooth-flow boundary of L9 and does not alter its consumer
API.

## Progress accounting

- Core extraction: 100%, warning-free focused green and named-refreshed.
- `redVolume_ball_unif`: 100%, warning-free focused green and named-refreshed.
- `smooth_nlc`: 100%, warning-free focused green and named-refreshed.
- Dedicated compact ordinary-flow L9 machinery is 100%; complete-flow and
  surgery/eventwise extensions remain separate phases.
- Reused generic infrastructure is 100%; whole P0--P9 remains 15--25%.
