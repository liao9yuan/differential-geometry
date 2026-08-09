# MetricDiffJoint

## Current state

This file publicizes the fixed-background metric-difference facts needed by
the reverse-realization uniqueness route.  It is deliberately below the
Ricci--DeTurck strong-pair assembly layer.

Current producers in `MetricDiffJoint.lean`:

- `metricDiff_raw`: the unsymmetrized tensor extracted from
  `metricDifferenceCcTensor q h` evaluates to `h.inner - q.inner`.
- `metricDiff_unit`: the same identity in the `unitModel` component idiom used
  by the spectral strong-solution bridge.
- `metricDiff_symm`: a metric-difference tensor is already symmetric, before
  applying `ccTensorBilinSymm`.
- `metricDiff_symVal`: its symmetrization is exactly `h.inner - q.inner`.
- `realize_metricDiff`: realizing this tensor about `q` recovers `h` exactly.
- `metricDiff_joint`: a `MetricFamilySmoothOn` family gives a jointly smooth
  fixed-background metric-difference path on `D.regular`.
- `metricDiff_shift`: the same joint smoothness after translating time by a
  fixed interior restart time, provided the translated open set remains in
  `D.regular`.

The joint-smoothness proof is the generic version of the formerly private
argument in `Garding/ScalarFluxJetBound.lean`; it uses the live
`MetricFamilySmoothOn.pairSmoothAt` API and the canonical parametric tensor
section criterion.

Verification status: **focused green**, with no local warning and no
`sorry`/`admit`. The exact artifact refresh is still pending.

The first exact downstream attempt exposed old API drift rather than a
mathematical gap. The repair uses the canonical TensorRS reduced-transparency
setting, imports the existing `ccTensorModel_sub` producer, opens the public
Ricci-linearization joint-section bridge, and corrects the section notation
from `Cₘ` to `Cₛ`. Public statements and assumptions are unchanged.

Scope warning: `metricDiff_shift` is an **interior regular-time** producer.  It
does not assert joint smoothness at an original flow edge where only `C0`
control is known, and it is not an endpoint-startup uniqueness theorem.

Forward uniqueness is already complete elsewhere. This file now feeds the
moving-edge branch of uniform low-regularity existence. The black-box theorem
`ricci_flow_unif_existence` remains unproved (0 percent); its dedicated
machinery remains approximately 84--87 percent complete.
