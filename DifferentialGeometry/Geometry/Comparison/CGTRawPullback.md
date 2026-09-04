# Raw framed-exponential pullback metric

## Role

This module is the first geometric producer for the completeness-free raw CGT
propeller route.  It does not state either final injectivity endpoint.  It only
puts the generic local-pullback metric and path-length API on the raw framed
exponential restricted to a centered model-space ball.

The P1b theorem endpoints E1/E2 remain unstated and therefore 0% complete.  The
dedicated P1b machinery remains about 96% complete, while the whole Poincare
endpoint remains 0% complete.

## Mathematical route

`rawPullBall` is the open centered ball in the frame model.  A caller supplies
the actual local-diffeomorphism theorem for `framedExpMap`; `rawExpOn_local`
restricts it to the ball.  The generic `localPullMetric` then gives
`rawPullMetric`, and `localPull_pathLen` gives the exact length identity
`rawPull_pathLen`.

The ambient/restricted derivative bridge `rawExpOn_mfderiv` uses smoothness
already carried by the caller's local-diffeomorphism hypothesis.  This gives
the pointwise pullback evaluation `rawPullMetric_inner`.  Generic local
pullback curvature naturality then yields `rawPull_rm04`, and the existing
orthonormal-basis curvature estimate yields `rawPull_quad_le` directly from an
ambient raw `Rm`-norm bound.

This layer deliberately does not repeat the radial-domain, curvature, or
Gronwall assumptions used to construct the local diffeomorphism.  It also needs
no completeness, connectedness, positive-finrank, core, transport, or Jensen
hypothesis.

## Reuse and boundary

- Reused directly: `hloc_restrict_open`, `localPullMetric`, and
  `localPull_pathLen`.
- Curvature reuse: `Integral.Connection.rm04_localPull`,
  `Integral.Connection.riemann_quad_le`, `rm04_eq_inner`, and
  `exists_gOrthonormalBasis`.
- The caller may obtain its `hloc` from `framed_locdiff_rm`, but this module is
  independent of that construction.
- The intrinsic pullback module was used only to identify the thin adapter
  shape.  No intrinsic completeness machinery is imported or duplicated.

The next geometric lemma is a raw transport-curve length identity using
`rawPull_pathLen` on a canonical `IsLiftOn`.  Raw minimizing joins and their
distance-realizing length identity remain the later, genuinely geometric
frontier; strict Jensen is not yet required for length nonexpansion.

## Verification

The first focused pass exposed a tangent-space norm instance diamond between
the tensor-bundle default and the metric-induced Riemannian bundle.  Selecting
the canonical Riemannian-bundle norm in the path-length layer resolves that
local typeclass mismatch without strengthening any public assumption.

The curvature extension elaborated on its first pass; its only target warnings
were unused inherited tangent-bundle separation instances on the two curvature
theorems.  They are now explicitly omitted.  Final focused verification is
warning-free GREEN after that mechanical cleanup.

The downstream pinned-exponential proof later exposed that those omissions
hid a stronger ambient `T2Space M`/`SigmaCompactSpace M` dependency inherited
from the generic local-pullback curvature theorem.  The target-side
sigma-compactness has now been removed at that canonical lower layer.  The raw
curvature proofs source-derive `T2Space M` from their existing
`T2Space (TangentBundle I M)` input via `gauss_t2Space_base`; no ambient
sigma-compactness or new public hypothesis is added.  This signature cleanup
is warning-free focused GREEN after the lower artifact refresh.
