# IntrinsicBallVolume

## State - 2026-07-28

This module supplies the lower-volume bridge used by the sequence CGT decay
producer.

`toEuclidean` is an arbitrary continuous linear equivalence, not an isometry.
The proof therefore records the positive coefficient `modelCoeffMin` instead
of silently identifying the two norms.  `param_dens_ge` converts the half-metric
Rayleigh bound into a determinant-density lower bound, and
`intrBall_vol_ge` transports that estimate through an `IntrinsicBallChart` to
the intrinsic Riemannian ball.

The initially tempting isometric-normalizer shortcut was rejected because it
is not provided by the existing API.  The positive antilipschitz coefficient
is the correct reusable replacement and adds no geometric hypothesis.

Focused verification and the exact module refresh passed.  The public
`intrBall_vol_ge` axiom audit contains only `propext`, `Classical.choice`, and
`Quot.sound`.

The lower-volume theorem is 100%, its dedicated Jacobian/determinant machinery
is 100%, and it closes the basepoint-volume brick of the sequence
`InjRadiusDecayInput` producer.
