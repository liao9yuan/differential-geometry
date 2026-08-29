# Shi cutoff support bridge

`support_of_scaled` is warning-free focused GREEN.  It turns a
`DistanceBarrierCore.ScaledDistSupport` into a nonempty
`ShiCutoffLowerSupportAt` for the actual `CutoffProfile.evalue` cutoff.

The interface assumes only eventual finiteness of the moving intrinsic distance
on the spacetime neighborhood; it does not demand a global distance-continuity
hypothesis.  Its bounds preserve the scale-invariant errors
`Csq * a^2 * U^2` for the gradient term and
`Ceta * (2 * c * a^2 * U^2 + a * U * Q + a^2 * U^2)` for the parabolic term.

The next real consumer is
`Perelman/LGeometry/ShiBallCutoff.exists_cutoff_ne`.
