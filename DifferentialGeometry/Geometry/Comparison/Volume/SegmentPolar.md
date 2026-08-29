# Segment-polar base API

`transDens_eq_rigid` now has its canonical home in
`SegmentPolarEquality.lean`.  Its complete public statement, docstring,
attribute wrapper, and proof were moved verbatim across that abstraction
boundary.  This base module no longer imports `JacobiRiccati` solely for the
equality theorem and is now 2883 source lines, below the 3000-line limit.

`segBall_vol_le_int` is now the public canonical bridge from segment-ball volume to the
integral of exponential-Jacobian density; its statement and proof are unchanged.
Likewise, `gBall_model_int` is the public canonical evaluation of the model-density
integral over a metric tangent ball; only its visibility and name changed.

`expJac_radial` now exposes the radial scaling identity previously used only
inside this module: the exponential Jacobian times the Euclidean radial power
is the transverse Jacobi density.  This is the next reusable input for the
distance-specific polar proof of weak Laplacian comparison.

`segBall_reg_zero` records that an intrinsic ball differs by a
Riemannian-volume null set from the exponential image of the interior
minimizing segments inside the corresponding tangent ball.  The proof uses
Lusin--Souslin measurability of the injective exponential image and identifies
both set measures with the same Jacobian integral.  It is the setwise bridge
needed to replace manifold integrals by regular radial data; it does not assert
distance differentiability.

After the split, this base module passed warning-free focused verification and
its named refresh.  The focused check and explicit named refresh after
exporting `expJac_radial` also pass without warnings.  The new
equality module also passed both gates.  The
equality theorem's canonical status is recorded in `SegmentPolarEquality.md`;
its direct axiom audit remains pending.  The focused check after exporting
`segBall_reg_zero` and its explicit named refresh also pass without warnings.

Progress: P1a endpoints are 7/8 (87.5%).  All formal P1c endpoints remain
unstated and therefore 0%; this result advances only the dedicated direct-polar
machinery.
