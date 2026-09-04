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

The closed metric tangent ball declarations (`closedGBall`,
`isClosed_closedGBall`, and `isCompact_closedGBall`) were moved mechanically to
`SegmentDomain.lean`, their lowest natural layer.  This file continues to reuse
the same names through its existing `SegmentDomain` import; no public signature
or segment-polar theorem changed.  Verification of this source-only relocation
is pending the explicitly released focused-check window.

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

## Raw compact-closure ball area bridge (2026-08-30)

`rawBall_vol_le_int` is the local counterpart of the complete intrinsic
`segBall_vol_le_int`.  Given strict radii `R < R₀` and compact closure of the
`R₀` metric ball, it combines `ball_sub_rawSeg`, `isCompact_rawSeg`, the
pointwise compact-buffer producer `mem_expDom_of_cpt`, and
`riemVol_rawExp_le`.  Its integral is over the raw minimizing equality locus
truncated by `closedGBall g p R`, and its integrand is the existing
time-one radial `curveDensity`.

The old complete theorem and all of its consumers remain unchanged.  The new
statement assumes neither ambient completeness nor connectedness; strict
buffering is used only for compactness and raw-domain membership, while ball
coverage consumes its weak form `R ≤ R₀`.

Source implementation and the four-step dependency route have been reviewed.
The first downstream refresh exposed only a stale `omit [CompleteSpace E]`
whose instance was no longer in the section scope.  Removing that vacuous
binder leaves the public statement and proof body unchanged, and the full file
now passes warning-free focused verification.

The new theorem and its dedicated source proof are focused-verified and exact-
refresh green (100% at the theorem/source layer).  The final compact-closure
Bishop comparison remains unstated (0% theorem completion); the remaining
mathematical producer is the local Jacobi/Ricci pointwise bound for this raw
radial density.
