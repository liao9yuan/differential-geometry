# BishopBall.lean

## 2026-07-18 local normal-ball comparison

The center-metric polar integration stage is complete and sorry-free.
`exists_framed_ratio` supplies one common source radius and the radial
parametrized-density ratio in every framed unit direction.  The private radial
lintegral bridge converts `volumeIoiPow` to the ordinary weighted interval
integral, and a localized cumulative-ratio lemma permits comparison at every
pair of radii strictly inside the common source.

The public outputs are:

- `hypRadVol` and its positivity theorem `hypRadVol_pos`;
- `normalBallVolume`, the Riemannian volume of the framed exponential image of
  the center-metric tangent ball;
- `normalBall_cross`, the cross-multiplied local Bishop inequality; and
- `normalBall_ratio`, the corresponding ENNReal quotient antitonicity.

Focused verification passed without warnings.  No cut-time or measurable
direction choice is used.

`normalBall_ratio` is complete (100%).  The next theorem `localBall_ratio`
remains 0% until the framed normal image is identified with the intrinsic
metric ball on the chosen radius.  Dedicated Route B machinery is now about
68--72%; the full V1--V3 volume-comparison/CGT theorem program is about
44--48%.  Global Bishop--Gromov and the unconditional HCG compactness endpoint
remain 0%.

## 2026-07-27 canonical model-ball integral

Added the reusable producer `hypBall_lintegral`.  It computes the lintegral of
`hypDensity (q * ‖w‖) (finrank E - 1) 1` over a ball in a finite-dimensional
real inner-product space.  The proof uses the existing polar product measure,
combines its radial power with `hypDens_scale`, and identifies the remaining
ordinary integral with `hypRadVol`.

This theorem deliberately uses the canonical inner-product volume on its model
space.  It must not be restated with `modelHaar` from an arbitrary chart basis:
the project's `chartModelBasis` comes from `toEuclidean`, which is not an
isometry in general, while the radial ball and sphere use the ambient norm.

Focused verification passed without warnings.  The theorem itself is complete
(100%).  It closes the model-integral producer for `SegmentPolar.segBall_vol_le`;
that endpoint theorem remains unproved (0%).  Its dedicated segment-polar
machinery is now about 55--60%.  The relative theorem `segBall_vol_rel` remains
unproved (0%) and still needs a measurable cut-time / segment-domain polar
representation rather than another radial integration identity.

`volSphere_finrank` identifies this E-valued canonical sphere mass with the
canonical sphere mass on the standard Euclidean space of the same real
dimension.  This preserves the existing dimension-only endpoint normal form.
Focused verification passed.

The radial calculation is now also exposed as the reusable theorem
`hypRad_lintegral`.  For `R > 0`, it integrates the strict-radius indicator
`Iio ⟨R,hR⟩` of
`ENNReal.ofReal (hypDensity (q * r) d 1)` over `Ioi 0` against
`Measure.volumeIoiPow d`, and returns
`ENNReal.ofReal (hypRadVol q d R)`.  This endpoint-normalized integrand is
essential: using `hypDensity q d r` against `volumeIoiPow d` would count the
radial power twice.

`hypBall_lintegral` now calls this public radial producer instead of carrying a
second copy of the conversion proof.  Focused verification passed without
warnings.  `hypRad_lintegral` is complete (100%); it is routine model-side
machinery for the still-unproved `segBall_vol_rel` theorem (0%).

The scaling identity used by both radial proofs is now the public theorem
`hypDens_scale`:
`δ ^ d * hypDensity (q * δ) d t = hypDensity q d (δ * t)` for `δ ≠ 0`.
This is the model-side rewrite needed downstream to cancel the radial
`volumeIoiPow` factor; no new assumptions were introduced.
