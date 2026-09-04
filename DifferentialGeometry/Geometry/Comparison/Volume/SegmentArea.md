# SegmentArea

## Mathematical route

`expJacDensity_nonneg` records the canonical sign projection for the
exponential Jacobian density.  The density is the square root of the Jacobi
Gram determinant, so nonnegativity is immediate and requires no geometric
hypothesis beyond those of the definition.

The signed exponential change-of-variables layer uses this lemma to simplify
the finite density `ENNReal.ofReal expJacDensity` back to a real scalar.

## Verification

Focused verification passed without warnings.  The theorem uses no new
assumptions or axioms; the two ambient instances unused by this projection are
explicitly omitted.

## Raw exponential image adapter (2026-08-30)

### Mathematical route

`riemVol_rawExp_le` applies the general local-map area inequality
`riemVol_image_le` on the open raw exponential domain.  The domain-local
smoothness input is `expMap_contMDiffOn`; `raw_exp_density` then identifies the
general Gram-Jacobian density pointwise with the existing `curveDensity` of the
time-one radial variation fields.  Thus the public conclusion is already in
the density language used by the Jacobi comparison stack, without defining a
second raw density object.

The compact set is assumed only to lie in `expDomain`.  The adapter does not
use ambient metric completeness, connectedness, pseudo-emetric structure,
Ricci bounds, or a metric-norm identification.  The previous complete
intrinsic exponential endpoint and its proof are unchanged.

### Verification

Focused verification passed without warnings.  The only repair after the first
full elaboration was to omit the unused positive-finrank section instance from
the theorem scope; the statement and proof route are unchanged.  No refresh or
broader build was run during the parallel-task window.

### Progress

`riemVol_rawExp_le` and its dedicated source proof are verified (100%).  The
compact-closure local Bishop endpoint remains unstated (0% theorem completion);
this adapter supplies its area-image step but not the later pointwise
Jacobi/Ricci density bound.
