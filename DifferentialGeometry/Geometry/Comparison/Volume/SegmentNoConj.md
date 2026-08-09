# SegmentNoConj

## Purpose

`segDom_no_conj` connects the distance-realizing `SegDom` predicate to the
index-form theorem that a minimizing geodesic has no conjugate vector at an
interior radial time.  The file is separate from `SegmentDomain.lean` so the
set/measurability layer does not import the heavier variation machinery.

## Status

The proof uses only the existing minimizing-geodesic, arc-length, and
no-conjugate APIs.  It adds no connectedness, injectivity-radius, cut-time, or
endpoint-nondegeneracy assumption.  Focused verification passed without
diagnostics.

## Project accounting

- `segDom_no_conj`: proved and focused-verified.
- `segBall_vol_le`: not yet proved.
- `segBall_vol_rel`: not yet proved.
- The dedicated A0-prime segment-polar machinery is approximately 68% complete;
  the two public volume endpoints remain 0%.
