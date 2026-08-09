# SegmentInterior.lean — strict minimizing-segment endpoint API

## Status

GREEN, sorry-free, and targeted-build current (3847 jobs).

## Public API

- `segEnd_zero` identifies the endpoint map at the zero tangent vector.
- The file packages the strict minimizing-segment membership and endpoint facts
  consumed by `SegmentPolar.segBall_area_eq` and `segBall_vol_rel`.

## Role in the volume route

This is a producer layer, not the A0′ endpoint.  It lets the relative
Bishop–Gromov proof work on the actual strict segment set, including the
zero-radius endpoint, without choosing a global cut-time function or adding a
chart-selection assumption.
