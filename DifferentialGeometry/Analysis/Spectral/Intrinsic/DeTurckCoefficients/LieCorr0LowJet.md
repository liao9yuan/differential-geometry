# LieCorr0LowJet

## Proved-source targets

- `pureTrace` and `pureTrace_split` expose the canonical moving cometric
  double trace from the curvature coefficient tower.
- `lc0Trace_fiber` identifies the reindexed field with the trace step used by
  `lieCorr0`.
- `riem_refold` writes the fixed-curvature correction as one moving trace
  applied to one fixed smooth curvature passenger.
- `trace2_grid` gives pointwise covariant-jet control of that moving trace by
  the intrinsic antidiagonal metric-jet window.

The exact first-order Leibniz factors are therefore
`trace^0 * fixed^0` at order zero and
`trace^1 * fixed^0 + trace^0 * fixed^1` at order one.  No pointwise second
metric derivative is requested.

## Verification state

Source has been written while the shared Lean artifact repair is exclusive.
No theorem in this file has yet been checked.  Endpoint completion remains
0%; this is producer machinery only.
