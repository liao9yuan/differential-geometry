# PreconnectedPropagation

## 2026-08-30: global geodesic-field support migration

### Mathematical route

- The Picard lift remains a chart-geodesic-vector-field integral curve on the
  small ball, and its chart-source membership remains part of the public
  result.
- At the `IsGeodesicOnWithInitial` boundary, `chart_vf_on_iff` converts that
  chart-local integral-curve proof to the global `geodesicVectorField` support
  now required by maximal geodesics.
- On the intersection with the chosen maximal interval, the Picard lift is
  converted to the global field and compared with the chosen global lift by
  `gvf_eqOn`.
- `isMIntegralCurveOn_eq_of_isPreconnected` is intentionally left
  chart-specific for its remaining chart-flow consumers.

No completeness, source, or uniqueness assumption was added to a public
signature. The existing `Boundaryless` instance is now used by the chart/global
field bridge instead of being omitted.

### Reuse and failures

- Reused `chart_vf_on_iff`; no adapter theorem or new assumption wrapper was
  introduced.
- Reused `gvf_eqOn`; the old chart-specific comparison is no longer applied to
  the chosen global maximal witness.
- The first focused verification failed only because one existing subscripted
  local name was mistyped. After correcting that identifier, focused
  verification passed without warnings.

### Project position

- The two global-support migrations in this file: 100%.
- This file's migration and regression verification: 100%.
- The compact-closure local Bishop endpoint itself is still unstated here and
  remains 0%; this change is support-semantic infrastructure, not its raw polar
  or measure-comparison producer.

