# PointedDensitySource

## Route

- Pull each compact approximating integral back with `riemVol_param_lint`.
- On the compact source and bump-one region, rewrite its parametric density by
  `paramDens_src_eq` to the common `gSeqExt` chart density.
- Use `riemVol_chart_lint` on the limit side and discharge the resulting common
  coordinate convergence with `redDensity_cpt_lim`.

## Status

- `redDensity_src_lim`: warning-free focused GREEN.  Its direct axiom audit
  reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Its exact named module refresh is GREEN now that the umbrella and unified
  audit genuinely consume the exported declaration.
- The theorem is the genuine source-manifold endpoint.  It does not assume the
  desired integral convergence; compact confinement, measurability, pointwise
  reduced-density convergence, and the uniform reduced-density bound remain
  explicit.
- Source membership and bump-one are required only eventually in `k`, matching
  the finite-prefix freedom of pointed compactness and `Tendsto`.

## Progress

- `redDensity_src_lim` theorem endpoint: 100%.
- Dedicated source change-of-variables machinery: 100% for this compact-chart
  endpoint.
- Broader P2b endpoint package: still unstated (0%); its dedicated machinery is
  about 92--94%.
