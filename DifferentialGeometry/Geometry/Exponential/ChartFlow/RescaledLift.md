# RescaledLift

## 2026-08-30: global geodesic-field support migration

### Mathematical route

- The rescaled chart-flow lift remains a chart-geodesic-vector-field integral
  curve on `J`.
- Its existing target and projection lemmas prove that the projected lift stays
  in the fixed chart source throughout `J`; `chart_vf_on_iff` converts the
  chart-local support to the global `geodesicVectorField` support required by
  `IsGeodesicOnWithInitial`.
- On `J ∩ J'`, both the rescaled lift and the chosen maximal lift are global
  geodesic-vector-field integral curves. `gvf_eqOn` supplies their equality from
  the common initial value.

The public signatures and the source-side target hypotheses are unchanged. No
new completeness, source, or uniqueness assumption was introduced.

### Reuse and verification

- Reused `chart_vf_on_iff`, the existing rescaled-lift projection-source lemma,
  and `gvf_eqOn`; no adapter theorem or assumption wrapper was added.
- The first verification attempt was deferred because another active Lean
  elaboration held the shared resource. The retry completed successfully and
  without warnings.

### Project position

- The two chart/global migrations in this file: 100%.
- This file's migration and regression verification: 100%.
- The compact-closure local Bishop endpoint remains unstated here and is still
  0%; this is support-semantic infrastructure rather than the raw polar or
  measure-comparison producer.

