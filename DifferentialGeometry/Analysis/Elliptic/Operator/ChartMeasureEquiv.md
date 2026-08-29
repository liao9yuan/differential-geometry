# ChartMeasureEquiv

## 2026-08-29: noncompact signed chart-integral adapters

### Result

Four short public theorems now expose the signed chart formulas without a
global `CompactSpace M` assumption:

- `integral_model`
- `integral_model_ind`
- `integral_euclid`
- `integral_euclid_ind`

Each assumes exactly `Continuous f`, `HasCompactSupport f`, and
`tsupport f ⊆ (chartAt H α).source`, in addition to the pre-existing manifold
assumptions. The model-space formula consumes
`DivergenceTheorem.integral_eq_chart`; the Euclidean formula is the existing
measurable-equivalence transport applied after that result.

All four pre-existing compact-space theorem signatures remain unchanged. Their
proofs now obtain compact support from `CompactSpace M` and reuse the new
noncompact theorems, so existing consumers require no migration.

### Verification

Focused verification and the explicit named module refresh passed without
warnings. The axiom audit for all four new theorems reports only `propext`,
`Classical.choice`, and `Quot.sound`. No `sorry`, new axiom, class, instance, or
notation was added.

### Project accounting

This supplies the measure-equivalence portion of P1c Route A. The formal
viscosity-to-distributional Laplacian endpoint is still unstated and therefore
0% complete. Its dedicated Route-A infrastructure is approximately 15%
complete; local coefficient and analytic passage lemmas remain the main work.
