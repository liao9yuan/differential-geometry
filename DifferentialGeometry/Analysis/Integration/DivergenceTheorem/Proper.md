# Proper

## 2026-08-29: public chart-local integral adapter

### Result

The existing noncompact-manifold proof is now public as
`DifferentialGeometry.Integral.DivergenceTheorem.integral_eq_chart`:

```lean
theorem integral_eq_chart
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α₀ : M)
    {h : M → ℝ} (hh_cont : Continuous h) (hh_cs : HasCompactSupport h)
    (hh_supp : tsupport h ⊆ (chartAt H α₀).source) :
    ∫ x, h x ∂riemannianVolumeMeasure (I := I) (M := M) g =
      ∫ x, h x ∂chartLocalMeasure (I := I) g α₀
```

This is the former private lemma, exposed in place rather than copied. The
compact-support divergence theorem in this file now reuses the public name.

### Verification

Focused verification and the explicit named module refresh passed without
warnings. The axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, new axiom, class, instance, or notation was added.

## 2026-08-29: compact-set measurable transport

`volume_restrict_comp` strengthens the chart adapter at the correct measure
layer: if a compact set lies in one chart source, Riemannian volume and that
chart's local measure have equal restrictions to the compact set.  Its proof
uses the existing finite partition-of-unity reduction on the compact set,
chart-overlap invariance, and the partition sum; it does not assume continuity
of a future integrand.

`chart_int_eq_volume` is the corresponding integrable-function interface.  A
chart-locally integrable function whose compact support lies in that chart is
globally volume-integrable and has the same integral.  This is the exact bridge
needed for compactly supported Lipschitz tangent actions, which need not be
continuous on their nondifferentiability set.

Focused verification passed without warnings.  No new assumption, axiom,
instance, notation, or theorem-shaped placeholder was introduced.  A named
refresh is deferred until the noncompact weak-gradient consumer imports these
new declarations.

### Project accounting

The continuous adapter and the compact-set measurable transport close the
measure-level chart-local gap shared by the direct distance route and the
larger viscosity route.  They remain infrastructure: the formal
distance-distributional endpoint is still unstated and therefore 0% complete.
