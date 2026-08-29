# MetricComparison

## Purpose

This is the canonical low-level home for one-sided comparison of Riemannian
volume densities and measures. It removes the accidental dependency on the
Ricci-flow compactness tree and uses the native countable atlas partition of
unity, so no `CompactSpace` assumption is needed.

## Public API

- `chartDensity_le` turns the pointwise quadratic-form inequality
  `h(v,v) ≤ Q g(v,v)` into the sharp local density bound with factor
  `sqrt (Q^n)`.
- `volumeMeasure_le` integrates that comparison through the countable atlas
  partition and returns an inequality of Riemannian volume measures with the
  same factor.
- `volume_restrict_le` assumes the quadratic-form comparison only on a
  measurable set `s` and compares the two Riemannian volume measures after
  restricting both to `s`.  It is the correct interface for ball-local metric
  comparison; it does not promote a local estimate to a global one.

The determinant step is adapted from the private Loewner-order argument in the
high-level Ricci-flow compactness file `CovariantSumCross`; this module does not
import or modify that file. The measure step reuses `chart_lintegral_le` and
`riemannianMeasure_lintegral_eq`.

## Verification and progress

Focused verification passes without placeholders or linter warnings, and the
named module artifact has been refreshed successfully.

The new set-local declaration passes focused verification without warnings or
placeholders.  Its only new upstream dependency is the likewise verified and
refreshed set-local chart-integral core `chart_lint_le_on`.  The named artifact
for this module should be refreshed only when a real downstream source consumes
`volume_restrict_le`.

The global and set-local chart-density and measure-comparison theorems are
complete (**100%**), as is their dedicated determinant/countable-partition
machinery.  The L9 consumer remains a separate theorem and is not counted as
complete here.
