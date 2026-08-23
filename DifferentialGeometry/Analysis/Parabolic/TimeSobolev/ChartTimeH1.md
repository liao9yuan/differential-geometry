# ChartTimeH1

## Scope

This file is the generic fixed-chart bridge from a manifold-valued `C¹` curve
to the existing vector-valued `timeH1` API. It does not define a
manifold-valued Sobolev space and does not assert compatibility between
different charts.

The chart condition is explicit: the curve maps the whole compact time
interval into the source of one fixed `chartAt`. The realized coordinate curve
is exactly `extChartAt I p ∘ gamma`.

## API

- `chartCoord_contDiff` proves that the fixed-chart coordinate curve is `C¹`.
- `chartTimeH1` applies the existing `timeH1.ofContDiffOn` constructor.
- `chartTimeH1_toFun` identifies its continuous representative.
- `chartTimeH1_deriv` identifies its weak derivative almost everywhere with
  the ordinary derivative of the coordinate curve.

## Verification and frontier

Focused verification passes without warnings or placeholders. The upstream
`TimeH1` artifact was refreshed once because this new downstream module needed
the newly exported `timeH1.ofContDiffOn` declarations.

The next geometric frontier is not another local wrapper: it is finite-chart
localization together with a weak chain rule on chart overlaps. Only after that
can local weak velocities be assembled into a chart-independent
manifold-valued realization.
