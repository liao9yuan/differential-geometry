# SecondVariationMinimiser

## Status

The existing public local-minimum second-derivative theorem now delegates to the pure calculus producer in `Analysis/Calculus/UpperSupport.lean`. Focused and full-project verification passed.

This preserves the variation-layer API while removing the analytic fact from the geometric dependency direction. No theorem statement changed.

## Project position

- Compatibility wrapper: 100%.
- One-dimensional upper-support concavity calculus: 100%.
- Smooth-geodesic Busemann composition concavity: 100%.
- Soul theorem: unstated, 0%; dedicated machinery approximately 24%.
