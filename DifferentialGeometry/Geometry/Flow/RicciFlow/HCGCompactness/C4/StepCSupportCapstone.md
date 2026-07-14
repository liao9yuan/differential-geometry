# Source-local finite-support capstone

## Purpose

`StepCSupportCapstone.lean` is the upper B/C assembly layer.  It imports the
producer chain and the support-local branch readout without reversing either
dependency.  A source slot owns its normal chart and limit-weight family; an
actual interacting target remains an old-`L` `InterSlot`.  The file never
defines a glued weight, an overlap-compatibility theorem, or a pointwise chart
selector.

## Checked result

- `HasSuppCmFin` records the finite source-patch cover, patch-to-hat
  containment, chart-local `WeightDataOn`, positive active radii, a common
  epsilon-dependent radius tail, and one common pair-index tail for the
  conditional selected-branch center equation.
- `HasSourceCmFin` is the global-ball existential-source form.
- `HasSuppCmFin.toSource` derives the latter with the same threshold by using
  the finite cover; the source chart remains an existential witness.
- `MetricCompactBase.exists_supp_cm_fin` first selects the common minimizing
  scale, then chooses the divisor once, instantiates packing, obtains one
  stable net and one master subsequence, and finally takes finite maxima over
  target and source slots.
- `MetricCompactBase.exists_cm_on_source` is the global-ball corollary.

The source-local capstone and its global corollary are focused-green and have
no local warnings.  The preceding fused producer was strengthened only by the
derived fact `sourcePatch alpha ⊆ hatBall alpha`; no new input was added.

## Honest frontier and accounting

The final implication still consumes `StrictDistInput`.  Producing that input
uniformly from the full convexity/Hessian--Neumann argument is independent of
this finite-cover assembly and remains open.  No endpoint radius hypothesis
was introduced.

- This conditional source-local/global capstone theorem: **100%**.
- Dedicated source-cover, sparse-point, and pair-to-capstone machinery:
  **100%** for the approved architecture.
- Concrete `StepB1RawInput` producer: **0%**; textbook B1 theorem: **0%**.
- Dedicated Step-B/B1 machinery: about **88%**.
- Chapter 4 machinery: about **82%**.
- Whole HCG machinery: about **54%**.
- Conditional/unconditional compactness endpoints and `ham3_cgh_limit`:
  **0%** proved.

The smallest remaining analytic producer is the support-uniform
`StrictDistInput`/Hessian--Neumann continuation at the already selected
physical scale.  This looks like a substantial analytic frontier, not a local
coercion or tactic repair.
