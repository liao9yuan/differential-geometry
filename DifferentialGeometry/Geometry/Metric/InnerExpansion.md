# InnerExpansion

## 2026-07-28 metric-length algebra

Added `sqrt_inner_add_le` and `sqrt_inner_smul`.  They identify the square root
of the pointwise metric quadratic form with the norm induced by
`tangentMetricData_gen`, then reuse the ordinary norm triangle and scalar laws.
This replaces several downstream private copies of the same fibre calculation.

Focused verification and the exact artifact refresh passed.  These
lemmas are reusable metric infrastructure; they do not by themselves prove the
H6 normal-coordinate radius theorem.
