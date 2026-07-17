# WVariation

## 2026-07-16 raw first variation

`w_rev_hasDerivAt` is checked.  Its inputs are the actual reversed Ricci-flow
metric, the actual `conjCoeff S (T - r)` conjugate-heat coefficient, a positive
`IsHeatPotOn` solution, and only the regular-time conditions needed at the
evaluation time.  The coefficient is reduced internally by `conjCoeff_apply`;
no parallel heat equation or supplied regularity package is exposed to the
consumer.

The proof stays scalar and interval-local.  On the open regular-time patch it
uses `potential_joint`, `revGram_smooth`, `gradSq_joint`, and `scalar_joint` to
feed `first_var_joint`.  The pointwise derivatives are supplied by
`potential_pde`, `revScalar_time`, `revGradSq_time`, and `revTrace_eq`.
`wFunctional_base` performs only the weighted-measure-to-base-measure conversion;
it now lives publicly in `Defs.lean` because later fixed-metric estimates need
the same canonical normal form.
No global frame, whole tensor/Hom equality, `HasLocallyConstantChartAt`, or new
consumer assumption is used.

Focused verification passed without a new `sorry`.  The raw theorem
`w_rev_hasDerivAt` and its dedicated first-variation machinery are 100%.
Weighted Hessian square completion and W monotonicity remain theorem-level 0%;
Perelman no-local-collapsing and `ham3_noncollapse` remain 0%.  Broader
entropy/noncollapse machinery is approximately 67%, while whole HCG machinery
remains approximately 60% with its endpoints at 0%.

The next exact producer is `ricDriftDiv`, followed by
`weighted_hess_split`.  `hessSec_inner_cov` and `ricHess_eq_inner` are checked;
the remaining low-level adapters are the canonical scalar-curvature bridge and
the public orthonormal trace formula needed by the divergence calculation.

## 2026-07-16 square and derivative sign

`w_rev_square` is checked.  It converts the actual raw reverse-flow variation
to the canonical weighted square through a scalar base-measure/
`e^{-f} dmu` bridge and `weighted_w_square`.  `w_rev_deriv_nonpos` then proves
that the actual `deriv`-based first variation is nonpositive at every positive
regular time covered by the hypotheses.  No dimension, chart, supplied
regularity, or other consumer assumption was added.

Focused verification passed without a local `sorry`.  The raw first variation,
weighted square, and local derivative-sign theorems are each 100%, as is their
dedicated machinery.  A separate interval-level `MonotoneOn` wrapper is not yet
stated (0%), and the cutoff contradiction, Perelman no-local-collapsing, and
`ham3_noncollapse` remain theorem-level 0%.  Broader entropy/noncollapse
machinery is approximately 75%; whole HCG machinery remains approximately 60%
with its endpoint theorems at 0%.

## 2026-07-16 interval monotonicity

`w_rev_antitone` is checked.  On every positive closed reverse-time interval
contained in the reverse and original regular-time domains, it combines the
actual square first variation with the derivative mean-value theorem to prove
`AntitoneOn` for the genuine reversed-flow `W` path.  This is the interval
theorem required by the noncollapsing route; no global regularity, chart
selector, dimension, or supplied monotonicity assumption was introduced.

The raw first variation, square identity, derivative sign, and interval
antitonicity theorems are each **100%**, together with their dedicated
machinery.  The fixed-metric W lower bound, cutoff contradiction, Perelman
no-local-collapsing, and `ham3_noncollapse` remain theorem-level **0%**.  The
next honest analytic producer is a uniform closed-manifold Sobolev constant,
then a fixed-metric log-Sobolev/W lower bound.  Broader entropy/noncollapse
machinery is approximately **78%**; whole HCG machinery remains approximately
**60%**, with its endpoint theorems at **0%**.
