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
`w_base_eq` performs only the local weighted-measure-to-base-measure conversion.
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
