# GeneralCurvatureCommutation

## Role

This module supplies the general intrinsic curvature commutator required to
differentiate Jacobi equations in launch parameters.  It sits in the variation
layer and does not depend on HCG compactness records.

## Result

`cov_commute_curv` states

`D_s D_t V - D_t D_s V = R(partial_s f, partial_t f)V`

for an arbitrary vector field along a smooth two-parameter variation.  Its
hypotheses are exactly the chart-representation regularity needed to define and
compare the two nested covariant derivatives.

`curvAlong` names `R(X,Y)Z` along one curve. `curvDerivAlong` is its direct
intrinsic covariant derivative with the three slot derivatives removed, and
`cov_curvAlong` gives the corresponding Leibniz expansion.

`cov_snd_smooth` and `cov_fst_smooth` close the joint-smoothness bookkeeping
for parameterwise covariant derivatives. `cov_snd2_expand` gives the fully
expanded second commutator, and `jacobi_var_eq` proves the first
inhomogeneous Jacobi equation for a smooth parameter family of Jacobi fields.
Its forcing is the explicit sum of one covariant curvature derivative and the
five lower slot-derivative terms; no forcing-bound hypothesis was introduced.

`chartRep_snd_diff` is now public. It projects any jointly smooth tangent field
to differentiability of its pinned chart representation on a fixed
second-parameter slice. This is the regularity bridge used by H6 for the mixed
launch field and its time covariant derivative.

`jacCurv_smooth` is the joint two-parameter analogue needed by the finite jet
recurrence. It applies the smooth curvature-operator bundle section to a
jointly smooth field and the jointly smooth time velocity twice; it does not
infer joint smoothness from separate one-parameter slices.

Focused verification is green with no diagnostics and there is no
`sorry`/`admit`/`axiom` in the module. The exact artifact is current and green
`3704/3704`.

## H6 impact

The prior library only had this identity for the longitudinal and transverse
velocity fields.  The general form is the missing commutation step for the
first inhomogeneous launch-Jacobi equation.

- `exists_h6NormalData`: theorem completion remains 0%.
- All-order intrinsic metric-jet machinery: about 66%.
- Whole native H6 producer machinery: about 73%.
- Whole HCG compactness machinery: about 62%; the unconditional textbook
  compactness endpoint remains 0%.

The intrinsic-launch instantiation and finite residual recurrence are now
exact-current in `IntrinsicJacobiJets.lean`. The next target is normalization
of the recurrence correction into curvature-tower terms and lower launch jets,
followed by constants-first fixed-tube Gronwall bounds.
