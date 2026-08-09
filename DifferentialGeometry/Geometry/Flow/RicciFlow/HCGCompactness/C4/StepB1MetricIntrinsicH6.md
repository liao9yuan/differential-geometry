# H6 intrinsic metric tails

`H6NormalData.cov_comp_tail`, the local bump bridge, `fwd_norm_tail`, and
`inv_norm_tail` prove the forward and exact-inverse intrinsic metric-error
tails using `d.chart`. The reverse proof localizes at the moving target
coordinate and decodes only inside `restrictBall.target`; it does not use
`normalQuarter`, `NormalRadiusProfile`, or `le_exp_radius`.

Focused verification passes, and exact verification passes (`4232/4232`).
The provider-native intrinsic metric consumer is complete.
