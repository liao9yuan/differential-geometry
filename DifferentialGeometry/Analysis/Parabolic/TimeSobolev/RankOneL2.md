# RankOneL2

## Result

The generic normalized rank-one time-operator API is complete. The direction
space is a real inner-product space, while the residual/output space is only
required to be a real normed space; in particular the API applies when both
are real Hilbert spaces.

- `rankOneAlong` is the normalized pointwise rank-one family, with inverse
  scalar zero at a zero direction;
- `rankOneAlong_self` proves exact self-action under the honest compatibility
  condition `u t = 0 -> r t = 0`;
- `norm_rankOneAlong_le` transfers `||r t|| <= b ||u t||` to the operator bound
  `||rankOneAlong u r t|| <= b`;
- `rankOneAlong_aesm` constructs operator-valued AE strong measurability from
  measurable `u` and `r`;
- `memLp_rankOneAlong` transfers any real scalar `MemLp` relative majorant to
  the operator family, for arbitrary exponent and measure on time.

The measurable rank-one proof uses `rankOne_def`, the measurable dual path
through `innerSL`, and `smulRightL`. This avoids treating the star-linear
second slot of `rankOne` as an ordinary bilinear application. The reciprocal
norm-square is handled through measurable inversion, which remains valid at
zero.

Focused verification passed without warnings or proof placeholders.

## Project position

- This module and its four theorem endpoints: 100%.
- Its dedicated generic rank-one/`MemLp` machinery: 100%.
- The rank-one factorization brick is only about 1--2% of the remaining
  low-base/same-horizon order-two bootstrap work: the geometric consumer must
  still construct the residual and prove the relative bound.
- `LowBaseActionSplit`: not stated and proved, 0%.
- `(N) ricci_flow_unif_existence`: not stated and proved, 0%.
- `(N)` dedicated machinery remains approximately 97%; this isolated helper
  does not count as progress on the still-unstated endpoint theorem.
