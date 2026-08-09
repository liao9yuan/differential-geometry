# PartialMfderiv.Basic

## Local time-partial regularity

`timeDeriv_smoothAt` is the pointwise finite-order version of the existing
global bundled theorem: if a scalar function on `Real × M` is jointly `C^n`
at a point, its partial derivative in the real factor is jointly `C^m` there
when `m + 1 ≤ n`.

Focused verification passed.

## Closed-edge spatial derivative regularity

`prodExtDeriv_joint` preserves joint `C∞`-within regularity on an
arbitrary time set times an open spatial set when taking the spatial
`extDerivFun` along a smooth vector field. It uses the native
`mfderivWithin_apply` interface and converts back to the full derivative only
through openness of the spatial set.

Focused verification passed.
