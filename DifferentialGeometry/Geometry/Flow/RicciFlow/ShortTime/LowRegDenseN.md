# LowRegDenseN

## 2026-07-27

The first low-regularity dense-extension bridge is now written:

- `smoothHs_inj` specializes the generic injectivity of the smooth spectral
  embedding to the rank-two scale used by Ricci--DeTurck;
- `smoothN_wd` shows that equal smooth spectral representatives give the same
  `deTurckSmoothN`, with no supercritical-order hypothesis.  Equality of the
  spectral representatives first gives equality of the smooth tensors, and
  the two metric realizations are then equal by their common inner-product
  formula.
- `smoothCore` is the dense smooth part of the live lower `H2` state ball,
  with its ambient, lower, and target Sobolev exponents written in the exact
  `lowerState g₀ 1 R` form;
- `coreRep`, `coreSymm_h2`, and `coreN` turn that core into a well-defined
  genuine smooth Ricci--DeTurck nonlinearity valued in `H1`.

This is a real simplification of the dimension-three `Dense.extend` route, but
it is not itself the Lipschitz or mixed estimate.  Focused verification passed.
The next consumer is `LowRegCoreTame`, which must supply the quantitative
Lipschitz estimate on this dense core before extension.  The explicit uniform
short-time-existence endpoint theorem remains unproved.
