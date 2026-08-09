# LowRegBootstrapOne status

## Endpoint accounting

- `ricci_flow_unif_existence`: 0%. Its exact Lean theorem is not yet proved.
- Low-regularity Phase N machinery: about 81%. The mixed `H3 -> H1`
  nonlinearity and forcing-space solver are now checked, and this file supplies
  the first same-horizon trace bootstrap. The spatial parabolic bootstrap to a
  smooth solution is still missing.
- `extends_of_rmBounded`: still depends directly on the unproved endpoint.

## Source added here

`LowRegBootstrapOne.lean` packages an affine maximal-regularity Duhamel solution
as a `CrossScaleField`.  Its intended exported facts are:

- `crossRepr_toFun`: the Lions--Magenes `H^(a+1)` representative includes to
  the `H^a` carrier for every `t` in the original `Icc 0 T`;
- `crossRepr_hi_ae`: it equals the `H^(a+1)` inclusion of the `L2_t H^(a+2)`
  companion almost everywhere;
- `crossRepr_ball`: an a.e. `H^(a+1)` ball bound becomes an every-time bound,
  using continuity of the squared intermediate norm;
- `duhRepr_toFun`, `duhRepr_field_ae`, and `duhRepr_ball`: direct Duhamel
  specializations for an arbitrary intermediate-order state bound;
- `duhRepr_meas`, `duhRepr_memLp`, `duhReprL2`, `duhReprL2_ae`, and
  `duhReprL2_ae_le`: the intermediate representative as an honest
  same-horizon time-`L2` field, retaining the prescribed state-ball bound.

All conclusions retain the solver's original `T`; no `d <= T` is introduced.
Focused Lean verification passed without local warnings after the time-`L2`
packaging was added on 2026-07-27.

## Three audited bootstrap routes

### 1. Re-run maximal regularity at `a = 2`

The order-two affine map requires initial data in `H4` and forcing in
`timeL2 H2`.  The zero initial perturbation is available in every order, but
the current fixed point only supplies

`gforce : timeL2 H1`

and `lowRegN` is a static map `H3 -> H1`.  A generic static `H3 -> H2` estimate
is false for the quasilinear second-order arm.  The exact missing input for
this route is an `H2` forcing lift obtained from the equation's parabolic
structure, not from a stronger restatement of `lowRegN`.

### 2. Pure spectral Duhamel smoothing

`duhamel_into_all_tensorHs` assumes, for every `c >= 0`, summability of

`weight(c) * integral_0^t |forcing_mode|^2`.

The order-one solver provides this mass only at `c = 1`.  The homogeneous heat
theorem `heat_semigroup_into_all_tensorHs` smooths the initial term, but the
initial perturbation here is already zero and it does not improve the
inhomogeneous forcing.  Generic `L2_t H1` forcing gives the sharp
`L2_t H3` maximal-regularity field; it does not give `L2_t H4`.  Thus this route
cannot produce the required next spatial order without new nonlinear input.

### 3. Differentiate/bootstrap the geometric PDE

The existing finite-order and all-order forcing regularity ladders start from
high base order.  In dimension three their visible hypotheses are
`2 * dim + 10 <= a` (hence `16 <= a`) and, for the later all-order ladder,
`4 * dim + 10 <= a` (hence `22 <= a`).  They also return an existential
positive `d <= T`.  They therefore neither accept the live `a = 1` solution nor
preserve its already fixed uniform horizon.

The faithful next producer is the low-base, same-horizon variable-coefficient
step.  The actual `H4 -> H2` principal operator and its measurable time-family
packaging are now available; the remaining geometric input is the
principal-subtracted `H3 -> H2` lower-order family with an `L2` time norm.
Once that family is produced, the mixed nonautonomous solver can construct the
order-two maximal-regularity solution on the same preselected `T`.

The import surface was narrowed to the cross-scale and maximal-regularity
layers actually used here.  This avoids pulling the full low-regularity
Ricci--DeTurck coefficient tree into checks of the trace package.

