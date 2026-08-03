# LowRegBgA2Time

## Role

This module supplies the same-background complete second-order time packet for
the adjacent-scale low-regularity lift.  Its coefficient is
`LowBaseActionData.C2`, which already contains the full principal deviation
after subtraction of the fixed rough Laplacian.  It must not be added to the
older separate principal family.

## Exports

- `lowA2Bg_small` gives one positive cutoff cap and one nonnegative constant.
  At every smaller cutoff `r`, both completed coefficient maps are continuous,
  compatible, and bounded by `C * r`.
- `hiAffA2Bg` and `loAffA2Bg` freeze the same H2 radial scalar on the H4 and H3
  passenger scales.
- `hiAffA2Bg_le` and `loAffA2Bg_le` show that radializing the passenger does not
  enlarge either operator norm.
- `affA2Bg_comm` is the pointwise adjacent-scale commuting square.
- `affA2Bg_data` gives strong measurability and uniform bounds for both time
  families along any a.e. strongly measurable H3 trajectory.

## Proof route

The smooth-core pointwise and two-jet estimate comes from `c2_h2_small`; the
high/low action bounds and their core compatibility come from `a2_pair`.  The
same-background completed maps and their Lipschitz/core read-offs come from
`radialA2Bg_lip`.  Closed-set density transfers the uniform core bounds to the
whole completed H2 state space.  The time packet then uses the existing
measurability of `radialCLM` and its exact commutation with Sobolev inclusion.

## Verification

Persistent-LSP elaboration, the focused file check, and the named module
refresh are GREEN.  The file contains no `sorry`, `admit`, `axiom`, `whnf`, or
`trace`.  The focused wrapper evicted the sole file worker while retaining the
project server, so no LSP/focused memory overlap occurred.

One probe query accidentally used a line beyond the end of the file.  The
daemon correctly remained alive, but the goal RPC waited for its full cold
readiness timeout.  This was a probe-side cursor-validation issue, not Lean
elaboration or a proof-performance problem.

## Frontier and accounting

The next brick is the final same-background adjacent-scale assembly: combine
this A2 packet with `LowRegBgA1Time`, the existing static-force inclusion, and
the low affine fixed-point identity at `lowreg_realize_two` without using the
obsolete global-affine A1 or separate-principal A2 routes.

`ricci_flow_unif_existence` itself remains 0% because its endpoint placeholder
has not been proved.  Its dedicated low-regularity machinery is approximately
78% complete after this A2 packet; the whole HCG compactness project remains in
the low single digits.
