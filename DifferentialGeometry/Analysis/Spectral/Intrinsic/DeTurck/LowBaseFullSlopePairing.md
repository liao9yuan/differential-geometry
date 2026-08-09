# LowBaseFullSlopePairing

`lowBase_path_nf` is the exact state-equals-acted-state path normal form for
the complete low-base action.  It separates the top-path deviation consumed
by the class-first principal-form estimate from the corrected zero-order and
first-order paths.  It does not assert the false arbitrary-passenger refold.

`lowBase_L_nf` is the exact `1 - Δ∇` residual router.  With `P0`, `P1`, and
`P2` the three path coefficients, `K0` the carrier curvature fold, and
`LT = (1 - Δ∇)T`, it leaves

```text
B02 + (1 - Δ∇)(P1 · ∇T) + K0 · LT,

B02 = (1 - Δ∇)(P0 · T)
    + ((1 - Δ∇)(P2 · ∇²T) - P2 · ∇²LT).
```

The fixed curvature fold is therefore never differentiated.  `B02` must stay
joint: estimating its two summands separately breaks the remaining diagonal
order-zero/order-two cancellation.  The generic coefficient-commutator norm
theorem is not a replacement, since in dimension three it asks for an `H5`
coefficient-state ball.

`low0_path_refold` records the honest integrated diagonal identity

```text
P0 · T = R0 · T + Q(T) · T,
```

where `R0` is `rhsRefold0Int` and `Q(U)` is the canonical path-integrated raw
Riemann--Lie pair with arrays `ricciRefoldQA`, `ricciRefoldQB`, `lieRefoldQ`,
and `lieRefoldEps`.  Only the diagonal `U = T`, passenger `T` refold is used.

`b02_raw_nf` then gives the exact algebraic router

```text
B02 = RawComm + TopComm + Q(LT) · T + Q(T) · LT - Q(T) · T,
```

with `PairComm = L(Q(T)·T) - Q(LT)·T - Q(T)·LT + Q(T)·T`,
`RawComm = L(R0·T) + PairComm`, and the unchanged centered `TopComm`.
The off-diagonal values of `Q` are used only as an algebraic polarized kernel;
no arbitrary-`U` low-base refold is asserted.

`b02_center_nf` performs the carrier centering without discarding the pair
commutator.  With `Z = Q(T)·T`,
`Cross = Q(LT)·T + Q(T)·LT`, `C = P2 - Phi0`, and

```text
PairComm = LZ - Q(LT)·T - Q(T)·LT + Z,
J = L((R0 + K0)·T) + PairComm
    + (L(C·nabla²T) - C·nabla²LT) - Z,
```

the exact identity is `B02 + K0·LT = J + Cross`.  The terms
`PairComm - Z` are essential: omitting them would falsely assert
`L(Q(T)·T) = Cross`.  This is only an exact router and makes no estimate.

Focused verification and exact targeted refresh passed for the complete file
under the Route-(c) resource cap, with no local warning.  Thus
`low0_path_refold`, `b02_raw_nf`, and `b02_center_nf` are each 100% complete as
the exact theorems stated here.  The next genuinely analytic
producer remains separate and 0% in this file: a C3/H2-cap paired estimate for
the centered joint block,
followed by the cross-sum swap estimate and the first-order block.
Consequently `lowbase_full3_unif` and `ricci_flow_unif_existence` remain 0%;
dedicated fixed-background direct-smoothing machinery is approximately 92%,
and the whole HCG project approximately 3%.
