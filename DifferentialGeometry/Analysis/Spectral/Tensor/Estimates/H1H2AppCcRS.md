# Mixed `appCcRS` H1-H2 estimate

## Verified result

`appRS_h1_h2_h1` proves the dimension-three mixed-tensor product estimate

`H1(operator field) x H2(mixed passenger) -> H1(output)`

for `appCcRS`.  Its hypotheses are the intrinsic squared jet sums through
orders one and two, respectively.  The proof uses the mixed `H1 -> L6`
embedding, finite-volume `L6 -> L3`, the sharp pointwise jet estimate for the
passenger, and the covariant Leibniz rule.

`appRS_h1_of` is now the metric-local analytic kernel beneath that theorem.
It accepts an exact-range-three pointwise jet provider, an `H¹ -> L⁶`
coefficient provider, and an `H¹ -> L³` passenger-gradient provider.  Its
explicit coefficient is
`Cpt + (Cpt + sqrt(finrank) * CΦ * CG)`.  The original theorem has been
refactored to supply these inputs and call the kernel; its former duplicated
proof body was removed.  The public provider statement uses `fiberLpFun`, so
the private mixed-product implementation helpers remain private.

`appRS_h2_of` is the complementary supplied-provider kernel

`H2(operator field) x H1(mixed passenger) -> H1(output)`.

It takes the exact range-three pointwise provider for the operator, an
`H1 -> L6` provider for its derivative, and an `H1 -> L3` provider for the
passenger.  Its explicit coefficient is
`Cpt + (CG * CW + sqrt(finrank) * Cpt)`.  The original
`appRS_h2_h1_h1` now constructs those providers and calls the kernel; the old
duplicated proof body was removed.

`h1_jet_sq` is the public exact bridge from the `SmoothCcTensorH1` norm square
to the zeroth- and first-covariant-derivative `L2` jet sum.  It is used to
return the mixed product estimate to the coefficient-jet shape consumed by
the low-regularity Ricci--DeTurck remainder theorem.

`appRS_h2_h2_h2` is the dimension-three mixed-tensor `H2` algebra producer.
It integrates the canonical antidiagonal Leibniz grid with the existing
two-arm Gagliardo--Nirenberg estimate.  This lets the nested VB and AMix
normal forms be assembled in `H2` before the final order-zero `H1` readout.

The focused source check passes for the complete module with four Lean threads,
without local warnings or sorries.  Temporary axiom censuses for
`appRS_h1_of` and the refactored `appRS_h1_h2_h1` reported only `propext`,
`Classical.choice`, and `Quot.sound`; the prints were removed.  This also
includes the public `h1_jet_sq` bridge and `appRS_h2_h2_h2`.  The complementary
kernel and its refactored wrapper also pass the same focused four-thread check.

## Scope

This is the abstract product producer needed by the faithful low-regularity
Ricci--DeTurck coefficient route.  It does not itself prove the concrete
`rhsLow0Coeff` or `rhsLow1Coeff` jet bounds, the mixed remainder theorem, or
uniform short-time existence.
