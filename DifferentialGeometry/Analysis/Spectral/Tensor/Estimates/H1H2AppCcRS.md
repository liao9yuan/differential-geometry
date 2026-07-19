# Mixed `appCcRS` H1-H2 estimate

## Verified result

`appRS_h1_h2_h1` proves the dimension-three mixed-tensor product estimate

`H1(operator field) x H2(mixed passenger) -> H1(output)`

for `appCcRS`.  Its hypotheses are the intrinsic squared jet sums through
orders one and two, respectively.  The proof uses the mixed `H1 -> L6`
embedding, finite-volume `L6 -> L3`, the sharp pointwise jet estimate for the
passenger, and the covariant Leibniz rule.

The focused source check and the named `.olean` export pass.  The module has
no `sorry`, `admit`, or new axiom.  Warnings printed during the named build are
pre-existing replayed dependency warnings; the focused check introduces no
local warning.

## Scope

This is the abstract product producer needed by the faithful low-regularity
Ricci--DeTurck coefficient route.  It does not itself prove the concrete
`rhsLow0Coeff` or `rhsLow1Coeff` jet bounds, the mixed remainder theorem, or
uniform short-time existence.
