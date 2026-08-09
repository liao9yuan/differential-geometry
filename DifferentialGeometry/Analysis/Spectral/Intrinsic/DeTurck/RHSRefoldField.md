# RHSRefoldField

## Role

This file expresses the complete order-zero Ricci--DeTurck refold after the
principal Ricci and DeTurck cancellations, before any Sobolev estimate.

## Status

`ricciRefold_eq` identifies the Ricci part with the
connection-difference field and one explicit Palatini kernel; the `AA` and
background-curvature residual fields cancel exactly.

`rhsRefold_eq` is now written as the complete six-field identity:

- Ricci connection difference;
- Ricci Palatini kernel;
- DLa;
- DLb;
- `lieCorr0`; and
- the negative DeTurck Lie pair.

The previously missing curvature-coefficient tower artifact was rebuilt
successfully.  This file then passed both focused and exact verification;
`rhsRefold_eq` is therefore 100% complete as stated and exact-current.  The
identity performs the full Ricci plus DeTurck principal cancellation before
any Sobolev estimate.

The source contains no `sorry`, `admit`, axiom declaration, or `whnf`.
