# EdgeRicciBound

## Scope

This file handles only the derivative-only part `ricciDAArm` of the
order-zero Ricci connection-difference coefficient.  It does not claim the
full `edgeRate0` estimate and it does not prove forward uniqueness.

## Source state

- `ricciPart_bds` gives pointwise zeroth- and first-covariant-derivative
  bounds for the exact partner `ricciDAPart`.
- The bounds use one relative inverse-metric insertion, so both squared fibre
  bounds retain `delta^2`.  Only `W` and `nabla W` occur.
- `ricciBase_l2` bounds the rotated lowered connection difference consumed by
  `ricciDA_green` using the public connection-difference fibre estimate and
  `connLow_rfns`.
- `ricciDA_path_le` specializes to the genuine segment `P = s W` and absorbs
  the exact `-2` multiple of the DA pairing into one eighth of the Dirichlet
  energy plus `K * ||W||^2`.
- There is no `sorry`, `admit`, or new axiom in this file.
- The tensor-symmetry step is proved locally by extensionality.  This avoids a
  declaration with the same purpose that lives outside the file's import
  closure and avoids adding a heavy downstream import.

The post-merge source passes focused verification with no local diagnostic,
and its named exact artifact is GREEN.  The proof is therefore a current
producer, not merely an unverified draft.

## Failed or rejected routes

1. Reusing `edgePairMono` was rejected: it contains two moving traces and has
   the wrong scaling.  The Ricci derivative cancellation leaves one moving
   trace.
2. Estimating `ricciDAArm` before pairing was rejected: it exposes a
   derivative of the connection difference and would require an inadmissible
   second derivative of the arbitrary edge difference.
3. A proposed cancellation with the complete order-one coefficient was not
   used.  Its five connection-action placements do not exactly match the two
   DA flux monomials; separate low-order estimates are the faithful route.

## Remaining adjacent frontier

After the exact split

`linearizedRicciConnDiffOrder0CoeffField = ricciAAArm + ricciDAArm`,

the companion quadratic and order-one Ricci estimates are supplied by
exact-current `ricciAA_path_le` and `ricci1_path_le`; the Riemann--Palatini
block is cancelled by exact-current `exists_edgeLieRef`.  The remaining
visible rate child is the non-Ricci DeTurck lower-arm pairing, followed by the
space--slope packaging.  It must be estimated jointly rather than by a
pointwise envelope for the complete `edgeRate0`.

Endpoint accounting remains unchanged:

- `ricci_flow_forward_unique`: complete and axiom-clean.
- `ricci_flow_unif_existence`: 0% as a theorem; this file is dedicated
  machinery only.
- `extends_of_rmBounded`: still depends on both missing endpoints.
