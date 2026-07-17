# LowRegPathLower

## Role

This module packages the dimension-three Sobolev estimate for lower
Ricci--DeTurck path arms after an exact C0/C1 coefficient realization has been
constructed.

## Current state

`lower_coeff_h1` proves that a C0 coefficient with a pointwise bound and one L2
covariant derivative, together with a C1 coefficient controlled through two L2
covariant derivatives, acts from spectral H2 to spectral H1.  The theorem is
independent of any high metric Sobolev order.

Focused verification passed without local `sorry`s.  This analytic packaging
is complete, but the mixed H3-to-H1 endpoint theorem is still unstated and 0%
complete.  The Ricci pointwise coefficient producer and the public Lie C0
correction field now exist without high-order assumptions.  What remains is
the exact public lower-arm readout plus the q=0,1 uniform C3 bounds for the
resulting C0/C1 coefficient pair along the realized metric path.
