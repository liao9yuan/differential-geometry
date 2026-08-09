# CrossScaleParabolicTraceEnergy

## Result

`repr_sq_le_norms` discharges the integral in the sharp cross-scale energy
estimate by time Cauchy--Schwarz:

`||repr t||^2 <= ||repr 0||^2 + 2 ||hiL2|| ||lo.deriv||`.

The constant is independent of the time horizon.  In particular, a
zero-initial maximal-regularity Duhamel field has a uniform
`L-infinity_t H^(a+1)` representative controlled by its two `L2_t` fields.

## Role

This is the generic analytic input needed for a nonautonomous first-order
coefficient that is only `L2` in time.  It does not construct the
Ricci--DeTurck coefficient family and does not prove the uniform-existence
endpoint.

Focused verification passed without local warnings.
