# LipschitzSupersolution

## Role

This module is the first-order bridge needed by the supplied-line splitting
route.  It uses the existing noncompact Lipschitz Green identity to convert the
compact-test distributional inequality into an energy inequality.  It does not
assume a Sobolev witness or add regularity to the splitting endpoint.

## Native route

For a smooth compactly supported nonnegative test function, its Riemannian
gradient is a compactly supported smooth vector field.  `lip_green_comp`
identifies the action of that vector field on the Lipschitz function with the
negative distributional Laplacian pairing.  Negating `IsLapLEDistribOn.test_le`
then gives `neg_int_le_energy`; the zero-source specialization is
`lip_energy_nonneg`.

The remaining frontier is to express this smooth-test energy inequality in a
local Euclidean chart and extend it to the `H₀¹` tests consumed by
`DeGiorgi.IsSupersolution`.  The Busemann pair is already intrinsic-Lipschitz,
so no general continuous-to-Sobolev regularity theorem is required for that
consumer.

## Verification

Focused verification passed without warnings.  No named refresh has been run
yet because no downstream module currently imports the new declarations.
