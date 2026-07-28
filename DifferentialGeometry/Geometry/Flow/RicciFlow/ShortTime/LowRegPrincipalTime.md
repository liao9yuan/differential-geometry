# LowRegPrincipalTime

## Purpose

This module connects the order-one low-regularity Ricci--DeTurck solve to the
actual time-dependent principal coefficient used by the order-two
nonautonomous bootstrap.

## Current status

The same-horizon intermediate representative is packaged as an honest
`timeL2 H2` field, with a canonical isometric identification between the
formal exponent `1 + 1` and the literal exponent `2`.  It agrees almost
everywhere with the direct `H3 -> H2` inclusion of the top companion field and
retains the prescribed state radius.

`lowRegA2Time` is the actual low-regularity Ricci--DeTurck principal operator
along that state.  `lowRegA2_data` chooses one positive three-dimensional
control radius and works on every smaller radius, proving strong
measurability, the sharp `C * R` operator bound, and almost-everywhere
agreement with `lowRegPrincipal` of the original top companion field.
Focused verification passed without local warnings.

`ricci_flow_unif_existence` remains unproved (0%).  This file is dedicated
machinery only.  The actual `H4 -> H2` principal time family is complete; the
next genuine geometric frontier is the principal-subtracted `H3 -> H2`
lower-order family with an `L2` time norm.
