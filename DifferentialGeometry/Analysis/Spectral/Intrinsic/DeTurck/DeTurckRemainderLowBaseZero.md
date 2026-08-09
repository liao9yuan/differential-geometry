# DeTurckRemainderLowBaseZero

## Role

This path is now an import compatibility shim for
`DeTurckRemainderLowBaseAction`.

## Migration

The former `zeroA2Act`, `zeroLowAct`, and `zeroPath_split` declarations used
the obsolete `rhsRefold2Int` and `refoldTopInt_eq` interface.  They had no
declaration consumers in `DifferentialGeometry/` and represented an earlier,
incomplete zero-head split.

Those declarations were retired rather than repaired into a competing
decomposition.  The canonical exact identity is now `remainder_low_split`,
whose `LowBaseActionData.a2` contains the complete refolded second-order
coefficient and whose `a1` is genuinely first order.

## Verified state

Focused verification of this import shim passes against the refreshed Action
module.  The file contains no proof declarations or forbidden placeholders.
