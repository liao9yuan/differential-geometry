# DeTurckRemainderLowBasePair

## Role

This path is now an import compatibility shim for
`DeTurckRemainderLowBaseAction`.

## Migration

The former pair-reduced API depended on the obsolete `extraA2Act`
decomposition.  It had no declaration consumers in `DifferentialGeometry/`;
`DeTurckRemainderLowBaseZero` only used this module as a transitive import and
now imports the canonical Action module directly.

The old `pairRedA2*`, `pathA1Act`, and `remainder_path_split` declarations were
retired rather than restated with new assumptions.  Their mathematical role is
replaced by `LowBaseActionData.a2` and `remainder_low_split`; operator
completions must wait for the missing complete `C2` smallness producer.

## Verified state

Focused verification of this import shim passes against the refreshed Action
module.  The file contains no proof declarations or forbidden placeholders.
