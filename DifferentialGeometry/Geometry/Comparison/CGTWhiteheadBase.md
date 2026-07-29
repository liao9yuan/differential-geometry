# CGTWhiteheadBase

## State — 2026-07-28

This module is the base layer for the native localized
Cheeger--Gromov--Taylor Whitehead argument.  It supplies the complete compact
perturbation, fenced joins and launches, exact distance transfer under a
strict budget, short-launch nonconjugacy, and the pullback Jacobi endpoint
pairing used by the bigon layer.

The final base producer `exists_fenced_min` is current.  The formerly missing
general launch fence and endpoint regularity are represented by
`intrExt_shortLaunch_fenced` and `intrExt_not_conj_of_shortLaunch`; both are
consumed by `CGTWhiteheadBigon.lean`.  Direct work on the incomplete pullback
carrier and any fake completeness instance were rejected.  No global
`ConnectedSpace` hypothesis was added.

Focused verification and the exact targeted refresh passed.  This file has no
local placeholder.

Accounting:

- complete-extension/fence/distance-transfer base: theorem endpoints 100%,
  dedicated machinery 100%;
- short-launch nonconjugacy base: theorem 100%, dedicated machinery 100%;
- `intrCore_jensen`: theorem 0%; its dedicated machinery is about 93%;
- whole HCG supporting machinery: about 62%.

The next frontier is the consumer theorem `intrCore_jensen`; no further base
producer is currently known to be missing.
