# NormalBranchScale

## Role

This module is the relative-scale acceptance layer for the explicit selected
normal branch.  It combines the proportional phase-radius producer, the
fixed-`q` normal endpoint worker, and the transported intrinsic branch.

## Current state

- `normalBrHat` is the direct covering-scale inequality: if `c < a * D`, then
  `c * lambda D R < a * mu R`.
- `normalBrAccept` chooses global positive coefficients `aq`, `aδ`, and `aρ`.
  For every `R >= 0` it selects one `q = aq * mu R` and one explicit target
  radius `δ >= aδ * mu R`, uniformly before quantifying over the sequence index
  and center.
- Its `HasNormalBrFull` conclusion explicitly retains `NormalDiagFence`, the
  common consumer ball, the whole quantitative `δ` target ball in the intrinsic
  branch domain, both full transport equalities, and the inverse formula on the
  whole target and on `closedBall 0 δ`.
- `normalBrScale` is the compatibility projection to the older
  `HasNormalBranchDom` consumer interface, so existing cage code is unchanged.
- The transported intrinsic branch contains the image under `normalPair` of the
  common closed model ball of radius `aρ * mu R`.  The proof takes
  `aρ = min aδ (aq / 2)`, preserving a positive relative coefficient while
  satisfying both the target-ball and normal-coordinate source fences.
- Focused verification and the targeted module build passed without local
  warnings or local `sorry`s.  The finite-cage downstream focused check and
  targeted build also passed after refreshing this module.

## Frontier and accounting

- The architecture-2 acceptance theorem is complete: quantifier order,
  relative scales, full transport, whole-target domain, inverse formula, and
  backward-compatible consumers are all checked.
- `normalBrAccept`/`normalBrScale` are producer machinery.  `StepB1RawInput` and textbook B1 are
  still unstated and 0% complete.
- Dedicated Step-B/B1 machinery is about 77%; Chapter 4 machinery about 74%;
  whole HCG compactness machinery about 51%.  Conditional and final compactness
  endpoints remain 0%.
