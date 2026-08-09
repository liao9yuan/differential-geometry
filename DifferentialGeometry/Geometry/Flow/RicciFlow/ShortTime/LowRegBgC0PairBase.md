# LowRegBgC0PairBase

## Role

First link of the pair-estimate branch of the C0Core split.  Base two-state
lemmas: `lowOneAInt`/`lowOneADiff`/`lowOneIntSub` integral forms and the
inner-product pair estimates (`innerOnePairH2`, `innerOneBddH2`,
`innerActPairH2`) plus the `aaBlkOne` block pair lemma.

Chain position: `LowRegBgC0One → this → LowRegBgC0PairCurv`.

## Verification

Focused check + targeted `.olean` build GREEN, 2026-08-02.  Zero
sorry/admit/axiom/whnf/trace.  No notable performance hotspot.
