# LowRegBgC0Joint

## Role

Second chunk of the C0Core split.  Joint-continuity (`_joint`) layer for the
order-zero operators built in `LowRegBgC0Alg`: `c0j_*` parametrized-continuity
combinators, joint lemmas for trace/AMix/VB/Ricci one-level maps, the
quadratic operators (`qbOne`/`qaOne`/`quadOp`/`quadMid`/`quadAct`) with their
joint lemmas, and the `*Smul` scaling family.

Chain position: `LowRegBgC0Alg → this → LowRegBgC0Zero`.

## Verification

Focused check + targeted `.olean` build GREEN, 2026-08-02.  Zero
sorry/admit/axiom/whnf/trace.  No notable performance hotspot.
