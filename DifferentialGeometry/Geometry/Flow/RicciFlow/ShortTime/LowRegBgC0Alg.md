# LowRegBgC0Alg

## Role

Root chunk of the C0Core split (the former 12.3k-line `LowRegBgC0Core.lean`
monolith, split 2026-08-02 to resolve a real single-process OOM; monolith
backup lives in `.codex-scratch/c0core-split/`).  Holds the slot-algebra,
permutation, Koszul/MCD one-form, AMix/VB one-level operators, and the
`ricciOne`/`self_decomp` algebra layer that every later chunk consumes.

Chain position: imports `DeTurckRemainderLowBaseC2Lip` +
`DeTurckRemainderLowBaseH2Pair` (the monolith's two DeTurck roots; its third
import `LowRegBgC1Time` was intentionally NOT inherited here — no chunk uses
C1Time exports, and the two consumers that need its transitive closure import
narrowly: see `LowRegBgC0Assemble.md`, `LowRegBgC0Core.md`).  Downstream:
`LowRegBgC0Joint`.

## Verification

Focused check + targeted `.olean` build GREEN, 2026-08-02.  Zero
sorry/admit/axiom/whnf/trace.  No notable performance hotspot.
