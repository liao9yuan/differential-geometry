# LowRegBgC0One

## Role

Fourth chunk of the C0Core split and the fan-out hub.  Order-one H² layer:
`vbOne_h2`, `amixOne_h2`, the Omega family (`omegaOne_h2`,
`omegaOnePairH2`), the quadratic H² packages (`QbaH2`/`QuadOpH2`/
`QuadMidH2`/`QuadActH2` with their pair lemmas), and `lowOne_h2`/`lowOneA_h2`.

Chain position: `LowRegBgC0Zero → this`, then three independent branches all
import this hub: the Pair chain (`PairBase → PairCurv → PairDA → PairRic`),
the VB branch (`PairEst`), and the AMix branch (`Amix`).

## Verification

Focused check + targeted `.olean` build GREEN, 2026-08-02.  Zero
sorry/admit/axiom/whnf/trace.  No notable performance hotspot.
