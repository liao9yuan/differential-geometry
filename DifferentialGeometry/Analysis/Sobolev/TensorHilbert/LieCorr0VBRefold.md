# LieCorr0VBRefold

## Purpose

This module exposes the exact nested RicciFlower operator form of `lc0VB` by
combining the already checked public factorizations `lc0VB_eq_app` and
`vbSplit`.  It avoids the unfinished frame-level `LieCorr0LowJet` route and
introduces no analytic hypotheses.

## Current state

`lc0VBFormRF` and `vb_refold_rf` are implemented. Verification is pending.
