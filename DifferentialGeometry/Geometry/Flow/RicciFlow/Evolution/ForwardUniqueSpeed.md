# ForwardUniqueSpeed

## Role

This module is the invariant single-flow speed layer needed by the second term
of `gapDot_uhl`.  It keeps the speed as a genuine `(0,4)` tensor rather than a
bare raised-component carrier.

The own-lowered speed is

```text
roughLap(Rm) - 2 * bComb(Rm) - ricciDrift(Ric,Rm)
  + 2 * lowerTri(Ric,Rm)
```

with exactly the signs in the pre-Uhlenbeck evolution and in `uhlSpeed_low`.

## Source-complete declarations

- `ricciDriftOwnSq_le`: the four Ricci slot actions cost
  `16 * n^6 * |Ric|^2 * |Rm|^2`.
- `uhlSpeed04`: the intrinsic own-lowered speed tensor.
- `uhlSpeed04_low`: arbitrary-basis reconstruction of the exact four component
  terms used by `uhlSpeed_low`.
- `uhlSpeedSq_le`: the full estimate
  `8*n^6*|nabla^2 Rm|^2 + 512*n^14*|Rm|^4
    + 72*n^6*|Ric|^2*|Rm|^2`.

The constants come from nesting the standard squared-norm add/subtract bound in
the definition's actual order.  No slab constant or solution-specific
hypothesis is introduced.  The quadratic input is the canonical
`ForwardUniqueQuad.bCombSq_le`.

## Component bridge status

`uhlSpeed04_low` is the basis-independent reconstruction needed by the
component-level `uhlSpeed_low`.  `ForwardUniqueQuad.bComb_comp` supplies the
exact arbitrary-basis reading of its quadratic term.  A solution-specific
bridge can therefore be assembled from those results together with
`fuLapRm_real`, `ricciDrift_low`, and the definitions of `fuBRm` and `fuRicUp`;
this module deliberately does not import the higher `ForwardUniqueWiring`
layer.  Do not identify the supplied `B` component family with `bComb` by
definitional equality.  The `hrem` assembly audit confirmed that this interface
is sufficient; no stronger generic speed/component theorem is needed.

## Verification

Focused verification and the targeted export refresh are green and
warning-free.  The first proof pass exposed
one API-selection trap: the same-named Ricci-flow scaling lemma carries stronger
inner-product and compactness assumptions than this invariant pointwise layer.
The final proof instead imports and uses the generic tensor-layer
`Tensor0SBundle.normSq0S_smul`; no higher assumptions or heartbeat override are
needed.

## Progress

`ricci_flow_forward_unique` remains 0% until its endpoint sorry is removed.
Its dedicated machinery is about 95%; this module is one local producer inside
the final `hrem` brick.  The whole HCG-compactness program remains about 10%.
